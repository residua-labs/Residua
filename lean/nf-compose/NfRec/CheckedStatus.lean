-- provenance: ours (searched: lean/nf-compose, lean/nf-rec with git grep for collectAxioms /
-- isDefEq matching / statement printer over lean/ at main c86b44eb2f — no checker of
-- obligations-table rows against the environment exists; NfRec/Table.lean only prints
-- statements, NfRec/LrcWasm0Check.lean runs the executable sanity twin).
-- closure_claim = 0.
import Lean

/-!
# CheckedStatus: proof-row status computed by the checker (atlas-check lane)

Given an obligations table (a TSV whose `lean_field` column names the field
projections of an obligations structure and whose `statement_q` column is the
sha256 of the field's printed statement, printed exactly as NfRec/Table.lean
prints it), a list of carrier namespaces, a list of proof namespaces and the
delta set of the printer, this program reports per field, from the environment
alone (stdout protocol, parsed by the caller):

* `STMT   <field> <text>`   the field's statement printed exactly as
  NfRec/Table.lean prints it (delta set expanded, width 1000000, newlines to
  spaces). The sha256 of `<text>` is the row's `q_now`; the caller takes it
  with shasum, it is not re-implemented here.
* `CARRIER <field> <name>`  a carrier for the field: a definition in a carrier
  namespace whose conclusion is defeq to the field's statement at a full
  instantiation of the structure's parameters (the plug's per-row wrapper;
  Lean itself type-checked the wrapper's body `ob.<field>` against the field
  projection at that instantiation, so the wrapper is the mechanical bridge
  from the abstract statement to the plugged one — the bridge is the kernel's
  own check, not an assumption of this program).
* `PROOF  <field> <carrier> <theorem> <axioms>` a theorem in a proof namespace
  that proves the carrier's statement: the theorem's type with every binder
  instantiated by a metavariable is defeq to the carrier's conclusion, and
  every metavariable of the applied theorem is assigned by that defeq, so the
  applied theorem is a complete proof term of the carrier's statement (a
  helper whose hypothesis the match does not supply is rejected). `<axioms>`
  is `Lean.collectAxioms`'s answer, `;`-joined (`-` if none).
* `REFUTE <field> <carrier> <theorem> <axioms>` the same match against the
  negation of the carrier's statement (a machine-checked counterexample).
* `NOFIELD <field> <name>`  the table names a constant the environment lacks.

All matching happens inside the carrier's own binder context, so a
metavariable assignment can only mention what the carrier's statement
mentions. The program names no field, no structure and no table: everything
comes from `Config`, which the generated driver supplies. Statuses
(checked / open / stale-statement / nonstandard-axioms / refuted) are
assembled by the caller from these lines.
-/

namespace NfRec.CheckedStatus

open Lean Lean.Meta Lean.Elab Command

/-- configuration of one table run; supplied by the generated driver -/
structure Config where
  /-- the obligations TSV, relative to the run's working directory -/
  table : String
  /-- namespaces scanned for carrier definitions (the plug's wrappers) -/
  carriers : List Name
  /-- namespaces scanned for candidate theorems (the proof modules) -/
  proofs : List Name
  /-- constants delta-expanded when printing statements (Table.lean's set) -/
  delta : List Name

/-- the theorem-shaped constants -/
def isThm (ci : ConstantInfo) : Bool :=
  match ci with
  | .thmInfo _ => true
  | _ => false

/-- the definition-shaped constants -/
def isDefn (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => true
  | _ => false

/-- is `n` under namespace `ns`? (structural prefix of name components) -/
def underNs (n : Name) (ns : Name) : Bool :=
  ns == n || ns.isPrefixOf n

/-- skip internal, private and example names -/
def reportable (n : Name) : Bool :=
  !n.isInternal
  && !n.components.any (fun s => s.toString == "example")

/-- all reportable constants under one of `nss`, of the given shape -/
def scan (nss : List Name) (shape : ConstantInfo → Bool) : MetaM (Array Name) := do
  let env ← getEnv
  let mut out : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if shape ci && reportable n && nss.any (fun ns => underNs n ns) then
      out := out.push n
  return out

partial def peelLoop (e : Expr) (ty : Expr) : MetaM (Expr × Expr) := do
  match ty with
  | .forallE _ d b _ =>
      let m ← mkFreshExprMVar d
      peelLoop (mkApp e m) (b.instantiate1 m)
  | _ => return (e, ty)

/-- peel every syntactic `∀` binder of `c`'s type by a fresh metavariable.
Returns the constant applied to the metavariables and the remaining body (the
statement at those metavariables). No `whnf`: a statement body that is itself
a definition applied to arguments (`LinkRow …`) is not unfolded here. -/
def peelWithMetas (c : Name) : MetaM (Expr × Expr) := do
  let e ← mkConstWithFreshMVarLevels c
  let ci ← getConstInfo c
  peelLoop e ci.type

/-- `true` iff the fully instantiated `e` still contains an expression
metavariable: an unassigned hypothesis of a theorem, or a structure parameter
the statement itself does not pin -/
def incomplete (e : Expr) : MetaM Bool := do
  return (← instantiateMVars e).hasExprMVar

/-- run `x`, answer `none` on any error -/
def attempt {α} (x : MetaM α) : MetaM (Option α) := do
  try
    return some (← x)
  catch _ =>
    return none

/-- what a theorem candidate did against a carrier statement -/
inductive Match where
  /-- neither proves nor refutes -/
  | no
  /-- defeq but the applied theorem kept a metavariable -/
  | incomplete
  /-- proves the carrier's statement -/
  | proof (t : Name)
  /-- proves the carrier statement's negation -/
  | refute (t : Name)

/-- match one theorem against one carrier conclusion (in the carrier's
binder context) -/
def matchThm (concl : Expr) (t : Name) : MetaM Match := do
  let (tapp, cty) ← peelWithMetas t
  if ← isDefEq concl cty then
    if ← incomplete tapp then return .incomplete
    return .proof t
  else if ← isDefEq (mkApp (mkConst ``Not) concl) cty then
    if ← incomplete tapp then return .incomplete
    return .refute t
  else
    return .no

/-- one field's report -/
structure FieldReport where
  field : String
  stmt : String
  carriers : Array Name := #[]
  /-- carrier, theorem, axioms -/
  proofs : Array (Name × Name × String) := #[]
  refutes : Array (Name × Name × String) := #[]

/-- check one field: print its statement, find carriers, find provers and
refuters. A carrier matches when its conclusion is the field's statement at a
full instantiation of the structure's parameters; a theorem matches when it
proves (or refutes) that conclusion by specialization. -/
def checkField (deltaPred : Name → Bool) (thms : Array Name)
    (carriersAll : Array Name) (field : String) (projName : Name) :
    MetaM FieldReport := do
  -- the statement text: Table.lean's printing, verbatim
  let ci ← getConstInfo projName
  let ty ← deltaExpand ci.type deltaPred
  let fmt ← ppExpr ty
  let text := (fmt.pretty 1000000).replace "\n" " "
  let mut rep : FieldReport := { field := field, stmt := text }
  for carrier in carriersAll do
    let cci ← getConstInfo carrier
    let res? ← attempt (forallTelescope cci.type fun _fvars concl => do
      -- (a) the carrier's conclusion is the field statement at a full
      --     instantiation of the structure's parameters
      let (_p, stmt) ← peelWithMetas projName
      unless ← isDefEq stmt concl do
        throwError "carrier conclusion is not the field statement"
      if ← incomplete stmt then
        throwError "field statement not pinned by the carrier"
      -- (b) theorems proving, or refuting, the carrier's statement
      let mut proofs : Array (Name × Name × String) := #[]
      let mut refutes : Array (Name × Name × String) := #[]
      for t in thms do
        match ← matchThm concl t with
        | .proof t =>
            let axs ← collectAxioms t
            let ax := String.intercalate ";" (axs.toList.map toString)
            proofs := proofs.push (carrier, t, ax)
        | .refute t =>
            let axs ← collectAxioms t
            let ax := String.intercalate ";" (axs.toList.map toString)
            refutes := refutes.push (carrier, t, ax)
        | _ => pure ()
      return (proofs, refutes))
    match res? with
    | some (proofs, refutes) =>
        if !(proofs.isEmpty && refutes.isEmpty) then
          rep := { rep with carriers := rep.carriers.push carrier,
                             proofs := rep.proofs.append proofs,
                             refutes := rep.refutes.append refutes }
    | none => pure ()
  return rep

/-- is `s` a 64-digit hex string (a listed statement q)? -/
def isQ (s : String) : Bool :=
  s.length == 64 && s.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

/-- parse the table: (field, projection name, listed q) per row. The
`lean_field` column is the last, `statement_q` the third. -/
def parseTable (cfg : Config) : IO (Array (String × Name × String)) := do
  let txt ← IO.FS.readFile cfg.table
  let mut rows : Array (String × Name × String) := #[]
  let mut first := true
  for line in txt.splitOn "\n" do
    if line.isEmpty then
      continue
    if first then
      first := false
      continue
    let cols := line.splitOn "\t"
    if cols.length < 3 then
      continue
    let lf := cols[cols.length - 1]!.trim
    let q := cols[2]!.trim
    unless (lf.splitOn ".").length > 1 && isQ q do
      continue
    let n := (lf.splitOn ".").foldl (fun acc s => .str acc s) .anonymous
    let field := lf.splitOn "." |>.getLastD ""
    rows := rows.push (field, n, q)
  return rows

/-- run one table: emit the protocol lines on stdout -/
def run (cfg : Config) : CommandElabM Unit := do
  let rows ← liftIO (parseTable cfg)
  let deltaPred (n : Name) : Bool := cfg.delta.contains n
  let codes ← liftTermElabM do
    let carriersAll ← scan cfg.carriers isDefn
    let thms ← scan cfg.proofs isThm
    let mut bad := 0
    for (field, projName, _q) in rows do
      match ← attempt (getConstInfo projName) with
      | none =>
          IO.println s!"NOFIELD\t{field}\t{projName}"
          bad := bad + 1
      | some _ =>
          let rep ← checkField deltaPred thms carriersAll field projName
          IO.println s!"STMT\t{rep.field}\t{rep.stmt}"
          for c in rep.carriers do
            IO.println s!"CARRIER\t{rep.field}\t{c}"
          for (c, t, a) in rep.proofs do
            let ax := if a.isEmpty then "-" else a
            IO.println s!"PROOF\t{rep.field}\t{c}\t{t}\t{ax}"
          for (c, t, a) in rep.refutes do
            let ax := if a.isEmpty then "-" else a
            IO.println s!"REFUTE\t{rep.field}\t{c}\t{t}\t{ax}"
    return bad
  IO.println s!"DONE\t{rows.size}\tbad={codes}"

end NfRec.CheckedStatus

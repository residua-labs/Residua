import Lean
import rcic.RcicFabricQ
import rcic.RcicFabricPatch
import rcic.RcicEnv

/-!
# Agent proof fabric — the per-declaration fact index (C2) as a producer

ADR draft #7925 §3 C2; plan #7929 P1.2. **Tooling, not sealed, not imported by any seal.** It is the
executable `rcic-fabric-index` (own `lean_exe` block). It loads a list of modules from compiled `.olean`
files, walks every declaration whose module is in the `rcic` namespace, and prints one JSON record per
declaration (fields sorted, records sorted by name):

```text
{ "name", "module", "kind", "stmt_q" | null, "body_q" | null, "axioms": [..],
  "stmt_error"?: residue, "body_error"?: residue,
  "edge": null | { "premises": [goal_q..], "conclusion": goal_q,
                   "premise_names": [name | null ..], "conclusion_name": name | null, "context": k } }
```

- `stmt_q` / `body_q` are `Rcic.Fabric.Q.stmtQ` / `bodyQ` (`RcicFabricQ`): the import lane's encoding
  (#7927, `trExpr` + `Rcic.LeanImport.stmtQ` / `bodyQ`) composed with a per-declaration reference table.
  The producer calls those definitions directly; it has no encoding of its own and no cache. A term
  the import translation refuses carries the import lane's residue (`stmt_error` / `body_error`), and
  a term whose tree is larger than `--payload-bound` nodes carries `[fabric_payload_bound]` (#7927's
  payload is a flat string of the unshared tree, so its size is the tree size, not the DAG size).
- `axioms` is the axiom closure, with the reachability of `Lean.CollectAxioms` (type, value, inductive
  constructors), computed with ONE memo table shared by every declaration. `--check-axioms N` compares it
  with a fresh `CollectAxioms` run on `N` declarations (a measurement of the shared memo, nothing more).
- `edge` is set on a theorem `∀ (x₁ … x_k), P₁ → … → Pₙ → G` (n ≥ 1) whose leading binders `x` are not
  propositions (the *context*) and whose premises are non-dependent propositions. Every premise and the
  conclusion must be either closed (its `goal_q` is its `stmt_q`) or a constant fully applied to
  distinct context variables (its `goal_q` is the `goal_q` of that constant's universal closure, as
  for goal candidates). With `k = 0` this is the closed arrow chain of slice 1. A context edge is a
  pointwise implication: at every context, the premises imply the conclusion.

`closure_claim = 0`.
-/

namespace Rcic.Fabric.Index

open Lean

def residuePayloadBound : String := "[fabric_payload_bound]"

/-- Tree size without sharing, stopping at `bound`. -/
partial def treeSizeLe (bound : Nat) (e : Expr) : Option Nat :=
  go e 0
where
  go (e : Expr) (acc : Nat) : Option Nat :=
    if acc > bound then none else
    match e with
    | .app f a => go f (acc + 1) >>= go a
    | .lam _ t b _ | .forallE _ t b _ => go t (acc + 1) >>= go b
    | .letE _ t v b _ => go t (acc + 1) >>= go v >>= go b
    | .mdata _ e | .proj _ _ e => go e (acc + 1)
    | _ => some (acc + 1)

/-- One of `Rcic.Fabric.Q.stmtQ` / `bodyQ`, on a term of at most `bound` nodes (translation fuel
`bound + 1`, which exceeds any depth of such a term). -/
def boundedQ (bound : Nat) (f : Nat → List Name → Expr → Except String String) (ps : List Name)
    (e : Expr) : Except String String :=
  match treeSizeLe bound e with
  | none => .error residuePayloadBound
  | some _ => f (bound + 1) ps e

/-! ## Axiom closure with one shared memo -/

/-- The constants `Lean.CollectAxioms` follows from a declaration. -/
def followed (ci : ConstantInfo) : Array Name :=
  match ci with
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

abbrev AxMemo := Std.HashMap Name (Array Name)

def sortNames (xs : Array Name) : Array Name :=
  xs.qsort (fun a b => a.toString < b.toString)

def union (a b : Array Name) : Array Name :=
  b.foldl (fun acc x => if acc.contains x then acc else acc.push x) a

/-- Axiom closure of `root`: Tarjan's strongly connected components over the constant graph,
iteratively (explicit frame stack) so deep dependency chains cannot exhaust the stack. The memo is
shared by every query and holds only **completed** closures: a node is memoized exactly when its whole
SCC is, and every member of an SCC gets the same closure (the union of its members' own axiom and of
the closures of every successor outside the SCC, all of which are already memoized). Cycles are
ordinary: an inductive type refers to its constructors and they refer back to it. A node on the
current DFS stack is never given a closure early, so no query order can record a partial one.
Cost is linear in the newly explored part of the graph. A constant absent from `env` contributes
nothing. -/
def axiomsOf (env : Environment) (root : Name) : StateM AxMemo (Array Name) := do
  if (← get).contains root then return (← get).getD root #[]
  let mut idx : Std.HashMap Name Nat := {}
  let mut low : Std.HashMap Name Nat := {}
  let mut onT : Std.HashSet Name := {}
  let mut tstack : Array Name := #[]
  -- frame: (node, its successors, next successor to look at)
  let mut frames : Array (Name × Array Name × Nat) := #[]
  let mut pending : Option Name := some root
  let mut counter := 0
  while pending.isSome || frames.size > 0 do
    if let some c := pending then
      pending := none
      match env.find? c with
      | none => pure ()
      | some ci =>
          idx := idx.insert c counter
          low := low.insert c counter
          counter := counter + 1
          tstack := tstack.push c
          onT := onT.insert c
          frames := frames.push (c, followed ci, 0)
      continue
    let (c, kids, i) := frames.back!
    if i < kids.size then
      frames := frames.set! (frames.size - 1) (c, kids, i + 1)
      let k := kids[i]!
      if (← get).contains k || (env.find? k).isNone then continue
      if let some ik := idx[k]? then
        -- already discovered in this query: a back/cross edge matters only while `k` is still open
        if onT.contains k then low := low.insert c (min (low.getD c 0) ik)
      else
        pending := some k
    else
      frames := frames.pop
      let lc := low.getD c 0
      if lc == idx.getD c 0 then
        -- `c` roots an SCC: pop its members and close them together
        let mut members : Array Name := #[]
        repeat
          let m := tstack.back!
          tstack := tstack.pop
          onT := onT.erase m
          members := members.push m
          if m == c then break
        let mut acc : Array Name := #[]
        for m in members do
          if let some ci := env.find? m then
            if let .axiomInfo _ := ci then acc := union acc #[m]
            for k in followed ci do
              if let some r := (← get)[k]? then acc := union acc r
        let closed := sortNames acc
        for m in members do
          modify (·.insert m closed)
      if let some (p, _, _) := frames.back? then
        low := low.insert p (min (low.getD p 0) lc)
  return (← get).getD root #[]

/-! ## Edge view (slice 2 reads it; slice 1 only emits it) -/

/-- Syntactic proposition test: after a `∀` telescope, the head constant's declared type ends in
`Prop`. Sound for the purpose of labelling a premise; it never reads a proof. -/
partial def isPropSyn (env : Environment) (e : Expr) : Bool :=
  match e.consumeMData with
  | .forallE _ _ b _ => isPropSyn env b
  | e =>
    match e.getAppFn.consumeMData with
    | .const c _ =>
        match env.find? c with
        | some ci => endsInProp ci.type
        | none => false
    | _ => false
where
  endsInProp : Expr → Bool
    | .forallE _ _ b _ => endsInProp b
    | .mdata _ e => endsInProp e
    | .sort .zero => true
    | _ => false

/-- Arity of a `Prop`-valued telescope. -/
def propArity? (t : Expr) : Option Nat := go t 0
where
  go : Expr → Nat → Option Nat
    | .forallE _ _ b _, k => go b (k + 1)
    | .mdata _ e, k => go e k
    | .sort .zero, k => some k
    | _, _ => none

/-- `∀ xs, W xs` over `W`'s own type telescope. -/
def closureOf (c : Name) (ps : List Name) (t : Expr) : Expr := go t 0
where
  go : Expr → Nat → Expr
    | .forallE n d b bi, i => .forallE n d (go b (i + 1)) bi
    | .mdata _ e, i => go e i
    | _, i => mkAppN (.const c (ps.map Level.param)) ((List.range i).reverse.map Expr.bvar).toArray

/-- `∀ (x₁ … x_k), P₁ → … → Pₙ → G`: the context size `k`, the premises and the conclusion (premises
and conclusion keep their loose variables, which refer to the context). -/
partial def edgeShape (env : Environment) (e : Expr) : Nat × Array Expr × Expr :=
  ctx e 0
where
  ctx (e : Expr) (k : Nat) : Nat × Array Expr × Expr :=
    match e.consumeMData with
    | .forallE _ t b _ => if isPropSyn env t then prem e k #[] else ctx b (k + 1)
    | e => (k, #[], e)
  prem (e : Expr) (k : Nat) (ps : Array Expr) : Nat × Array Expr × Expr :=
    match e.consumeMData with
    | .forallE _ t b _ =>
        if !b.hasLooseBVar 0 && isPropSyn env t then prem (b.lowerLooseBVars 1 1) k (ps.push t)
        else (k, ps, e)
    | e => (k, ps, e)

/-- A premise or conclusion as a goal: closed (its own statement), or a constant fully applied to
distinct context variables (that constant's universal closure). -/
def goalOf? (env : Environment) (bound : Nat) (ps : List Name) (p : Expr) :
    Option (Except String String × Option Name) :=
  if !p.hasLooseBVars then
    let nm := match p.consumeMData with | .const c _ => some c | _ => none
    some (boundedQ bound Rcic.Fabric.Q.stmtQ ps p, nm)
  else
    match p.consumeMData.getAppFn with
    | .const c _ =>
        let args := p.consumeMData.getAppArgs
        let idx := args.filterMap fun a => match a with | .bvar i => some i | _ => none
        let distinct := idx.toList.eraseDups.length == idx.size
        match env.find? c with
        | some ci =>
            if idx.size == args.size && distinct && propArity? ci.type == some args.size then
              some (boundedQ bound Rcic.Fabric.Q.goalQ ci.levelParams
                (closureOf c ci.levelParams ci.type), some c)
            else none
        | none => none
    | _ => none

/-! ## Records -/

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "recursor"
  | .inductInfo _ => "inductive"

def valueOf? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

def isRcicModule (m : Name) : Bool := m.getRoot == `rcic

structure Opts where
  modulesFile : String := ""
  out : String := ""
  checkAxioms : Nat := 0
  goalsFrom : String := ""
  payloadBound : Nat := 200000
  exportScm : Nat := 0
  exportBound : Nat := 2000
  patchModules : String := ""

def parseArgs : List String → Opts → Opts
  | "--modules" :: f :: r, o => parseArgs r { o with modulesFile := f }
  | "--out" :: f :: r, o => parseArgs r { o with out := f }
  | "--check-axioms" :: n :: r, o => parseArgs r { o with checkAxioms := n.toNat! }
  | "--goals-from" :: f :: r, o => parseArgs r { o with goalsFrom := f }
  | "--payload-bound" :: n :: r, o => parseArgs r { o with payloadBound := n.toNat! }
  | "--export-scm" :: n :: r, o => parseArgs r { o with exportScm := n.toNat! }
  | "--export-bound" :: n :: r, o => parseArgs r { o with exportBound := n.toNat! }
  | "--patch-modules" :: f :: r, o => parseArgs r { o with patchModules := f }
  | _ :: r, o => parseArgs r o
  | [], o => o

def jstr (s : String) : Json := Json.str s

/-- Canonical JSON object: keys sorted (byte order), values compact. -/
def renderObj (kvs : List (String × String)) : String :=
  let kvs := kvs.toArray.qsort (fun a b => a.1 < b.1)
  "{" ++ ",".intercalate (kvs.toList.map fun (k, v) => (Json.str k).compress ++ ":" ++ v) ++ "}"
def jnames (xs : Array Name) : Json := Json.arr (xs.map (fun n => Json.str n.toString))


/-! ## Goals (slice 1 step 4): candidate goals and their state, read off the fact index

A *goal candidate* is a `def` in an `rcic` module whose type telescope ends in `Prop`, and which is
either closed (arity 0: the definition *is* a statement) or a named wall (its last name component
contains `Wall`, `Remaining` or `Stmt`, the R-CIC naming of named open premises). Its goal is the
universal closure `∀ xs, W xs`, hashed by `goalQ` under `W`'s own level parameters; `goal_q_unfolded`
hashes `∀ xs, body` when the value is a lambda telescope of the same arity, so a theorem that states
the body directly is also found. The state is read off the index, never asserted:
- `proved` — some theorem's `stmt_q` equals `goal_q` or `goal_q_unfolded`;
- `refuted` — some theorem concludes `¬ W args` (or `W args → False`); `scope` is `instance` when the
  refuting theorem has no leading binders, `family` otherwise;
- `open` — neither. -/

/-- `fun xs => body` with exactly `k` leading lambdas, as `∀ xs, body`. -/
def lamToForall : Expr → Nat → Option Expr
  | e, 0 => some e
  | .lam n d b bi, k + 1 => (lamToForall b k).map (fun b' => .forallE n d b' bi)
  | .mdata _ e, k => lamToForall e k
  | _, _ => none

def wallTokens : List String := ["Wall", "Remaining", "Stmt"]

def isNamedWall (n : Name) : Bool :=
  match n with
  | .str _ s => wallTokens.any (fun t => (s.splitOn t).length > 1)
  | _ => false

/-- The negated proposition of a conclusion `¬ X` or `X → False`, after a `∀` telescope; with the
number of binders peeled. -/
partial def negatedConcl (e : Expr) (k : Nat := 0) : Option (Expr × Nat) :=
  match e.consumeMData with
  | .app (.const ``Not _) x => some (x, k)
  | .forallE _ x (.const ``False _) _ => some (x, k)
  | .forallE _ _ b _ => negatedConcl b (k + 1)
  | _ => none

def goalsMain (env : Environment) (bound : Nat) (factsFile out : String) : IO UInt32 := do
  -- stmt_q → theorem names, from the fact index
  let mut byStmt : Std.HashMap String (Array String) := {}
  for line in ← IO.FS.lines factsFile do
    if line.isEmpty then continue
    let some j := (Json.parse line).toOption | IO.eprintln "[fabric_goals_bad_fact_line]"; return 5
    let kind := (j.getObjValAs? String "kind").toOption.getD ""
    if kind != "theorem" then continue
    let some q := (j.getObjValAs? String "stmt_q").toOption | continue
    let nm := (j.getObjValAs? String "name").toOption.getD ""
    byStmt := byStmt.insert q ((byStmt.getD q #[]).push nm)
  let modOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)
  -- candidates
  let mut cands : Array (Name × Nat × String) := #[]
  for (n, ci) in env.constants.toList do
    let some m := modOf n | continue
    if !isRcicModule m || n.isInternal then continue
    let .defnInfo v := ci | continue
    let some k := propArity? v.type | continue
    let src := if k == 0 then "closed_prop" else if isNamedWall n then "named_wall" else ""
    if src.isEmpty then continue
    cands := cands.push (n, k, src)
  let candSet : Std.HashSet Name := cands.foldl (fun s (n, _, _) => s.insert n) {}
  -- refutations: theorems concluding ¬ W args
  let mut refuters : Std.HashMap Name (Array (String × String)) := {}
  for (n, ci) in env.constants.toList do
    let some m := modOf n | continue
    if !isRcicModule m || n.isInternal then continue
    let .thmInfo v := ci | continue
    let some (x, k) := negatedConcl v.type | continue
    let .const w _ := x.getAppFn.consumeMData | continue
    if !candSet.contains w then continue
    let scope := if k == 0 then "instance" else "family"
    refuters := refuters.insert w ((refuters.getD w #[]).push (n.toString, scope))
  let h ← IO.FS.Handle.mk out .write
  let mut lines : Array (String × String) := #[]
  for (n, k, src) in cands do
    let some (.defnInfo v) := env.find? n | continue
    let ps := v.levelParams
    let cl := closureOf n ps v.type
    let unf := lamToForall v.value k
    -- the unfolded form is optional: its refusal (e.g. a string literal in the body) leaves `goal_q`
    let guE : Option (Except String String) := unf.map (boundedQ bound Rcic.Fabric.Q.goalQ ps)
    let res : Except String (String × Option String) := do
      let g ← boundedQ bound Rcic.Fabric.Q.goalQ ps cl
      pure (g, match guE with | some (.ok u) => some u | _ => none)
    let js (x : String) : String := (Json.str x).compress
    match res with
    | .error r =>
        lines := lines.push (n.toString, renderObj [("name", js n.toString), ("arity", toString k),
          ("source", js src), ("goal_q", "null"), ("error", js r)])
    | .ok (g, gu) =>
        let provers := (byStmt.getD g #[]) ++ (match gu with | some u => byStmt.getD u #[] | none => #[])
        let refs := refuters.getD n #[]
        let state := if !provers.isEmpty && !refs.isEmpty then "conflict"
          else if !provers.isEmpty then "proved" else if !refs.isEmpty then "refuted" else "open"
        let m := (modOf n).getD .anonymous
        lines := lines.push (n.toString, renderObj [
          ("name", js n.toString), ("module", js m.toString), ("arity", toString k),
          ("source", js src), ("goal_q", js g),
          ("goal_q_unfolded", match gu with | some u => js u | none => "null"),
          ("goal_q_unfolded_error", match guE with | some (.error r) => js r | _ => "null"),
          ("state", js state),
          ("proved_by", (Json.arr (provers.qsort (· < ·) |>.map Json.str)).compress),
          ("refuted_by", (Json.arr (refs.qsort (fun a b => a.1 < b.1) |>.map fun (r, sc) =>
              Json.mkObj [("scope", Json.str sc), ("theorem", Json.str r)])).compress)])
  for (_, l) in lines.qsort (fun a b => a.1 < b.1) do
    h.putStrLn l
  h.flush
  IO.eprintln s!"goals: {cands.size} candidates, {refuters.size} with refutations"
  return 0

/-! ## Export for the cross-engine agreement check (plan #7929 P1.1)

`--export-scm N` writes a corpus for #7927's scm encoder `rcic.lean_import_tr_enc_expr`: for the first
`N` declarations in name order whose type has at most `--export-bound` nodes and translates, the type
in the scm expression wire (`bvar` / `const` / `app` / `lam` / `pi` / `let` / `sort` / `lit` /
`mdata`), the reference binding (`export_id` = 1000 + position, `member_ref` = position, the table of
`Rcic.Fabric.Q.localResolve`), and as `expected` the record `{ok: 1, text: encExpr t', code: ""}`
where `t'` is the Lean translation. Running the scm encoder on that corpus compares the two engines'
encodings byte for byte. -/

def vInt (n : Nat) : Json := Json.mkObj [("tag", "int"), ("n", (n : Int))]
def vStr (s : String) : Json := Json.mkObj [("tag", "str"), ("s", s)]
def vList (xs : Array Json) : Json := Json.mkObj [("tag", "list"), ("xs", Json.arr xs)]
def vRec (kvs : List (String × Json)) : Json :=
  let kvs := kvs.toArray.qsort (fun a b => a.1 < b.1)
  Json.mkObj [("tag", "record"), ("kvs", Json.arr (kvs.map fun (k, v) => Json.arr #[Json.str k, v]))]

partial def levelWire (ps : List Name) : Level → Json
  | .zero => vRec [("tag", vStr "zero")]
  | .succ l => vRec [("tag", vStr "succ"), ("a", levelWire ps l)]
  | .max a b => vRec [("tag", vStr "max"), ("a", levelWire ps a), ("b", levelWire ps b)]
  | .imax a b => vRec [("tag", vStr "imax"), ("a", levelWire ps a), ("b", levelWire ps b)]
  | .param n => vRec [("tag", vStr "param"), ("i", vInt ((Rcic.LeanImport.indexOfName ps n).getD 0))]
  | .mvar _ => vRec [("tag", vStr "mvar")]

partial def exprWire (ps : List Name) (refs : List Name) : Expr → Json
  | .bvar i => vRec [("tag", vStr "bvar"), ("i", vInt i)]
  | .fvar _ => vRec [("tag", vStr "fvar")]
  | .mvar _ => vRec [("tag", vStr "mvar")]
  | .sort u => vRec [("tag", vStr "sort"), ("a", levelWire ps u)]
  | .const n us =>
      if Rcic.LeanImport.isQuotName n then vRec [("tag", vStr "quot")] else
      vRec [("tag", vStr "const"), ("i", vInt (1000 + (Rcic.LeanImport.indexOfName refs n).getD 0)),
        ("levels", vList (us.toArray.map (levelWire ps)))]
  | .app f x => vRec [("tag", vStr "app"), ("a", exprWire ps refs f), ("b", exprWire ps refs x)]
  | .lam _ t b _ => vRec [("tag", vStr "lam"), ("a", exprWire ps refs t), ("b", exprWire ps refs b)]
  | .forallE _ t b _ => vRec [("tag", vStr "pi"), ("a", exprWire ps refs t), ("b", exprWire ps refs b)]
  | .letE _ t v b _ => vRec [("tag", vStr "let"), ("a", exprWire ps refs t), ("b", exprWire ps refs v),
      ("c", exprWire ps refs b)]
  | .lit (.natVal k) => vRec [("tag", vStr "lit"), ("s", vStr "nat"), ("i", vInt k)]
  | .lit (.strVal _) => vRec [("tag", vStr "lit"), ("s", vStr "str"), ("i", vInt 0)]
  | .mdata _ e => vRec [("tag", vStr "mdata"), ("inner", exprWire ps refs e)]
  | .proj _ _ _ => vRec [("tag", vStr "proj")]

def exportMain (env : Environment) (names : Array Name) (o : Opts) : IO UInt32 := do
  let mut rows : Array Json := #[]
  let mut skipBig := 0
  let mut skipRefused := 0
  for n in names do
    if rows.size ≥ o.exportScm then break
    let some ci := env.find? n | continue
    let ps := ci.levelParams
    if (treeSizeLe o.exportBound ci.type).isNone then
      skipBig := skipBig + 1
      continue
    let refs := Rcic.Fabric.Q.refsOf ci.type
    match Rcic.LeanImport.trExpr (o.exportBound + 1) ps (Rcic.Fabric.Q.localResolve refs) ci.type with
    | .error _ => skipRefused := skipRefused + 1
    | .ok t' =>
        let binding := (List.range refs.length).toArray.map fun i =>
          vRec [("export_id", vInt (1000 + i)), ("member_ref", vInt i)]
        rows := rows.push (Json.mkObj [
          ("label", Json.str n.toString),
          ("env", Json.mkObj [("expr", exprWire ps refs ci.type), ("binding", vList binding),
            ("fuel", vInt (o.exportBound + 1))]),
          ("expected", vRec [("code", vStr ""), ("ok", vInt 1),
            ("text", vStr (Rcic.LeanImport.encExpr t'))])])
  IO.FS.writeFile o.out ((Json.arr rows).pretty ++ "\n")
  IO.eprintln s!"export: {rows.size} rows; skipped {skipBig} over {o.exportBound} nodes, {skipRefused} refused by the translation"
  return 0

/-! ## Conflux patch proposals (`--patch-modules FILE`)

For every declaration of the listed modules, one proposal with the two fields the fabric supplies to a
Conflux P2 patch (`RcicFabricPatch`): `expected_q` (statement, the constants its statement and evidence
mention with their class and `q`, axiom closure; a structure projection function is class `proj`, by
`stmt_q`: its body is generated from its structure and is a projection, which #7927 refuses) and `new_subtree_q` (the fact). `target_goal_q` names
the goal the fact is for; Conflux's target addressing for a fact is undefined (see `RcicFabricPatch`). A
dependency whose `q` the import encoding refuses makes the proposal carry `expected_error` naming it. -/

abbrev DepMemo := Std.HashMap Name (Except String Rcic.Fabric.Patch.Dep)

def depOf (env : Environment) (bound : Nat) (c : Name) : StateM DepMemo (Except String Rcic.Fabric.Patch.Dep) := do
  if let some d := (← get)[c]? then return d
  let d : Except String Rcic.Fabric.Patch.Dep := match env.find? c with
    | none => .error s!"{c}: not in environment"
    | some ci =>
      let ps := ci.levelParams
      let mk (cls : String) (r : Except String String) : Except String Rcic.Fabric.Patch.Dep :=
        match r with
        | .ok q => .ok ⟨cls, c.toString, q⟩
        | .error e => .error s!"{c}: {e}"
      if env.isProjectionFn c then mk "proj" (boundedQ bound Rcic.Fabric.Q.stmtQ ps ci.type) else
      match ci with
      | .defnInfo v => mk "delta" (boundedQ bound Rcic.Fabric.Q.bodyQ ps v.value)
      | .thmInfo _ | .opaqueInfo _ => mk "logical" (boundedQ bound Rcic.Fabric.Q.stmtQ ps ci.type)
      | _ => mk "type" (boundedQ bound Rcic.Fabric.Q.stmtQ ps ci.type)
  modify (·.insert c d)
  return d

def patchMain (env : Environment) (o : Opts) : IO UInt32 := do
  let mods := (← IO.FS.lines o.patchModules).filter (!·.isEmpty) |>.map String.toName
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    match env.getModuleIdxFor? n with
    | some idx => if mods.contains env.header.moduleNames[idx.toNat]! && !n.isInternal then acc.push n else acc
    | none => acc
  let names := names.qsort (fun a b => a.toString < b.toString)
  let h ← IO.FS.Handle.mk o.out .write
  let mut axMemo : AxMemo := {}
  let mut memo : DepMemo := {}
  let mut nOk := 0
  let mut nErr := 0
  let js (x : String) : String := (Json.str x).compress
  for n in names do
    let some ci := env.find? n | continue
    let ps := ci.levelParams
    let (axs, m1) := (axiomsOf env n).run axMemo
    axMemo := m1
    let axStrs := axs.toList.map Name.toString
    let refs := match valueOf? ci with
      | some v => Rcic.Fabric.Q.refsAcc v (Rcic.Fabric.Q.refsOf ci.type)
      | none => Rcic.Fabric.Q.refsOf ci.type
    let refs := refs.filter (· != n)
    let (deps, m2) := (refs.mapM (depOf env o.payloadBound)).run memo
    memo := m2
    let mut kvs : List (String × String) := [("name", js n.toString), ("kind", js (kindOf ci)),
      ("n_deps", toString refs.length)]
    let stmt := boundedQ o.payloadBound Rcic.Fabric.Q.stmtQ ps ci.type
    let body : Except String String := match valueOf? ci with
      | some v => boundedQ o.payloadBound Rcic.Fabric.Q.bodyQ ps v
      | none => .ok ""
    match stmt, body, deps.mapM id with
    | .ok sq, .ok bq, .ok ds =>
        nOk := nOk + 1
        kvs := kvs ++ [("target_goal_q", js sq),
          ("expected_q", js (Rcic.Fabric.Patch.expectedQ sq ds axStrs)),
          ("new_subtree_q", js (Rcic.Fabric.Patch.factQ sq bq axStrs))]
    | .error e, _, _ | _, .error e, _ =>
        nErr := nErr + 1
        kvs := kvs ++ [("expected_error", js s!"{n}: {e}")]
    | _, _, .error e =>
        nErr := nErr + 1
        kvs := kvs ++ [("expected_error", js e)]
    h.putStrLn (renderObj kvs)
  h.flush
  IO.eprintln s!"done: {names.size} proposals, {nOk} with expected_q, {nErr} refused"
  return 0



/-- CLI entry; root `main` lives in `Residua.Exe.RcicFabricIndex` (no root `main` in a library module). -/
def cliMain (args : List String) : IO UInt32 := do
  let o := parseArgs args {}
  if o.modulesFile.isEmpty || o.out.isEmpty then
    IO.eprintln "usage: rcic-fabric-index --modules FILE --out FILE [--payload-bound N] [--check-axioms N] [--goals-from FACTS] [--export-scm N]"
    return 2
  let mods := (← IO.FS.lines o.modulesFile).filter (!·.isEmpty) |>.map String.toName
  initSearchPath (← findSysroot)
  IO.eprintln s!"importing {mods.size} modules"
  let env ← importModules (mods.map ({ module := · })) {} (trustLevel := 1024)
  if !o.goalsFrom.isEmpty then
    return ← goalsMain env o.payloadBound o.goalsFrom o.out
  if !o.patchModules.isEmpty then
    return ← patchMain env o
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    match env.getModuleIdxFor? n with
    | some idx =>
        let m := env.header.moduleNames[idx.toNat]!
        if isRcicModule m && !n.isInternal then acc.push n else acc
    | none => acc
  let names := names.qsort (fun a b => a.toString < b.toString)
  IO.eprintln s!"{names.size} rcic declarations"
  if o.exportScm > 0 then
    return ← exportMain env names o
  let mut memo : AxMemo := {}
  let h ← IO.FS.Handle.mk o.out .write
  let mut nStmtErr := 0
  let mut nBodyErr := 0
  let mut nEdges := 0
  let mut nAxChecked := 0
  let mut i := 0
  let js (x : String) : String := (Json.str x).compress
  for n in names do
    i := i + 1
    if i % 5000 == 0 then IO.eprintln s!"  {i}/{names.size}"
    let some ci := env.find? n | continue
    let ps := ci.levelParams
    let m := env.header.moduleNames[(env.getModuleIdxFor? n).get!.toNat]!
    let (axs, memo') := (axiomsOf env n).run memo
    memo := memo'
    let mut kvs : List (String × String) :=
      [("name", js n.toString), ("module", js m.toString), ("kind", js (kindOf ci)),
       ("axioms", (jnames axs).compress)]
    match boundedQ o.payloadBound Rcic.Fabric.Q.stmtQ ps ci.type with
    | .ok q => kvs := kvs ++ [("stmt_q", js q)]
    | .error r =>
        nStmtErr := nStmtErr + 1
        kvs := kvs ++ [("stmt_q", "null"), ("stmt_error", js r)]
    match valueOf? ci with
    | none => kvs := kvs ++ [("body_q", "null")]
    | some v =>
        match boundedQ o.payloadBound Rcic.Fabric.Q.bodyQ ps v with
        | .ok q => kvs := kvs ++ [("body_q", js q)]
        | .error r =>
            nBodyErr := nBodyErr + 1
            kvs := kvs ++ [("body_q", "null"), ("body_error", js r)]
    let edge : String := match ci with
      | .thmInfo _ =>
          let (k, prem, g) := edgeShape env ci.type
          if prem.isEmpty then "null" else
          match prem.mapM (goalOf? env o.payloadBound ps), goalOf? env o.payloadBound ps g with
          | some pg, some gg =>
              match pg.mapM (·.1), gg.1 with
              | .ok pq, .ok gq =>
                  let nm (x : Option Name) : Json := match x with | some c => Json.str c.toString | none => Json.null
                  renderObj [("premises", (Json.arr (pq.map jstr)).compress), ("conclusion", js gq),
                    ("premise_names", (Json.arr (pg.map (nm ·.2))).compress),
                    ("conclusion_name", (nm gg.2).compress), ("context", toString k)]
              | _, _ => "null"
          | _, _ => "null"
      | _ => "null"
    if edge != "null" then nEdges := nEdges + 1
    kvs := kvs ++ [("edge", edge)]
    if nAxChecked < o.checkAxioms then
      nAxChecked := nAxChecked + 1
      let (_, st) := ((CollectAxioms.collect n).run env).run {}
      let fresh := sortNames st.axioms
      unless fresh == axs do
        IO.eprintln s!"[fabric_index_axiom_mismatch] {n}: shared {axs} fresh {fresh}"
        return 4
    h.putStrLn (renderObj kvs)
  h.flush
  IO.eprintln s!"done: {names.size} records, {nStmtErr} stmt refusals, {nBodyErr} body refusals, {nEdges} edges, axioms-checked {nAxChecked}"
  return 0

/-! ## Regression: the memoized closure equals a fresh `CollectAxioms`, for every query order

An inductive type and its constructors refer to each other, so cycles in the constant graph are
ordinary. These checks run at elaboration time and fail the module build if a memoized result differs
from `Lean.collectAxioms` computed fresh, whichever member of a cycle is queried first. -/

section Regression

theorem fabricTestAx : (1 = 1) = True := propext ⟨fun _ => trivial, fun _ => rfl⟩

/-- Self-referential inductive: the constructor `step` mentions the type and an axiom user. -/
inductive FabricTestInd : Nat → Type
  | base : FabricTestInd 0
  | step (n : Nat) (h : fabricTestAx = fabricTestAx) (t : FabricTestInd n) : FabricTestInd (n + 1)

mutual
inductive FabricTestEven : Nat → Type
  | zero : FabricTestEven 0
  | succ (n : Nat) (t : FabricTestOdd n) : FabricTestEven (n + 1)
inductive FabricTestOdd : Nat → Type
  | succ (n : Nat) (h : fabricTestAx = fabricTestAx) (t : FabricTestEven n) : FabricTestOdd (n + 1)
end

open Lean Elab Command in
/-- For every first-queried constant of `names` (fresh memo) and for the forward and the reverse
sequential order over one shared memo, every answer equals a fresh `CollectAxioms`. -/
def checkMemoAgainstFresh (names : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let fresh (n : Name) : Array Name :=
    sortNames ((((CollectAxioms.collect n).run env).run {}).2.axioms)
  let run (order : List Name) : CommandElabM Unit := do
    let mut memo : AxMemo := {}
    for n in order do
      let (a, m) := (axiomsOf env n).run memo
      memo := m
      unless a == fresh n do
        throwError "[fabric_index_axiom_mismatch] {n}: memo {a} fresh {fresh n} (order {order})"
  for n in names do run (n :: names)
  run names
  run names.reverse

open Lean Elab Command in
run_cmd do
  let fam (t : Name) (cs : List Name) : List Name := t :: (t ++ `rec) :: cs
  checkMemoAgainstFresh (fam ``FabricTestInd [``FabricTestInd.base, ``FabricTestInd.step])
  checkMemoAgainstFresh
    (fam ``FabricTestEven [``FabricTestEven.zero, ``FabricTestEven.succ]
      ++ fam ``FabricTestOdd [``FabricTestOdd.succ])
  checkMemoAgainstFresh
    (fam ``Rcic.Declarative.EnvWf
      [``Rcic.Declarative.EnvWf.empty, ``Rcic.Declarative.EnvWf.axiom, ``Rcic.Declarative.EnvWf.definition])
  -- the reported failing pair, explicitly: the child queried after (and before) the parent
  checkMemoAgainstFresh [``Rcic.Declarative.EnvWf, ``Rcic.Declarative.EnvWf.empty]

end Regression

end Rcic.Fabric.Index

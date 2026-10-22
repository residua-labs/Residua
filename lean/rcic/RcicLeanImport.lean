/-
Lean → RCIC slice 1 (R-CIC-0ι). Translator only: `Lean.Expr` / `Lean.Level` /
`ConstantInfo` become `Rcic.Declarative` members, or a named residue.

No second semantics. Typing stays `Rcic.Machine.checkCert` / `runRaw`.
`HasTy.lit` is not edited. Native `natVal` reuses `Expr.lit` and the landed
`natExpand` shape (family 0, zero 1, succ 2). Metadata that §8 treats as
decorative (mdata, binder names, `BinderInfo`, `letE` nonDep, reducibility
hints) is not stored. Safety flags are refused, not erased.

Measurement (2026-10-22, main only): `ExprWire` does not round-trip
`Expr Nat` (`const` is `String`, `lit` is absent). There is no
`Lean.Expr.proj` → `Expr Nat` mapping; projections refuse.
-/
import Lean
import rcic.RcicDeclarative

namespace Rcic.LeanImport

open Rcic.Declarative (MemberClass CheckedMember ResolvedEnv emptyEnv extendEnv natExpand)

abbrev RCExpr := Rcic.Declarative.Expr Nat
abbrev RCLevel := Rcic.Declarative.Level

/-! ## Named residues. A refusal is one of these strings, never a dropped decl. -/

def residueQuot : String := "[rcic_import_quot]"
def residueMutual : String := "[rcic_import_mutual_inductive]"
def residueNested : String := "[rcic_import_nested_inductive]"
def residueUnsafe : String := "[rcic_import_unsafe]"
def residuePartial : String := "[rcic_import_partial]"
def residueFvar : String := "[rcic_import_fvar]"
def residueMvar : String := "[rcic_import_mvar]"
def residueLevelMVar : String := "[rcic_import_level_mvar]"
def residueProj : String := "[rcic_import_proj]"
def residueUncoveredLit : String := "[rcic_import_uncovered_literal]"
def residueUnresolvedRef : String := "[rcic_import_unresolved_ref]"
def residueUnresolvedLevel : String := "[rcic_import_unresolved_level_param]"
def residueMissingCtor : String := "[rcic_import_missing_ctor]"
def residueMissingRec : String := "[rcic_import_missing_recursor]"
def residueDepth : String := "[rcic_import_depth]"

/-- `true` when landed `natExpand` is still `succ^n zero` at refs 1 and 2.
    Any other shape means this slice does not know a nat literal profile,
    so `natVal` refuses instead of inventing an expansion. -/
def nativeNatLit : Bool :=
  match natExpand 0, natExpand 1 with
  | .const 1 [], .app (.const 2 []) (.const 1 []) => true
  | _, _ => false

/-- The imported literal's meaning is the landed expansion, not a new one. -/
def importedNatExpansion (n : Nat) : RCExpr :=
  natExpand n

def isQuotName (n : Lean.Name) : Bool :=
  Lean.Name.isPrefixOf `Quot n

def indexOfName : List Lean.Name → Lean.Name → Option Nat
  | [], _ => none
  | n :: ns, m =>
      if n == m then some 0
      else (indexOfName ns m).map (· + 1)

def trLevel (ps : List Lean.Name) : Lean.Level → Except String RCLevel
  | .zero => .ok .zero
  | .succ u =>
      match trLevel ps u with
      | .ok l => .ok (.succ l)
      | .error e => .error e
  | .max a b =>
      match trLevel ps a, trLevel ps b with
      | .ok a, .ok b => .ok (.max a b)
      | .error e, _ => .error e
      | _, .error e => .error e
  | .imax a b =>
      match trLevel ps a, trLevel ps b with
      | .ok a, .ok b => .ok (.imax a b)
      | .error e, _ => .error e
      | _, .error e => .error e
  | .param n =>
      match indexOfName ps n with
      | some i => .ok (.param i)
      | none => .error residueUnresolvedLevel
  | .mvar _ => .error residueLevelMVar

def trLevels (ps : List Lean.Name) : List Lean.Level → Except String (List RCLevel)
  | [] => .ok []
  | u :: us =>
      match trLevel ps u, trLevels ps us with
      | .ok l, .ok ls => .ok (l :: ls)
      | .error e, _ => .error e
      | _, .error e => .error e

/-- Node budget. Each real constructor spends one. `mdata` spends one too
    and contributes no RCIC constructor (erasure). Fuel 0 refuses; it does
    not truncate into an accepted term. -/
def trExpr (fuel : Nat) (ps : List Lean.Name) (resolve : Lean.Name → Option Nat)
    (e : Lean.Expr) : Except String RCExpr :=
  match fuel with
  | 0 => .error residueDepth
  | n + 1 =>
      match e with
      | .bvar i => .ok (.bvar i)
      | .fvar _ => .error residueFvar
      | .mvar _ => .error residueMvar
      | .sort u =>
          match trLevel ps u with
          | .ok l => .ok (.sort l)
          | .error err => .error err
      | .const name ls =>
          if isQuotName name then .error residueQuot
          else
            match resolve name with
            | none => .error residueUnresolvedRef
            | some r =>
                match trLevels ps ls with
                | .ok ls' => .ok (.const r ls')
                | .error err => .error err
      | .app f x =>
          match trExpr n ps resolve f, trExpr n ps resolve x with
          | .ok f', .ok x' => .ok (.app f' x')
          | .error err, _ => .error err
          | _, .error err => .error err
      | .lam _ ty body _ =>
          match trExpr n ps resolve ty, trExpr n ps resolve body with
          | .ok a, .ok b => .ok (.lam a b)
          | .error err, _ => .error err
          | _, .error err => .error err
      | .forallE _ ty body _ =>
          match trExpr n ps resolve ty, trExpr n ps resolve body with
          | .ok a, .ok b => .ok (.pi a b)
          | .error err, _ => .error err
          | _, .error err => .error err
      | .letE _ ty val body _ =>
          match trExpr n ps resolve ty, trExpr n ps resolve val, trExpr n ps resolve body with
          | .ok a, .ok v, .ok b => .ok (.letE a v b)
          | .error err, _, _ => .error err
          | _, .error err, _ => .error err
          | _, _, .error err => .error err
      | .lit l =>
          match l with
          | .natVal k =>
              if nativeNatLit then .ok (.lit k) else .error residueUncoveredLit
          | .strVal _ => .error residueUncoveredLit
      | .mdata _ inner => trExpr n ps resolve inner
      | .proj _ _ _ => .error residueProj

/-! ## Declarations. -/

structure TranslatedDecl where
  name : String
  refId : Nat
  mclass : MemberClass
  levelParams : List Lean.Name
  mtype : RCExpr
  body : Option RCExpr

def checkedOf (d : TranslatedDecl) : CheckedMember where
  mclass := d.mclass
  arity := d.levelParams.length
  mtype := d.mtype
  body := d.body

def addMembers (E : ResolvedEnv) (ds : List TranslatedDecl) : ResolvedEnv :=
  ds.foldl (fun env d => extendEnv env d.refId (checkedOf d)) E

def className : MemberClass → String
  | .axiomM => "axiomM"
  | .definitionM => "definitionM"
  | .theoremM => "theoremM"
  | .opaqueM => "opaqueM"
  | .inductiveM => "inductiveM"
  | .constructorM => "constructorM"
  | .recursorM => "recursorM"

def resolveRef (table : List (Lean.Name × Nat)) (n : Lean.Name) : Option Nat :=
  match table with
  | [] => none
  | (m, r) :: rest => if m == n then some r else resolveRef rest n

private def mkDecl (vName : Lean.Name) (ps : List Lean.Name) (cls : MemberClass)
    (ty : RCExpr) (body : Option RCExpr) (resolve : Lean.Name → Option Nat) :
    Except String TranslatedDecl :=
  match resolve vName with
  | none => .error residueUnresolvedRef
  | some r =>
      .ok { name := vName.toString, refId := r, mclass := cls
            , levelParams := ps, mtype := ty, body := body }

private def trTypeBody (fuel : Nat) (ps : List Lean.Name)
    (resolve : Lean.Name → Option Nat) (ty : Lean.Expr) (val : Option Lean.Expr) :
    Except String (RCExpr × Option RCExpr) :=
  match trExpr fuel ps resolve ty with
  | .error e => .error e
  | .ok ty' =>
      match val with
      | none => .ok (ty', none)
      | some v =>
          match trExpr fuel ps resolve v with
          | .error e => .error e
          | .ok v' => .ok (ty', some v')

private def safetyResidue : Lean.DefinitionSafety → Option String
  | .safe => none
  | .«unsafe» => some residueUnsafe
  | .«partial» => some residuePartial

def translateAxiom (fuel : Nat) (v : Lean.AxiomVal) (resolve : Lean.Name → Option Nat) :
    Except String TranslatedDecl :=
  if v.isUnsafe then .error residueUnsafe
  else if isQuotName v.name then .error residueQuot
  else
    match trTypeBody fuel v.levelParams resolve v.type none with
    | .error e => .error e
    | .ok (ty, body) => mkDecl v.name v.levelParams .axiomM ty body resolve

def translateDefn (fuel : Nat) (v : Lean.DefinitionVal) (resolve : Lean.Name → Option Nat) :
    Except String TranslatedDecl :=
  match safetyResidue v.safety with
  | some e => .error e
  | none =>
      if isQuotName v.name then .error residueQuot
      else
        match trTypeBody fuel v.levelParams resolve v.type (some v.value) with
        | .error e => .error e
        | .ok (ty, body) => mkDecl v.name v.levelParams .definitionM ty body resolve

def translateThm (fuel : Nat) (v : Lean.TheoremVal) (resolve : Lean.Name → Option Nat) :
    Except String TranslatedDecl :=
  if isQuotName v.name then .error residueQuot
  else
    match trTypeBody fuel v.levelParams resolve v.type (some v.value) with
    | .error e => .error e
    | .ok (ty, body) => mkDecl v.name v.levelParams .theoremM ty body resolve

def translateOpaque (fuel : Nat) (v : Lean.OpaqueVal) (resolve : Lean.Name → Option Nat) :
    Except String TranslatedDecl :=
  if v.isUnsafe then .error residueUnsafe
  else if isQuotName v.name then .error residueQuot
  else
    match trTypeBody fuel v.levelParams resolve v.type (some v.value) with
    | .error e => .error e
    | .ok (ty, body) => mkDecl v.name v.levelParams .opaqueM ty body resolve

/-- One-family non-nested inductive, plus its constructors and its `.rec`.
    Mutual, nested, and unsafe groups refuse before any member is built. -/
def translateInductiveGroup (fuel : Nat) (ind : Lean.InductiveVal)
    (ctors : List Lean.ConstructorVal) (rec : Lean.RecursorVal)
    (resolve : Lean.Name → Option Nat) : Except String (List TranslatedDecl) :=
  if ind.isUnsafe || rec.isUnsafe || ctors.any (·.isUnsafe) then .error residueUnsafe
  else if isQuotName ind.name then .error residueQuot
  else if ind.all.length ≠ 1 || rec.all.length ≠ 1 then .error residueMutual
  else if ind.numNested ≠ 0 then .error residueNested
  else if ind.ctors.length ≠ ctors.length then .error residueMissingCtor
  else
    let rec goCtors : List Lean.ConstructorVal → Except String (List TranslatedDecl)
      | [] => .ok []
      | c :: cs =>
          if c.induct ≠ ind.name then .error residueMissingCtor
          else
            match trTypeBody fuel c.levelParams resolve c.type none with
            | .error e => .error e
            | .ok (ty, body) =>
                match mkDecl c.name c.levelParams .constructorM ty body resolve, goCtors cs with
                | .ok d, .ok ds => .ok (d :: ds)
                | .error e, _ => .error e
                | _, .error e => .error e
    match trTypeBody fuel ind.levelParams resolve ind.type none with
    | .error e => .error e
    | .ok (ty, body) =>
        match mkDecl ind.name ind.levelParams .inductiveM ty body resolve with
        | .error e => .error e
        | .ok dInd =>
            match goCtors ctors with
            | .error e => .error e
            | .ok dCtors =>
                match trTypeBody fuel rec.levelParams resolve rec.type none with
                | .error e => .error e
                | .ok (rty, rbody) =>
                    match mkDecl rec.name rec.levelParams .recursorM rty rbody resolve with
                    | .error e => .error e
                    | .ok dRec => .ok (dInd :: dCtors ++ [dRec])

private def findInfo (find : Lean.Name → Option Lean.ConstantInfo) (n : Lean.Name) :
    Option Lean.ConstantInfo :=
  find n

private def parentInductive (find : Lean.Name → Option Lean.ConstantInfo) (n : Lean.Name) :
    Except String Lean.InductiveVal :=
  match find n with
  | some (.inductInfo v) =>
      if v.isUnsafe then .error residueUnsafe
      else if v.all.length ≠ 1 then .error residueMutual
      else if v.numNested ≠ 0 then .error residueNested
      else .ok v
  | _ => .error residueUnresolvedRef

def translateCtor (fuel : Nat) (c : Lean.ConstructorVal)
    (find : Lean.Name → Option Lean.ConstantInfo) (resolve : Lean.Name → Option Nat) :
    Except String TranslatedDecl :=
  if c.isUnsafe then .error residueUnsafe
  else
    match parentInductive find c.induct with
    | .error e => .error e
    | .ok _ =>
        match trTypeBody fuel c.levelParams resolve c.type none with
        | .error e => .error e
        | .ok (ty, body) => mkDecl c.name c.levelParams .constructorM ty body resolve

def translateRec (fuel : Nat) (r : Lean.RecursorVal)
    (find : Lean.Name → Option Lean.ConstantInfo) (resolve : Lean.Name → Option Nat) :
    Except String TranslatedDecl :=
  if r.isUnsafe then .error residueUnsafe
  else if r.all.length ≠ 1 then .error residueMutual
  else
    match r.all with
    | [] => .error residueMissingRec
    | parent :: _ =>
        match parentInductive find parent with
        | .error e => .error e
        | .ok _ =>
            match trTypeBody fuel r.levelParams resolve r.type none with
            | .error e => .error e
            | .ok (ty, body) => mkDecl r.name r.levelParams .recursorM ty body resolve

/-- Translate one environment constant. An in-profile inductive returns the
    inductive, each constructor, and the recursor. A residue returns no members. -/
def translateInfo (fuel : Nat) (info : Lean.ConstantInfo)
    (find : Lean.Name → Option Lean.ConstantInfo) (resolve : Lean.Name → Option Nat) :
    Except String (List TranslatedDecl) :=
  match info with
  | .axiomInfo v => (translateAxiom fuel v resolve).map fun d => [d]
  | .defnInfo v => (translateDefn fuel v resolve).map fun d => [d]
  | .thmInfo v => (translateThm fuel v resolve).map fun d => [d]
  | .opaqueInfo v => (translateOpaque fuel v resolve).map fun d => [d]
  | .quotInfo _ => .error residueQuot
  | .ctorInfo v => (translateCtor fuel v find resolve).map fun d => [d]
  | .recInfo v => (translateRec fuel v find resolve).map fun d => [d]
  | .inductInfo ind =>
      if ind.isUnsafe then .error residueUnsafe
      else if ind.all.length ≠ 1 then .error residueMutual
      else if ind.numNested ≠ 0 then .error residueNested
      else
        let ctorInfos : Except String (List Lean.ConstructorVal) :=
          ind.ctors.foldl (fun acc n =>
            match acc with
            | .error e => .error e
            | .ok cs =>
                match find n with
                | some (.ctorInfo c) => .ok (cs ++ [c])
                | _ => .error residueMissingCtor) (.ok [])
        match ctorInfos with
        | .error e => .error e
        | .ok cs =>
            match find (Lean.Name.mkStr ind.name "rec") with
            | some (.recInfo r) => translateInductiveGroup fuel ind cs r resolve
            | _ => .error residueMissingRec

def visibleClasses (r : Except String (List TranslatedDecl)) : List String :=
  match r with
  | .ok ds => ds.map fun d => className d.mclass
  | .error _ => []

/-! ## Erasure facts. `mdata`, binder names, `BinderInfo`, and `letE` nonDep
    are not arguments of the recursive call, so they cannot appear in the image. -/

theorem li_mdata_erased (n : Nat) (ps : List Lean.Name) (resolve : Lean.Name → Option Nat)
    (d : Lean.MData) (e : Lean.Expr) :
    trExpr (n + 1) ps resolve (.mdata d e) = trExpr n ps resolve e := by
  rfl

theorem li_lam_binder_erased (n : Nat) (ps : List Lean.Name) (resolve : Lean.Name → Option Nat)
    (n1 n2 : Lean.Name) (bi1 bi2 : Lean.BinderInfo) (ty body : Lean.Expr) :
    trExpr (n + 1) ps resolve (.lam n1 ty body bi1)
      = trExpr (n + 1) ps resolve (.lam n2 ty body bi2) := by
  rfl

theorem li_let_nondep_erased (n : Nat) (ps : List Lean.Name) (resolve : Lean.Name → Option Nat)
    (nm : Lean.Name) (ty val body : Lean.Expr) :
    trExpr (n + 1) ps resolve (.letE nm ty val body true)
      = trExpr (n + 1) ps resolve (.letE nm ty val body false) := by
  rfl

theorem li_level_mvar_refused (ps : List Lean.Name) (m : Lean.LMVarId) :
    trLevel ps (.mvar m) = .error residueLevelMVar := by
  rfl

theorem li_native_nat_lit : nativeNatLit = true := by
  rfl

theorem li_nat_expansion_landed (n : Nat) :
    importedNatExpansion n = natExpand n := by
  rfl

end Rcic.LeanImport

/-
RCIC 07 §3 — G2-S1: `EnvWfT` admission of the `BNat` support block
(`bnatMembersAt 5 0`, `RcicG2Objects`) — one `EnvWfT.group` step on top
of `Pos`'s admitted block (`posBlockWfT`), since `pos : Pos → BNat` names
`Pos`'s family (the List-after-Nat precedent, `RcicTypedGroupPinsList`).

The family is `natFamMember`'s shape at ref 5; `zero` is field-free and
`pos`'s one field is the foreign family `Pos` — non-recursive, so the
recursor's `pos` minor has no induction hypothesis. `.anySort` by
`uniformType`; the stored `bnatRecTy 5 0` is the policy recursor type by
`rfl`. Every env here is a `foldEnv` of a concrete table, so census,
contiguity, no-recursor and field-permission obligations are the
`ScmSrcGroupsAdm` Bool deciders' (`*_sound` over a `decide` leaf).
-/
import rcic.RcicG2AdmitPos

set_option maxRecDepth 8192

namespace Rcic.G2
open Rcic.Declarative
open Rcic.Scm.SrcG (sortTyAtC foldEnv noRecursorForB_sound ctorContiguousB_sound
  ctorCensusB_sound ctorFieldsPermitted_of_B)

/-! ## (1) the members and the prefix chain -/

def bnZeroMember : CheckedMember := ⟨.constructorM, 0, .const 5 [], none⟩
def bnPosMember : CheckedMember := ⟨.constructorM, 0, .pi (.const 0 []) (.const 5 []), none⟩
def bnRecMember : CheckedMember := ⟨.recursorM, 1, bnatRecTy 5 0, none⟩

theorem bnatMembersAt_five :
    bnatMembersAt 5 0 =
      [(5, natFamMember), (6, bnZeroMember), (7, bnPosMember), (8, bnRecMember)] := rfl

/-- `Pos`'s block, then `BNat`'s first `k` members, as one table. -/
def bnTbl (k : Nat) : List (Nat × CheckedMember) := posMembersAt 0 ++ (bnatMembersAt 5 0).take k

def bnE1 : ResolvedEnv := extendEnv posEnv 5 natFamMember
def bnE2 : ResolvedEnv := extendEnv bnE1 6 bnZeroMember
def bnPrefix : ResolvedEnv := extendEnv bnE2 7 bnPosMember
def bnEnv : ResolvedEnv := extendEnv bnPrefix 8 bnRecMember

theorem bnBlockEnv_eq : blockEnv posEnv (bnatMembersAt 5 0) = bnEnv := rfl

/-! ## (2) the views -/

/-- `BNat : Sort 1` at ref 5: no parameter, no index. -/
def bnFamView (E : ResolvedEnv) (h : E.members 5 = some natFamMember) :
    PolicyFamilyView E where
  ref := 5
  member := natFamMember
  present := h
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def bnZeroView (E : ResolvedEnv) (h : E.members 5 = some natFamMember) :
    PolicyConstructorView E (bnFamView E h) bnZeroMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := .empty _ _
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ hx => nomatch hx

/-- `pos : Pos → BNat`: one field, `Pos`'s family (`Sort 1`). -/
def bnPosView (E : ResolvedEnv) (h : E.members 5 = some natFamMember)
    (h0 : E.members 0 = some natFamMember) :
    PolicyConstructorView E (bnFamView E h) bnPosMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.const 0 []]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun
      | ⟨0, _⟩ => HasTy.const [] 0 [] natFamMember h0 rfl (fun _ hx => nomatch hx) }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ hx => nomatch hx

theorem bnPosUniverse (E : ResolvedEnv) (h : E.members 5 = some natFamMember)
    (h0 : E.members 0 = some natFamMember) :
    FieldUniverseAdmitted (bnPosView E h h0)
  | ⟨0, _⟩ => Or.inr ⟨uniformType_succ_zero, leN_refl _⟩

/-! ## (3) the family and constructor admissions -/

def bnFamAdmitted : IndGroupAdmitted posEnv 5 natFamMember :=
  .family rfl (bnFamView bnE1 rfl) rfl rfl (Or.inr uniformType_succ_zero)

theorem bnZeroBefore : CtorBeforeRecursors bnE1 bnZeroMember :=
  ⟨5, rfl, noRecursorForB_sound (tbl := bnTbl 1) (by decide) (by decide)⟩

theorem bnZeroContig : CtorContiguous bnE1 6 bnZeroMember :=
  ctorContiguousB_sound (tbl := bnTbl 1) (by decide) (by decide)

def bnZeroAdmitted : IndGroupAdmitted bnE1 6 bnZeroMember :=
  .constructor (bnFamView bnE1 rfl) (bnZeroView bnE1 rfl) rfl bnZeroBefore bnZeroContig
    (fun j => j.elim0) (fun j => j.elim0)

theorem bnPosBefore : CtorBeforeRecursors bnE2 bnPosMember :=
  ⟨5, rfl, noRecursorForB_sound (tbl := bnTbl 2) (by decide) (by decide)⟩

theorem bnPosContig : CtorContiguous bnE2 7 bnPosMember :=
  ctorContiguousB_sound (tbl := bnTbl 2) (by decide) (by decide)

theorem bnPosFields : CtorFieldsPermitted (bnPosView bnE2 rfl rfl) :=
  ctorFieldsPermitted_of_B _ 8 (by decide)

def bnPosAdmitted : IndGroupAdmitted bnE2 7 bnPosMember :=
  .constructor (bnFamView bnE2 rfl) (bnPosView bnE2 rfl rfl) rfl bnPosBefore bnPosContig
    (bnPosUniverse _ rfl rfl) bnPosFields

/-! ## (4) the recursor admission -/

theorem bnCensus : CtorCensus bnPrefix 5 8 :=
  ctorCensusB_sound (tbl := bnTbl 3) (by decide) (by decide)

/-- `P zero`; `Π p : Pos, P (pos p)` (foreign field, no IH). -/
def bnMinors : List (Expr Nat) :=
  [ .app (.bvar 0) (.const 6 []),
    .pi (.const 0 []) (.app (.bvar 2) (.app (.const 7 []) (.bvar 0))) ]

def bnGroupAdm : RecursorEliminationAdmitted bnPrefix 8 bnRecMember where
  family := bnFamView bnPrefix rfl
  constructors := [bnZeroMember, bnPosMember]
  constructorViews
    | ⟨0, _⟩ => bnZeroView bnPrefix rfl
    | ⟨1, _⟩ => bnPosView bnPrefix rfl rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  recursorRef := rfl
  minorTypes := bnMinors
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

theorem bnMinorMatch : MinorPremisesMatch bnGroupAdm
  | ⟨0, _⟩ => ⟨[], 8, rfl, rfl⟩
  | ⟨1, _⟩ => ⟨[.nonrecursive], 8, rfl, rfl⟩

def bnMotTy : Expr Nat := .pi (.const 5 []) (.sort (.param 0))

/-- `[ms, mz, P]` — `zero`'s equation context. -/
def bnCtx0 : LCtx :=
  [.assumption (bnMinors[1]'(by decide)), .assumption (bnMinors[0]'(by decide)),
    .assumption bnMotTy]

/-- `[p, ms, mz, P]` — `pos`'s (one field `p : Pos`). -/
def bnCtx1 : LCtx := .assumption (.const 0 []) :: bnCtx0

/-- `rec P mz ms zero ⇝ mz`. -/
def bnZeroIotaTy : HasTy bnEnv 1 bnCtx0 (.bvar 1) (.app (.bvar 2) (.const 6 [])) :=
  HasTy.bvar _ 1 _ rfl

/-- `rec P mz ms (pos p) ⇝ ms p`. -/
def bnPosIotaTy :
    HasTy bnEnv 1 bnCtx1 (.app (.bvar 1) (.bvar 0))
      (.app (.bvar 3) (.app (.const 7 []) (.bvar 0))) :=
  HasTy.app _ (.bvar 1) (.bvar 0) (.const 0 [])
    (.app (.bvar 4) (.app (.const 7 []) (.bvar 0)))
    (HasTy.bvar _ 1 _ rfl) (HasTy.bvar _ 0 _ rfl)

def bnIotaZero : IotaEquationTyped bnGroupAdm ⟨0, by decide⟩ 8 [] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact bnZeroIotaTy

def bnIotaPos : IotaEquationTyped bnGroupAdm ⟨1, by decide⟩ 8 [.nonrecursive] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact bnPosIotaTy

def bnShapes : Fin bnGroupAdm.constructors.length → List FieldShape
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => [.nonrecursive]

def bnIotaClause : IotaDescriptorClause bnPrefix bnGroupAdm where
  signatureOnly := rfl
  shapesAt := bnShapes
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  typed
    | ⟨0, _⟩ => bnIotaZero
    | ⟨1, _⟩ => bnIotaPos

def bnRecAdmitted : IndGroupAdmitted bnPrefix 8 bnRecMember :=
  .recursor bnGroupAdm rfl bnCensus
    (fun | ⟨0, _⟩ => fun j => j.elim0 | ⟨1, _⟩ => bnPosUniverse _ rfl rfl)
    (fun | ⟨0, _⟩ => fun j => j.elim0
         | ⟨1, _⟩ => ctorFieldsPermitted_of_B (bnPosView bnPrefix rfl rfl) 8 (by decide))
    bnMinorMatch bnIotaClause

/-! ## (5) checker leaves, the chain, and the group step -/

kernel_rfl_theorem bnSortB0 :
    (sortTyAtC posEnv 0 96 [] natFamMember.mtype).isSome = true

kernel_rfl_theorem bnSortB1 :
    (sortTyAtC bnE1 0 96 [] bnZeroMember.mtype).isSome = true

kernel_rfl_theorem bnSortB2 :
    (sortTyAtC bnE2 0 96 [] bnPosMember.mtype).isSome = true

kernel_rfl_theorem bnSortB3 :
    (sortTyAtC bnPrefix 1 96 [] bnRecMember.mtype).isSome = true

kernel_rfl_theorem bnAccB0 :
    memberAcceptB bnE1 posEnv 96 bnFamAdmitted
      ((sortTyAtC posEnv 0 96 [] natFamMember.mtype).get bnSortB0).1 = true

kernel_rfl_theorem bnAccB1 :
    memberAcceptB bnE1 bnE1 96 bnZeroAdmitted
      ((sortTyAtC bnE1 0 96 [] bnZeroMember.mtype).get bnSortB1).1 = true

kernel_rfl_theorem bnAccB2 :
    memberAcceptB bnE1 bnE2 96 bnPosAdmitted
      ((sortTyAtC bnE2 0 96 [] bnPosMember.mtype).get bnSortB2).1 = true

kernel_rfl_theorem bnAccB3 :
    memberAcceptB bnE1 bnPrefix 96 bnRecAdmitted
      ((sortTyAtC bnPrefix 1 96 [] bnRecMember.mtype).get bnSortB3).1 = true

def bnGroupChain :
    GroupAcceptChain bnE1 96 posEnv
      [(5, natFamMember), (6, bnZeroMember), (7, bnPosMember), (8, bnRecMember)] bnEnv :=
  .cons posEnv 5 natFamMember _ _ bnFamAdmitted bnSortB0 bnAccB0
    (.cons bnE1 6 bnZeroMember _ _ bnZeroAdmitted bnSortB1 bnAccB1
      (.cons bnE2 7 bnPosMember _ _ bnPosAdmitted bnSortB2 bnAccB2
        (.cons bnPrefix 8 bnRecMember _ _ bnRecAdmitted bnSortB3 bnAccB3
          (.nil bnEnv))))

kernel_rfl_theorem bnClassB :
    groupClassB natFamMember [(6, bnZeroMember), (7, bnPosMember)] bnRecMember = true

/-- `BNat`'s block admits on top of `Pos`'s: two `EnvWfT.group` steps from
    the empty env, `Pos` then `BNat`. -/
def bnatBlockWfT : EnvWfT (blockEnv (blockEnv emptyEnv (posMembersAt 0)) (bnatMembersAt 5 0)) :=
  EG010T_group_accepted posBlockWfT 96 bnClassB bnGroupChain

end Rcic.G2

/-
RCIC 07 §3 — G2-S1: `EnvWfT` admission of the `SV<sum [i64, bool]>` block
(`svMembersAt svSup svRefOf 31 (.sum [.i64, .bool])`) on top of
`SV<pair i64 bool>`'s (`svPairBlockWfT`). One injection per summand,
`injᵢ : SV<tᵢ> → SV<sum …>`, each a foreign field with no IH.
-/
import rcic.RcicG2AdmitSVPair

set_option maxRecDepth 8192

namespace Rcic.G2
open Rcic.Declarative Rcic.Scm
open Rcic.Scm.SrcG (sortTyAtC foldEnv noRecursorForB_sound ctorContiguousB_sound
  ctorCensusB_sound ctorFieldsPermitted_of_B)

def svSumTy : CoreTy := .sum [.i64, .bool]

def svSumInj0 : CheckedMember := ctor1Member 31 9
def svSumInj1 : CheckedMember := ctor1Member 31 12
def svSumRec : CheckedMember :=
  ⟨.recursorM, 1, svRecTy 31 [(32, [⟨.const 9 [], false⟩]), (33, [⟨.const 12 [], false⟩])], none⟩

theorem svSumMembers :
    svMembersAt svSup svRefOf 31 svSumTy =
      [(31, natFamMember), (32, svSumInj0), (33, svSumInj1), (34, svSumRec)] := rfl

def svSumTbl (k : Nat) : List (Nat × CheckedMember) :=
  svPairTbl 3 ++ (svMembersAt svSup svRefOf 31 svSumTy).take k

def svSumE1 : ResolvedEnv := extendEnv svPairEnv 31 natFamMember
def svSumE2 : ResolvedEnv := extendEnv svSumE1 32 svSumInj0
def svSumPrefix : ResolvedEnv := extendEnv svSumE2 33 svSumInj1
def svSumEnv : ResolvedEnv := extendEnv svSumPrefix 34 svSumRec

theorem svSumBlockEnv_eq : blockEnv svPairEnv (svMembersAt svSup svRefOf 31 svSumTy) = svSumEnv :=
  rfl

def svSumFamAdmitted : IndGroupAdmitted svPairEnv 31 natFamMember :=
  .family rfl (sortOneFamView svSumE1 31 rfl) rfl rfl (Or.inr uniformType_succ_zero)

def svSumInj0Admitted : IndGroupAdmitted svSumE1 32 svSumInj0 :=
  .constructor (sortOneFamView svSumE1 31 rfl) (ctor1View svSumE1 31 9 rfl rfl) rfl
    ⟨31, rfl, noRecursorForB_sound (tbl := svSumTbl 1) (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := svSumTbl 1) (by decide) (by decide))
    (ctor1Universe _ 31 9 rfl rfl) (ctorFieldsPermitted_of_B _ 8 (by decide))

def svSumInj1Admitted : IndGroupAdmitted svSumE2 33 svSumInj1 :=
  .constructor (sortOneFamView svSumE2 31 rfl) (ctor1View svSumE2 31 12 rfl rfl) rfl
    ⟨31, rfl, noRecursorForB_sound (tbl := svSumTbl 2) (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := svSumTbl 2) (by decide) (by decide))
    (ctor1Universe _ 31 12 rfl rfl) (ctorFieldsPermitted_of_B _ 8 (by decide))

theorem svSumCensus : CtorCensus svSumPrefix 31 34 :=
  ctorCensusB_sound (tbl := svSumTbl 3) (by decide) (by decide)

/-- `Π x : SV<i64>, P (inj0 x)`; `Π x : SV<bool>, P (inj1 x)`. -/
def svSumMinors : List (Expr Nat) :=
  [ .pi (.const 9 []) (.app (.bvar 1) (.app (.const 32 []) (.bvar 0))),
    .pi (.const 12 []) (.app (.bvar 2) (.app (.const 33 []) (.bvar 0))) ]

def svSumGroupAdm : RecursorEliminationAdmitted svSumPrefix 34 svSumRec where
  family := sortOneFamView svSumPrefix 31 rfl
  constructors := [svSumInj0, svSumInj1]
  constructorViews
    | ⟨0, _⟩ => ctor1View svSumPrefix 31 9 rfl rfl
    | ⟨1, _⟩ => ctor1View svSumPrefix 31 12 rfl rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  recursorRef := rfl
  minorTypes := svSumMinors
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

theorem svSumMinorMatch : MinorPremisesMatch svSumGroupAdm
  | ⟨0, _⟩ => ⟨[.nonrecursive], 8, rfl, rfl⟩
  | ⟨1, _⟩ => ⟨[.nonrecursive], 8, rfl, rfl⟩

/-- `[m1, m0, P]`. -/
def svSumCtx : LCtx :=
  [.assumption (svSumMinors[1]'(by decide)), .assumption (svSumMinors[0]'(by decide)),
    .assumption (.pi (.const 31 []) (.sort (.param 0)))]

/-- `rec P m0 m1 (inj0 x) ⇝ m0 x`. -/
def svSumInj0IotaTy :
    HasTy svSumEnv 1 (.assumption (.const 9 []) :: svSumCtx) (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 3) (.app (.const 32 []) (.bvar 0))) :=
  HasTy.app _ _ _ _ _ (HasTy.bvar (.assumption (.const 9 []) :: svSumCtx) 2 _ rfl)
    (HasTy.bvar (.assumption (.const 9 []) :: svSumCtx) 0 _ rfl)

/-- `rec P m0 m1 (inj1 x) ⇝ m1 x`. -/
def svSumInj1IotaTy :
    HasTy svSumEnv 1 (.assumption (.const 12 []) :: svSumCtx) (.app (.bvar 1) (.bvar 0))
      (.app (.bvar 3) (.app (.const 33 []) (.bvar 0))) :=
  HasTy.app _ _ _ _ _ (HasTy.bvar (.assumption (.const 12 []) :: svSumCtx) 1 _ rfl)
    (HasTy.bvar (.assumption (.const 12 []) :: svSumCtx) 0 _ rfl)

def svSumIota0 : IotaEquationTyped svSumGroupAdm ⟨0, by decide⟩ 8 [.nonrecursive] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact svSumInj0IotaTy

def svSumIota1 : IotaEquationTyped svSumGroupAdm ⟨1, by decide⟩ 8 [.nonrecursive] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact svSumInj1IotaTy

def svSumIotaClause : IotaDescriptorClause svSumPrefix svSumGroupAdm where
  signatureOnly := rfl
  shapesAt := fun _ => [.nonrecursive]
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  typed
    | ⟨0, _⟩ => svSumIota0
    | ⟨1, _⟩ => svSumIota1

def svSumRecAdmitted : IndGroupAdmitted svSumPrefix 34 svSumRec :=
  .recursor svSumGroupAdm rfl svSumCensus
    (fun | ⟨0, _⟩ => ctor1Universe _ 31 9 rfl rfl | ⟨1, _⟩ => ctor1Universe _ 31 12 rfl rfl)
    (fun | ⟨0, _⟩ => ctorFieldsPermitted_of_B (ctor1View svSumPrefix 31 9 rfl rfl) 8 (by decide)
         | ⟨1, _⟩ => ctorFieldsPermitted_of_B (ctor1View svSumPrefix 31 12 rfl rfl) 8 (by decide))
    svSumMinorMatch svSumIotaClause

kernel_rfl_theorem svSumSortB0 : (sortTyAtC svPairEnv 0 96 [] natFamMember.mtype).isSome = true
kernel_rfl_theorem svSumSortB1 : (sortTyAtC svSumE1 0 96 [] svSumInj0.mtype).isSome = true
kernel_rfl_theorem svSumSortB2 : (sortTyAtC svSumE2 0 96 [] svSumInj1.mtype).isSome = true
kernel_rfl_theorem svSumSortB3 : (sortTyAtC svSumPrefix 1 96 [] svSumRec.mtype).isSome = true

kernel_rfl_theorem svSumAccB0 :
    memberAcceptB svSumE1 svPairEnv 96 svSumFamAdmitted
      ((sortTyAtC svPairEnv 0 96 [] natFamMember.mtype).get svSumSortB0).1 = true

kernel_rfl_theorem svSumAccB1 :
    memberAcceptB svSumE1 svSumE1 96 svSumInj0Admitted
      ((sortTyAtC svSumE1 0 96 [] svSumInj0.mtype).get svSumSortB1).1 = true

kernel_rfl_theorem svSumAccB2 :
    memberAcceptB svSumE1 svSumE2 96 svSumInj1Admitted
      ((sortTyAtC svSumE2 0 96 [] svSumInj1.mtype).get svSumSortB2).1 = true

kernel_rfl_theorem svSumAccB3 :
    memberAcceptB svSumE1 svSumPrefix 96 svSumRecAdmitted
      ((sortTyAtC svSumPrefix 1 96 [] svSumRec.mtype).get svSumSortB3).1 = true

def svSumGroupChain :
    GroupAcceptChain svSumE1 96 svPairEnv
      [(31, natFamMember), (32, svSumInj0), (33, svSumInj1), (34, svSumRec)] svSumEnv :=
  .cons svPairEnv 31 natFamMember _ _ svSumFamAdmitted svSumSortB0 svSumAccB0
    (.cons svSumE1 32 svSumInj0 _ _ svSumInj0Admitted svSumSortB1 svSumAccB1
      (.cons svSumE2 33 svSumInj1 _ _ svSumInj1Admitted svSumSortB2 svSumAccB2
        (.cons svSumPrefix 34 svSumRec _ _ svSumRecAdmitted svSumSortB3 svSumAccB3
          (.nil svSumEnv))))

kernel_rfl_theorem svSumClassB :
    groupClassB natFamMember [(32, svSumInj0), (33, svSumInj1)] svSumRec = true

def svSumBlockWfT : EnvWfT svSumEnv :=
  EG010T_group_accepted svPairBlockWfT 96 svSumClassB svSumGroupChain

end Rcic.G2

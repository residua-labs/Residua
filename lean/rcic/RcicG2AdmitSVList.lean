/-
RCIC 07 §3 — G2-S1: `EnvWfT` admission of the `SV<list i64>` block
(`svMembersAt svSup svRefOf 16 (.list .i64)`) on top of `SV<bool>`'s
(`svBoolBlockWfT`). `cons : SV<i64> → SV<list i64> → SV<list i64>` has a
self field, so its minor carries one induction hypothesis and its ι reduct
is `m x xs (rec P mnil mcons xs)`.
-/
import rcic.RcicG2AdmitSVBool

set_option maxRecDepth 8192

namespace Rcic.G2
open Rcic.Declarative Rcic.Scm
open Rcic.Scm.SrcG (sortTyAtC foldEnv noRecursorForB_sound ctorContiguousB_sound
  ctorCensusB_sound ctorFieldsPermitted_of_B)

def svListCons : CheckedMember := ctor2Member 16 9 16
def svListRecTy : Expr Nat :=
  svRecTy 16 [(17, []), (18, [⟨.const 9 [], false⟩, ⟨.const 16 [], true⟩])]
def svListRec : CheckedMember := ⟨.recursorM, 1, svListRecTy, none⟩

theorem svListMembers :
    svMembersAt svSup svRefOf 16 (.list .i64) =
      [(16, natFamMember), (17, ctor0Member 16), (18, svListCons), (19, svListRec)] := rfl

def svListTbl (k : Nat) : List (Nat × CheckedMember) :=
  svBoolTbl 4 ++ (svMembersAt svSup svRefOf 16 (.list .i64)).take k

def svListE1 : ResolvedEnv := extendEnv svBoolEnv 16 natFamMember
def svListE2 : ResolvedEnv := extendEnv svListE1 17 (ctor0Member 16)
def svListPrefix : ResolvedEnv := extendEnv svListE2 18 svListCons
def svListEnv : ResolvedEnv := extendEnv svListPrefix 19 svListRec

theorem svListBlockEnv_eq :
    blockEnv svBoolEnv (svMembersAt svSup svRefOf 16 (.list .i64)) = svListEnv := rfl

def svListFamAdmitted : IndGroupAdmitted svBoolEnv 16 natFamMember :=
  .family rfl (sortOneFamView svListE1 16 rfl) rfl rfl (Or.inr uniformType_succ_zero)

def svListNilAdmitted : IndGroupAdmitted svListE1 17 (ctor0Member 16) :=
  .constructor (sortOneFamView svListE1 16 rfl) (ctor0View svListE1 16 rfl) rfl
    ⟨16, rfl, noRecursorForB_sound (tbl := svListTbl 1) (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := svListTbl 1) (by decide) (by decide))
    (fun j => j.elim0) (fun j => j.elim0)

def svListConsAdmitted : IndGroupAdmitted svListE2 18 svListCons :=
  .constructor (sortOneFamView svListE2 16 rfl) (ctor2View svListE2 16 9 16 rfl rfl rfl) rfl
    ⟨16, rfl, noRecursorForB_sound (tbl := svListTbl 2) (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := svListTbl 2) (by decide) (by decide))
    (ctor2Universe _ 16 9 16 rfl rfl rfl) (ctorFieldsPermitted_of_B _ 8 (by decide))

theorem svListCensus : CtorCensus svListPrefix 16 19 :=
  ctorCensusB_sound (tbl := svListTbl 3) (by decide) (by decide)

/-- `P nil`; `Π x xs, P xs → P (cons x xs)`. -/
def svListMinors : List (Expr Nat) :=
  [ .app (.bvar 0) (.const 17 []),
    .pi (.const 9 []) (.pi (.const 16 []) (.pi (.app (.bvar 3) (.bvar 0))
      (.app (.bvar 4) (.app (.app (.const 18 []) (.bvar 2)) (.bvar 1))))) ]

def svListGroupAdm : RecursorEliminationAdmitted svListPrefix 19 svListRec where
  family := sortOneFamView svListPrefix 16 rfl
  constructors := [ctor0Member 16, svListCons]
  constructorViews
    | ⟨0, _⟩ => ctor0View svListPrefix 16 rfl
    | ⟨1, _⟩ => ctor2View svListPrefix 16 9 16 rfl rfl rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  recursorRef := rfl
  minorTypes := svListMinors
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

theorem svListMinorMatch : MinorPremisesMatch svListGroupAdm
  | ⟨0, _⟩ => ⟨[], 8, rfl, rfl⟩
  | ⟨1, _⟩ => ⟨[.nonrecursive, .recursive 0], 8, rfl, rfl⟩

/-- `[mcons, mnil, P]` — `nil`'s equation context. -/
def svListCtx0 : LCtx :=
  [.assumption (svListMinors[1]'(by decide)), .assumption (svListMinors[0]'(by decide)),
    .assumption (.pi (.const 16 []) (.sort (.param 0)))]

/-- `[xs, x, mcons, mnil, P]` — `cons`'s. -/
def svListCtx2 : LCtx := .assumption (.const 16 []) :: .assumption (.const 9 []) :: svListCtx0

def svListRecApplied : Expr Nat :=
  foldApps (.const 19 [.param 0]) [.bvar 4, .bvar 3, .bvar 2, .bvar 0]

def svListRecHeadTy : HasTy svListEnv 1 svListCtx2 (.const 19 [.param 0]) svListRecTy :=
  HasTy.const svListCtx2 19 [.param 0] svListRec rfl rfl (by
    intro l hl
    have hl' : l = .param 0 := by simpa using hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩)

def svListRecAppliedTy :
    HasTy svListEnv 1 svListCtx2 svListRecApplied (.app (.bvar 4) (.bvar 0)) :=
  HasTy.app _ _ _ _ _
    (HasTy.app _ _ _ _ _
      (HasTy.app _ _ _ _ _
        (HasTy.app _ _ _ _ _ svListRecHeadTy (HasTy.bvar _ 4 _ rfl))
        (HasTy.bvar _ 3 _ rfl))
      (HasTy.bvar _ 2 _ rfl))
    (HasTy.bvar _ 0 _ rfl)

/-- `rec P mnil mcons nil ⇝ mnil`. -/
def svListNilIotaTy : HasTy svListEnv 1 svListCtx0 (.bvar 1) (.app (.bvar 2) (.const 17 [])) :=
  HasTy.bvar _ 1 _ rfl

/-- `rec P mnil mcons (cons x xs) ⇝ mcons x xs (rec P mnil mcons xs)`. -/
def svListConsIotaTy :
    HasTy svListEnv 1 svListCtx2
      (.app (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) svListRecApplied)
      (.app (.bvar 4) (.app (.app (.const 18 []) (.bvar 1)) (.bvar 0))) :=
  HasTy.app _ _ _ _ _
    (HasTy.app _ _ _ _ _
      (HasTy.app _ _ _ _ _ (HasTy.bvar svListCtx2 2 _ rfl) (HasTy.bvar svListCtx2 1 _ rfl))
      (HasTy.bvar svListCtx2 0 _ rfl))
    svListRecAppliedTy

def svListIotaNil : IotaEquationTyped svListGroupAdm ⟨0, by decide⟩ 8 [] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact svListNilIotaTy

def svListIotaCons :
    IotaEquationTyped svListGroupAdm ⟨1, by decide⟩ 8 [.nonrecursive, .recursive 0] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact svListConsIotaTy

def svListIotaClause : IotaDescriptorClause svListPrefix svListGroupAdm where
  signatureOnly := rfl
  shapesAt
    | ⟨0, _⟩ => []
    | ⟨1, _⟩ => [.nonrecursive, .recursive 0]
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  typed
    | ⟨0, _⟩ => svListIotaNil
    | ⟨1, _⟩ => svListIotaCons

def svListRecAdmitted : IndGroupAdmitted svListPrefix 19 svListRec :=
  .recursor svListGroupAdm rfl svListCensus
    (fun | ⟨0, _⟩ => fun j => j.elim0 | ⟨1, _⟩ => ctor2Universe _ 16 9 16 rfl rfl rfl)
    (fun | ⟨0, _⟩ => fun j => j.elim0
         | ⟨1, _⟩ => ctorFieldsPermitted_of_B (ctor2View svListPrefix 16 9 16 rfl rfl rfl) 8
              (by decide))
    svListMinorMatch svListIotaClause

kernel_rfl_theorem svListSortB0 : (sortTyAtC svBoolEnv 0 96 [] natFamMember.mtype).isSome = true
kernel_rfl_theorem svListSortB1 : (sortTyAtC svListE1 0 96 [] (ctor0Member 16).mtype).isSome = true
kernel_rfl_theorem svListSortB2 : (sortTyAtC svListE2 0 96 [] svListCons.mtype).isSome = true
kernel_rfl_theorem svListSortB3 : (sortTyAtC svListPrefix 1 96 [] svListRec.mtype).isSome = true

kernel_rfl_theorem svListAccB0 :
    memberAcceptB svListE1 svBoolEnv 96 svListFamAdmitted
      ((sortTyAtC svBoolEnv 0 96 [] natFamMember.mtype).get svListSortB0).1 = true

kernel_rfl_theorem svListAccB1 :
    memberAcceptB svListE1 svListE1 96 svListNilAdmitted
      ((sortTyAtC svListE1 0 96 [] (ctor0Member 16).mtype).get svListSortB1).1 = true

kernel_rfl_theorem svListAccB2 :
    memberAcceptB svListE1 svListE2 96 svListConsAdmitted
      ((sortTyAtC svListE2 0 96 [] svListCons.mtype).get svListSortB2).1 = true

kernel_rfl_theorem svListAccB3 :
    memberAcceptB svListE1 svListPrefix 96 svListRecAdmitted
      ((sortTyAtC svListPrefix 1 96 [] svListRec.mtype).get svListSortB3).1 = true

def svListGroupChain :
    GroupAcceptChain svListE1 96 svBoolEnv
      [(16, natFamMember), (17, ctor0Member 16), (18, svListCons), (19, svListRec)] svListEnv :=
  .cons svBoolEnv 16 natFamMember _ _ svListFamAdmitted svListSortB0 svListAccB0
    (.cons svListE1 17 (ctor0Member 16) _ _ svListNilAdmitted svListSortB1 svListAccB1
      (.cons svListE2 18 svListCons _ _ svListConsAdmitted svListSortB2 svListAccB2
        (.cons svListPrefix 19 svListRec _ _ svListRecAdmitted svListSortB3 svListAccB3
          (.nil svListEnv))))

kernel_rfl_theorem svListClassB :
    groupClassB natFamMember [(17, ctor0Member 16), (18, svListCons)] svListRec = true

def svListBlockWfT : EnvWfT svListEnv :=
  EG010T_group_accepted svBoolBlockWfT 96 svListClassB svListGroupChain

end Rcic.G2

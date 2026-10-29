/-
RCIC 07 §3 — G2-S1: `EnvWfT` admission of the `SV<str>` block
(`svMembersAt svSup svRefOf 20 .str`) on top of `SV<list i64>`'s (`svListBlockWfT`).
Same shape as `SV<list i64>` (`RcicG2AdmitSVList`) with `BNat` (ref 5) as the
element family: `snil`, `scons : BNat → SV<str> → SV<str>` (a code point, then the rest)
— one self field, one induction hypothesis.
-/
import rcic.RcicG2AdmitSVList

set_option maxRecDepth 8192

namespace Rcic.G2
open Rcic.Declarative Rcic.Scm
open Rcic.Scm.SrcG (sortTyAtC foldEnv noRecursorForB_sound ctorContiguousB_sound
  ctorCensusB_sound ctorFieldsPermitted_of_B)

def svStrCons : CheckedMember := ctor2Member 20 5 20
def svStrRecTy : Expr Nat :=
  svRecTy 20 [(21, []), (22, [⟨.const 5 [], false⟩, ⟨.const 20 [], true⟩])]
def svStrRec : CheckedMember := ⟨.recursorM, 1, svStrRecTy, none⟩

theorem svStrMembers :
    svMembersAt svSup svRefOf 20 .str =
      [(20, natFamMember), (21, ctor0Member 20), (22, svStrCons), (23, svStrRec)] := rfl

def svStrTbl (k : Nat) : List (Nat × CheckedMember) :=
  svListTbl 4 ++ (svMembersAt svSup svRefOf 20 .str).take k

def svStrE1 : ResolvedEnv := extendEnv svListEnv 20 natFamMember
def svStrE2 : ResolvedEnv := extendEnv svStrE1 21 (ctor0Member 20)
def svStrPrefix : ResolvedEnv := extendEnv svStrE2 22 svStrCons
def svStrEnv : ResolvedEnv := extendEnv svStrPrefix 23 svStrRec

theorem svStrBlockEnv_eq :
    blockEnv svListEnv (svMembersAt svSup svRefOf 20 .str) = svStrEnv := rfl

def svStrFamAdmitted : IndGroupAdmitted svListEnv 20 natFamMember :=
  .family rfl (sortOneFamView svStrE1 20 rfl) rfl rfl (Or.inr uniformType_succ_zero)

def svStrNilAdmitted : IndGroupAdmitted svStrE1 21 (ctor0Member 20) :=
  .constructor (sortOneFamView svStrE1 20 rfl) (ctor0View svStrE1 20 rfl) rfl
    ⟨20, rfl, noRecursorForB_sound (tbl := svStrTbl 1) (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := svStrTbl 1) (by decide) (by decide))
    (fun j => j.elim0) (fun j => j.elim0)

def svStrConsAdmitted : IndGroupAdmitted svStrE2 22 svStrCons :=
  .constructor (sortOneFamView svStrE2 20 rfl) (ctor2View svStrE2 20 5 20 rfl rfl rfl) rfl
    ⟨20, rfl, noRecursorForB_sound (tbl := svStrTbl 2) (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := svStrTbl 2) (by decide) (by decide))
    (ctor2Universe _ 20 5 20 rfl rfl rfl) (ctorFieldsPermitted_of_B _ 8 (by decide))

theorem svStrCensus : CtorCensus svStrPrefix 20 23 :=
  ctorCensusB_sound (tbl := svStrTbl 3) (by decide) (by decide)

/-- `P nil`; `Π x xs, P xs → P (cons x xs)`. -/
def svStrMinors : List (Expr Nat) :=
  [ .app (.bvar 0) (.const 21 []),
    .pi (.const 5 []) (.pi (.const 20 []) (.pi (.app (.bvar 3) (.bvar 0))
      (.app (.bvar 4) (.app (.app (.const 22 []) (.bvar 2)) (.bvar 1))))) ]

def svStrGroupAdm : RecursorEliminationAdmitted svStrPrefix 23 svStrRec where
  family := sortOneFamView svStrPrefix 20 rfl
  constructors := [ctor0Member 20, svStrCons]
  constructorViews
    | ⟨0, _⟩ => ctor0View svStrPrefix 20 rfl
    | ⟨1, _⟩ => ctor2View svStrPrefix 20 5 20 rfl rfl rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  recursorRef := rfl
  minorTypes := svStrMinors
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

theorem svStrMinorMatch : MinorPremisesMatch svStrGroupAdm
  | ⟨0, _⟩ => ⟨[], 8, rfl, rfl⟩
  | ⟨1, _⟩ => ⟨[.nonrecursive, .recursive 0], 8, rfl, rfl⟩

/-- `[mcons, mnil, P]` — `nil`'s equation context. -/
def svStrCtx0 : LCtx :=
  [.assumption (svStrMinors[1]'(by decide)), .assumption (svStrMinors[0]'(by decide)),
    .assumption (.pi (.const 20 []) (.sort (.param 0)))]

/-- `[xs, x, mcons, mnil, P]` — `cons`'s. -/
def svStrCtx2 : LCtx := .assumption (.const 20 []) :: .assumption (.const 5 []) :: svStrCtx0

def svStrRecApplied : Expr Nat :=
  foldApps (.const 23 [.param 0]) [.bvar 4, .bvar 3, .bvar 2, .bvar 0]

def svStrRecHeadTy : HasTy svStrEnv 1 svStrCtx2 (.const 23 [.param 0]) svStrRecTy :=
  HasTy.const svStrCtx2 23 [.param 0] svStrRec rfl rfl (by
    intro l hl
    have hl' : l = .param 0 := by simpa using hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩)

def svStrRecAppliedTy :
    HasTy svStrEnv 1 svStrCtx2 svStrRecApplied (.app (.bvar 4) (.bvar 0)) :=
  HasTy.app _ _ _ _ _
    (HasTy.app _ _ _ _ _
      (HasTy.app _ _ _ _ _
        (HasTy.app _ _ _ _ _ svStrRecHeadTy (HasTy.bvar _ 4 _ rfl))
        (HasTy.bvar _ 3 _ rfl))
      (HasTy.bvar _ 2 _ rfl))
    (HasTy.bvar _ 0 _ rfl)

/-- `rec P mnil mcons nil ⇝ mnil`. -/
def svStrNilIotaTy : HasTy svStrEnv 1 svStrCtx0 (.bvar 1) (.app (.bvar 2) (.const 21 [])) :=
  HasTy.bvar _ 1 _ rfl

/-- `rec P mnil mcons (cons x xs) ⇝ mcons x xs (rec P mnil mcons xs)`. -/
def svStrConsIotaTy :
    HasTy svStrEnv 1 svStrCtx2
      (.app (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) svStrRecApplied)
      (.app (.bvar 4) (.app (.app (.const 22 []) (.bvar 1)) (.bvar 0))) :=
  HasTy.app _ _ _ _ _
    (HasTy.app _ _ _ _ _
      (HasTy.app _ _ _ _ _ (HasTy.bvar svStrCtx2 2 _ rfl) (HasTy.bvar svStrCtx2 1 _ rfl))
      (HasTy.bvar svStrCtx2 0 _ rfl))
    svStrRecAppliedTy

def svStrIotaNil : IotaEquationTyped svStrGroupAdm ⟨0, by decide⟩ 8 [] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact svStrNilIotaTy

def svStrIotaCons :
    IotaEquationTyped svStrGroupAdm ⟨1, by decide⟩ 8 [.nonrecursive, .recursive 0] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact svStrConsIotaTy

def svStrIotaClause : IotaDescriptorClause svStrPrefix svStrGroupAdm where
  signatureOnly := rfl
  shapesAt
    | ⟨0, _⟩ => []
    | ⟨1, _⟩ => [.nonrecursive, .recursive 0]
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  typed
    | ⟨0, _⟩ => svStrIotaNil
    | ⟨1, _⟩ => svStrIotaCons

def svStrRecAdmitted : IndGroupAdmitted svStrPrefix 23 svStrRec :=
  .recursor svStrGroupAdm rfl svStrCensus
    (fun | ⟨0, _⟩ => fun j => j.elim0 | ⟨1, _⟩ => ctor2Universe _ 20 5 20 rfl rfl rfl)
    (fun | ⟨0, _⟩ => fun j => j.elim0
         | ⟨1, _⟩ => ctorFieldsPermitted_of_B (ctor2View svStrPrefix 20 5 20 rfl rfl rfl) 8
              (by decide))
    svStrMinorMatch svStrIotaClause

kernel_rfl_theorem svStrSortB0 : (sortTyAtC svListEnv 0 96 [] natFamMember.mtype).isSome = true
kernel_rfl_theorem svStrSortB1 : (sortTyAtC svStrE1 0 96 [] (ctor0Member 20).mtype).isSome = true
kernel_rfl_theorem svStrSortB2 : (sortTyAtC svStrE2 0 96 [] svStrCons.mtype).isSome = true
kernel_rfl_theorem svStrSortB3 : (sortTyAtC svStrPrefix 1 96 [] svStrRec.mtype).isSome = true

kernel_rfl_theorem svStrAccB0 :
    memberAcceptB svStrE1 svListEnv 96 svStrFamAdmitted
      ((sortTyAtC svListEnv 0 96 [] natFamMember.mtype).get svStrSortB0).1 = true

kernel_rfl_theorem svStrAccB1 :
    memberAcceptB svStrE1 svStrE1 96 svStrNilAdmitted
      ((sortTyAtC svStrE1 0 96 [] (ctor0Member 20).mtype).get svStrSortB1).1 = true

kernel_rfl_theorem svStrAccB2 :
    memberAcceptB svStrE1 svStrE2 96 svStrConsAdmitted
      ((sortTyAtC svStrE2 0 96 [] svStrCons.mtype).get svStrSortB2).1 = true

kernel_rfl_theorem svStrAccB3 :
    memberAcceptB svStrE1 svStrPrefix 96 svStrRecAdmitted
      ((sortTyAtC svStrPrefix 1 96 [] svStrRec.mtype).get svStrSortB3).1 = true

def svStrGroupChain :
    GroupAcceptChain svStrE1 96 svListEnv
      [(20, natFamMember), (21, ctor0Member 20), (22, svStrCons), (23, svStrRec)] svStrEnv :=
  .cons svListEnv 20 natFamMember _ _ svStrFamAdmitted svStrSortB0 svStrAccB0
    (.cons svStrE1 21 (ctor0Member 20) _ _ svStrNilAdmitted svStrSortB1 svStrAccB1
      (.cons svStrE2 22 svStrCons _ _ svStrConsAdmitted svStrSortB2 svStrAccB2
        (.cons svStrPrefix 23 svStrRec _ _ svStrRecAdmitted svStrSortB3 svStrAccB3
          (.nil svStrEnv))))

kernel_rfl_theorem svStrClassB :
    groupClassB natFamMember [(21, ctor0Member 20), (22, svStrCons)] svStrRec = true

def svStrBlockWfT : EnvWfT svStrEnv :=
  EG010T_group_accepted svListBlockWfT 96 svStrClassB svStrGroupChain

end Rcic.G2

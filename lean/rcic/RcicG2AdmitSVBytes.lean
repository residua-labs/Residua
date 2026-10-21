/-
RCIC 07 §3 — G2-S1: `EnvWfT` admission of the `SV<bytes>` block
(`svMembersAt svSup svRefOf 24 .bytes`) on top of `SV<str>`'s (`svStrBlockWfT`).
Same shape as `SV<list i64>` (`RcicG2AdmitSVList`) with `BNat` (ref 5) as the
element family: `bnil`, `bcons : BNat → SV<bytes> → SV<bytes>` (a byte, then the rest)
— one self field, one induction hypothesis.
-/
import rcic.RcicG2AdmitSVStr

set_option maxRecDepth 8192

namespace Rcic.G2
open Rcic.Declarative Rcic.Scm
open Rcic.Scm.SrcG (sortTyAtC foldEnv noRecursorForB_sound ctorContiguousB_sound
  ctorCensusB_sound ctorFieldsPermitted_of_B)

def svBytesCons : CheckedMember := ctor2Member 24 5 24
def svBytesRecTy : Expr Nat :=
  svRecTy 24 [(25, []), (26, [⟨.const 5 [], false⟩, ⟨.const 24 [], true⟩])]
def svBytesRec : CheckedMember := ⟨.recursorM, 1, svBytesRecTy, none⟩

theorem svBytesMembers :
    svMembersAt svSup svRefOf 24 .bytes =
      [(24, natFamMember), (25, ctor0Member 24), (26, svBytesCons), (27, svBytesRec)] := rfl

def svBytesTbl (k : Nat) : List (Nat × CheckedMember) :=
  svStrTbl 4 ++ (svMembersAt svSup svRefOf 24 .bytes).take k

def svBytesE1 : ResolvedEnv := extendEnv svStrEnv 24 natFamMember
def svBytesE2 : ResolvedEnv := extendEnv svBytesE1 25 (ctor0Member 24)
def svBytesPrefix : ResolvedEnv := extendEnv svBytesE2 26 svBytesCons
def svBytesEnv : ResolvedEnv := extendEnv svBytesPrefix 27 svBytesRec

theorem svBytesBlockEnv_eq :
    blockEnv svStrEnv (svMembersAt svSup svRefOf 24 .bytes) = svBytesEnv := rfl

def svBytesFamAdmitted : IndGroupAdmitted svStrEnv 24 natFamMember :=
  .family rfl (sortOneFamView svBytesE1 24 rfl) rfl rfl (Or.inr uniformType_succ_zero)

def svBytesNilAdmitted : IndGroupAdmitted svBytesE1 25 (ctor0Member 24) :=
  .constructor (sortOneFamView svBytesE1 24 rfl) (ctor0View svBytesE1 24 rfl) rfl
    ⟨24, rfl, noRecursorForB_sound (tbl := svBytesTbl 1) (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := svBytesTbl 1) (by decide) (by decide))
    (fun j => j.elim0) (fun j => j.elim0)

def svBytesConsAdmitted : IndGroupAdmitted svBytesE2 26 svBytesCons :=
  .constructor (sortOneFamView svBytesE2 24 rfl) (ctor2View svBytesE2 24 5 24 rfl rfl rfl) rfl
    ⟨24, rfl, noRecursorForB_sound (tbl := svBytesTbl 2) (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := svBytesTbl 2) (by decide) (by decide))
    (ctor2Universe _ 24 5 24 rfl rfl rfl) (ctorFieldsPermitted_of_B _ 8 (by decide))

theorem svBytesCensus : CtorCensus svBytesPrefix 24 27 :=
  ctorCensusB_sound (tbl := svBytesTbl 3) (by decide) (by decide)

/-- `P nil`; `Π x xs, P xs → P (cons x xs)`. -/
def svBytesMinors : List (Expr Nat) :=
  [ .app (.bvar 0) (.const 25 []),
    .pi (.const 5 []) (.pi (.const 24 []) (.pi (.app (.bvar 3) (.bvar 0))
      (.app (.bvar 4) (.app (.app (.const 26 []) (.bvar 2)) (.bvar 1))))) ]

def svBytesGroupAdm : RecursorEliminationAdmitted svBytesPrefix 27 svBytesRec where
  family := sortOneFamView svBytesPrefix 24 rfl
  constructors := [ctor0Member 24, svBytesCons]
  constructorViews
    | ⟨0, _⟩ => ctor0View svBytesPrefix 24 rfl
    | ⟨1, _⟩ => ctor2View svBytesPrefix 24 5 24 rfl rfl rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  recursorRef := rfl
  minorTypes := svBytesMinors
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

theorem svBytesMinorMatch : MinorPremisesMatch svBytesGroupAdm
  | ⟨0, _⟩ => ⟨[], 8, rfl, rfl⟩
  | ⟨1, _⟩ => ⟨[.nonrecursive, .recursive 0], 8, rfl, rfl⟩

/-- `[mcons, mnil, P]` — `nil`'s equation context. -/
def svBytesCtx0 : LCtx :=
  [.assumption (svBytesMinors[1]'(by decide)), .assumption (svBytesMinors[0]'(by decide)),
    .assumption (.pi (.const 24 []) (.sort (.param 0)))]

/-- `[xs, x, mcons, mnil, P]` — `cons`'s. -/
def svBytesCtx2 : LCtx := .assumption (.const 24 []) :: .assumption (.const 5 []) :: svBytesCtx0

def svBytesRecApplied : Expr Nat :=
  foldApps (.const 27 [.param 0]) [.bvar 4, .bvar 3, .bvar 2, .bvar 0]

def svBytesRecHeadTy : HasTy svBytesEnv 1 svBytesCtx2 (.const 27 [.param 0]) svBytesRecTy :=
  HasTy.const svBytesCtx2 27 [.param 0] svBytesRec rfl rfl (by
    intro l hl
    have hl' : l = .param 0 := by simpa using hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩)

def svBytesRecAppliedTy :
    HasTy svBytesEnv 1 svBytesCtx2 svBytesRecApplied (.app (.bvar 4) (.bvar 0)) :=
  HasTy.app _ _ _ _ _
    (HasTy.app _ _ _ _ _
      (HasTy.app _ _ _ _ _
        (HasTy.app _ _ _ _ _ svBytesRecHeadTy (HasTy.bvar _ 4 _ rfl))
        (HasTy.bvar _ 3 _ rfl))
      (HasTy.bvar _ 2 _ rfl))
    (HasTy.bvar _ 0 _ rfl)

/-- `rec P mnil mcons nil ⇝ mnil`. -/
def svBytesNilIotaTy : HasTy svBytesEnv 1 svBytesCtx0 (.bvar 1) (.app (.bvar 2) (.const 25 [])) :=
  HasTy.bvar _ 1 _ rfl

/-- `rec P mnil mcons (cons x xs) ⇝ mcons x xs (rec P mnil mcons xs)`. -/
def svBytesConsIotaTy :
    HasTy svBytesEnv 1 svBytesCtx2
      (.app (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) svBytesRecApplied)
      (.app (.bvar 4) (.app (.app (.const 26 []) (.bvar 1)) (.bvar 0))) :=
  HasTy.app _ _ _ _ _
    (HasTy.app _ _ _ _ _
      (HasTy.app _ _ _ _ _ (HasTy.bvar svBytesCtx2 2 _ rfl) (HasTy.bvar svBytesCtx2 1 _ rfl))
      (HasTy.bvar svBytesCtx2 0 _ rfl))
    svBytesRecAppliedTy

def svBytesIotaNil : IotaEquationTyped svBytesGroupAdm ⟨0, by decide⟩ 8 [] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact svBytesNilIotaTy

def svBytesIotaCons :
    IotaEquationTyped svBytesGroupAdm ⟨1, by decide⟩ 8 [.nonrecursive, .recursive 0] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact svBytesConsIotaTy

def svBytesIotaClause : IotaDescriptorClause svBytesPrefix svBytesGroupAdm where
  signatureOnly := rfl
  shapesAt
    | ⟨0, _⟩ => []
    | ⟨1, _⟩ => [.nonrecursive, .recursive 0]
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  typed
    | ⟨0, _⟩ => svBytesIotaNil
    | ⟨1, _⟩ => svBytesIotaCons

def svBytesRecAdmitted : IndGroupAdmitted svBytesPrefix 27 svBytesRec :=
  .recursor svBytesGroupAdm rfl svBytesCensus
    (fun | ⟨0, _⟩ => fun j => j.elim0 | ⟨1, _⟩ => ctor2Universe _ 24 5 24 rfl rfl rfl)
    (fun | ⟨0, _⟩ => fun j => j.elim0
         | ⟨1, _⟩ => ctorFieldsPermitted_of_B (ctor2View svBytesPrefix 24 5 24 rfl rfl rfl) 8
              (by decide))
    svBytesMinorMatch svBytesIotaClause

kernel_rfl_theorem svBytesSortB0 : (sortTyAtC svStrEnv 0 96 [] natFamMember.mtype).isSome = true
kernel_rfl_theorem svBytesSortB1 : (sortTyAtC svBytesE1 0 96 [] (ctor0Member 24).mtype).isSome = true
kernel_rfl_theorem svBytesSortB2 : (sortTyAtC svBytesE2 0 96 [] svBytesCons.mtype).isSome = true
kernel_rfl_theorem svBytesSortB3 : (sortTyAtC svBytesPrefix 1 96 [] svBytesRec.mtype).isSome = true

kernel_rfl_theorem svBytesAccB0 :
    memberAcceptB svBytesE1 svStrEnv 96 svBytesFamAdmitted
      ((sortTyAtC svStrEnv 0 96 [] natFamMember.mtype).get svBytesSortB0).1 = true

kernel_rfl_theorem svBytesAccB1 :
    memberAcceptB svBytesE1 svBytesE1 96 svBytesNilAdmitted
      ((sortTyAtC svBytesE1 0 96 [] (ctor0Member 24).mtype).get svBytesSortB1).1 = true

kernel_rfl_theorem svBytesAccB2 :
    memberAcceptB svBytesE1 svBytesE2 96 svBytesConsAdmitted
      ((sortTyAtC svBytesE2 0 96 [] svBytesCons.mtype).get svBytesSortB2).1 = true

kernel_rfl_theorem svBytesAccB3 :
    memberAcceptB svBytesE1 svBytesPrefix 96 svBytesRecAdmitted
      ((sortTyAtC svBytesPrefix 1 96 [] svBytesRec.mtype).get svBytesSortB3).1 = true

def svBytesGroupChain :
    GroupAcceptChain svBytesE1 96 svStrEnv
      [(24, natFamMember), (25, ctor0Member 24), (26, svBytesCons), (27, svBytesRec)] svBytesEnv :=
  .cons svStrEnv 24 natFamMember _ _ svBytesFamAdmitted svBytesSortB0 svBytesAccB0
    (.cons svBytesE1 25 (ctor0Member 24) _ _ svBytesNilAdmitted svBytesSortB1 svBytesAccB1
      (.cons svBytesE2 26 svBytesCons _ _ svBytesConsAdmitted svBytesSortB2 svBytesAccB2
        (.cons svBytesPrefix 27 svBytesRec _ _ svBytesRecAdmitted svBytesSortB3 svBytesAccB3
          (.nil svBytesEnv))))

kernel_rfl_theorem svBytesClassB :
    groupClassB natFamMember [(25, ctor0Member 24), (26, svBytesCons)] svBytesRec = true

def svBytesBlockWfT : EnvWfT svBytesEnv :=
  EG010T_group_accepted svStrBlockWfT 96 svBytesClassB svBytesGroupChain

end Rcic.G2

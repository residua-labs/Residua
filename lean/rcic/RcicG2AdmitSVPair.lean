/-
RCIC 07 §3 — G2-S1: `EnvWfT` admission of the `SV<pair i64 bool>` block
(`svMembersAt svSup svRefOf 28 (.pair .i64 .bool)`) on top of `SV<bytes>`'s
(`svBytesBlockWfT`). One constructor `mk : SV<i64> → SV<bool> → SV<pair …>`,
two foreign fields, no induction hypothesis.
-/
import rcic.RcicG2AdmitSVBytes

set_option maxRecDepth 8192

namespace Rcic.G2
open Rcic.Declarative Rcic.Scm
open Rcic.Scm.SrcG (sortTyAtC foldEnv noRecursorForB_sound ctorContiguousB_sound
  ctorCensusB_sound ctorFieldsPermitted_of_B)

def svPairMk : CheckedMember := ctor2Member 28 9 12
def svPairRec : CheckedMember :=
  ⟨.recursorM, 1, svRecTy 28 [(29, [⟨.const 9 [], false⟩, ⟨.const 12 [], false⟩])], none⟩

theorem svPairMembers :
    svMembersAt svSup svRefOf 28 (.pair .i64 .bool) =
      [(28, natFamMember), (29, svPairMk), (30, svPairRec)] := rfl

def svPairTbl (k : Nat) : List (Nat × CheckedMember) :=
  svBytesTbl 4 ++ (svMembersAt svSup svRefOf 28 (.pair .i64 .bool)).take k

def svPairE1 : ResolvedEnv := extendEnv svBytesEnv 28 natFamMember
def svPairPrefix : ResolvedEnv := extendEnv svPairE1 29 svPairMk
def svPairEnv : ResolvedEnv := extendEnv svPairPrefix 30 svPairRec

theorem svPairBlockEnv_eq :
    blockEnv svBytesEnv (svMembersAt svSup svRefOf 28 (.pair .i64 .bool)) = svPairEnv := rfl

def svPairFamAdmitted : IndGroupAdmitted svBytesEnv 28 natFamMember :=
  .family rfl (sortOneFamView svPairE1 28 rfl) rfl rfl (Or.inr uniformType_succ_zero)

def svPairMkAdmitted : IndGroupAdmitted svPairE1 29 svPairMk :=
  .constructor (sortOneFamView svPairE1 28 rfl) (ctor2View svPairE1 28 9 12 rfl rfl rfl) rfl
    ⟨28, rfl, noRecursorForB_sound (tbl := svPairTbl 1) (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := svPairTbl 1) (by decide) (by decide))
    (ctor2Universe _ 28 9 12 rfl rfl rfl) (ctorFieldsPermitted_of_B _ 8 (by decide))

theorem svPairCensus : CtorCensus svPairPrefix 28 30 :=
  ctorCensusB_sound (tbl := svPairTbl 2) (by decide) (by decide)

/-- `Π a b, P (mk a b)`. -/
def svPairMinors : List (Expr Nat) :=
  [.pi (.const 9 []) (.pi (.const 12 [])
    (.app (.bvar 2) (.app (.app (.const 29 []) (.bvar 1)) (.bvar 0))))]

def svPairGroupAdm : RecursorEliminationAdmitted svPairPrefix 30 svPairRec where
  family := sortOneFamView svPairPrefix 28 rfl
  constructors := [svPairMk]
  constructorViews | ⟨0, _⟩ => ctor2View svPairPrefix 28 9 12 rfl rfl rfl
  constructorsPresent | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := svPairMinors
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

theorem svPairMinorMatch : MinorPremisesMatch svPairGroupAdm
  | ⟨0, _⟩ => ⟨[.nonrecursive, .nonrecursive], 8, rfl, rfl⟩

/-- `[b, a, m, P]`. -/
def svPairCtx : LCtx :=
  [.assumption (.const 12 []), .assumption (.const 9 []),
    .assumption (svPairMinors[0]'(by decide)),
    .assumption (.pi (.const 28 []) (.sort (.param 0)))]

/-- `rec P m (mk a b) ⇝ m a b`. -/
def svPairIotaTy :
    HasTy svPairEnv 1 svPairCtx (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
      (.app (.bvar 3) (.app (.app (.const 29 []) (.bvar 1)) (.bvar 0))) :=
  HasTy.app _ _ _ _ _
    (HasTy.app _ _ _ _ _ (HasTy.bvar svPairCtx 2 _ rfl) (HasTy.bvar svPairCtx 1 _ rfl))
    (HasTy.bvar svPairCtx 0 _ rfl)

def svPairIotaMk :
    IotaEquationTyped svPairGroupAdm ⟨0, by decide⟩ 8 [.nonrecursive, .nonrecursive] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact svPairIotaTy

def svPairIotaClause : IotaDescriptorClause svPairPrefix svPairGroupAdm where
  signatureOnly := rfl
  shapesAt := fun | ⟨0, _⟩ => [.nonrecursive, .nonrecursive]
  fuelAt := fun _ => 8
  analyzed | ⟨0, _⟩ => rfl
  typed | ⟨0, _⟩ => svPairIotaMk

def svPairRecAdmitted : IndGroupAdmitted svPairPrefix 30 svPairRec :=
  .recursor svPairGroupAdm rfl svPairCensus
    (fun | ⟨0, _⟩ => ctor2Universe _ 28 9 12 rfl rfl rfl)
    (fun | ⟨0, _⟩ => ctorFieldsPermitted_of_B (ctor2View svPairPrefix 28 9 12 rfl rfl rfl) 8
            (by decide))
    svPairMinorMatch svPairIotaClause

kernel_rfl_theorem svPairSortB0 : (sortTyAtC svBytesEnv 0 96 [] natFamMember.mtype).isSome = true
kernel_rfl_theorem svPairSortB1 : (sortTyAtC svPairE1 0 96 [] svPairMk.mtype).isSome = true
kernel_rfl_theorem svPairSortB2 : (sortTyAtC svPairPrefix 1 96 [] svPairRec.mtype).isSome = true

kernel_rfl_theorem svPairAccB0 :
    memberAcceptB svPairE1 svBytesEnv 96 svPairFamAdmitted
      ((sortTyAtC svBytesEnv 0 96 [] natFamMember.mtype).get svPairSortB0).1 = true

kernel_rfl_theorem svPairAccB1 :
    memberAcceptB svPairE1 svPairE1 96 svPairMkAdmitted
      ((sortTyAtC svPairE1 0 96 [] svPairMk.mtype).get svPairSortB1).1 = true

kernel_rfl_theorem svPairAccB2 :
    memberAcceptB svPairE1 svPairPrefix 96 svPairRecAdmitted
      ((sortTyAtC svPairPrefix 1 96 [] svPairRec.mtype).get svPairSortB2).1 = true

def svPairGroupChain :
    GroupAcceptChain svPairE1 96 svBytesEnv [(28, natFamMember), (29, svPairMk), (30, svPairRec)]
      svPairEnv :=
  .cons svBytesEnv 28 natFamMember _ _ svPairFamAdmitted svPairSortB0 svPairAccB0
    (.cons svPairE1 29 svPairMk _ _ svPairMkAdmitted svPairSortB1 svPairAccB1
      (.cons svPairPrefix 30 svPairRec _ _ svPairRecAdmitted svPairSortB2 svPairAccB2
        (.nil svPairEnv)))

kernel_rfl_theorem svPairClassB : groupClassB natFamMember [(29, svPairMk)] svPairRec = true

def svPairBlockWfT : EnvWfT svPairEnv :=
  EG010T_group_accepted svBytesBlockWfT 96 svPairClassB svPairGroupChain

end Rcic.G2

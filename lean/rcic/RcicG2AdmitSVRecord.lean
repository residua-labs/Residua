/-
RCIC 07 §3 — G2-S1: `EnvWfT` admission of the `SV<record [a : i64, b : bool]>` block
(`svMembersAt svSup svRefOf 35 svRecordTy`) on top of `SV<sum [i64, bool]>`'s
(`svSumBlockWfT`). One constructor whose fields are the record's, in schema
order (`mk : SV<i64> → SV<bool> → SV<record …>`) — `SV<pair>`'s shape
(`RcicG2AdmitSVPair`); keys are not part of the block.
-/
import rcic.RcicG2AdmitSVSum

set_option maxRecDepth 8192

namespace Rcic.G2
open Rcic.Declarative Rcic.Scm
open Rcic.Scm.SrcG (sortTyAtC foldEnv noRecursorForB_sound ctorContiguousB_sound
  ctorCensusB_sound ctorFieldsPermitted_of_B)

/-- schema order `a`, `b`. -/
def svRecordTy : CoreTy := .record [("a", .i64), ("b", .bool)]

def svRecordMk : CheckedMember := ctor2Member 35 9 12
def svRecordRec : CheckedMember :=
  ⟨.recursorM, 1, svRecTy 35 [(36, [⟨.const 9 [], false⟩, ⟨.const 12 [], false⟩])], none⟩

theorem svRecordMembers :
    svMembersAt svSup svRefOf 35 svRecordTy =
      [(35, natFamMember), (36, svRecordMk), (37, svRecordRec)] := rfl

def svRecordTbl (k : Nat) : List (Nat × CheckedMember) :=
  svSumTbl 4 ++ (svMembersAt svSup svRefOf 35 svRecordTy).take k

def svRecordE1 : ResolvedEnv := extendEnv svSumEnv 35 natFamMember
def svRecordPrefix : ResolvedEnv := extendEnv svRecordE1 36 svRecordMk
def svRecordEnv : ResolvedEnv := extendEnv svRecordPrefix 37 svRecordRec

theorem svRecordBlockEnv_eq :
    blockEnv svSumEnv (svMembersAt svSup svRefOf 35 svRecordTy) = svRecordEnv := rfl

def svRecordFamAdmitted : IndGroupAdmitted svSumEnv 35 natFamMember :=
  .family rfl (sortOneFamView svRecordE1 35 rfl) rfl rfl (Or.inr uniformType_succ_zero)

def svRecordMkAdmitted : IndGroupAdmitted svRecordE1 36 svRecordMk :=
  .constructor (sortOneFamView svRecordE1 35 rfl) (ctor2View svRecordE1 35 9 12 rfl rfl rfl) rfl
    ⟨35, rfl, noRecursorForB_sound (tbl := svRecordTbl 1) (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := svRecordTbl 1) (by decide) (by decide))
    (ctor2Universe _ 35 9 12 rfl rfl rfl) (ctorFieldsPermitted_of_B _ 8 (by decide))

theorem svRecordCensus : CtorCensus svRecordPrefix 35 37 :=
  ctorCensusB_sound (tbl := svRecordTbl 2) (by decide) (by decide)

/-- `Π a b, P (mk a b)`. -/
def svRecordMinors : List (Expr Nat) :=
  [.pi (.const 9 []) (.pi (.const 12 [])
    (.app (.bvar 2) (.app (.app (.const 36 []) (.bvar 1)) (.bvar 0))))]

def svRecordGroupAdm : RecursorEliminationAdmitted svRecordPrefix 37 svRecordRec where
  family := sortOneFamView svRecordPrefix 35 rfl
  constructors := [svRecordMk]
  constructorViews | ⟨0, _⟩ => ctor2View svRecordPrefix 35 9 12 rfl rfl rfl
  constructorsPresent | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := svRecordMinors
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

theorem svRecordMinorMatch : MinorPremisesMatch svRecordGroupAdm
  | ⟨0, _⟩ => ⟨[.nonrecursive, .nonrecursive], 8, rfl, rfl⟩

/-- `[b, a, m, P]`. -/
def svRecordCtx : LCtx :=
  [.assumption (.const 12 []), .assumption (.const 9 []),
    .assumption (svRecordMinors[0]'(by decide)),
    .assumption (.pi (.const 35 []) (.sort (.param 0)))]

/-- `rec P m (mk a b) ⇝ m a b`. -/
def svRecordIotaTy :
    HasTy svRecordEnv 1 svRecordCtx (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
      (.app (.bvar 3) (.app (.app (.const 36 []) (.bvar 1)) (.bvar 0))) :=
  HasTy.app _ _ _ _ _
    (HasTy.app _ _ _ _ _ (HasTy.bvar svRecordCtx 2 _ rfl) (HasTy.bvar svRecordCtx 1 _ rfl))
    (HasTy.bvar svRecordCtx 0 _ rfl)

def svRecordIotaMk :
    IotaEquationTyped svRecordGroupAdm ⟨0, by decide⟩ 8 [.nonrecursive, .nonrecursive] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact svRecordIotaTy

def svRecordIotaClause : IotaDescriptorClause svRecordPrefix svRecordGroupAdm where
  signatureOnly := rfl
  shapesAt := fun | ⟨0, _⟩ => [.nonrecursive, .nonrecursive]
  fuelAt := fun _ => 8
  analyzed | ⟨0, _⟩ => rfl
  typed | ⟨0, _⟩ => svRecordIotaMk

def svRecordRecAdmitted : IndGroupAdmitted svRecordPrefix 37 svRecordRec :=
  .recursor svRecordGroupAdm rfl svRecordCensus
    (fun | ⟨0, _⟩ => ctor2Universe _ 35 9 12 rfl rfl rfl)
    (fun | ⟨0, _⟩ => ctorFieldsPermitted_of_B (ctor2View svRecordPrefix 35 9 12 rfl rfl rfl) 8
            (by decide))
    svRecordMinorMatch svRecordIotaClause

kernel_rfl_theorem svRecordSortB0 : (sortTyAtC svSumEnv 0 96 [] natFamMember.mtype).isSome = true
kernel_rfl_theorem svRecordSortB1 : (sortTyAtC svRecordE1 0 96 [] svRecordMk.mtype).isSome = true
kernel_rfl_theorem svRecordSortB2 : (sortTyAtC svRecordPrefix 1 96 [] svRecordRec.mtype).isSome = true

kernel_rfl_theorem svRecordAccB0 :
    memberAcceptB svRecordE1 svSumEnv 96 svRecordFamAdmitted
      ((sortTyAtC svSumEnv 0 96 [] natFamMember.mtype).get svRecordSortB0).1 = true

kernel_rfl_theorem svRecordAccB1 :
    memberAcceptB svRecordE1 svRecordE1 96 svRecordMkAdmitted
      ((sortTyAtC svRecordE1 0 96 [] svRecordMk.mtype).get svRecordSortB1).1 = true

kernel_rfl_theorem svRecordAccB2 :
    memberAcceptB svRecordE1 svRecordPrefix 96 svRecordRecAdmitted
      ((sortTyAtC svRecordPrefix 1 96 [] svRecordRec.mtype).get svRecordSortB2).1 = true

def svRecordGroupChain :
    GroupAcceptChain svRecordE1 96 svSumEnv [(35, natFamMember), (36, svRecordMk), (37, svRecordRec)]
      svRecordEnv :=
  .cons svSumEnv 35 natFamMember _ _ svRecordFamAdmitted svRecordSortB0 svRecordAccB0
    (.cons svRecordE1 36 svRecordMk _ _ svRecordMkAdmitted svRecordSortB1 svRecordAccB1
      (.cons svRecordPrefix 37 svRecordRec _ _ svRecordRecAdmitted svRecordSortB2 svRecordAccB2
        (.nil svRecordEnv)))

kernel_rfl_theorem svRecordClassB : groupClassB natFamMember [(36, svRecordMk)] svRecordRec = true

def svRecordBlockWfT : EnvWfT svRecordEnv :=
  EG010T_group_accepted svSumBlockWfT 96 svRecordClassB svRecordGroupChain

end Rcic.G2

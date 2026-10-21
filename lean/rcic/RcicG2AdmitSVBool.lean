/-
RCIC 07 §3 — G2-S1: `EnvWfT` admission of the `SV<bool>` block
(`svMembersAt svSup svRefOf 12 .bool`) on top of `SV<i64>`'s
(`svI64BlockWfT`). Two field-free constructors `ff`/`tt`, so each ι
reduct is its minor variable.
-/
import rcic.RcicG2AdmitSVI64

set_option maxRecDepth 8192

namespace Rcic.G2
open Rcic.Declarative Rcic.Scm
open Rcic.Scm.SrcG (sortTyAtC foldEnv noRecursorForB_sound ctorContiguousB_sound
  ctorCensusB_sound)

def svBoolRec : CheckedMember := ⟨.recursorM, 1, svRecTy 12 [(13, []), (14, [])], none⟩

theorem svBoolMembers :
    svMembersAt svSup svRefOf 12 .bool =
      [(12, natFamMember), (13, ctor0Member 12), (14, ctor0Member 12), (15, svBoolRec)] := rfl

def svBoolTbl (k : Nat) : List (Nat × CheckedMember) :=
  svI64Tbl 3 ++ (svMembersAt svSup svRefOf 12 .bool).take k

def svBoolE1 : ResolvedEnv := extendEnv svI64Env 12 natFamMember
def svBoolE2 : ResolvedEnv := extendEnv svBoolE1 13 (ctor0Member 12)
def svBoolPrefix : ResolvedEnv := extendEnv svBoolE2 14 (ctor0Member 12)
def svBoolEnv : ResolvedEnv := extendEnv svBoolPrefix 15 svBoolRec

theorem svBoolBlockEnv_eq :
    blockEnv svI64Env (svMembersAt svSup svRefOf 12 .bool) = svBoolEnv := rfl

def svBoolFamAdmitted : IndGroupAdmitted svI64Env 12 natFamMember :=
  .family rfl (sortOneFamView svBoolE1 12 rfl) rfl rfl (Or.inr uniformType_succ_zero)

def svBoolFFAdmitted : IndGroupAdmitted svBoolE1 13 (ctor0Member 12) :=
  .constructor (sortOneFamView svBoolE1 12 rfl) (ctor0View svBoolE1 12 rfl) rfl
    ⟨12, rfl, noRecursorForB_sound (tbl := svBoolTbl 1) (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := svBoolTbl 1) (by decide) (by decide))
    (fun j => j.elim0) (fun j => j.elim0)

def svBoolTTAdmitted : IndGroupAdmitted svBoolE2 14 (ctor0Member 12) :=
  .constructor (sortOneFamView svBoolE2 12 rfl) (ctor0View svBoolE2 12 rfl) rfl
    ⟨12, rfl, noRecursorForB_sound (tbl := svBoolTbl 2) (by decide) (by decide)⟩
    (ctorContiguousB_sound (tbl := svBoolTbl 2) (by decide) (by decide))
    (fun j => j.elim0) (fun j => j.elim0)

theorem svBoolCensus : CtorCensus svBoolPrefix 12 15 :=
  ctorCensusB_sound (tbl := svBoolTbl 3) (by decide) (by decide)

def svBoolMinors : List (Expr Nat) :=
  [.app (.bvar 0) (.const 13 []), .app (.bvar 1) (.const 14 [])]

def svBoolGroupAdm : RecursorEliminationAdmitted svBoolPrefix 15 svBoolRec where
  family := sortOneFamView svBoolPrefix 12 rfl
  constructors := [ctor0Member 12, ctor0Member 12]
  constructorViews
    | ⟨0, _⟩ => ctor0View svBoolPrefix 12 rfl
    | ⟨1, _⟩ => ctor0View svBoolPrefix 12 rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  recursorRef := rfl
  minorTypes := svBoolMinors
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

theorem svBoolMinorMatch : MinorPremisesMatch svBoolGroupAdm
  | ⟨0, _⟩ => ⟨[], 0, rfl, rfl⟩
  | ⟨1, _⟩ => ⟨[], 0, rfl, rfl⟩

/-- `[mt, mf, P]`. -/
def svBoolEqCtx : LCtx :=
  [.assumption (.app (.bvar 1) (.const 14 [])), .assumption (.app (.bvar 0) (.const 13 [])),
    .assumption (.pi (.const 12 []) (.sort (.param 0)))]

def svBoolIotaFF : IotaEquationTyped svBoolGroupAdm ⟨0, by decide⟩ 0 [] := by
  unfold IotaEquationTyped
  exact HasTy.bvar svBoolEqCtx 1 _ rfl

def svBoolIotaTT : IotaEquationTyped svBoolGroupAdm ⟨1, by decide⟩ 0 [] := by
  unfold IotaEquationTyped
  exact HasTy.bvar svBoolEqCtx 0 _ rfl

def svBoolIotaClause : IotaDescriptorClause svBoolPrefix svBoolGroupAdm where
  signatureOnly := rfl
  shapesAt := fun _ => []
  fuelAt := fun _ => 0
  analyzed
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  typed
    | ⟨0, _⟩ => svBoolIotaFF
    | ⟨1, _⟩ => svBoolIotaTT

def svBoolRecAdmitted : IndGroupAdmitted svBoolPrefix 15 svBoolRec :=
  .recursor svBoolGroupAdm rfl svBoolCensus
    (fun | ⟨0, _⟩ => fun j => j.elim0 | ⟨1, _⟩ => fun j => j.elim0)
    (fun | ⟨0, _⟩ => fun j => j.elim0 | ⟨1, _⟩ => fun j => j.elim0)
    svBoolMinorMatch svBoolIotaClause

kernel_rfl_theorem svBoolSortB0 : (sortTyAtC svI64Env 0 96 [] natFamMember.mtype).isSome = true
kernel_rfl_theorem svBoolSortB1 : (sortTyAtC svBoolE1 0 96 [] (ctor0Member 12).mtype).isSome = true
kernel_rfl_theorem svBoolSortB2 : (sortTyAtC svBoolE2 0 96 [] (ctor0Member 12).mtype).isSome = true
kernel_rfl_theorem svBoolSortB3 : (sortTyAtC svBoolPrefix 1 96 [] svBoolRec.mtype).isSome = true

kernel_rfl_theorem svBoolAccB0 :
    memberAcceptB svBoolE1 svI64Env 96 svBoolFamAdmitted
      ((sortTyAtC svI64Env 0 96 [] natFamMember.mtype).get svBoolSortB0).1 = true

kernel_rfl_theorem svBoolAccB1 :
    memberAcceptB svBoolE1 svBoolE1 96 svBoolFFAdmitted
      ((sortTyAtC svBoolE1 0 96 [] (ctor0Member 12).mtype).get svBoolSortB1).1 = true

kernel_rfl_theorem svBoolAccB2 :
    memberAcceptB svBoolE1 svBoolE2 96 svBoolTTAdmitted
      ((sortTyAtC svBoolE2 0 96 [] (ctor0Member 12).mtype).get svBoolSortB2).1 = true

kernel_rfl_theorem svBoolAccB3 :
    memberAcceptB svBoolE1 svBoolPrefix 96 svBoolRecAdmitted
      ((sortTyAtC svBoolPrefix 1 96 [] svBoolRec.mtype).get svBoolSortB3).1 = true

def svBoolGroupChain :
    GroupAcceptChain svBoolE1 96 svI64Env
      [(12, natFamMember), (13, ctor0Member 12), (14, ctor0Member 12), (15, svBoolRec)]
      svBoolEnv :=
  .cons svI64Env 12 natFamMember _ _ svBoolFamAdmitted svBoolSortB0 svBoolAccB0
    (.cons svBoolE1 13 (ctor0Member 12) _ _ svBoolFFAdmitted svBoolSortB1 svBoolAccB1
      (.cons svBoolE2 14 (ctor0Member 12) _ _ svBoolTTAdmitted svBoolSortB2 svBoolAccB2
        (.cons svBoolPrefix 15 svBoolRec _ _ svBoolRecAdmitted svBoolSortB3 svBoolAccB3
          (.nil svBoolEnv))))

kernel_rfl_theorem svBoolClassB :
    groupClassB natFamMember [(13, ctor0Member 12), (14, ctor0Member 12)] svBoolRec = true

def svBoolBlockWfT : EnvWfT svBoolEnv :=
  EG010T_group_accepted svI64BlockWfT 96 svBoolClassB svBoolGroupChain

end Rcic.G2

/-
RCIC 07 §3 — G2-S1: `EnvWfT` admission of the `SV<i64>` block
(`svMembersAt svSup svRefOf 9 .i64`, `RcicG2Objects`) — one
`EnvWfT.group` step on top of `Pos`+`BNat`'s admitted blocks
(`bnatBlockWfT`), since `mk : BNat → SV<i64>` names `BNat`'s family.

This file also fixes the layout the remaining `SV<d>` admissions stack
onto: `SV<i64>`@9, `SV<bool>`@12, `SV<list i64>`@16, `SV<str>`@20,
`SV<bytes>`@24, `SV<pair i64 bool>`@28, `SV<sum [i64, bool]>`@31,
`SV<record [a : i64, b : bool]>`@35 — one group per `CoreTy` form.

The stored recursor type is `svRecTy`'s output, and `recursorType := rfl`
checks it against `policyRecursorType` — the generic `svRecTy` is held to
the policy here, not restated by hand.
-/
import rcic.RcicG2AdmitSVViews

set_option maxRecDepth 8192

namespace Rcic.G2
open Rcic.Declarative Rcic.Scm
open Rcic.Scm.SrcG (sortTyAtC foldEnv noRecursorForB_sound ctorContiguousB_sound
  ctorCensusB_sound ctorFieldsPermitted_of_B)

/-! ## (0) the stack layout -/

/-- `Pos`@0, `BNat`@5. `bBool` is unused by `svCtors` (only `AssertTerm.bool`
    reads it), and this stack carries no `Bool` block. -/
def svSup : SupRefs := ⟨0, 5, 0⟩

/-- the `SV` family refs of this stack's component types. -/
def svRefOf : CoreTy → Nat
  | .i64 => 9
  | .bool => 12
  | _ => 0

/-! ## (1) the members and the prefix chain -/

def svI64Mk : CheckedMember := ctor1Member 9 5
def svI64Rec : CheckedMember := ⟨.recursorM, 1, svRecTy 9 [(10, [⟨.const 5 [], false⟩])], none⟩

theorem svI64Members :
    svMembersAt svSup svRefOf 9 .i64 = [(9, natFamMember), (10, svI64Mk), (11, svI64Rec)] := rfl

/-- `Pos`, `BNat`, then `SV<i64>`'s first `k` members, as one table. -/
def svI64Tbl (k : Nat) : List (Nat × CheckedMember) :=
  posMembersAt 0 ++ bnatMembersAt 5 0 ++ (svMembersAt svSup svRefOf 9 .i64).take k

def svI64E1 : ResolvedEnv := extendEnv bnEnv 9 natFamMember
def svI64Prefix : ResolvedEnv := extendEnv svI64E1 10 svI64Mk
def svI64Env : ResolvedEnv := extendEnv svI64Prefix 11 svI64Rec

theorem svI64BlockEnv_eq : blockEnv bnEnv (svMembersAt svSup svRefOf 9 .i64) = svI64Env := rfl

/-! ## (2) the family and constructor admissions -/

def svI64FamAdmitted : IndGroupAdmitted bnEnv 9 natFamMember :=
  .family rfl (sortOneFamView svI64E1 9 rfl) rfl rfl (Or.inr uniformType_succ_zero)

theorem svI64MkBefore : CtorBeforeRecursors svI64E1 svI64Mk :=
  ⟨9, rfl, noRecursorForB_sound (tbl := svI64Tbl 1) (by decide) (by decide)⟩

theorem svI64MkContig : CtorContiguous svI64E1 10 svI64Mk :=
  ctorContiguousB_sound (tbl := svI64Tbl 1) (by decide) (by decide)

def svI64MkAdmitted : IndGroupAdmitted svI64E1 10 svI64Mk :=
  .constructor (sortOneFamView svI64E1 9 rfl) (ctor1View svI64E1 9 5 rfl rfl) rfl
    svI64MkBefore svI64MkContig (ctor1Universe _ 9 5 rfl rfl)
    (ctorFieldsPermitted_of_B _ 8 (by decide))

/-! ## (3) the recursor admission -/

theorem svI64Census : CtorCensus svI64Prefix 9 11 :=
  ctorCensusB_sound (tbl := svI64Tbl 2) (by decide) (by decide)

/-- `Π n : BNat, P (mk n)` (foreign field, no IH). -/
def svI64Minors : List (Expr Nat) :=
  [.pi (.const 5 []) (.app (.bvar 1) (.app (.const 10 []) (.bvar 0)))]

def svI64GroupAdm : RecursorEliminationAdmitted svI64Prefix 11 svI64Rec where
  family := sortOneFamView svI64Prefix 9 rfl
  constructors := [svI64Mk]
  constructorViews | ⟨0, _⟩ => ctor1View svI64Prefix 9 5 rfl rfl
  constructorsPresent | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := svI64Minors
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

theorem svI64MinorMatch : MinorPremisesMatch svI64GroupAdm
  | ⟨0, _⟩ => ⟨[.nonrecursive], 8, rfl, rfl⟩

/-- `[n, m, P]` — `mk`'s equation context. -/
def svI64Ctx : LCtx :=
  [.assumption (.const 5 []), .assumption (svI64Minors[0]'(by decide)),
    .assumption (.pi (.const 9 []) (.sort (.param 0)))]

/-- `rec P m (mk n) ⇝ m n`. -/
def svI64IotaTy :
    HasTy svI64Env 1 svI64Ctx (.app (.bvar 1) (.bvar 0))
      (.app (.bvar 2) (.app (.const 10 []) (.bvar 0))) :=
  HasTy.app _ (.bvar 1) (.bvar 0) (.const 5 [])
    (.app (.bvar 3) (.app (.const 10 []) (.bvar 0)))
    (HasTy.bvar _ 1 _ rfl) (HasTy.bvar _ 0 _ rfl)

def svI64IotaMk : IotaEquationTyped svI64GroupAdm ⟨0, by decide⟩ 8 [.nonrecursive] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact svI64IotaTy

def svI64IotaClause : IotaDescriptorClause svI64Prefix svI64GroupAdm where
  signatureOnly := rfl
  shapesAt := fun | ⟨0, _⟩ => [.nonrecursive]
  fuelAt := fun _ => 8
  analyzed | ⟨0, _⟩ => rfl
  typed | ⟨0, _⟩ => svI64IotaMk

def svI64RecAdmitted : IndGroupAdmitted svI64Prefix 11 svI64Rec :=
  .recursor svI64GroupAdm rfl svI64Census
    (fun | ⟨0, _⟩ => ctor1Universe _ 9 5 rfl rfl)
    (fun | ⟨0, _⟩ => ctorFieldsPermitted_of_B (ctor1View svI64Prefix 9 5 rfl rfl) 8 (by decide))
    svI64MinorMatch svI64IotaClause

/-! ## (4) checker leaves, the chain, and the group step -/

kernel_rfl_theorem svI64SortB0 : (sortTyAtC bnEnv 0 96 [] natFamMember.mtype).isSome = true
kernel_rfl_theorem svI64SortB1 : (sortTyAtC svI64E1 0 96 [] svI64Mk.mtype).isSome = true
kernel_rfl_theorem svI64SortB2 : (sortTyAtC svI64Prefix 1 96 [] svI64Rec.mtype).isSome = true

kernel_rfl_theorem svI64AccB0 :
    memberAcceptB svI64E1 bnEnv 96 svI64FamAdmitted
      ((sortTyAtC bnEnv 0 96 [] natFamMember.mtype).get svI64SortB0).1 = true

kernel_rfl_theorem svI64AccB1 :
    memberAcceptB svI64E1 svI64E1 96 svI64MkAdmitted
      ((sortTyAtC svI64E1 0 96 [] svI64Mk.mtype).get svI64SortB1).1 = true

kernel_rfl_theorem svI64AccB2 :
    memberAcceptB svI64E1 svI64Prefix 96 svI64RecAdmitted
      ((sortTyAtC svI64Prefix 1 96 [] svI64Rec.mtype).get svI64SortB2).1 = true

def svI64GroupChain :
    GroupAcceptChain svI64E1 96 bnEnv [(9, natFamMember), (10, svI64Mk), (11, svI64Rec)]
      svI64Env :=
  .cons bnEnv 9 natFamMember _ _ svI64FamAdmitted svI64SortB0 svI64AccB0
    (.cons svI64E1 10 svI64Mk _ _ svI64MkAdmitted svI64SortB1 svI64AccB1
      (.cons svI64Prefix 11 svI64Rec _ _ svI64RecAdmitted svI64SortB2 svI64AccB2
        (.nil svI64Env)))

kernel_rfl_theorem svI64ClassB : groupClassB natFamMember [(10, svI64Mk)] svI64Rec = true

/-- `SV<i64>`'s block admits on top of `Pos`+`BNat`'s. -/
def svI64BlockWfT : EnvWfT svI64Env :=
  EG010T_group_accepted bnatBlockWfT 96 svI64ClassB svI64GroupChain

end Rcic.G2

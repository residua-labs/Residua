import rcic.RcicNativeReadbackCK2Index
import rcic.RcicNativeTypedModelK
import rcic.RcicNativeTypedModelTypingFin
import rcic.RcicNativeTypedModelCovPPositive

/-!
# An inhabited rigid type observation with a lambda argument

The existing admitted Eq environment supplies the family and both native
function indices. Its unchanged model observes the identity index at a
nonbottom lambda table and retains that table in the family's rigid spine.
Wrapping this proposition in `EqType → Prop` supplies a native type at
Sort 1 whose observed domain still contains the same lambda argument.

These are native/model witness data only. No provenance view, recursive
decoder, semantic relation, or interpretation is supplied here. All controls
use the existing well-formed Eq environment and the finite-joint typed,
let-coherent empty-context bottom valuation. The parameter `n` is the native
level-parameter arity, not a computation stage. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovTAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit TypedModelKFragmentAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2IndexAudit TypedModelCovPAudit

def covTProbe : CptT := .pi .bot []

def covTLambdaArg : CptT := .lam [([covTProbe], covTProbe)]

def covTRigidType : Expr Nat := binderIndexFamily indexId

def covTRigidTypeCode : CptT := .spine 63 [.bot, covTLambdaArg, .bot]

def covTWrappedType : Expr Nat := .pi covTRigidType (.sort .zero)

def covTWrappedTypeCode : CptT := .pi covTRigidTypeCode []

theorem covTProbe_nonbot : covTProbe ≠ .bot := CptT.noConfusion

theorem covTLambdaArg_nonbot : covTLambdaArg ≠ .bot := CptT.noConfusion

theorem covTRigidTypeCode_nonbot : covTRigidTypeCode ≠ .bot := CptT.noConfusion

theorem covTWrappedTypeCode_nonbot : covTWrappedTypeCode ≠ .bot := CptT.noConfusion

/-- The identity lambda's nonbottom demand is typed at its actual Prop
annotation code by the unchanged model typing. -/
theorem covTProbe_typed (E : ResolvedEnv) : CTyS E covTProbe .prop := by
  rw [covTProbe, CTyS]
  exact Or.inr (.pi .bot (fun _ h => (List.not_mem_nil _ h).elim))

/-- The lambda argument is observed using the actual nonempty demand row;
its body is the native bound variable in the matching demand valuation. -/
theorem covT_indexId_observed (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) : ApproxTK E n Γ ρ indexId covTLambdaArg := by
  refine .lam (a := .prop) (approxTK_sort_code E n Γ ρ .zero) ?_ ?_ ?_
  · intro row hrow u hu
    obtain rfl := List.mem_singleton.mp hrow
    obtain rfl := List.mem_singleton.mp hu
    exact covTProbe_typed E
  · exact ⟨([covTProbe], covTProbe), List.mem_singleton_self _, covTProbe_nonbot⟩
  · intro row hrow
    obtain rfl := List.mem_singleton.mp hrow
    exact .free (kFreeT_bvar E 0) (.bvar (List.mem_singleton_self _))

theorem covT_indexId_normal (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    NormalR (WhStepCK2 E n) Γ indexId :=
  normalR_lamCK2 Γ (.sort .zero) (.bvar 0)

theorem covT_eq_head_rigid : RigidConst eqEnvT 63 :=
  rigidConst_of_inductiveM pinEqGroupWfT (m := eqFamT) rfl rfl

theorem covT_eq_head_not_propCtor : ¬ PropCtorT eqEnvT 63 := by
  rintro ⟨m, fam, fm, hm, hctor, _⟩
  have he : m = eqFamT := Option.some.inj hm.symm
  subst m
  exact MemberClass.noConfusion hctor

theorem covT_eq_head_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK eqEnvT n Γ ρ (.const 63 []) (.spine 63 []) :=
  .free (kFreeT_rigid_const covT_eq_head_rigid [])
    (.const ρ 63 [] covT_eq_head_rigid covT_eq_head_not_propCtor)

def covTRigidType_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT eqEnvT n Γ covTRigidType (.sort .zero) :=
  binderIndexFamilyTy n Γ (indexIdTy eqEnvT n Γ)

/-- The native family application is weak-head normal even though one of
its actual observed arguments is a lambda compact. -/
theorem covTRigidType_normal (n : Nat) (Γ : LCtx) :
    NormalR (WhStepCK2 eqEnvT n) Γ covTRigidType :=
  normalR_famAppCK2 pinEqGroupWfT
    (rfl : eqEnvT.members 63 = some eqFamT) rfl Γ [] [indexFn, indexId, indexId]

theorem covTRigidType_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK eqEnvT n Γ ρ covTRigidType covTRigidTypeCode :=
  .appSpine
    (.appSpine (.appSpine (covT_eq_head_observed n Γ ρ) (.bot _ _ _))
      (covT_indexId_observed eqEnvT n Γ ρ))
    (.bot _ _ _)

theorem covTRigidTypeCode_positive : IsPropCTP eqEnvT covTRigidTypeCode :=
  .spine (m := eqFamT) rfl rfl

/-- The wrapper's native universe is Sort 1. Only the native level equation
`imax 0 1 = 1` is used to normalize the sort assigned by Pi formation. -/
def covTWrappedType_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT eqEnvT n Γ covTWrappedType (.sort (.succ .zero)) :=
  .conv _ _ _ _ _
    (.pi Γ covTRigidType .zero (.sort .zero) (.succ .zero)
      (covTRigidType_hasTy n Γ) (.sort _ .zero))
    (.sorts _ _ _ (fun _ => rfl))

theorem covTWrappedType_normal (n : Nat) (Γ : LCtx) :
    NormalR (WhStepCK2 eqEnvT n) Γ covTWrappedType :=
  normalR_piCK2 Γ covTRigidType (.sort .zero)

/-- The wrapper preserves the rigid domain's lambda argument. Its output
row list is empty, so there is no assumed binder-body observation. -/
theorem covTWrappedType_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK eqEnvT n Γ ρ covTWrappedType covTWrappedTypeCode :=
  .pi (covTRigidType_observed n Γ ρ)
    (fun _ h => (List.not_mem_nil _ h).elim)
    (fun _ h => (List.not_mem_nil _ h).elim)

/-- The selected wrapper observation has no positive proposition-code
certificate. This is separate from its supplied native Sort 1 typing. -/
theorem covTWrappedTypeCode_not_positive : ¬ IsPropCTP eqEnvT covTWrappedTypeCode :=
  not_isPropCTP_pi_nil eqEnvT covTRigidTypeCode

theorem covT_nil_env_typed (n : Nat) :
    EnvTypedFinAtT (ctxModelT_approxTK eqEnvT n []) [] EnvT.bot :=
  envTypedFinAtT_nil _ _

theorem covT_nil_ctx_coherent (n : Nat) :
    CtxEnvM (ctxModelT_approxTK eqEnvT n []) [] EnvT.bot := by
  intro i v hv
  exact Option.noConfusion hv

/-- Every guard needed for the rigid-type observation is inhabited in the
existing environment. The nonbottom lambda argument has its own native
typing, native self-conversion, actual observation, and source normality. -/
theorem covT_rigid_lambda_data (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n []) ∧
    EnvTypedFinAtT (ctxModelT_approxTK eqEnvT n []) [] EnvT.bot ∧
    CtxEnvM (ctxModelT_approxTK eqEnvT n []) [] EnvT.bot ∧
    Nonempty (HasTyT eqEnvT n [] indexFn (.sort (.succ .zero))) ∧
    Nonempty (HasTyT eqEnvT n [] indexId indexFn) ∧
    Nonempty (ConvT eqEnvT n [] indexId indexId indexFn) ∧
    ApproxTK eqEnvT n [] EnvT.bot indexId covTLambdaArg ∧
    NormalR (WhStepCK2 eqEnvT n) [] indexId ∧ covTLambdaArg ≠ .bot ∧
    Nonempty (HasTyT eqEnvT n [] covTRigidType (.sort .zero)) ∧
    Nonempty (ConvT eqEnvT n [] covTRigidType covTRigidType (.sort .zero)) ∧
    NormalR (WhStepCK2 eqEnvT n) [] covTRigidType ∧
    ApproxTK eqEnvT n [] EnvT.bot covTRigidType covTRigidTypeCode ∧
    covTRigidTypeCode ≠ .bot ∧ IsPropCTP eqEnvT covTRigidTypeCode :=
  ⟨⟨pinEqGroupWfT⟩, ⟨.nil⟩, covT_nil_env_typed n, covT_nil_ctx_coherent n,
    ⟨indexFnTy eqEnvT n []⟩, ⟨indexIdTy eqEnvT n []⟩,
    ⟨.refl _ _ _ (indexIdTy eqEnvT n [])⟩,
    covT_indexId_observed eqEnvT n [] EnvT.bot, covT_indexId_normal eqEnvT n [],
    covTLambdaArg_nonbot, ⟨covTRigidType_hasTy n []⟩,
    ⟨.refl _ _ _ (covTRigidType_hasTy n [])⟩, covTRigidType_normal n [],
    covTRigidType_observed n [] EnvT.bot, covTRigidTypeCode_nonbot,
    covTRigidTypeCode_positive⟩

/-- The Sort 1 wrapper carries all environment, native, coherence, and
observation premises independently of any proposition-code shortcut. -/
theorem covT_wrapped_lambda_data (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n []) ∧
    EnvTypedFinAtT (ctxModelT_approxTK eqEnvT n []) [] EnvT.bot ∧
    CtxEnvM (ctxModelT_approxTK eqEnvT n []) [] EnvT.bot ∧
    Nonempty (HasTyT eqEnvT n [] covTWrappedType (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n [] covTWrappedType covTWrappedType (.sort (.succ .zero))) ∧
    NormalR (WhStepCK2 eqEnvT n) [] covTWrappedType ∧
    ApproxTK eqEnvT n [] EnvT.bot covTWrappedType covTWrappedTypeCode ∧
    covTWrappedTypeCode ≠ .bot ∧ ¬ IsPropCTP eqEnvT covTWrappedTypeCode ∧
    ApproxTK eqEnvT n [] EnvT.bot indexId covTLambdaArg ∧
    covTLambdaArg ≠ .bot :=
  ⟨⟨pinEqGroupWfT⟩, ⟨.nil⟩, covT_nil_env_typed n, covT_nil_ctx_coherent n,
    ⟨covTWrappedType_hasTy n []⟩, ⟨.refl _ _ _ (covTWrappedType_hasTy n [])⟩,
    covTWrappedType_normal n [], covTWrappedType_observed n [] EnvT.bot,
    covTWrappedTypeCode_nonbot, covTWrappedTypeCode_not_positive,
    covT_indexId_observed eqEnvT n [] EnvT.bot, covTLambdaArg_nonbot⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_T_DATA_ROOTS
#print axioms covTProbe
#print axioms covTLambdaArg
#print axioms covTRigidType
#print axioms covTRigidTypeCode
#print axioms covTWrappedType
#print axioms covTWrappedTypeCode
#print axioms covTProbe_nonbot
#print axioms covTLambdaArg_nonbot
#print axioms covTRigidTypeCode_nonbot
#print axioms covTWrappedTypeCode_nonbot
#print axioms covTProbe_typed
#print axioms covT_indexId_observed
#print axioms covT_indexId_normal
#print axioms covT_eq_head_rigid
#print axioms covT_eq_head_not_propCtor
#print axioms covT_eq_head_observed
#print axioms covTRigidType_hasTy
#print axioms covTRigidType_normal
#print axioms covTRigidType_observed
#print axioms covTRigidTypeCode_positive
#print axioms covTWrappedType_hasTy
#print axioms covTWrappedType_normal
#print axioms covTWrappedType_observed
#print axioms covTWrappedTypeCode_not_positive
#print axioms covT_nil_env_typed
#print axioms covT_nil_ctx_coherent
#print axioms covT_rigid_lambda_data
#print axioms covT_wrapped_lambda_data
-- END RCIC_NATIVE_TYPED_MODEL_COV_T_DATA_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovTAudit

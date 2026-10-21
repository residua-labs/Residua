import rcic.RcicNativeTypedModelCovWNativeAliasControl
import rcic.RcicNativeTypedModelCovWMatrixIotaHead
import rcic.RcicNativeTypedModelCovWMatrixMajorIrrel
import rcic.RcicNativeTypedModelCovWMatrixRawIotaHead

/-!
# Actual native K and constructor-iota observations

The earlier K and structured-iota fixtures now have direct guarded nonbottom
observations. Every K certificate is the existing actual native premise,
and every iota certificate is an actual checked structured witness. The old
raw grammar is untouched; its raw RI exclusion is retained for comparison.
The major-irrelevance test shares `prop` in both calls. This is a concrete
positive observation result, not all-observation equality or a supplier for
general conversion contexts. `closure_claim = 0`.
-/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelKAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelKGuardAudit TypedModelKControlAudit TypedModelKObstructionAudit
open TypedModelKTransportAudit TypedModelCovTAudit TypedModelCovVAudit
open TypedModelCovWAudit TypedModelCovWIrrelAudit TypedModelCovWMatrixAudit
open TypedModelAudit.TypingFin TypedModelCovWEtaAudit TypedModelW6IotaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit ReadbackCK2IndexAudit
open ReadbackCK2ModelObstructionAudit ReadbackCK2InputsAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The eta-index fixture consumes all four actual native K gates. -/
theorem covWNative_etaIndex_prop (n : Nat) (ρ : EnvWIrrel) :
    ApproxTKWNative eqEnvT n etaEqCtx ρ etaIndexRedex .prop := by
  obtain ⟨hk, hn, hi, hc⟩ := covWMatrix_K_native_gates n
  exact .recursorPropK covWMatrixKWitness (.bvar 0) hk hn hi hc
    (.sort etaEqCtx ρ .zero)

theorem covWNative_etaIndex_observed (n : Nat) (ρ : EnvWIrrel) :
    CovWNativeObservation eqEnvT n etaEqCtx ρ etaIndexRedex .prop :=
  covWNative_observation_of (covWNative_etaIndex_prop n ρ)

/-- The old DI guard actually fails in the newly observed native K call. -/
theorem covWNative_etaIndex_native_not_DI (n : Nat) (ρ : EnvWIrrel) :
    KIndexConvAt eqEnvT n etaEqCtx covWMatrixKWitness ∧
    KCommonAt eqEnvT n etaEqCtx covWMatrixKWitness (.bvar 0) ∧
    (¬ KIndexGuardAt eqEnvT n etaEqCtx covWMatrixKWitness) ∧
    WhStepCK2 eqEnvT n etaEqCtx etaIndexRedex (.sort .zero) ∧
    ApproxTKWNative eqEnvT n etaEqCtx ρ etaIndexRedex .prop := by
  obtain ⟨_, _, hi, hc⟩ := covWMatrix_K_native_gates n
  exact ⟨hi, hc, covWMatrix_K_model_guard_fails n, covWMatrix_K_step n,
    covWNative_etaIndex_prop n ρ⟩

theorem covWNative_K_realized (n stage : Nat) :
    CovWNativeRealized eqEnvT n stage etaEqCtx EnvWIrrel.bot covWMatrixKSubst := by
  refine ⟨covWMatrixKSubst_typed n, ?_⟩
  intro i c hc
  cases hc
  exact ⟨.bot _ _ _, by simp [covWIrrelErase, covTObservationBudget]⟩

/-- The higher-order RHS consumes its constant minor's two empty rows. -/
theorem covWNative_iota_rhs_prop (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covUHoEnv n Γ ρ covWMatrixIotaTarget .prop := by
  change ApproxTKWNative covUHoEnv n Γ ρ (.app (.app covUHoMinor _) _) .prop
  apply covWNative_empty_app
  apply covWNative_empty_app
  apply covWNative_empty_lam (by intro h; cases h)
  apply covWNative_empty_lam (by intro h; cases h)
  exact .sort _ _ .zero

/-- An actual constructor major enables ordinary iota despite the failed
old ApproxTN source filter. -/
theorem covWNative_iota_source_prop (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covUHoEnv n Γ ρ covWMatrixIotaSource .prop :=
  .iota covWMatrixIotaWitness (covWNative_iota_rhs_prop n Γ ρ)

theorem covWNative_iota_native_not_filter (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    IsCtorSpine covUHoEnv covWMatrixIotaMajor ∧
    WhStepCK2 covUHoEnv n Γ covWMatrixIotaSource covWMatrixIotaTarget ∧
    Nonempty (HasTyT covUHoEnv n Γ covWMatrixIotaSource (.sort (.succ .zero))) ∧
    Nonempty (HasTyT covUHoEnv n Γ covWMatrixIotaTarget (.sort (.succ .zero))) ∧
    (¬ ApproxTN covUHoEnv (covWIrrelEnvErase ρ) covWMatrixIotaSource .prop) ∧
    ApproxTKWNative covUHoEnv n Γ ρ covWMatrixIotaSource .prop :=
  ⟨covWMatrix_iota_constructor_major, covWMatrix_iota_step n Γ,
    ⟨covWMatrixIotaSource_ty n Γ⟩, ⟨covWMatrixIotaTarget_ty n Γ⟩,
    covWMatrix_iota_source_filter_fails _, covWNative_iota_source_prop n Γ ρ⟩

/-- Reinstantiate the already checked True schema at the RI fixture's
actual universe, motive and minor. -/
def covWNativeTrueWitness : IotaWitnessS trueEnvU :=
  covW_iota_action_instance covVTrueWitness [.succ (.succ .zero)] []
    [kMot, .sort .zero] [] [] rfl rfl rfl rfl

theorem covWNative_true_witness_lhs :
    iotaLhsOfS covWNativeTrueWitness = iotaLhsOf wTrueRecU := rfl

theorem covWNative_true_witness_rhs :
    iotaRhsOfS covWNativeTrueWitness = .sort .zero := rfl

/-- The raw RI source now has an ordinary guarded iota observation. -/
theorem covWNative_true_iota_prop (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative trueEnvU n Γ ρ (iotaLhsOf wTrueRecU) .prop :=
  .iota covWNativeTrueWitness (.sort Γ ρ .zero)

theorem covWNative_true_raw_guarded_comparison (n : Nat) :
    WhStepCK2 trueEnvU n [] (iotaLhsOf wTrueRecU) (.sort .zero) ∧
    CovWMatrixNativePair trueEnvU n (iotaLhsOf wTrueRecU) (.sort .zero)
      (.sort (.succ .zero)) (.succ (.succ .zero)) ∧
    (¬ CovWIrrelRawObservation trueEnvU n EnvWIrrel.bot (iotaLhsOf wTrueRecU) .prop) ∧
    CovWNativeObservation trueEnvU n [] EnvWIrrel.bot (iotaLhsOf wTrueRecU) .prop :=
  ⟨covWMatrix_raw_true_iota_step n, covWMatrix_raw_true_iota_native n,
    covWMatrix_raw_true_iota_source_excluded n EnvWIrrel.bot,
    covWNative_observation_of (covWNative_true_iota_prop n [] EnvWIrrel.bot)⟩

/-- The constructor side of the proof-major comparison uses ordinary iota. -/
theorem covWNative_major_ctor_prop (n : Nat) (ρ : EnvWIrrel) :
    ApproxTKWNative eqEnvT n etaEqCtx ρ covWMatrixMajorCtorCall .prop :=
  .iota covWMatrixMajorWitness (.sort etaEqCtx ρ .zero)

/-- This inhabits both observations alongside their actual native major
irrelevance and application congruence. It is not all-observation equality. -/
theorem covWNative_major_shared_prop (n : Nat) (ρ : EnvWIrrel) :
    Nonempty (ConvT eqEnvT n etaEqCtx (.bvar 0) etaIndexCtor
      (etaIndexFamily etaIndex)) ∧
    Nonempty (ConvT eqEnvT n etaEqCtx etaIndexRedex covWMatrixMajorCtorCall
      (.sort (.succ .zero))) ∧
    CTyS eqEnvT .prop .sort ∧
    CovWNativeObservation eqEnvT n etaEqCtx ρ etaIndexRedex .prop ∧
    CovWNativeObservation eqEnvT n etaEqCtx ρ covWMatrixMajorCtorCall .prop :=
  ⟨⟨covWMatrixMajorIrr n⟩, ⟨covWMatrixMajorCongr n⟩,
    covWMatrix_K_compact_typed, covWNative_etaIndex_observed n ρ,
    covWNative_observation_of (covWNative_major_ctor_prop n ρ)⟩

/-- The new grammar cannot be forgotten into the old guarded grammar:
the actual native eta-index observation already contradicts such a map. -/
theorem covWNative_no_blanket_old_forgetting (n : Nat) (ρ : EnvWIrrel) :
    ¬ (∀ e c, ApproxTKWNative eqEnvT n etaEqCtx ρ e c →
      ApproxTKWIrrel eqEnvT n etaEqCtx ρ e c) := by
  intro h
  exact CptWIrrel.noConfusion
    (covWIrrel_etaIndex_only_bot (h _ _ (covWNative_etaIndex_prop n ρ)))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_COMPUTATIONS_ROOTS
#print axioms covWNative_etaIndex_prop
#print axioms covWNative_etaIndex_observed
#print axioms covWNative_etaIndex_native_not_DI
#print axioms covWNative_K_realized
#print axioms covWNative_iota_rhs_prop
#print axioms covWNative_iota_source_prop
#print axioms covWNative_iota_native_not_filter
#print axioms covWNativeTrueWitness
#print axioms covWNative_true_witness_lhs
#print axioms covWNative_true_witness_rhs
#print axioms covWNative_true_iota_prop
#print axioms covWNative_true_raw_guarded_comparison
#print axioms covWNative_major_ctor_prop
#print axioms covWNative_major_shared_prop
#print axioms covWNative_no_blanket_old_forgetting
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_COMPUTATIONS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

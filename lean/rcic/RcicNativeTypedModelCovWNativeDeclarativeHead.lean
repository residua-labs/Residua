import rcic.RcicNativeTypedModelCovWNativeContext

/-!
# The separate declarative-head supplier obligation

Native observation expansion along structured CK2 iota does not itself
supply a `ConvT` derivation: the landed `ConvT.iota` constructor consumes a
legacy witness. The admitted higher-order recursor has no such witness.
This module names a deliberately narrow typed `prop`-head adequacy target
and proves its exact concrete consequence. It also proves that the two
higher-order head-conversion obligations are equivalent via the genuinely
supplied native proof-irrelevance context conversion.

Neither head conversion, the adequacy supplier, nor its negation is asserted.
The no-normal-CK2-readback theorem must not be substituted for a theorem
about declarative conversion. `closure_claim = 0`.
-/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelCovTAudit TypedModelCovVAudit
open TypedModelCovWAudit TypedModelCovWIrrelAudit TypedModelCovWMatrixAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit

/-- A narrow declarative-head target at the particular strict compact
`prop : sort`. Even this target is separate from observation expansion. -/
def CovWNativePropHeadDeclarativeAdequacy : Prop :=
  ∀ (E : ResolvedEnv) (n : Nat) (e : Expr Nat),
    EnvWfT E → HasTyT E n [] e (.sort (.succ .zero)) →
    CovWNativeObservation E n [] EnvWIrrel.bot e .prop →
    Nonempty (ConvT E n [] e (.sort .zero) (.sort (.succ .zero)))

/-- The constructor-major head conversion that the narrow supplier must
produce at the already observed I* fixture. -/
def CovWNativeHoCtorHeadConversion (n : Nat) : Prop :=
  Nonempty (ConvT covUHoEnv n [] covWMatrixIotaSource (.sort .zero)
    (.sort (.succ .zero)))

/-- The corresponding declarative conversion for the divergent-major call.
Its absence is not inferred from absence of a finite CK2 normal readback. -/
def CovWNativeHoDivergentHeadConversion (n : Nat) : Prop :=
  Nonempty (ConvT covUHoEnv n [] covUHoType (.sort .zero)
    (.sort (.succ .zero)))

/-- Every premise of the narrow supplier is genuinely inhabited here. -/
theorem covWNative_prop_head_requires_Ho_ctor
    (h : CovWNativePropHeadDeclarativeAdequacy) (n : Nat) :
    CovWNativeHoCtorHeadConversion n :=
  h covUHoEnv n covWMatrixIotaSource covUHoEnv_wf
    (covWMatrixIotaSource_ty n [])
    (covWNative_observation_of (covWNative_iota_source_prop n [] EnvWIrrel.bot))

/-- Actual native irrelevance inside the same recursor prefix transports
the head-conversion obligation in both directions. -/
theorem covWNative_Ho_head_conversion_iff (n : Nat) :
    CovWNativeHoCtorHeadConversion n ↔ CovWNativeHoDivergentHeadConversion n := by
  constructor
  · rintro ⟨hc⟩
    exact ⟨.trans [] covUHoType covWMatrixIotaSource (.sort .zero)
      (.sort (.succ .zero)) (covWNativeHo_context_conv n []) hc⟩
  · rintro ⟨hc⟩
    exact ⟨.trans [] covWMatrixIotaSource covUHoType (.sort .zero)
      (.sort (.succ .zero)) (.symm _ _ _ _ (covWNativeHo_context_conv n [])) hc⟩

theorem covWNative_prop_head_requires_Ho_divergent
    (h : CovWNativePropHeadDeclarativeAdequacy) (n : Nat) :
    CovWNativeHoDivergentHeadConversion n :=
  (covWNative_Ho_head_conversion_iff n).mp (covWNative_prop_head_requires_Ho_ctor h n)

/-- This excludes a direct legacy iota generator only. It does not exclude
a longer declarative conversion derivation using other constructors. -/
theorem covWNative_Ho_no_legacy_iota_generator (target : Expr Nat) :
    ¬ Nonempty (DerivedIota covUHoEnv covWMatrixIotaSource target) := by
  rintro ⟨h⟩
  generalize he : covWMatrixIotaSource = lhs at h
  cases h with
  | of w =>
      have hh := congrArg (fun e => (appsSpine e).1) he
      simp only [covWMatrixIotaSource, iotaLhsOfS, iotaLhsOf, recCall,
        appsSpine_foldApps_const] at hh
      exact covUHo_no_legacy_witness w (Expr.const.inj hh).1.symm

/-- No observation predicate retaining the actual constructor-positive
case can have both native conversion invariance and finite CK2 normal-head
adequacy at the supplied Sort 1 typing. This result is independent of the
particular syntax chosen for that observation predicate. -/
theorem covWNative_prop_transport_readback_impossible (n : Nat)
    (O : Expr Nat → Prop) (hctor : O covWMatrixIotaSource) :
    ¬ ((∀ e e' : Expr Nat,
      HasTyT covUHoEnv n [] e (.sort (.succ .zero)) →
      HasTyT covUHoEnv n [] e' (.sort (.succ .zero)) →
      ConvT covUHoEnv n [] e e' (.sort (.succ .zero)) → (O e ↔ O e')) ∧
      (∀ e : Expr Nat, HasTyT covUHoEnv n [] e (.sort (.succ .zero)) →
        O e → ∃ N, RedR (WhStepCK2 covUHoEnv n) [] e N ∧
          NormalR (WhStepCK2 covUHoEnv n) [] N)) := by
  rintro ⟨htransport, hreadback⟩
  have hmajor : O covUHoType :=
    (htransport covUHoType covWMatrixIotaSource
      (covUHoType_hasTy n []) (covWMatrixIotaSource_ty n [])
      (covWNativeHo_context_conv n [])).mpr hctor
  exact covUHoType_no_normal_head n []
    (hreadback covUHoType (covUHoType_hasTy n []) hmajor)

/-- Requiring the normal head to equal Sort 0 is stronger still. -/
theorem covWNative_prop_transport_matching_head_impossible (n : Nat)
    (O : Expr Nat → Prop) (hctor : O covWMatrixIotaSource) :
    ¬ ((∀ e e' : Expr Nat,
      HasTyT covUHoEnv n [] e (.sort (.succ .zero)) →
      HasTyT covUHoEnv n [] e' (.sort (.succ .zero)) →
      ConvT covUHoEnv n [] e e' (.sort (.succ .zero)) → (O e ↔ O e')) ∧
      (∀ e : Expr Nat, HasTyT covUHoEnv n [] e (.sort (.succ .zero)) →
        O e → ∃ N, RedR (WhStepCK2 covUHoEnv n) [] e N ∧
          NormalR (WhStepCK2 covUHoEnv n) [] N ∧ N = .sort .zero)) := by
  rintro ⟨htransport, hhead⟩
  apply covWNative_prop_transport_readback_impossible n O hctor
  refine ⟨htransport, ?_⟩
  intro e he ho
  obtain ⟨N, hr, hn, _⟩ := hhead e he ho
  exact ⟨N, hr, hn⟩

/-- The contradiction's native comparison, new positive observation and
negative readback are supplied for one and the same admitted environment. -/
theorem covWNative_prop_target_failure_inhabited (n : Nat) :
    CovWMatrixNativePair covUHoEnv n covUHoType covWMatrixIotaSource
      (.sort (.succ .zero)) (.succ (.succ .zero)) ∧
    CovWNativeRealized covUHoEnv n 1 [] EnvWIrrel.bot SubstT.id ∧
    CovWNativeObservation covUHoEnv n [] EnvWIrrel.bot
      (.sort (.succ .zero)) .sort ∧
    CTyS covUHoEnv .prop .sort ∧
    CovWNativeObservation covUHoEnv n [] EnvWIrrel.bot covWMatrixIotaSource .prop ∧
    ¬ ∃ N, RedR (WhStepCK2 covUHoEnv n) [] covUHoType N ∧
      NormalR (WhStepCK2 covUHoEnv n) [] N :=
  ⟨covWNativeHo_context_pair n, covWNative_realized_nil covUHoEnv n 1,
    covWNative_observation_of (.sort [] EnvWIrrel.bot (.succ .zero)),
    covWMatrix_iota_compact_typed,
    covWNative_observation_of (covWNative_iota_source_prop n [] EnvWIrrel.bot),
    covUHoType_no_normal_head n []⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_DECLARATIVE_HEAD_ROOTS
#print axioms CovWNativePropHeadDeclarativeAdequacy
#print axioms CovWNativeHoCtorHeadConversion
#print axioms CovWNativeHoDivergentHeadConversion
#print axioms covWNative_prop_head_requires_Ho_ctor
#print axioms covWNative_Ho_head_conversion_iff
#print axioms covWNative_prop_head_requires_Ho_divergent
#print axioms covWNative_Ho_no_legacy_iota_generator
#print axioms covWNative_prop_transport_readback_impossible
#print axioms covWNative_prop_transport_matching_head_impossible
#print axioms covWNative_prop_target_failure_inhabited
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_DECLARATIVE_HEAD_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

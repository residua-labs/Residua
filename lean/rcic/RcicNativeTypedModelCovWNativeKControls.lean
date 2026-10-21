import rcic.RcicNativeTypedModelCovWNativeAliasControl
import rcic.RcicNativeTypedModelCovWIrrelKControls

/-!
# Checked positive K controls in the native grammar

The older DI guard certificates are used only through their native first
projection; all actual native common-typing and canon certificates remain
explicit. The RHS observations below are constructed afresh. No transfer
of old guarded observations, negative controls or global suppliers is used.
`closure_claim = 0`.
-/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelKAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelKIndexFreeAudit TypedModelKGuardAudit TypedModelKControlAudit
open TypedModelKObstructionAudit TypedModelKTransportAudit TypedModelW6IotaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open ReadbackCK2IndexAudit ReadbackCK2ModelObstructionAudit ReadbackCK2InputsAudit
open PiProbeModelBoundaryAudit TypedModelCovTAudit TypedModelCovVAudit
open TypedModelCovWAudit TypedModelCovWEtaAudit TypedModelCovWIrrelAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem covWNative_K_eqGap_observed (n : Nat) (ρ : EnvWIrrel) :
    ApproxTKWNative eqEnvT n eqGapCtx ρ eqGapRedex .prop :=
  .recursorPropK eqGapW (.bvar 0) (Or.inl ⟨rfl, rfl, rfl⟩)
    not_isCtorSpine_bvar (kIndexConvAt_eqGap n) (kCommonAt_eqGap n)
    (.sort eqGapCtx ρ .zero)

theorem covWNative_trueK_observed (n : Nat) (ρ : EnvWIrrel) :
    ApproxTKWNative trueEnvU n kVarCtx ρ (kRec (.bvar 0)) .prop :=
  .recursorPropK wTrueRecU (.bvar 0) (Or.inl ⟨rfl, rfl, rfl⟩)
    not_isCtorSpine_bvar (covW_trueK_index n).1 (covW_trueK_common n)
    (.sort kVarCtx ρ .zero)

theorem covWNative_andK_rhs_observed (ρ : EnvWIrrel) :
    ApproxTKWNative andEnvU 0 mixAndCtx ρ (iotaRhsOf covWAndCanonWitness)
      (.pi .bot []) := by
  apply covWNative_empty_app
  apply covWNative_empty_app
  apply covWNative_empty_lam (by intro h; cases h)
  apply covWNative_empty_lam (by intro h; cases h)
  exact .pi (.bot _ _ _) (fun _ h => (List.not_mem_nil _ h).elim)
    (fun _ h => (List.not_mem_nil _ h).elim)

theorem covWNative_andK_observed (ρ : EnvWIrrel) :
    ApproxTKWNative andEnvU 0 mixAndCtx ρ mixAndRedex (.pi .bot []) :=
  .recursorPropK covWAndCanonWitness (.bvar 0) covW_andK_canon
    not_isCtorSpine_bvar covW_andK_index.1 covW_andK_common
    (covWNative_andK_rhs_observed ρ)

theorem covWNative_K_positive_controls (n : Nat) :
    CovWNativeObservation eqEnvT n eqGapCtx EnvWIrrel.bot eqGapRedex .prop ∧
    CovWNativeObservation trueEnvU n kVarCtx EnvWIrrel.bot (kRec (.bvar 0)) .prop ∧
    CovWNativeObservation andEnvU 0 mixAndCtx EnvWIrrel.bot mixAndRedex (.pi .bot []) :=
  ⟨covWNative_observation_of (covWNative_K_eqGap_observed n EnvWIrrel.bot),
    covWNative_observation_of (covWNative_trueK_observed n EnvWIrrel.bot),
    covWNative_observation_of (covWNative_andK_observed EnvWIrrel.bot)⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_K_CONTROLS_ROOTS
#print axioms covWNative_K_eqGap_observed
#print axioms covWNative_trueK_observed
#print axioms covWNative_andK_rhs_observed
#print axioms covWNative_andK_observed
#print axioms covWNative_K_positive_controls
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_K_CONTROLS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

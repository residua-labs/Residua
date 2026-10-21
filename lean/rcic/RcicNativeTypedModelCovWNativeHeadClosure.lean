import rcic.RcicNativeTypedModelCovWNativeCore
import rcic.RcicNativeTypedModelCovVProjection

/-!
# Backward observation closure for the actual native head relations

Structured iota and native K consume the actual existing native witnesses.
Legacy iota is bridged to a structured witness by actual environment
admission. These are one-direction observation-expansion results. They do
not assert all-observation head equality or close any conversion context.
`closure_claim = 0`.
-/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open TypedModelCovWIrrelAudit TypedModelCovVAudit

/-- Admitted legacy iota has the same endpoints as a checked structured
witness, so the structured observation constructor handles it as well. -/
theorem covWNative_legacy_iota_expand {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {c : CptWIrrel} (hW : EnvWfT E) (w : IotaWitness E)
    (h : ApproxTKWNative E n Γ ρ (iotaRhsOf w) c) :
    ApproxTKWNative E n Γ ρ (iotaLhsOf w) c := by
  obtain ⟨hd⟩ := derivedIotaT_of_iotaWitness_envWfT hW w
  obtain ⟨s, hlhs, hrhs⟩ := derivedIotaT_inv hd
  rw [← hlhs]
  apply ApproxTKWNative.iota s
  rw [hrhs]
  exact h

/-- Both alternatives of the ordinary native iota relation are covered. -/
theorem covWNative_DerivedIotaU_expand {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {e e' : Expr Nat} {c : CptWIrrel}
    (hW : EnvWfT E) (hs : DerivedIotaU E e e')
    (ho : ApproxTKWNative E n Γ ρ e' c) : ApproxTKWNative E n Γ ρ e c := by
  cases hs with
  | ofU w => exact covWNative_legacy_iota_expand hW w ho
  | ofUS w => exact .iota w ho

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_HEAD_CLOSURE_ROOTS
#print axioms covWNative_legacy_iota_expand
#print axioms covWNative_DerivedIotaU_expand
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_HEAD_CLOSURE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

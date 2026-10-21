import rcic.RcicNativeTypedModelCovYFund
import rcic.RcicNativeTypedModelCovYEtaRealization
import rcic.RcicNativeTypedModelCovYPolyRealization

/-!
# Complete concrete fundamental suppliers at fixed finite codes

These wrappers quantify over every target context, every new hereditary
related substitution and every either-side observation. The pointwise action
proofs are imported. No conversion to the refuted raw environment guard, no
eager native type view, and no universal caller-code escape are assumed.

The imported concrete hereditary results additionally realize the SAME code
in every target valuation. This does not assert a general compatibility law
between a source valuation and a native substitution's target context.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelKFragmentAudit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit TypedModelCovXAudit
open TypedModelCovXEtaAudit TypedModelCovYEtaAudit TypedModelCovYPolyPropAudit

/-- A complete function-child supplier at the actual finite Nat-arrow code. -/
theorem fundTyCodeAtCovY_natSucc (n : Nat) (Γ : LCtx) :
    FundTyCodeAtCovY (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      covYNatArrowCode := by
  intro Δ ρ ρ' σ σ' _ _ c hc
  change LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Δ
    (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 [])) c covYNatArrowCode
  have hm := hc.elim (fun h => approxT_rigid_const_inv rigidConst_natEnvU_succ
    (approxTK_forget h)) (fun h => approxT_rigid_const_inv rigidConst_natEnvU_succ
    (approxTK_forget h))
  rcases hm with rfl | rfl
  · exact lrSCoreCovY_bot (C2 natEnvU) _ _ _ _ _
  · exact covY_natSucc_related n Δ

theorem fundTyAtCovY_natSucc (n : Nat) (Γ : LCtx) :
    FundTyAtCovY (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ (.const 2 []) (.pi (.const 0 []) (.const 0 [])) :=
  fundTyAtCovY_of_code (fundTyCodeAtCovY_natSucc n Γ)

/-- Every eta-left-only table is included by the complete OR-observation
theorem. This is an unconditional concrete supply, not an eta consumer. -/
theorem fundConvCodeAtCovY_eta_natSucc (n : Nat) (Γ : LCtx) :
    FundConvCodeAtCovY (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) covYNatArrowCode := by
  intro Δ ρ ρ' σ σ' _ _ c hc
  change LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Δ
    (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
    (.const 2 []) (.pi (.const 0 []) (.const 0 [])) c covYNatArrowCode
  exact covY_natSucc_eta_observed n Γ Δ ρ ρ' c hc

theorem fundConvAtCovY_eta_natSucc (n : Nat) (Γ : LCtx) :
    FundConvAtCovY (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) :=
  fundConvAtCovY_of_code (fundConvCodeAtCovY_eta_natSucc n Γ)

/-- The impredicative lambda has a complete motive at a single finite type
code for ALL of its model observations, not merely its displayed singleton. -/
theorem fundTyCodeAtCovY_polyPropLam (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (Γ : LCtx) :
    FundTyCodeAtCovY C (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
      n Γ covXPolyPropLam covXPolyPropLamTy covYPolyPropCode := by
  intro Δ ρ ρ' σ σ' _ _ c hc
  change LRSCoreCovY C (WhStepCK2 eqEnvT n) n Δ covXPolyPropLam
    covXPolyPropLam covXPolyPropLamTy c covYPolyPropCode
  exact hc.elim (covY_polyProp_related_observed C hS n Γ Δ ρ c)
    (covY_polyProp_related_observed C hS n Γ Δ ρ' c)

theorem fundTyAtCovY_polyPropLam (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (Γ : LCtx) :
    FundTyAtCovY C (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
      n Γ covXPolyPropLam covXPolyPropLamTy :=
  fundTyAtCovY_of_code (fundTyCodeAtCovY_polyPropLam C hS n Γ)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_CONCRETE_FUND_ROOTS
#print axioms fundTyCodeAtCovY_natSucc
#print axioms fundTyAtCovY_natSucc
#print axioms fundConvCodeAtCovY_eta_natSucc
#print axioms fundConvAtCovY_eta_natSucc
#print axioms fundTyCodeAtCovY_polyPropLam
#print axioms fundTyAtCovY_polyPropLam
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_CONCRETE_FUND_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYAudit

import rcic.RcicNativeTypedModelCovXBoundary
import rcic.RcicNativeTypedModelCovXEtaFund

/-!
# The next general eta obstruction is eager hereditary views

Native successor eta is now completely supplied. General eta still fails
for the measured finite-view candidate: the already typed function
`covXPolyPropLam` has a Pi domain `idPiProp`, whose eager view is impossible.
The obstruction is imported from the boundary module; its native typing and
actual non-bottom model observation are reused. This file supplies the exact
native eta edge and refutes its complete conversion motive with the actual
guarded related substitution and both endpoint typings present.

This is not an eta-shape obstruction and is not a refutation of a future
demand-indexed or step-indexed extensional relation. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelCovRelAudit TypedModelCovXAudit

/-- The actual native eta derivation has the imported function typing as
its genuine constructor child. -/
def covXPolyPropLam_eta (n : Nat) (Γ : LCtx) :
    ConvT eqEnvT n Γ
      (.lam idPiProp (.app (lift 0 1 covXPolyPropLam) (.bvar 0)))
      covXPolyPropLam covXPolyPropLamTy :=
  .eta Γ covXPolyPropLam idPiProp (.sort (.succ .zero))
    (covXPolyPropLam_typed n Γ)

/-- The new failure is independent of the eta endpoints' head forms: the
required type view is already impossible before the relation is inspected. -/
theorem not_lrSCoreCovX_eta_polyPropLam (C : CovTyping eqEnvT)
    (n : Nat) (Γ : LCtx) :
    ¬ LRSCoreCovX C (WhStepCK2 eqEnvT n) n Γ
      (.lam idPiProp (.app (lift 0 1 covXPolyPropLam) (.bvar 0)))
      covXPolyPropLam covXPolyPropLamTy (.lam [([], .prop)]) := by
  rintro (hb | ⟨v, hv⟩)
  · exact CptT.noConfusion hb
  · exact not_covXTypeView_pi_idPiProp n Γ (.sort (.succ .zero)) ⟨v⟩

/-- The exact full general eta motive is kernel-refuted for the eager
candidate, with no normalization or model-soundness assumption. -/
theorem not_fundConvAtCovX_eta_polyPropLam (C : CovTyping eqEnvT) (n : Nat) :
    ¬ FundConvAtCovX C (ctxModelT_approxTK eqEnvT n [])
      (WhStepCK2 eqEnvT n) n []
      (.lam idPiProp (.app (lift 0 1 covXPolyPropLam) (.bvar 0)))
      covXPolyPropLam covXPolyPropLamTy := by
  intro h
  have hS := relSubstAtCovX_nil C (ctxModelT_approxTK eqEnvT n [])
    (WhStepCK2 eqEnvT n) n [] EnvT.bot EnvT.bot SubstT.id SubstT.id
  have hrel := h .nil hS (.lam [([], .prop)])
    (Or.inr (covXPolyPropLam_observed n [] EnvT.bot))
  apply not_lrSCoreCovX_eta_polyPropLam C n []
  simpa only [substT_id] using hrel

/-- Both native endpoints and the actual eta derivation are inhabited.
Both covariant environment guards and the full related-substitution package
are present, together with the actual non-bottom observation used above. -/
theorem covX_eta_eager_view_counterexample (C : CovTyping eqEnvT) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n []) ∧
    Nonempty (HasTyT eqEnvT n []
      (.lam idPiProp (.app (lift 0 1 covXPolyPropLam) (.bvar 0)))
      covXPolyPropLamTy) ∧
    Nonempty (HasTyT eqEnvT n [] covXPolyPropLam covXPolyPropLamTy) ∧
    Nonempty (ConvT eqEnvT n []
      (.lam idPiProp (.app (lift 0 1 covXPolyPropLam) (.bvar 0)))
      covXPolyPropLam covXPolyPropLamTy) ∧
    EnvTypedCovAtP C (ctxModelT_approxTK eqEnvT n []) [] EnvT.bot ∧
    EnvTypedCovAtP C (ctxModelT_approxTK eqEnvT n []) [] EnvT.bot ∧
    RelSubstAtCovX C (ctxModelT_approxTK eqEnvT n [])
      (WhStepCK2 eqEnvT n) n [] EnvT.bot EnvT.bot SubstT.id SubstT.id [] ∧
    ApproxTK eqEnvT n [] EnvT.bot covXPolyPropLam (.lam [([], .prop)]) ∧
    (.lam [([], .prop)] : CptT) ≠ .bot ∧
    ¬ FundConvAtCovX C (ctxModelT_approxTK eqEnvT n [])
      (WhStepCK2 eqEnvT n) n []
      (.lam idPiProp (.app (lift 0 1 covXPolyPropLam) (.bvar 0)))
      covXPolyPropLam covXPolyPropLamTy := by
  have hS := relSubstAtCovX_nil C (ctxModelT_approxTK eqEnvT n [])
    (WhStepCK2 eqEnvT n) n [] EnvT.bot EnvT.bot SubstT.id SubstT.id
  exact ⟨⟨pinEqGroupWfT⟩, ⟨.nil⟩,
    ⟨(convEnds pinEqGroupWfT (CtxWfT.nil) (covXPolyPropLam_eta n [])).1⟩,
    ⟨covXPolyPropLam_typed n []⟩, ⟨covXPolyPropLam_eta n []⟩,
    hS.envL, hS.envR, hS, covXPolyPropLam_observed n [] EnvT.bot,
    fun h => CptT.noConfusion h, not_fundConvAtCovX_eta_polyPropLam C n⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_ETA_BOUNDARY_ROOTS
#print axioms covXPolyPropLam_eta
#print axioms not_lrSCoreCovX_eta_polyPropLam
#print axioms not_fundConvAtCovX_eta_polyPropLam
#print axioms covX_eta_eager_view_counterexample
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_ETA_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit

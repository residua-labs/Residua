import rcic.RcicNativeTypedModelCovYPolyRealization
import rcic.RcicNativeTypedModelCovYEnvironment

/-!
# An actual typed argument for the impredicative-function action

The target context contains `p : idPiProp`. The actual native argument `p`,
its reflexive conversion, the compact application, the selected semantic row,
and the new relation/realization are simultaneously inhabited. This control
composes the landed native one-layer fixture rather than copying its typing
and observation derivations. The function and output compacts are non-bottom.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYPolyPropAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelCovRelAudit TypedModelCovNormCov2Audit
open TypedModelCovXAudit TypedModelCovYAudit

/-- The repaired action is exercised on a real variable argument in a
well-formed target context. All native, model, environment and row premises
are supplied; the actual function relation produces its observed result. -/
theorem covY_polyProp_typed_action_control (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧
    Nonempty (CtxWfT eqEnvT n [.assumption idPiProp]) ∧
    Nonempty (HasTyT eqEnvT n [.assumption idPiProp] (.bvar 0) idPiProp) ∧
    Nonempty (ConvT eqEnvT n [.assumption idPiProp] (.bvar 0) (.bvar 0) idPiProp) ∧
    EnvTypedCovYAt C (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
      n [.assumption idPiProp] EnvT.bot ∧
    ApproxTK eqEnvT n [.assumption idPiProp] EnvT.bot covXPolyPropLam
      (.lam [([], .prop)]) ∧
    CovXCompactAction eqEnvT (.lam [([], .prop)]) [] .prop ∧
    CovYSelectedRow C [] .prop ([], .sort) ∧
    LRSCoreCovY C (WhStepCK2 eqEnvT n) n [.assumption idPiProp]
      (.bvar 0) (.bvar 0) idPiProp .bot .bot ∧
    LRSCoreCovY C (WhStepCK2 eqEnvT n) n [.assumption idPiProp]
      covXPolyPropLam covXPolyPropLam covXPolyPropLamTy
      (.lam [([], .prop)]) covYPolyPropCode ∧
    HereditaryCovRealizationYAt C (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n [.assumption idPiProp] EnvT.bot covXPolyPropLamTy
      (.lam [([], .prop)]) covYPolyPropCode ∧
    Nonempty (HasTyT eqEnvT n [.assumption idPiProp]
      (.app covXPolyPropLam (.bvar 0)) (.sort (.succ .zero))) ∧
    ApproxTK eqEnvT n [.assumption idPiProp] EnvT.bot
      (.app covXPolyPropLam (.bvar 0)) .prop ∧
    LRSCoreCovY C (WhStepCK2 eqEnvT n) n [.assumption idPiProp]
      (.app covXPolyPropLam (.bvar 0)) (.app covXPolyPropLam (.bvar 0))
      (.sort (.succ .zero)) .prop .sort ∧
    HereditaryCovRealizationYAt C (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n [.assumption idPiProp] EnvT.bot
      (.sort (.succ .zero)) .prop .sort ∧
    (.lam [([], .prop)] : CptT) ≠ .bot ∧ (.prop : CptT) ≠ .bot := by
  obtain ⟨hW, hΓ, ⟨hp⟩, hOldEnv, _, ha, ht, hm, _, _⟩ :=
    covXPolyPropLam_typed_action_control C hS n
  have hobs := covXPolyPropLam_observed n [.assumption idPiProp] EnvT.bot
  have hrel := covY_polyProp_related_observed C hS n [.assumption idPiProp]
    [.assumption idPiProp] EnvT.bot _ hobs
  have hreal := covY_polyProp_hereditary_observed C hS n [.assumption idPiProp]
    [.assumption idPiProp] EnvT.bot EnvT.bot _ hobs
  have hsel : CovYSelectedRow C [] .prop ([], .sort) :=
    ⟨fun _ h => (List.not_mem_nil _ h).elim, hS _ _ (ctyS_prop_sort eqEnvT)⟩
  have hc : Nonempty (ConvT eqEnvT n [.assumption idPiProp]
      (.bvar 0) (.bvar 0) idPiProp) := ⟨.refl _ _ _ hp⟩
  have hout := (lrSCoreCovY_pi_action C (readbackLaws_whStepCK2 eqEnvT n) hrel ha
    (List.mem_singleton_self ([], CptT.sort)) hsel (.bvar 0) (.bvar 0) hp hp hc
    (fun _ hu => (List.not_mem_nil _ hu).elim)).1
  have houtReal : HereditaryCovRealizationYAt C (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n [.assumption idPiProp] EnvT.bot
      (.sort (.succ .zero)) .prop .sort := by
    simpa only [TypingFin.sortCode_succ] using
      hereditaryCovRealizationYAt_sort C n (.succ .zero) (RedR.refl _)
        (show C.ty .prop (sortCode (.succ .zero)) by
          simpa only [TypingFin.sortCode_succ] using hS _ _ (ctyS_prop_sort eqEnvT))
  exact ⟨hW, hΓ, ⟨hp⟩, hc,
    envTypedCovYAt_bot C _ _ n _ hOldEnv.2, hobs, ha, hsel,
    lrSCoreCovY_bot C _ _ _ _ _, hrel, hreal, ht, hm, hout, houtReal,
    fun h => CptT.noConfusion h, fun h => CptT.noConfusion h⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_POLY_ACTION_CONTROL_ROOTS
#print axioms covY_polyProp_typed_action_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_POLY_ACTION_CONTROL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYPolyPropAudit

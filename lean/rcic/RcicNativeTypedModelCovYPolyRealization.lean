import rcic.RcicNativeTypedModelCovYPolyProp
import rcic.RcicNativeTypedModelCovYRealization

/-!
# Hereditary realization of every impredicative-lambda observation

The exact common code is the code used by relatedness. Bottom domain demands
terminate immediately; the actual codomain is Sort 1 in the binder context
and at both native argument instances. This is a supplied hereditary target
for all actual observations, not a general escape implication.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYPolyPropAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelCovRelAudit TypedModelCovNormCov2Audit
open TypedModelCovXAudit TypedModelCovYAudit

/-- Every observed lambda compact is hereditarily realized at the same
finite code, uniformly in the native context and the destination valuation. -/
theorem covY_polyProp_hereditary_observed (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (Ξ Γ : LCtx) (ρ τ : EnvT) (c : CptT)
    (h : ApproxTK eqEnvT n Ξ ρ covXPolyPropLam c) :
    HereditaryCovRealizationYAt C (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n Γ τ covXPolyPropLamTy c covYPolyPropCode := by
  rw [HereditaryCovRealizationYAt.eq_def]
  refine ⟨covY_polyProp_code_typed C hS h, Or.inr ⟨idPiProp,
    .sort (.succ .zero), .refl _, covY_polyProp_coverage C hS h, ?_⟩⟩
  intro ds out _ _ row hr hs N N' _ _ _ hd
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu
    have hb : u = .bot := C.bot_inv (lrSCoreCovY_typing C (hd u hu))
    subst u
    exact hereditaryCovRealizationYAt_bot C _ _ _ _ _ _ _
  · simpa only [TypingFin.sortCode_succ] using
      hereditaryCovRealizationYAt_sort C n (.succ .zero) (RedR.refl _)
        (show C.ty out (sortCode (.succ .zero)) from hs.2)
  · simpa only [TypingFin.sortCode_succ] using
      hereditaryCovRealizationYAt_sort C n (.succ .zero) (RedR.refl _)
        (show C.ty out (sortCode (.succ .zero)) from hs.2)
  · simpa only [TypingFin.sortCode_succ] using
      hereditaryCovRealizationYAt_sort C n (.succ .zero) (RedR.refl _)
        (show C.ty out (sortCode (.succ .zero)) from hs.2)

/-- The same actual type code witnesses both the new relation and escape.
No code replacement, raw domain observation, or eager view is assumed. -/
theorem covY_polyProp_relation_and_realization (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (Ξ Γ : LCtx) (ρ τ : EnvT) (c : CptT)
    (h : ApproxTK eqEnvT n Ξ ρ covXPolyPropLam c) :
    LRSCoreCovY C (WhStepCK2 eqEnvT n) n Γ covXPolyPropLam covXPolyPropLam
      covXPolyPropLamTy c covYPolyPropCode ∧
    HereditaryCovRealizationYAt C (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n Γ τ covXPolyPropLamTy c covYPolyPropCode :=
  ⟨covY_polyProp_related_observed C hS n Ξ Γ ρ c h,
    covY_polyProp_hereditary_observed C hS n Ξ Γ ρ τ c h⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_POLY_REALIZATION_ROOTS
#print axioms covY_polyProp_hereditary_observed
#print axioms covY_polyProp_relation_and_realization
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_POLY_REALIZATION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYPolyPropAudit

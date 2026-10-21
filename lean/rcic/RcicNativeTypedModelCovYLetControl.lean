import rcic.RcicNativeTypedModelCovYSubst
import rcic.RcicNativeTypedModelCovXLetControl

/-!
# A nonempty coherent let package at the hereditary environment interface

The landed CovX package supplies all native evidence and all four semantic
edges. Its displayed sort view transports each edge to the exact sort code;
its actual sort observations supply hereditary entry realization. Neither
the native let proof nor its four-edge proof is copied.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit TypedModelCovRelAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelCovXAudit
open TypedModelCovXLetAudit ReadbackCK2Audit

variable {E : ResolvedEnv} {n : Nat}

private theorem covY_from_covX_sort (C : CovTyping E) (hW : EnvWfT E)
    {Γ : LCtx} {x y : Expr Nat} {c : CptT} (l : Level)
    (h : LRSCoreCovX C (WhStepCK2 E n) n Γ x y (.sort l) c) :
    LRSCoreCovY C (WhStepCK2 E n) n Γ x y (.sort l) c (sortCode l) := by
  have hs := (lrSCoreCovX_iff_at_view C (readbackLaws_whStepCK2 E n)
    (normalUniqueR_whStepCK2 hW) (.sort l (.refl _)) c).mp h
  apply lrSCoreCovY_of_old_leaf C ?_ hs.1 hs.2
  intro d g he
  rcases sortCode_prop_or_sort l with hp | ht
  · rw [hp] at he
    cases he
  · rw [ht] at he
    cases he

private theorem covY_square_from_covX_sort (C : CovTyping E) (hW : EnvWfT E)
    {Γ : LCtx} {x x' y y' : Expr Nat} {c : CptT} (l : Level)
    (h : CovXSquare C (WhStepCK2 E n) n Γ x x' y y' (.sort l) (.sort l) c) :
    CovYSquare C (WhStepCK2 E n) n Γ x x' y y' (.sort l) (.sort l) c :=
  ⟨sortCode l, covY_from_covX_sort C hW l h.1,
    covY_from_covX_sort C hW l h.2.1, covY_from_covX_sort C hW l h.2.2.1,
    covY_from_covX_sort C hW l h.2.2.2⟩

private theorem covY_let_environment_of_raw (C : CovTyping E)
    (h : EnvTypedCovAtP C (ctxModelT_approxTK E n zetaLocalSortCtx)
      zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx)) :
    EnvTypedCovYAt C (ctxModelT_approxTK E n) (WhStepCK2 E n) n
      zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) := by
  refine ⟨?_, h.2⟩
  intro i A hA c hc
  have he := h.1 i A hA c hc
  cases i with
  | zero =>
      change some (.sort (.succ .zero)) = some A at hA
      cases Option.some.inj hA
      obtain ⟨a, ha, ht⟩ := he
      rcases approxTK_sort_inv ha with rfl | rfl
      · rw [C.bot_inv ht]
        exact hereditaryCovRealizationY_bot C _ _ n _ _ _
      · exact ⟨sortCode (.succ .zero), hereditaryCovRealizationYAt_sort C n
          (.succ .zero) (.refl _) ht⟩
  | succ i => simp [zetaLocalSortCtx, lookupType] at hA

/-- The old nonempty package composes into the new one at one common sort
code per four-edge square. Both actual hereditary environments are supplied. -/
theorem relSubstAtCovY_zetaLocalSortCtx_approxTK (hW : EnvWfT E) (n : Nat) :
    RelSubstAtCovY (covTypingCTyCov E) (ctxModelT_approxTK E n) (WhStepCK2 E n) n
      zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) (ctxEnvT E zetaLocalSortCtx)
      SubstT.id SubstT.id zetaLocalSortCtx := by
  have old := relSubstAtCovX_zetaLocalSortCtx_approxTK hW n zetaLocalSortCtx
  refine ⟨old.typedL, old.typedR, old.conv,
    covY_let_environment_of_raw _ old.envL, covY_let_environment_of_raw _ old.envR, ?_, ?_⟩
  · intro i A hA c hc
    have hs := old.vars i A hA c hc
    cases i with
    | zero =>
        change some (.sort (.succ .zero)) = some A at hA
        cases Option.some.inj hA
        simp only [SubstT.id, substT_id] at hs ⊢
        exact covY_square_from_covX_sort _ hW (.succ .zero) hs
    | succ i => simp [zetaLocalSortCtx, lookupType] at hA
  · intro i v A hv hA c hc
    have hs := old.lets i v A hv hA c hc
    cases i with
    | zero =>
        change some (.sort (.succ .zero)) = some A at hA
        cases Option.some.inj hA
        simp only [SubstT.id, substT_id] at hs ⊢
        exact covY_square_from_covX_sort _ hW (.succ .zero) hs
    | succ i => simp [zetaLocalSortCtx, lookupType] at hA

/-- All native and model guards coexist with the full repaired package and
a real non-bottom let observation. The actual two `CtxEnvM` fields remain. -/
theorem covY_zetaLocalSortCtx_control (hW : EnvWfT E) (n : Nat) :
    Nonempty (CtxWfT E n zetaLocalSortCtx) ∧
    Nonempty (HasTyT E n zetaLocalSortCtx (.bvar 0) (.sort (.succ .zero))) ∧
    Nonempty (ConvT E n zetaLocalSortCtx (.bvar 0) (.sort .zero) (.sort (.succ .zero))) ∧
    CtxEnvM (ctxModelT_approxTK E n zetaLocalSortCtx)
      zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) ∧
    CtxEnvM (ctxModelT_approxTK E n zetaLocalSortCtx)
      zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) ∧
    RelSubstAtCovY (covTypingCTyCov E) (ctxModelT_approxTK E n) (WhStepCK2 E n) n
      zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) (ctxEnvT E zetaLocalSortCtx)
      SubstT.id SubstT.id zetaLocalSortCtx ∧
    ctxEnvT E zetaLocalSortCtx 0 .prop ∧
    ApproxTK E n zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) (.bvar 0) .prop ∧
    ApproxTK E n zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) (.sort .zero) .prop ∧
    LRSCoreCovY (covTypingCTyCov E) (WhStepCK2 E n) n zetaLocalSortCtx
      (.bvar 0) (.sort .zero) (.sort (.succ .zero)) .prop (sortCode (.succ .zero)) ∧
    (.prop : CptT) ≠ .bot := by
  obtain ⟨hΓ, ht, hconv, _, _, _, hm, hx, hv, hr, hnb⟩ :=
    covX_zetaLocalSortCtx_control hW n zetaLocalSortCtx
  have hs := relSubstAtCovY_zetaLocalSortCtx_approxTK hW n
  exact ⟨hΓ, ht, hconv, hs.ctxEnvs.1, hs.ctxEnvs.2, hs, hm, hx, hv,
    covY_from_covX_sort _ hW (.succ .zero) hr, hnb⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_LET_CONTROL_ROOTS
#print axioms relSubstAtCovY_zetaLocalSortCtx_approxTK
#print axioms covY_zetaLocalSortCtx_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_LET_CONTROL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYAudit

import rcic.RcicNativeTypedModelCovYSubst

/-!
# The actual alias-assumption substitution package

The native target is the original Eq context. The new head maps to the
actual observed proposition `idPiProp`; the tail is the identity. This
avoids asking a neutral target variable to read back as a Pi type.
Native substitution extension is imported from the landed implementation.
All four head edges use the same exact semantic code `prop`, both source
environments have hereditary entries, and both actual coherence guards remain.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit TypedModelCovRelAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelKTypedBetaAudit
open TypedModelCovRelEscapeAudit TypedModelCovNormSubstAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open PiProbeRelIotaAudit TypedModelCovXEnvBoundaryAudit

private theorem covY_alias_probe_typing (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) : C.ty (.pi .bot []) .prop := by
  apply hS
  rw [CTyS]
  exact Or.inr (.pi .bot (fun _ hs => (List.not_mem_nil _ hs).elim))

/-- The alias's actual normal sort supplies the exact leaf code. The old
relation proof is composed directly, including its native Pi observation. -/
theorem lrSCoreCovY_idPiProp_alias (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (A B : Expr Nat) :
    LRSCoreCovY C (WhStepCK2 eqEnvT n) n eqGapCtx idPiProp idPiProp
      (eqGapDirectAlias A B) (.pi .bot []) .prop :=
  lrSCoreCovY_of_old_leaf C (fun _ _ h => CptT.noConfusion h)
    (covY_alias_probe_typing C hS) (idPiProp_covRel_at_alias C n A B)

/-- A complete, nonempty related-substitution package for the E fixture.
The only head premise is its genuine native argument typing. -/
theorem relSubstAtCovY_alias_cons (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (A B : Expr Nat)
    (hN : HasTyT eqEnvT n eqGapCtx idPiProp (eqGapDirectAlias A B)) :
    RelSubstAtCovY C (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n) n
      eqGapCtx
      (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
      (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
      (SubstT.cons idPiProp SubstT.id) (SubstT.cons idPiProp SubstT.id)
      (.assumption (eqGapDirectAlias A B) :: eqGapCtx) := by
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  have hid := typedSubstT_id (envClosed_of_envWfT pinEqGroupWfT) hΓ
  have ht := cov_typedSubst_cons hid (by simpa only [substT_id] using hN)
  have he := envTypedCovYAt_alias_cons C hS n A B
  refine ⟨ht, ht, ?_, he, he, ?_, ?_⟩
  · intro i T hT
    obtain ⟨h⟩ := ht.1 i T hT
    exact ⟨.refl _ _ _ h⟩
  · intro i T hT c hc
    have hm := hc.elim id id
    cases i with
    | zero =>
        have hEq : lift 0 1 (eqGapDirectAlias A B) = T := Option.some.inj hT
        subst T
        change c ∈ [CptT.pi .bot []] at hm
        obtain rfl := List.mem_singleton.mp hm
        simp only [SubstT.cons_zero, substT_cons_lift, substT_id]
        have hr := lrSCoreCovY_idPiProp_alias C hS n A B
        exact ⟨.prop, hr, hr, hr, hr⟩
    | succ i =>
        change c = .bot at hm
        subst c
        exact covYSquare_bot C _ n _ _ _ _ _ _ _
  · intro i v T hv
    cases i with
    | zero => cases hv
    | succ i =>
        rw [lookupValue_cons_succ, lookupValue_eqGapCtx_none] at hv
        exact Option.noConfusion hv

/-- Both coherent hereditary environments, the complete four-edge package,
and the observed non-bottom head are simultaneously inhabited. The old raw
environment guard remains refuted on this exact same source valuation. -/
theorem covY_alias_substitution_control (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    ∃ A B : Expr Nat, ∃ w : Level,
      Nonempty (HasTyT eqEnvT n eqGapCtx (eqGapDirectAlias A B) (.sort w)) ∧
      Nonempty (CtxWfT eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx)) ∧
      Nonempty (HasTyT eqEnvT n eqGapCtx idPiProp (eqGapDirectAlias A B)) ∧
      ApproxTK eqEnvT n eqGapCtx EnvT.bot idPiProp (.pi .bot []) ∧
      RelSubstAtCovY C (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n) n
        eqGapCtx
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (SubstT.cons idPiProp SubstT.id) (SubstT.cons idPiProp SubstT.id)
        (.assumption (eqGapDirectAlias A B) :: eqGapCtx) ∧
      LRSCoreCovY C (WhStepCK2 eqEnvT n) n eqGapCtx idPiProp idPiProp
        (eqGapDirectAlias A B) (.pi .bot []) .prop ∧
      HereditaryCovRealizationYAt C (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
        n eqGapCtx EnvT.bot (eqGapDirectAlias A B) (.pi .bot []) .prop ∧
      (¬ EnvTypedCovAtP C
        (ctxModelT_approxTK eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx))
        (.assumption (eqGapDirectAlias A B) :: eqGapCtx)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)) ∧
      (.pi .bot [] : CptT) ≠ .bot := by
  obtain ⟨hW, hΓ, _, A, B, w, hD, hΓ', ⟨hN⟩, hm, _, hraw, hnb⟩ :=
    covY_alias_environment_control C hS n
  refine ⟨hW, hΓ, A, B, w, hD, hΓ', ⟨hN⟩, hm,
    relSubstAtCovY_alias_cons C hS n A B hN,
    lrSCoreCovY_idPiProp_alias C hS n A B, ?_, hraw, hnb⟩
  simpa only [sortCode_zero] using hereditaryCovRealizationYAt_sort C n .zero
    (eqGapAlias_type_read n A B) (by
      simpa only [sortCode_zero] using covY_alias_probe_typing C hS)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_ALIAS_SUBST_ROOTS
#print axioms lrSCoreCovY_idPiProp_alias
#print axioms relSubstAtCovY_alias_cons
#print axioms covY_alias_substitution_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_ALIAS_SUBST_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYAudit

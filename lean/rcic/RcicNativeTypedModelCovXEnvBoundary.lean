import rcic.RcicNativeTypedModelCovXInterface
import rcic.RcicNativeTypedModelCovXRealization

/-!
# Hereditary domain realization does not extend the raw environment guard

The actual lifted Eq alias remains bottom-only: its lifted recursor prefix
still has only five arguments, so the landed prefix theorem applies. Full
application inversion then composes the landed variable-head collapse.
No general lifting law for the guarded model is asserted.

The original context is natively well formed and covariantly typed; an
observed non-bottom native argument is related and hereditarily realized at
the alias domain. Nevertheless its singleton-demand extension violates
`EnvTypedCovAtP` at lookup zero. Thus retaining that raw environment guard in
`RelSubstAtCovX` cannot supply this actual binder-extension step. Endpoint
hereditary escape alone does not repair environment extension.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXEnvBoundaryAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelKFailureAudit
open TypedModelKTypedBetaAudit TypedModelCovPropagationAudit
open TypedModelKTransportAudit TypedModelCovRelAudit
open TypedModelCovRelEscapeAudit TypedModelCovRelRealizationAudit
open TypedModelCovNormCov2Audit TypedModelCovXAudit
open TypedModelCovXRealizationAudit

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvT}

private theorem covX_function_variable_application_bot
    {D f arg : Expr Nat} {c : CptT}
    (hfbot : ∀ {u}, ApproxTK E n Γ ρ f u → u = .bot)
    (h : ApproxTK E n Γ ρ (.app (.lam D (.app (.bvar 0) arg)) f) c) :
    c = .bot := by
  rcases approxTK_app_inv h with hbot | ⟨g, s, hc, hf, hs, hargs⟩ |
    ⟨r, args, u, hc, hf, hx⟩ | hsat
  · exact hbot
  · rcases approxTK_lam_inv hf with hbot | ⟨a, g', he, _, _, hb⟩
    · exact (CptT.noConfusion hbot : False).elim
    · injection he with hg
      subst g'
      have hhead : ∀ {u}, ApproxTK E n (.assumption D :: Γ)
          (EnvT.cons (demandT s.1) ρ) (.bvar 0) u → u = .bot := by
        intro u hu
        rcases approxTK_bvar_inv hu with hbot | hm
        · exact hbot
        · exact hfbot (hargs u hm)
      exact hc.trans (approxTK_app_bot_of_function_bot
        (fun _ _ he => Expr.noConfusion he) hhead (hb s hs).2)
  · rcases approxTK_lam_inv hf with hbot | ⟨a, g, he, _⟩
    · exact (CptT.noConfusion hbot : False).elim
    · exact (CptT.noConfusion he : False).elim
  · exact (not_saturatedComputationTK_of_nonconst_head
      (fun _ _ he => Expr.noConfusion he) hsat).elim

/-- Lifting the five-argument Eq prefix does not saturate it. The existing
arity theorem supplies collapse independently of every lifted index. -/
theorem approxTK_lift_eqGapPrefix_bot (k : Nat) {c : CptT}
    (h : ApproxTK eqEnvT n Γ ρ (lift 0 k eqGapPrefix) c) : c = .bot := by
  rw [eqGapPrefix, foldApps_lift] at h
  exact approxTK_eqRec_fold_prefix_bot (by simp; decide) h

/-- The actual lifted alias has no non-bottom observation, at any frozen
native model context and valuation. -/
theorem approxTK_lift_eqGapDirectAlias_bot (A B : Expr Nat) {c : CptT}
    (h : ApproxTK eqEnvT n Γ ρ (lift 0 1 (eqGapDirectAlias A B)) c) : c = .bot := by
  change ApproxTK eqEnvT n Γ ρ
    (.app (.lam (lift 0 1 (.pi A B)) (.app (.bvar 0) (.bvar 2)))
      (lift 0 1 eqGapPrefix)) c at h
  exact covX_function_variable_application_bot (fun h => approxTK_lift_eqGapPrefix_bot 1 h) h

/-- Lookup zero is the lifted raw alias. Its only code is bottom, which
cannot type the actual non-bottom singleton demand. -/
theorem not_envTypedCovAtP_alias_cons (C : CovTyping eqEnvT) (n : Nat)
    (Ξ : LCtx) (A B : Expr Nat) :
    ¬ EnvTypedCovAtP C (ctxModelT_approxTK eqEnvT n Ξ)
      (.assumption (eqGapDirectAlias A B) :: eqGapCtx)
      (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot) := by
  intro h
  obtain ⟨a, ha, hc⟩ := h.1 0 (lift 0 1 (eqGapDirectAlias A B)) rfl
    (.pi .bot []) (List.mem_singleton.mpr rfl)
  have hb := approxTK_lift_eqGapDirectAlias_bot A B ha
  subst a
  exact CptT.noConfusion (C.bot_inv hc)

/-- The new package retains the refuted raw guard as its left environment
field, so no choice of target substitution repairs this extension. -/
theorem not_relSubstAtCovX_alias_cons (C : CovTyping eqEnvT) (n : Nat)
    (Ξ Δ : LCtx) (A B : Expr Nat) (ρ' : EnvT) (σ σ' : SubstT) :
    ¬ RelSubstAtCovX C (ctxModelT_approxTK eqEnvT n Ξ) (WhStepCK2 eqEnvT n) n
      Δ (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot) ρ' σ σ'
      (.assumption (eqGapDirectAlias A B) :: eqGapCtx) :=
  fun h => not_envTypedCovAtP_alias_cons C n Ξ A B h.envL

/-- Exact proposed raw assumption-extension port, with native type/argument
typing, actual observation, the new related argument, and its hereditary
realization all retained. This port is refuted below. -/
def CovXRawAssumptionExtension (C : CovTyping E) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {ρ : EnvT} {D N : Expr Nat} {w : Level} {u : CptT},
    CtxWfT E n Γ → HasTyT E n Γ D (.sort w) → HasTyT E n Γ N D →
    EnvTypedCovAtP C (ctxModelT_approxTK E n Γ) Γ ρ →
    ApproxTK E n Γ ρ N u →
    ∀ view : CovXTypeView E (WhStepCK2 E n) n Γ D,
      LRSCoreCovXAt C view N N u →
      HereditaryCovRealizationXAt C (ctxModelT_approxTK E n) view ρ u →
      EnvTypedCovAtP C (ctxModelT_approxTK E n (.assumption D :: Γ))
        (.assumption D :: Γ) (EnvT.cons (demandT [u]) ρ)

/-- The rejected extension's premises are all actual native/model inputs.
The original covariant environment guard, non-bottom related demand, and
hereditary domain realization remain simultaneously inhabited. -/
theorem covX_alias_raw_extension_counterexample (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    EnvTypedCovAtP C (ctxModelT_approxTK eqEnvT n eqGapCtx) eqGapCtx EnvT.bot ∧
    ∃ A B : Expr Nat, ∃ w : Level,
      Nonempty (HasTyT eqEnvT n eqGapCtx (eqGapDirectAlias A B) (.sort w)) ∧
      Nonempty (CtxWfT eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx)) ∧
      Nonempty (HasTyT eqEnvT n eqGapCtx idPiProp (eqGapDirectAlias A B)) ∧
      ApproxTK eqEnvT n eqGapCtx EnvT.bot idPiProp (.pi .bot []) ∧
      LRSCoreCovXAt (n := n) C (.sort .zero (eqGapAlias_type_read n A B))
        idPiProp idPiProp (.pi .bot []) ∧
      HereditaryCovRealizationXAt (n := n) C (ctxModelT_approxTK eqEnvT n)
        (.sort .zero (eqGapAlias_type_read n A B)) EnvT.bot (.pi .bot []) ∧
      (¬ EnvTypedCovAtP C
        (ctxModelT_approxTK eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx))
        (.assumption (eqGapDirectAlias A B) :: eqGapCtx)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)) ∧
      (.pi .bot [] : CptT) ≠ .bot := by
  obtain ⟨hW, ⟨hΓ⟩, hρ, A, B, ⟨hN⟩, hm, hr, _⟩ :=
    alias_type_escape_counterexample C n
  obtain ⟨w, hD⟩ := tySort pinEqGroupWfT hΓ hN
  have hg : C.ty (.pi .bot []) (sortCode .zero) := by
    rw [sortCode_zero]
    apply hS
    rw [CTyS]
    exact Or.inr (.pi .bot (fun _ hs => (List.not_mem_nil _ hs).elim))
  have hx : LRSCoreCovXAt (n := n) C (.sort .zero (eqGapAlias_type_read n A B))
      idPiProp idPiProp (.pi .bot []) := ⟨hg, hr⟩
  exact ⟨hW, ⟨hΓ⟩, hρ, A, B, w, ⟨hD⟩,
    ⟨.assumption eqGapCtx (eqGapDirectAlias A B) w hΓ hD⟩, ⟨hN⟩, hm, hx,
    hereditaryCovRealizationXAt_sort_of_related C n .zero
      (eqGapAlias_type_read n A B) EnvT.bot (.pi .bot []) hx,
    not_envTypedCovAtP_alias_cons C n _ A B, fun h => CptT.noConfusion h⟩

/-- Hereditary endpoint realization cannot discharge the retained raw
assumption-extension guard, even at actual typed and observed arguments. -/
theorem not_covXRawAssumptionExtension_eqGap (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) : ¬ CovXRawAssumptionExtension C n := by
  intro h
  obtain ⟨_, ⟨hΓ⟩, hρ, A, B, w, ⟨hD⟩, _, ⟨hN⟩, hm, hr, hh, hno, _⟩ :=
    covX_alias_raw_extension_counterexample C hS n
  exact hno (h hΓ hD hN hρ hm (.sort .zero (eqGapAlias_type_read n A B)) hr hh)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_ENV_BOUNDARY_ROOTS
#print axioms approxTK_lift_eqGapPrefix_bot
#print axioms approxTK_lift_eqGapDirectAlias_bot
#print axioms not_envTypedCovAtP_alias_cons
#print axioms not_relSubstAtCovX_alias_cons
#print axioms CovXRawAssumptionExtension
#print axioms covX_alias_raw_extension_counterexample
#print axioms not_covXRawAssumptionExtension_eqGap
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_ENV_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXEnvBoundaryAudit

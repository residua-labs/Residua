import rcic.RcicNativeTypedModelCovZWall4

/-!
# An inhabited relevant function demand

The function compact used by the relevant-alias measurement is realized by
the actual native function `fun (_ : Prop) => idPiProp`. Its non-bottom
action is exercised at the genuine proposition `idPiProp`. This tests the
inner relation premise independently of the outer generic action consumer.
No fixture from an unlanded dependency is defined here.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovZAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelKTypedBetaAudit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit
open TypedModelCovXAudit TypedModelCovYAudit TypedModelCovYEtaAudit

/-- A real native function inhabits the relevant domain. -/
def covZ_relevant_argument_native (n : Nat) :
    HasTyT eqEnvT n eqGapCtx (.lam (.sort .zero) idPiProp)
      (.pi (.sort .zero) (.sort .zero)) :=
  .lam _ _ _ _ _ (.sort _ _)
    (apartLeft_ty n (.assumption (.sort .zero) :: eqGapCtx))

/-- Its model observation is the exact non-bottom function demand. -/
theorem covZ_relevant_argument_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK eqEnvT n Γ ρ (.lam (.sort .zero) idPiProp)
      (.lam [([.bot], .pi .bot [])]) := by
  refine .lam (a := .prop) ?_ ?_ ?_ ?_
  · simpa only [sortCode_zero] using approxTK_sort_code eqEnvT n Γ ρ .zero
  · intro row hrow u hu
    obtain rfl := List.mem_singleton.mp hrow
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · exact ⟨([.bot], .pi .bot []), List.mem_singleton_self _,
      fun h => CptT.noConfusion h⟩
  · intro row hrow
    obtain rfl := List.mem_singleton.mp hrow
    exact approxTK_pi_bot_nil eqEnvT n (.assumption (.sort .zero) :: Γ)
      (EnvT.cons (demandT [.bot]) ρ) (.sort .zero) (.bvar 0)

/-- The relevant demand's applicative relation has a concrete inhabitant.
Every non-bottom action reduces to the imported proposition relation. -/
theorem lrSCoreCovY_relevant_argument (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) :
    LRSCoreCovY C (WhStepCK2 eqEnvT n) n eqGapCtx
      (.lam (.sort .zero) idPiProp) (.lam (.sort .zero) idPiProp)
      (.pi (.sort .zero) (.sort .zero))
      (.lam [([.bot], .pi .bot [])]) covZPropArrowCode := by
  have hgate := covZ_relevant_demand_typing C hS
  rw [LRSCoreCovY.eq_def]
  refine ⟨hgate, Or.inr ⟨.sort .zero, .sort .zero, .refl _,
    covYActionCoverage_lam_of_typing C hgate, ?_⟩⟩
  intro ds out ha row hrow hsel N N' hN hN' hconv hd
  obtain rfl := List.mem_singleton.mp hrow
  cases ha with
  | bot =>
      exact ⟨lrSCoreCovY_bot C _ _ _ _ _, lrSCoreCovY_bot C _ _ _ _ _⟩
  | app hs hx =>
      obtain rfl := List.mem_singleton.mp hs
      have hbase := (covY_idPiProp_two_relation_codes C hS n).2
      have hr (N : Expr Nat) : RedR (WhStepCK2 eqEnvT n) eqGapCtx
          (.app (.lam (.sort .zero) idPiProp) N) idPiProp :=
        .step ((readbackLaws_whStepCK2 eqEnvT n).beta eqGapCtx
          (.sort .zero) idPiProp N) (.refl _)
      have h := lrSCoreCovY_expand_red_both C (readbackLaws_whStepCK2 eqEnvT n)
        .prop (hr N) (hr N') hbase
      exact ⟨h, h⟩

/-- The inner action premise is inhabited with native/context guards,
model observations, hereditary environment typing, the exact relation and
realization, and a genuinely non-bottom tested application result. -/
theorem covZ_relevant_argument_control (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    EnvTypedCovYAt C (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
      n eqGapCtx EnvT.bot ∧
    Nonempty (HasTyT eqEnvT n eqGapCtx (.lam (.sort .zero) idPiProp)
      (.pi (.sort .zero) (.sort .zero))) ∧
    Nonempty (HasTyT eqEnvT n eqGapCtx idPiProp (.sort .zero)) ∧
    Nonempty (ConvT eqEnvT n eqGapCtx idPiProp idPiProp (.sort .zero)) ∧
    ApproxTK eqEnvT n eqGapCtx EnvT.bot (.lam (.sort .zero) idPiProp)
      (.lam [([.bot], .pi .bot [])]) ∧
    LRSCoreCovY C (WhStepCK2 eqEnvT n) n eqGapCtx
      (.lam (.sort .zero) idPiProp) (.lam (.sort .zero) idPiProp)
      (.pi (.sort .zero) (.sort .zero))
      (.lam [([.bot], .pi .bot [])]) covZPropArrowCode ∧
    HereditaryCovRealizationYAt C (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n eqGapCtx EnvT.bot
      (.pi (.sort .zero) (.sort .zero))
      (.lam [([.bot], .pi .bot [])]) covZPropArrowCode ∧
    CovXCompactAction eqEnvT (.lam [([.bot], .pi .bot [])]) [.bot] (.pi .bot []) ∧
    CovYSelectedRow C [.bot] (.pi .bot []) ([], .prop) ∧
    Nonempty (HasTyT eqEnvT n eqGapCtx
      (.app (.lam (.sort .zero) idPiProp) idPiProp) (.sort .zero)) ∧
    ApproxTK eqEnvT n eqGapCtx EnvT.bot
      (.app (.lam (.sort .zero) idPiProp) idPiProp) (.pi .bot []) ∧
    LRSCoreCovY C (WhStepCK2 eqEnvT n) n eqGapCtx
      (.app (.lam (.sort .zero) idPiProp) idPiProp)
      (.app (.lam (.sort .zero) idPiProp) idPiProp)
      (.sort .zero) (.pi .bot []) .prop ∧
    HereditaryCovRealizationYAt C (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n eqGapCtx EnvT.bot (.sort .zero) (.pi .bot []) .prop ∧
    (.lam [([.bot], .pi .bot [])] : CptT) ≠ .bot ∧ (.pi .bot [] : CptT) ≠ .bot := by
  have hrel := lrSCoreCovY_relevant_argument C hS n
  have ht := apartLeft_ty n eqGapCtx
  have hconv : Nonempty (ConvT eqEnvT n eqGapCtx idPiProp idPiProp (.sort .zero)) :=
    ⟨.refl _ _ _ ht⟩
  have ha : CovXCompactAction eqEnvT (.lam [([.bot], .pi .bot [])])
      [.bot] (.pi .bot []) := by
    refine .app (List.mem_singleton_self _) ?_
    intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact .bot _ _
  have hsel : CovYSelectedRow C [.bot] (.pi .bot []) ([], .prop) :=
    ⟨fun _ hu => (List.not_mem_nil _ hu).elim, (covY_idPiProp_two_code_gates C hS).2⟩
  have hout := (lrSCoreCovY_pi_action C (readbackLaws_whStepCK2 eqEnvT n)
    hrel ha (List.mem_singleton_self _) hsel idPiProp idPiProp ht ht hconv
      (fun u hu => by
        obtain rfl := List.mem_singleton.mp hu
        exact lrSCoreCovY_bot C _ _ _ _ _)).1
  have houtObs : ApproxTK eqEnvT n eqGapCtx EnvT.bot
      (.app (.lam (.sort .zero) idPiProp) idPiProp) (.pi .bot []) := by
    refine .app (covZ_relevant_argument_observed n eqGapCtx EnvT.bot)
      (List.mem_singleton_self _) ?_
    intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact .bot _ _ _
  exact ⟨⟨pinEqGroupWfT⟩, eqGapCtx_wf n, envTypedCovYAt_eqGap_bot C n,
    ⟨covZ_relevant_argument_native n⟩, ⟨ht⟩, hconv,
    covZ_relevant_argument_observed n eqGapCtx EnvT.bot, hrel,
    hereditaryCovRealizationYAt_relevant_domain C n EnvT.bot (.refl _) hrel,
    ha, hsel, ⟨.app _ _ _ _ _ (covZ_relevant_argument_native n) ht⟩, houtObs,
    hout, covY_idPiProp_realized_at_prop_code C hS n eqGapCtx EnvT.bot,
    fun h => CptT.noConfusion h, fun h => CptT.noConfusion h⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Z_WALL4_CONTROL_ROOTS
#print axioms covZ_relevant_argument_native
#print axioms covZ_relevant_argument_observed
#print axioms lrSCoreCovY_relevant_argument
#print axioms covZ_relevant_argument_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Z_WALL4_CONTROL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovZAudit

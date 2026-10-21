import rcic.RcicNativeTypedModelCovYEnvironment
import rcic.RcicNativeTypedModelCovYTransport

/-!
# A fixed relation code need not be the native type's realized code

The actual proposition `idPiProp : Sort 0` is observed at `pi bot []`.
The relation accepts this observation both at code `sort` and at code `prop`:
the imported universe payload is the same, and both compact typing gates hold.
But `Sort 0` is CK2-normal and observes only `bot` or `prop`, so hereditary
realization at the exact code `sort` is false. Realization at `prop` is proved.

The refuted implication retains EnvWf, CtxWf, both native typings, both actual
observations and both NEW hereditary environment guards. The counterexample
uses identical endpoints, so each displayed native/model/environment witness
inhabits both sides. It does not refute existential-code escape, and does not
change the relation by adding its desired conclusion as a new conjunct.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelKFailureAudit
open TypedModelCovRelAudit TypedModelCovRelEscapeAudit TypedModelCovNormCov2Audit

/-- Both code gates hold for the same genuine non-bottom proposition probe. -/
theorem covY_idPiProp_two_code_gates (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) :
    C.ty (.pi .bot []) .sort ∧ C.ty (.pi .bot []) .prop := by
  constructor
  · apply hS
    rw [CTyS]
    exact Or.inr (.pi .bot (fun _ hs => (List.not_mem_nil _ hs).elim))
  · apply hS
    rw [CTyS]
    exact Or.inr (.pi .bot (fun _ hs => (List.not_mem_nil _ hs).elim))

/-- These are actual fixed-code relation witnesses, obtained by composition
with the landed alias witness and the new readback transport. -/
theorem covY_idPiProp_two_relation_codes (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) :
    LRSCoreCovY C (WhStepCK2 eqEnvT n) n eqGapCtx idPiProp idPiProp
      (.sort .zero) (.pi .bot []) .sort ∧
    LRSCoreCovY C (WhStepCK2 eqEnvT n) n eqGapCtx idPiProp idPiProp
      (.sort .zero) (.pi .bot []) .prop := by
  have old := idPiProp_covRel_at_alias C n (.sort .zero) (.sort .zero)
  have move := lrSCoreCovY_type_readback_iff (n := n) (x := idPiProp) (y := idPiProp)
    C (readbackLaws_whStepCK2 eqEnvT n)
    (detR_whStepCK2 pinEqGroupWfT)
    (eqGapAlias_type_read n (.sort .zero) (.sort .zero)) (.pi .bot [])
  have gates := covY_idPiProp_two_code_gates C hS
  exact ⟨(move .sort).mp (lrSCoreCovY_of_old_leaf C
      (by intro d g h; cases h) gates.1 old),
    (move .prop).mp (lrSCoreCovY_of_old_leaf C
      (by intro d g h; cases h) gates.2 old)⟩

/-- Exact-code realization rejects `sort` at native `Sort 0`, uniformly in
the model valuation and native context. -/
theorem not_covY_idPiProp_realized_at_sort_code (C : CovTyping eqEnvT)
    (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ¬ HereditaryCovRealizationYAt C (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n Γ ρ (.sort .zero) (.pi .bot []) .sort := by
  intro h
  rw [HereditaryCovRealizationYAt.eq_def] at h
  rcases h.2 with hb | ⟨A₀, hr, _, ho⟩
  · cases hb
  · have he := redR_of_normal (normalR_sortCK2 (E := eqEnvT) (n := n) Γ .zero) hr
    subst A₀
    change ApproxTK eqEnvT n Γ ρ (.sort .zero) .sort at ho
    rcases approxTK_sort_inv ho with hb | hc
    · cases hb
    · rw [sortCode_zero] at hc
      cases hc

/-- The appropriate native type code supplies the complete hereditary
target at exactly the same non-bottom observation. -/
theorem covY_idPiProp_realized_at_prop_code (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    HereditaryCovRealizationYAt C (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n Γ ρ (.sort .zero) (.pi .bot []) .prop := by
  simpa only [sortCode_zero] using
    hereditaryCovRealizationYAt_sort C n .zero (Γ := Γ) (ρ := ρ)
      (RedR.refl _) (show C.ty (.pi .bot []) (sortCode .zero) by
        rw [sortCode_zero]
        exact (covY_idPiProp_two_code_gates C hS).2)

/-- Naive escape retaining the caller's literal relation code. All of the
native, observation and new two-sided environment guards are explicit. -/
def CovYFixedCodeEscape (C : CovTyping eqEnvT) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {ρ ρ' : EnvT} {x y A : Expr Nat} {c a : CptT},
    EnvWfT eqEnvT → CtxWfT eqEnvT n Γ →
    HasTyT eqEnvT n Γ x A → HasTyT eqEnvT n Γ y A →
    EnvTypedCovYAt C (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n) n Γ ρ →
    EnvTypedCovYAt C (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n) n Γ ρ' →
    ApproxTK eqEnvT n Γ ρ x c → ApproxTK eqEnvT n Γ ρ' y c →
    LRSCoreCovY C (WhStepCK2 eqEnvT n) n Γ x y A c a →
    HereditaryCovRealizationYAt C (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n Γ ρ A c a ∧
    HereditaryCovRealizationYAt C (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n Γ ρ' A c a

theorem not_covYFixedCodeEscape (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) : ¬ CovYFixedCodeEscape C n := by
  intro escape
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  have ht := apartLeft_ty n eqGapCtx
  have ho := approxTK_pi_bot_nil eqEnvT n eqGapCtx EnvT.bot (.sort .zero) (.bvar 0)
  have henv := envTypedCovYAt_eqGap_bot C n
  exact not_covY_idPiProp_realized_at_sort_code C n eqGapCtx EnvT.bot
    (escape pinEqGroupWfT hΓ ht ht henv henv ho ho
      (covY_idPiProp_two_relation_codes C hS n).1).1

/-- No abstract typing or environment port is left unsupplied in the C2
instance of the fixed-code counterexample. -/
theorem not_covYFixedCodeEscape_C2 (n : Nat) :
    ¬ CovYFixedCodeEscape (covTypingCTyCov2 eqEnvT) n :=
  not_covYFixedCodeEscape _ (covTypingCTyCov2_includesS eqEnvT) n

/-- The same witnessed native fixture has both the wrong-code relation and
the correctly anchored relation-plus-realization. The observation is nonzero. -/
theorem covY_code_anchor_control (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    Nonempty (HasTyT eqEnvT n eqGapCtx idPiProp (.sort .zero)) ∧
    ApproxTK eqEnvT n eqGapCtx EnvT.bot idPiProp (.pi .bot []) ∧
    EnvTypedCovYAt C (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
      n eqGapCtx EnvT.bot ∧
    LRSCoreCovY C (WhStepCK2 eqEnvT n) n eqGapCtx idPiProp idPiProp
      (.sort .zero) (.pi .bot []) .sort ∧
    (¬ HereditaryCovRealizationYAt C (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n eqGapCtx EnvT.bot (.sort .zero) (.pi .bot []) .sort) ∧
    LRSCoreCovY C (WhStepCK2 eqEnvT n) n eqGapCtx idPiProp idPiProp
      (.sort .zero) (.pi .bot []) .prop ∧
    HereditaryCovRealizationYAt C (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n eqGapCtx EnvT.bot (.sort .zero) (.pi .bot []) .prop ∧
    (.pi .bot [] : CptT) ≠ .bot :=
  ⟨⟨pinEqGroupWfT⟩, eqGapCtx_wf n, ⟨apartLeft_ty n eqGapCtx⟩,
    approxTK_pi_bot_nil eqEnvT n eqGapCtx EnvT.bot _ _, envTypedCovYAt_eqGap_bot C n,
    (covY_idPiProp_two_relation_codes C hS n).1,
    not_covY_idPiProp_realized_at_sort_code C n eqGapCtx EnvT.bot,
    (covY_idPiProp_two_relation_codes C hS n).2,
    covY_idPiProp_realized_at_prop_code C hS n eqGapCtx EnvT.bot,
    fun h => CptT.noConfusion h⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_CODE_BOUNDARY_ROOTS
#print axioms covY_idPiProp_two_code_gates
#print axioms covY_idPiProp_two_relation_codes
#print axioms not_covY_idPiProp_realized_at_sort_code
#print axioms covY_idPiProp_realized_at_prop_code
#print axioms CovYFixedCodeEscape
#print axioms not_covYFixedCodeEscape
#print axioms not_covYFixedCodeEscape_C2
#print axioms covY_code_anchor_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_CODE_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYAudit

import rcic.RcicNativeReadbackCK2Gap
import rcic.RcicNativeTypedModelCovPropagation
import rcic.RcicNativeTypedModelCovRelFund

/-!
# The full Eq target supplier and its exact native arity boundary

This leaf retains all substitutions, both semantic environments, every
target context, and every source compact in `FundTyAt` and `FundTyAtCov`.
The new motive also retains both typed environment guards and their let-value
coherence.  Their equivalences do not discharge the native arity statement:
they identify precisely the outstanding input, including the complete
converse at bottom semantic environments.  The original non-bottom
observation is present in that converse, so the arity boundary is not a
vacuous relation counterexample.

All landed definitions and observations are unchanged. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelKAudit TypedModelKFailureAudit
open TypedModelKControlAudit TypedModelKTypedBetaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2InputsAudit ReadbackCK2GapAudit
open PiProbeRelIotaAudit
open TypedModelCovPropagationAudit TypedModelCovRelAudit

variable {n : Nat} {Δ : LCtx}

/-- A native typed substitution computes the entire substituted Eq target
once the exact constructor arity condition is supplied. -/
theorem eqGap_subst_read_of_typedCtorArity (hAr : EqGapTypedCtorArity n)
    (hΔ : CtxWfT eqEnvT n Δ) {σ : SubstT}
    (hT : TypedSubstT eqEnvT n Δ σ eqGapCtx) :
    RedR (WhStepCK2 eqEnvT n) Δ (substT σ eqGapRedex) (.sort .zero) := by
  rcases eqMajor_cases (σ 0) with ⟨us, args, he⟩ | hnc
  · have hc := (isCtorSpine_eq_iff (σ 0)).mpr ⟨us, args, he⟩
    rw [substT_eqGapRedex]
    exact .step (.ctx (whStepCtx_gapCall_ctor_two hc (hAr hΔ hT hc))) (.refl _)
  · exact redR_eqGap_subst_nonCtor_native hT hnc

/-- Exact characterization of the full target supplier requested by the
function-variable beta adapter.  The fixed native model context does not
remove either substituted target context or the native arity obligation. -/
theorem eqGapFundTyAt_approxTK_iff_typedCtorArity (n : Nat) :
    FundTyAt (ctxModelT_approxTK eqEnvT n eqGapCtx) (WhStepCK2 eqEnvT n)
      n eqGapCtx eqGapRedex (.sort (.succ .zero)) ↔ EqGapTypedCtorArity n := by
  constructor
  · intro hF Δ σ hΔ hT hc
    have hS := relSubstAtT_eqGap_bot_diagonal
      (ctxModelT_approxTK eqEnvT n eqGapCtx) (WhStepCK2 eqEnvT n) hT
    have hrel := hF hΔ hS .prop (Or.inl (approxTK_eqGap_prop n EnvT.bot))
    obtain ⟨_, u, _, hr, _⟩ := (lrSCoreS_prop_iff _ _ _ _).mp hrel
    rw [substT_eqGapRedex] at hr
    exact redR_gapCall_ctor_arity_native hc hr
  · intro hAr Δ ρ ρ' σ σ' hΔ hS c hc
    have hshape : c = .bot ∨ c = .prop := by
      rcases hc with hc | hc <;> exact eqGap_model_shape (approxTK_forget hc)
    rcases hshape with rfl | rfl
    · exact lrSCoreS_bot _ _ _ _
    · rw [lrSCoreS_prop_iff]
      exact ⟨⟨.succ .zero, .refl _⟩, .zero, .zero,
        eqGap_subst_read_of_typedCtorArity hAr hΔ hS.1,
        eqGap_subst_read_of_typedCtorArity hAr hΔ hS.2.1⟩

/-- A native wrong-arity witness would refute the complete supplier,
using a complete related substitution and the actual `.prop` observation.
The wrong-arity witness is an explicit premise, not asserted here. -/
theorem not_eqGapFundTyAt_approxTK_of_typed_badarity
    (hΔ : CtxWfT eqEnvT n Δ) {σ : SubstT}
    (hT : TypedSubstT eqEnvT n Δ σ eqGapCtx)
    (hc : IsCtorSpine eqEnvT (σ 0))
    (hbad : (appsSpine (σ 0)).2.length ≠ 2) :
    ¬ FundTyAt (ctxModelT_approxTK eqEnvT n eqGapCtx) (WhStepCK2 eqEnvT n)
      n eqGapCtx eqGapRedex (.sort (.succ .zero)) := by
  intro hF
  exact hbad ((eqGapFundTyAt_approxTK_iff_typedCtorArity n).mp hF hΔ hT hc)

/-- With the native arity input, the beta adapter receives the entire
quantified target supplier, not only the identity-substitution readback. -/
theorem eqGapDirectAlias_fundConvAt_of_typedCtorArity
    (hAr : EqGapTypedCtorArity n) (A B : Expr Nat) :
    FundConvAt (ctxModelT_approxTK eqEnvT n eqGapCtx) (WhStepCK2 eqEnvT n)
      n eqGapCtx (eqGapDirectAlias A B) eqGapRedex (.sort (.succ .zero)) := by
  exact fundConvAt_beta_of_model_contractT (readbackLaws_whStepCK2 eqEnvT n)
    (D := .pi A B) (body := .app (.bvar 0) (.bvar 1)) (arg := eqGapPrefix)
    (fun _ _ h => approxTK_function_variable_beta_contract h)
    ((eqGapFundTyAt_approxTK_iff_typedCtorArity n).mpr hAr)

/-- The complete new related package is inhabited at bottom by every native
typed substitution into the Eq source context, for any compact typing law.
Both environment guards and their let-coherence components are retained. -/
theorem relSubstAtCov_eqGap_bot_diagonal (C : CovTyping eqEnvT)
    {σ : SubstT} (hT : TypedSubstT eqEnvT n Δ σ eqGapCtx) :
    RelSubstAtCov C (ctxModelT_approxTK eqEnvT n eqGapCtx)
      (WhStepCK2 eqEnvT n) n Δ EnvT.bot EnvT.bot σ σ eqGapCtx :=
  relSubstAtCov_bot_diagonal_of_no_values C hT
    (fun A => ApproxTK.bot eqGapCtx EnvT.bot A) lookupValue_eqGapCtx_none

/-- Replacing every recursive occurrence by the new relation and adding both
coherent environment guards leaves exactly the same native arity obligation.
This statement covers every `CovTyping`, including a proposed Cov2 extension. -/
theorem eqGapFundTyAtCov_approxTK_iff_typedCtorArity
    (C : CovTyping eqEnvT) (n : Nat) :
    FundTyAtCov C (ctxModelT_approxTK eqEnvT n eqGapCtx) (WhStepCK2 eqEnvT n)
      n eqGapCtx eqGapRedex (.sort (.succ .zero)) ↔ EqGapTypedCtorArity n := by
  constructor
  · intro hF Δ σ hΔ hT hc
    have hS := relSubstAtCov_eqGap_bot_diagonal C hT
    have hrel := hF hΔ hS .prop (Or.inl (approxTK_eqGap_prop n EnvT.bot))
    obtain ⟨_, u, _, hr, _⟩ := (lrSCoreCov_prop_iff C _ _ _ _).mp hrel
    rw [substT_eqGapRedex] at hr
    exact redR_gapCall_ctor_arity_native hc hr
  · intro hAr Δ ρ ρ' σ σ' hΔ hS c hc
    have hshape : c = .bot ∨ c = .prop := by
      rcases hc with hc | hc <;> exact eqGap_model_shape (approxTK_forget hc)
    rcases hshape with rfl | rfl
    · exact lrSCoreCov_bot C _ _ _ _
    · rw [lrSCoreCov_prop_iff]
      exact ⟨⟨.succ .zero, .refl _⟩, .zero, .zero,
        eqGap_subst_read_of_typedCtorArity hAr hΔ hS.typedL,
        eqGap_subst_read_of_typedCtorArity hAr hΔ hS.typedR⟩

/-- The complete old and new Eq target motives agree, without assuming any
agreement between their recursive typing gates away from this target. -/
theorem eqGapFundTyAtCov_approxTK_iff_old (C : CovTyping eqEnvT) (n : Nat) :
    FundTyAtCov C (ctxModelT_approxTK eqEnvT n eqGapCtx) (WhStepCK2 eqEnvT n)
      n eqGapCtx eqGapRedex (.sort (.succ .zero)) ↔
    FundTyAt (ctxModelT_approxTK eqEnvT n eqGapCtx) (WhStepCK2 eqEnvT n)
      n eqGapCtx eqGapRedex (.sort (.succ .zero)) :=
  (eqGapFundTyAtCov_approxTK_iff_typedCtorArity C n).trans
    (eqGapFundTyAt_approxTK_iff_typedCtorArity n).symm

/-- The new beta adapter receives the entire target motive exactly when the
native constructor-arity input is supplied.  It uses the generic adapter,
without reproducing either its substitution or its expansion proof. -/
theorem eqGapDirectAlias_fundConvAtCov_of_typedCtorArity
    (C : CovTyping eqEnvT) (hAr : EqGapTypedCtorArity n) (A B : Expr Nat) :
    FundConvAtCov C (ctxModelT_approxTK eqEnvT n eqGapCtx) (WhStepCK2 eqEnvT n)
      n eqGapCtx (eqGapDirectAlias A B) eqGapRedex (.sort (.succ .zero)) := by
  exact fundConvAtCov_beta_of_model_contract (C := C)
    (readbackLaws_whStepCK2 eqEnvT n)
    (D := .pi A B) (body := .app (.bvar 0) (.bvar 1)) (arg := eqGapPrefix)
    (fun _ _ h => approxTK_function_variable_beta_contract h)
    ((eqGapFundTyAtCov_approxTK_iff_typedCtorArity C n).mpr hAr)

/-- The full Cov beta-conversion conclusion has the same exact boundary:
its actual non-bottom right-hand observation recovers the native arity fact. -/
theorem eqGapDirectAlias_fundConvAtCov_iff_typedCtorArity
    (C : CovTyping eqEnvT) (n : Nat) (A B : Expr Nat) :
    FundConvAtCov C (ctxModelT_approxTK eqEnvT n eqGapCtx) (WhStepCK2 eqEnvT n)
      n eqGapCtx (eqGapDirectAlias A B) eqGapRedex (.sort (.succ .zero)) ↔
    EqGapTypedCtorArity n := by
  constructor
  · intro hF Δ σ hΔ hT hc
    have hS := relSubstAtCov_eqGap_bot_diagonal C hT
    have hrel := hF hΔ hS .prop (Or.inr (approxTK_eqGap_prop n EnvT.bot))
    obtain ⟨_, _, u, _, hr⟩ := (lrSCoreCov_prop_iff C _ _ _ _).mp hrel
    rw [substT_eqGapRedex] at hr
    exact redR_gapCall_ctor_arity_native hc hr
  · intro hAr
    exact eqGapDirectAlias_fundConvAtCov_of_typedCtorArity C hAr A B

/-- The constructor branch is positively inhabited by the landed native
canonical substitution.  The full new related package, the actual source
observation and the target relation coexist.  This is one substitution,
and does not assert the universal native constructor-arity condition. -/
theorem eqGapCanonical_cov_control (C : CovTyping eqEnvT) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n []) ∧
    TypedSubstT eqEnvT n [] gapCanonicalSubst eqGapCtx ∧
    RelSubstAtCov C (ctxModelT_approxTK eqEnvT n eqGapCtx)
      (WhStepCK2 eqEnvT n) n [] EnvT.bot EnvT.bot
      gapCanonicalSubst gapCanonicalSubst eqGapCtx ∧
    IsCtorSpine eqEnvT (gapCanonicalSubst 0) ∧
    (appsSpine (gapCanonicalSubst 0)).2.length = 2 ∧
    ApproxTK eqEnvT n eqGapCtx EnvT.bot eqGapRedex .prop ∧
    LRSCoreCov C (WhStepCK2 eqEnvT n) n []
      (substT gapCanonicalSubst eqGapRedex) (substT gapCanonicalSubst eqGapRedex)
      (.sort (.succ .zero)) .prop ∧ CptT.prop ≠ .bot := by
  obtain ⟨hW, hΓ, hT, _, hc, hlen⟩ := gapCanonical_control (WhStepCK2 eqEnvT n) n
  refine ⟨hW, hΓ, hT, relSubstAtCov_eqGap_bot_diagonal C hT, hc, hlen,
    approxTK_eqGap_prop n EnvT.bot, ?_, fun h => CptT.noConfusion h⟩
  rw [lrSCoreCov_prop_iff]
  exact ⟨⟨.succ .zero, .refl _⟩, .zero, .zero,
    (gapCanonical_readbacks n).1, (gapCanonical_readbacks n).1⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_REL_EQ_GAP_ROOTS
#print axioms eqGap_subst_read_of_typedCtorArity
#print axioms eqGapFundTyAt_approxTK_iff_typedCtorArity
#print axioms not_eqGapFundTyAt_approxTK_of_typed_badarity
#print axioms eqGapDirectAlias_fundConvAt_of_typedCtorArity
#print axioms relSubstAtCov_eqGap_bot_diagonal
#print axioms eqGapFundTyAtCov_approxTK_iff_typedCtorArity
#print axioms eqGapFundTyAtCov_approxTK_iff_old
#print axioms eqGapDirectAlias_fundConvAtCov_of_typedCtorArity
#print axioms eqGapDirectAlias_fundConvAtCov_iff_typedCtorArity
#print axioms eqGapCanonical_cov_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_REL_EQ_GAP_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit

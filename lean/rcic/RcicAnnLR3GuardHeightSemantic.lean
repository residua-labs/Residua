import rcic.RcicAnnLR3GuardHeightBoundary

/-!
# Inhabited LR3 heights for the nested-irrelevance K guard

The outer call and its minor are interpreted in the actual LR3 tower.
The minor is `Pi (Sort 0) (Sort 0)`, whose domain and codomain use the
height-free proposition-sort clause; equality of those sort carriers is
available at height 1. The supplied K reduction transports these explicit
Pi constructors to the call.

The final witness therefore has a real `LRRelA3` at `Sort 1`, ambient
height 2, and applies the preceding carrier-demand theorem to it. The
non-decreasing guard-carrier comparison is not conditioned on an absent
semantic environment or an uninhabited logical-relation premise. As in
the preceding module, this is a carrier-height boundary; it does not show
that the minimal proposition-key coherence request itself has that height.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3.GuardHeightBoundary

open Rcic.Declarative EqLargeFixture

private abbrev H : HeadLayerA3 env (iotaIfaceA env) 0 :=
  contextualHeadLayerA3 env (iotaIfaceA env) 0

private def propRel (Γ : LCtxA) (a b : ExprA) : Prop :=
  PropValidA3 env (iotaIfaceA env) 0 H Γ a ∧
  PropValidA3 env (iotaIfaceA env) 0 H Γ b ∧
  Nonempty (HasTyA env (iotaIfaceA env) 0 Γ a (.sort .zero)) ∧
  Nonempty (HasTyA env (iotaIfaceA env) 0 Γ b (.sort .zero)) ∧
  Nonempty (ConvA env (iotaIfaceA env) 0 Γ a b (.sort .zero)) ∧
  PropEqA3 env (iotaIfaceA env) 0 H Γ a b

private theorem resultNotProp (Γ : LCtxA) : ¬ IsPropTyA3 env (iotaIfaceA env) 0 H Γ result := by
  intro hp
  have hz := (isPropTyA3_pi_iff env (iotaIfaceA env) 0 H Γ
    (.sort .zero) one (.sort .zero) one).1 hp
  exact Bool.noConfusion hz

private theorem resultValidFromWhTy (ρ₀ : Nat → Nat) {Γ : LCtxA} {A : ExprA}
    (hA : WhTyA3 env (iotaIfaceA env) 0 H Γ A result) :
    ∃ R, LRTyA3 env (iotaIfaceA env) 0 H ρ₀ 1 Γ A R := by
  let R : ExprA → ExprA → Prop := fun f g =>
    (∀ ρ : WkSpecA, WkOkA env (iotaIfaceA env) 0 ρ Γ →
      ∀ a a' : ExprA, propRel (wkCtxA ρ Γ) a a' →
        propRel (wkCtxA ρ Γ) (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 Γ f result) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 Γ g result) ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 Γ f g result)
  refine ⟨R, ?_⟩
  rw [LRTyA3_eq]
  refine TyKA3.pi (D := .sort .zero) (u := one) (C := .sort .zero) (v := one)
    hA (resultNotProp Γ) ⟨.sort _ .zero⟩ ⟨.sort _ .zero⟩
    (fun ρ => propRel (wkCtxA ρ Γ)) ?_
    (fun ρ _ => propRel (wkCtxA ρ Γ)) ?_ ?_
  · intro ρ _
    simp only [wkExprA_sort]
    exact .sortP (whTyA3_sort _ .zero) rfl
  · intro ρ _ a b _
    simp only [wkExprA_sort]
    exact .sortP (whTyA3_sort _ .zero) rfl
  · intro ρ _ a b _
    simp only [wkExprA_sort]
    exact .sort (whTyA3_sort _ .zero) (whTyA3_sort _ .zero)
      (by change 0 < 1; exact Nat.zero_lt_succ 0) (eqNA_refl _) ⟨.refl _ _⟩

/-- The actual minor's type interpretation at the lower height 1. -/
theorem resultTypeAtOne (ρ₀ : Nat → Nat) (Γ : LCtxA) :
    ∃ R, LRTyA3 env (iotaIfaceA env) 0 H ρ₀ 1 Γ result R :=
  resultValidFromWhTy ρ₀
    (whTyA3_of_hasTy resultTyped (LR3EqHead.resultNormal Γ))

/-- The actual outer K call has its own type interpretation at height 1. -/
theorem outerTypeAtOne (ρ₀ : Nat → Nat) :
    ∃ R, LRTyA3 env (iotaIfaceA env) 0 H ρ₀ 1 context outerShape.source R :=
  resultValidFromWhTy ρ₀ outerWhTy

/-- The call and minor are equal as types at the same height, with all
Pi-domain, codomain and world premises supplied directly. -/
theorem outerEqAtOne (ρ₀ : Nat → Nat) :
    LREqA3 env (iotaIfaceA env) 0 H ρ₀ 1 context outerShape.source result := by
  obtain ⟨hc⟩ := outerHeadSort.conv closed liftIface (iotaFnA_recHead env) substIface contextWf
  obtain ⟨ht⟩ := outerCallTyped
  have htc : Nonempty (TyConvA env (iotaIfaceA env) 0 context outerShape.source result) :=
    ⟨.of context _ _ one one one ht (eqNA_refl _) resultTyped (eqNA_refl _) hc⟩
  rw [LREqA3_eq]
  refine EqKA3.pi (D := .sort .zero) (u := one) (C := .sort .zero) (v := one)
    (D' := .sort .zero) (u' := one) (C' := .sort .zero) (v' := one)
    outerWhTy (whTyA3_of_hasTy resultTyped (LR3EqHead.resultNormal context))
    (eqNA_refl _) (eqNA_refl _) ⟨.sort _ .zero⟩ ⟨.sort _ .zero⟩
    ⟨.sort _ .zero⟩ ⟨.sort _ .zero⟩ (fun ρ => propRel (wkCtxA ρ context))
    ?_ ?_ ?_ htc
  · intro ρ _
    simp only [wkExprA_sort]
    exact .sortP (whTyA3_sort _ .zero) rfl
  · intro ρ _
    simp only [wkExprA_sort]
    exact .sort (whTyA3_sort _ .zero) (whTyA3_sort _ .zero)
      (by change 0 < 1; exact Nat.zero_lt_succ 0) (eqNA_refl _) ⟨.refl _ _⟩
  · intro ρ _ a b _
    simp only [wkExprA_sort]
    exact .sort (whTyA3_sort _ .zero) (whTyA3_sort _ .zero)
      (by change 0 < 1; exact Nat.zero_lt_succ 0) (eqNA_refl _) ⟨.refl _ _⟩

/-- Actual term relatedness at the motive's `Sort 1`, ambient height 2. -/
theorem outerRelatedAtTwo (ρ₀ : Nat → Nat) :
    LRRelA3 env (iotaIfaceA env) 0 H ρ₀ 2 context (.sort one) outerShape.source result := by
  obtain ⟨hc⟩ := outerHeadSort.conv closed liftIface (iotaFnA_recHead env) substIface contextWf
  let R : ExprA → ExprA → Prop := fun a b =>
    LREqA3 env (iotaIfaceA env) 0 H ρ₀ 1 context a b ∧
    (∃ S, LRTyA3 env (iotaIfaceA env) 0 H ρ₀ 1 context a S) ∧
    (∃ S, LRTyA3 env (iotaIfaceA env) 0 H ρ₀ 1 context b S) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context a (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context b (.sort one)) ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 context a b (.sort one))
  refine ⟨R, ?_, outerEqAtOne ρ₀, outerTypeAtOne ρ₀, resultTypeAtOne ρ₀ context,
    outerCallTyped, ⟨resultTyped⟩, ⟨hc⟩⟩
  rw [LRTyA3_eq]
  exact .sortT (whTyA3_sort context one) rfl (by change 1 < 2; decide)

/-- Both the guard and the relevant semantic height are inhabited. The
lower interpretation is extracted from the supplied LR term relation. -/
theorem inhabited_semantic_guard_height_boundary (ρ₀ : Nat → Nat) :
    eraseEnv env = eqEnvT ∧ Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 context) ∧
    Nonempty (SubstTyA env (iotaIfaceA env) 0 [] closeContext context) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context (.sort .zero) (.sort one)) ∧
    (∃ hg : ConvA env (iotaIfaceA env) 0 context parameter actualIndex (.sort .zero),
      UsesEqCarrierIrr (.sort .zero) hg ∧
      Nonempty (KStage.Frame env (iotaIfaceA env) 0 context outerShape)) ∧
    outerShape.declaredIndices ≠ outerShape.actualIndices ∧
    hStepFnA env (iotaIfaceA env).fn context outerShape.source = none ∧
    HeadA3 env (iotaIfaceA env) 0 context outerShape.source result (.sort one) ∧
    LRRelA3 env (iotaIfaceA env) 0 H ρ₀ 2 context (.sort one) outerShape.source result ∧
    (∃ R, LRTyA3 env (iotaIfaceA env) 0 H ρ₀ 1 context outerShape.source R) ∧
    (∃ R, LRTyA3 env (iotaIfaceA env) 0 H ρ₀ 1 context result R) ∧
    ht ρ₀ one = 1 ∧ ¬ ht ρ₀ one < 1 :=
  ⟨erase_env, wf, ⟨contextWf⟩, ⟨contextClosingTyped⟩, ⟨.sort context .zero⟩,
    frameWithGuardIrr, indicesDiffer, outerOldHeadNone, outerHeadSort,
    outerRelatedAtTwo ρ₀, sortOneCarrierDemand (outerRelatedAtTwo ρ₀),
    resultTypeAtOne ρ₀ context, rfl, Nat.lt_irrefl 1⟩

#print axioms resultTypeAtOne
#print axioms outerTypeAtOne
#print axioms outerEqAtOne
#print axioms outerRelatedAtTwo
#print axioms inhabited_semantic_guard_height_boundary

end Rcic.Declarative.Ann.LR3.GuardHeightBoundary

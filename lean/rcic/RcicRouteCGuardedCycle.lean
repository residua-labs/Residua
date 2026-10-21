import rcic.RcicSynInst

set_option autoImplicit false

/-!
# Route C: a diagnostic for unilateral coinductive unfolding

This module tests one precisely stated operator. Its recursive clauses may
unfold either side and immediately reuse the candidate relation. A finite
positive cycle therefore relates its source to every term. The existing
erased `loopRule`, applied to an identity minor, supplies such a cycle:
one constant-rule unfolding and three beta steps. Its table is already
proved well-formed, and its two distinct sorts are already proved not
finitely convertible.

The consequences concern this operator: it is not transitive and cannot
soundly imply the landed finite `ConvMod`. They do not refute an unspecified
productive typed design. In particular, a finite conversion between the
compared endpoints is different from a finite receipt for each unfolding.
No native or annotated typing of `loopInput` is claimed here. No reduction
rule, erasure function, annotated semantics, or observation model is changed.
`closure_claim = 0`.
-/

namespace Rcic.Syn.RouteCGuardedCycle

/-! ## The operator under test -/

/-- A structural base case, or one unilateral step before a recursive call.
There is no visible-head progress condition and no cross-endpoint conversion
premise in this particular diagnostic operator. -/
def UnilateralF {α : Type} (R Q S : α → α → Prop) (a b : α) : Prop :=
  Q a b ∨ (∃ a', R a a' ∧ S a' b) ∨ (∃ b', R b b' ∧ S a b')

/-- The union of all postfixed relations for `UnilateralF`, expressed by an
explicit relation witness. No choice or coinductive axiom is used. -/
def Unilateral {α : Type} (R Q : α → α → Prop) (a b : α) : Prop :=
  ∃ S : α → α → Prop, S a b ∧ ∀ x y, S x y → UnilateralF R Q S x y

/-- Each witnessed postfixed relation unfolds into the same union. -/
theorem unilateral_unfold {α : Type} {R Q : α → α → Prop} {a b : α}
    (h : Unilateral R Q a b) : UnilateralF R Q (Unilateral R Q) a b := by
  obtain ⟨S, hab, hS⟩ := h
  rcases hS a b hab with hq | ⟨a', ha, hab'⟩ | ⟨b', hb, hab'⟩
  · exact Or.inl hq
  · exact Or.inr (Or.inl ⟨a', ha, ⟨S, hab', hS⟩⟩)
  · exact Or.inr (Or.inr ⟨b', hb, ⟨S, hab', hS⟩⟩)

/-- A positive cycle suffices for comparison with an arbitrary right side.
The witness consists of all left terms with a finite path back to `a`.
At `a` itself, the supplied first step makes the recursive clause fire. -/
theorem unilateral_of_positive_cycle {α : Type} {R Q : α → α → Prop}
    {a z : α} (hstep : R a z) (hback : RStar R z a) (b : α) :
    Unilateral R Q a b := by
  refine ⟨fun x y => y = b ∧ RStar R x a, ⟨rfl, .refl a⟩, ?_⟩
  intro x y hxy
  obtain ⟨rfl, hpath⟩ := hxy
  cases hpath with
  | refl => exact Or.inr (Or.inl ⟨z, hstep, rfl, hback⟩)
  | step hs ht => exact Or.inr (Or.inl ⟨_, hs, rfl, ht⟩)

/-- Reversing the postfixed witness exchanges the two unfolding clauses. -/
theorem unilateral_symm {α : Type} {R Q : α → α → Prop}
    (hQ : ∀ {a b : α}, Q a b → Q b a) {a b : α}
    (h : Unilateral R Q a b) : Unilateral R Q b a := by
  obtain ⟨S, hab, hS⟩ := h
  refine ⟨fun x y => S y x, hab, ?_⟩
  intro x y hyx
  rcases hS y x hyx with hq | ⟨y', hy, hyx'⟩ | ⟨x', hx, hyx'⟩
  · exact Or.inl (hQ hq)
  · exact Or.inr (Or.inr ⟨y', hy, hyx'⟩)
  · exact Or.inr (Or.inl ⟨x', hx, hyx'⟩)

/-- At two normal endpoints the diagnostic has only its structural case. -/
theorem unilateral_normal_iff {α : Type} {R Q : α → α → Prop} {a b : α}
    (ha : ∀ a', ¬ R a a') (hb : ∀ b', ¬ R b b') :
    Unilateral R Q a b ↔ Q a b := by
  constructor
  · intro h
    rcases unilateral_unfold h with hq | ⟨a', hs, _⟩ | ⟨b', hs, _⟩
    · exact hq
    · exact (ha a' hs).elim
    · exact (hb b' hs).elim
  · intro hq
    exact ⟨Q, hq, fun _ _ h => Or.inl h⟩

/-! ## A concrete cycle in the landed erased relation -/

/-- The erased minor returns its induction-hypothesis argument. -/
def loopIdentity : ETm := .lam (.bvar 0)

/-- `rec (sort 0) (fun ih => ih)` for the existing head-7 Loop rule.
This is an erased syntax fixture, with no native typing claim. -/
def loopInput : ETm := .app (.app (.const 7 []) (.sort .zero)) loopIdentity

private def loopUnfold : ETm :=
  .app (.app (loopRule.rhs [] []) (.sort .zero)) loopIdentity

private def loopAfterMotive : ETm :=
  .app (.lam (.app (.bvar 0)
    (.app (.app (.const 7 []) (.sort .zero)) (.bvar 0)))) loopIdentity

private def loopAfterMinor : ETm := .app loopIdentity loopInput

/-- The guard is genuinely exercised: one constant step and exactly three
beta steps return to the same source. All intermediate terms are supplied. -/
theorem loop_identity_cycle :
    ∃ b c d, CStep [loopRule] loopInput b ∧ BetaStep b c ∧
      BetaStep c d ∧ BetaStep d loopInput := by
  refine ⟨loopUnfold, loopAfterMotive, loopAfterMinor, ?_, ?_, ?_, ?_⟩
  · exact .appL loopIdentity (.appL (.sort .zero)
      (.cr (.bare (List.mem_singleton_self loopRule) rfl [] [] rfl)))
  · exact .appL loopIdentity (.beta _ _)
  · exact .beta _ _
  · exact .beta _ _

/-- The explicit constant/beta cycle is a positive cycle of the unchanged
`EStep [loopRule]`, using the landed embeddings of its two subrelations. -/
theorem loop_positive_cycle :
    ∃ b, EStep [loopRule] loopInput b ∧
      RStar (EStep [loopRule]) b loopInput := by
  obtain ⟨b, c, d, hc, hb₁, hb₂, hb₃⟩ := loop_identity_cycle
  exact ⟨b, Or.inl (rStep_of_cStep hc),
    .step (Or.inl (rStep_of_betaStep hb₁))
      (.step (Or.inl (rStep_of_betaStep hb₂))
        (.single (Or.inl (rStep_of_betaStep hb₃))))⟩

/-- The table premise and the positive-cycle premise are both inhabited. -/
theorem loop_table_and_cycle :
    TableWF [loopRule] ∧ ∃ b, EStep [loopRule] loopInput b ∧
      RStar (EStep [loopRule]) b loopInput :=
  ⟨loopTable_wf, loop_positive_cycle⟩

/-- Unilateral coinductive unfolding relates this one cycle to every term. -/
theorem loop_relates_every (t : ETm) :
    Unilateral (EStep [loopRule]) LvlEq loopInput t := by
  obtain ⟨b, hstep, hback⟩ := loop_positive_cycle
  exact unilateral_of_positive_cycle hstep hback t

/-- The same operator still refuses two distinct normal sorts. -/
theorem loop_sorts_not_related :
    ¬ Unilateral (EStep [loopRule]) LvlEq
      (.sort .zero) (.sort (.succ .zero)) := by
  intro h
  have hq : LvlEq (.sort .zero) (.sort (.succ .zero)) :=
    (unilateral_normal_iff (eStep_sort_normal [loopRule] .zero)
      (eStep_sort_normal [loopRule] (.succ .zero))).mp h
  exact loop_not_convE_sort_zero_one (.eqv hq)

/-- The cycle is a common related term for the two normal sorts, so the
diagnostic cannot serve as a transitive equality relation. -/
theorem loop_unilateral_not_transitive :
    ¬ (∀ {a b c : ETm},
      Unilateral (EStep [loopRule]) LvlEq a b →
      Unilateral (EStep [loopRule]) LvlEq b c →
      Unilateral (EStep [loopRule]) LvlEq a c) := by
  intro ht
  have h₀ : Unilateral (EStep [loopRule]) LvlEq (.sort .zero) loopInput :=
    unilateral_symm LvlEq.symm' (loop_relates_every (.sort .zero))
  have h₁ := loop_relates_every (.sort (.succ .zero))
  exact loop_sorts_not_related (ht h₀ h₁)

/-- No universal promotion of this diagnostic to the landed finite
conversion relation exists, even for the actual well-formed Loop table.
The contradiction uses only the two inhabited cycle comparisons and the
already checked sort-separation theorem. -/
theorem loop_unilateral_not_finite_conversion_sound :
    TableWF [loopRule] ∧
      ¬ (∀ a b, Unilateral (EStep [loopRule]) LvlEq a b →
        ConvMod (EStep [loopRule]) LvlEq a b) := by
  refine ⟨loopTable_wf, ?_⟩
  intro hs
  have h₀ := hs loopInput (.sort .zero) (loop_relates_every (.sort .zero))
  have h₁ := hs loopInput (.sort (.succ .zero))
    (loop_relates_every (.sort (.succ .zero)))
  exact loop_not_convE_sort_zero_one
    (.trans (ConvMod.symm' LvlEq.symm' h₀) h₁)

-- BEGIN RCIC_ROUTE_C_GUARDED_CYCLE_ROOTS
#print axioms UnilateralF
#print axioms Unilateral
#print axioms unilateral_unfold
#print axioms unilateral_of_positive_cycle
#print axioms unilateral_symm
#print axioms unilateral_normal_iff
#print axioms loopIdentity
#print axioms loopInput
#print axioms loop_identity_cycle
#print axioms loop_positive_cycle
#print axioms loop_table_and_cycle
#print axioms loop_relates_every
#print axioms loop_sorts_not_related
#print axioms loop_unilateral_not_transitive
#print axioms loop_unilateral_not_finite_conversion_sound
-- END RCIC_ROUTE_C_GUARDED_CYCLE_ROOTS

end Rcic.Syn.RouteCGuardedCycle

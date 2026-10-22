import rcic.RcicAnnLR3Core

/-!
# The positive normal-form demand of LR3

The recursor environment contract asks for semantic relatedness, not directly
for normality. Nevertheless, the landed tower requires finite, positively
terminal reduction when a related term is itself a type (a term of a sort),
and the family fixed point requires such reduction of its inhabitants.

These are necessary consequences of the existing clauses, not an environment
supplier or an impossibility theorem. They isolate the exact D1 demand without
changing the tower, deciding conversion, or producing semantic apartness.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

/-- Every type-validity constructor carries a positive terminal type chain. -/
theorem tyKA3_normalDemand {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {H : HeadLayerA3 E I n} {ρ₀ : Nat → Nat} {k : Nat}
    {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA} {A : ExprA}
    {R : ExprA → ExprA → Prop}
    (h : TyKA3 E I n H ρ₀ k LE LT Γ A R) :
    ∃ N, WhTyA3 E I n H Γ A N := by
  cases h <;> exact ⟨_, by assumption⟩

/-- Tying the height knot does not remove the terminal-chain demand. -/
theorem lrTyA3_normalDemand {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {H : HeadLayerA3 E I n} {ρ₀ : Nat → Nat} {k : Nat}
    {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : LRTyA3 E I n H ρ₀ k Γ A R) :
    ∃ N, WhTyA3 E I n H Γ A N := by
  rw [LRTyA3_eq] at h
  exact tyKA3_normalDemand h

/-- Related terms of any sort have positive normal forms on both sides.
This includes the Type-sort case relevant to large elimination. -/
theorem lrRelA3_sort_normalDemand {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {H : HeadLayerA3 E I n} {ρ₀ : Nat → Nat} {k : Nat}
    {Γ : LCtxA} {l : Level} {a b : ExprA}
    (h : LRRelA3 E I n H ρ₀ k Γ (.sort l) a b) :
    (∃ N, WhTyA3 E I n H Γ a N) ∧ (∃ N', WhTyA3 E I n H Γ b N') := by
  obtain ⟨R, hR, hab⟩ := h
  rw [LRTyA3_eq] at hR
  have hS : WhTyA3 E I n H Γ (.sort l) (.sort l) := whTyA3_sort Γ l
  cases hR with
  | prop hA _ hP =>
      have he := whTyA3_det hA hS
      subst he
      exact absurd hP (not_isPropTyA3_sort E I n H Γ l)
  | sortT _ _ _ =>
      obtain ⟨Ra, ha⟩ := hab.2.1
      obtain ⟨Rb, hb⟩ := hab.2.2.1
      exact ⟨lrTyA3_normalDemand ha, lrTyA3_normalDemand hb⟩
  | sortP _ _ =>
      obtain ⟨N, ha, _⟩ := hab.1
      obtain ⟨N', hb, _⟩ := hab.2.1
      exact ⟨⟨N, ha⟩, ⟨N', hb⟩⟩
  | pi hA _ _ _ _ _ _ _ _ =>
      have he := whTyA3_det hA hS
      cases he
  | fam hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      have he := whTyA3_det hA hS
      exact absurd he (foldAppsA_const_ne_sort _ _ _ _)
  | stuck hA hN =>
      have he := whTyA3_det hA hS
      subst he
      exact (hN.2 (by trivial)).elim

/-- Inspecting the first constructor of an inhabited terminal chain supplies
positive normality or a typed head step. This uses no step-or-normal decision. -/
theorem whTyA3_headDemand {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {H : HeadLayerA3 E I n} {Γ : LCtxA} {A N : ExprA}
    (h : WhTyA3 E I n H Γ A N) :
    H.normal Γ A ∨ ∃ (u : Level) (A' : ExprA), H.step Γ A A' (.sort u) := by
  obtain ⟨⟨t⟩, hN⟩ := h
  cases t
  · exact Or.inl hN
  · exact Or.inr ⟨_, _, by assumption⟩

/-- A semantic relation at a sort supplies this positive head alternative for
both endpoints. It does not manufacture that alternative from typing alone. -/
theorem lrRelA3_sort_headDemand {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {H : HeadLayerA3 E I n} {ρ₀ : Nat → Nat} {k : Nat}
    {Γ : LCtxA} {l : Level} {a b : ExprA}
    (h : LRRelA3 E I n H ρ₀ k Γ (.sort l) a b) :
    (H.normal Γ a ∨ ∃ (u : Level) (a' : ExprA), H.step Γ a a' (.sort u)) ∧
    (H.normal Γ b ∨ ∃ (u : Level) (b' : ExprA), H.step Γ b b' (.sort u)) := by
  obtain ⟨⟨N, ha⟩, ⟨N', hb⟩⟩ := lrRelA3_sort_normalDemand h
  exact ⟨whTyA3_headDemand ha, whTyA3_headDemand hb⟩

/-- The family fixed point also consumes positive terminal term chains.
Neither its constructor case nor its neutral case bypasses this demand. -/
theorem lfpWA_famPhiWParamA_normal_left3
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {red : LCtxA → ExprA → ExprA → ExprA → Prop} {normal : LCtxA → ExprA → Prop}
    {Γ : LCtxA} {r : Nat} {m : CheckedMemberA}
    {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsI : InnerRelsA} {ρ : WkSpecA} {A a b : ExprA}
    (h : LfpWA (FamPhiWParamA3 E I n red normal Γ r m Rs RsI) ρ A a b) :
    ∃ N, red (wkCtxA ρ Γ) a N A ∧ normal (wkCtxA ρ Γ) N := by
  have hu := LfpWA.unfold famPhiWParamA_mono3 h
  rcases hu.2 with
    ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', h1, h2, h3,
      h4, h4', h5, hT, hT', h6, hp₁, hp₂, h7, h8, hn, hn', h9⟩ | hst
  · exact ⟨_, h7, hn⟩
  · obtain ⟨N, N', ha, hb, hn, hn'⟩ := hst
    exact ⟨N, ha, hn.1⟩

/-- Concrete family relation: a finite LR3 term chain to a positive endpoint. -/
theorem lfpWA_famPhiWA3_normal_left
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    {Γ : LCtxA} {r : Nat} {m : CheckedMemberA}
    {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsI : InnerRelsA} {ρ : WkSpecA} {A a b : ExprA}
    (h : LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ A a b) :
    ∃ N, TyHRedStarA3 E I n H (wkCtxA ρ Γ) a N A ∧ H.normal (wkCtxA ρ Γ) N :=
  lfpWA_famPhiWParamA_normal_left3 h

#print axioms tyKA3_normalDemand
#print axioms lrTyA3_normalDemand
#print axioms lrRelA3_sort_normalDemand
#print axioms whTyA3_headDemand
#print axioms lrRelA3_sort_headDemand
#print axioms lfpWA_famPhiWParamA_normal_left3
#print axioms lfpWA_famPhiWA3_normal_left

end Rcic.Declarative.Ann.LR3

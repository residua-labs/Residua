import rcic.RcicAnnLR3NoneUniverseBoundary

/-!
# The exact finite-valuation boundary for admitted source sorts

The paired source statements quantify over all Option-valued valuations.
Agreement of the two valuations does not require them to be defined on
the source level parameters. The existing admitted sort at parameter zero
is a concrete witness, even with explicit level bounds on both its subject
and its type.

Definedness on the first n parameters is sufficient and necessary for
every n-bounded level to evaluate to a finite natural. That premise is
stated explicitly here; it is not silently added to PairedTyGoal or eqN.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.OptionAdmittedLevels

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements

/-- Exactly the additional valuation condition needed for all bounded
levels to be finite. Values outside the bound remain unrestricted. -/
def FiniteOn (n : Nat) (ν : Valuation) : Prop :=
  ∀ i : Nat, i < n → ∃ k : Nat, ν i = some k

theorem eval_finite_of_bounded {n : Nat} {ν : Valuation}
    (hν : FiniteOn n ν) (l : Level) (hl : levelBounded n l = true) :
    ∃ k : Nat, eval ν l = some k := by
  induction l with
  | zero => exact ⟨0, rfl⟩
  | succ l ih =>
    obtain ⟨k, hk⟩ := ih hl
    exact ⟨k + 1, by simp [eval, hk]⟩
  | max a b iha ihb =>
    have hs : levelBounded n a = true ∧ levelBounded n b = true :=
      by
        change (levelBounded n a && levelBounded n b) = true at hl
        cases ha : levelBounded n a <;> cases hb : levelBounded n b <;> simp_all
    obtain ⟨x, hx⟩ := iha hs.1
    obtain ⟨y, hy⟩ := ihb hs.2
    exact ⟨max x y, by simp [eval, hx, hy]⟩
  | imax a b iha ihb =>
    have hs : levelBounded n a = true ∧ levelBounded n b = true :=
      by
        change (levelBounded n a && levelBounded n b) = true at hl
        cases ha : levelBounded n a <;> cases hb : levelBounded n b <;> simp_all
    obtain ⟨x, hx⟩ := iha hs.1
    obtain ⟨y, hy⟩ := ihb hs.2
    by_cases hz : y = 0
    · exact ⟨0, by simp [eval, hx, hy, hz]⟩
    · exact ⟨max x y, by simp [eval, hx, hy, hz]⟩
  | param i => exact hν i (of_decide_eq_true hl)

theorem finiteOn_iff_bounded_levels_finite (n : Nat) (ν : Valuation) :
    FiniteOn n ν ↔
      ∀ l : Level, levelBounded n l = true → ∃ k : Nat, eval ν l = some k := by
  constructor
  · exact eval_finite_of_bounded
  · intro h i hi
    exact h (.param i) (decide_eq_true hi)

theorem noneValuation_not_finiteOn :
    ¬ FiniteOn 1 UniverseDecoderBoundary.noneValuation := by
  intro h
  obtain ⟨k, hk⟩ := h 0 (by decide)
  cases hk

/-- All original admission premises are supplied. Boundedness of source
levels is also supplied, so an unbound parameter is not the explanation. -/
theorem admitted_none_packet (M : AnnSemantics) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 1 []) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 1 []
      UniverseDecoderBoundary.noneSort (.sort (.succ (.param 0)))) ∧
    exprLevelsBoundedA 1 UniverseDecoderBoundary.noneSort = true ∧
    exprLevelsBoundedA 1 (.sort (.succ (.param 0))) = true ∧
    ValuationRel UniverseDecoderBoundary.noneValuation
      UniverseDecoderBoundary.noneValuation ∧
    PairedRealises M UniverseDecoderBoundary.noneValuation
      UniverseDecoderBoundary.noneValuation [] EnvI.bot EnvI.bot ∧
    eval UniverseDecoderBoundary.noneValuation (.param 0) = none ∧
    eval UniverseDecoderBoundary.noneValuation (.succ (.param 0)) = none ∧
    ¬ (∃ k : Nat,
      eval UniverseDecoderBoundary.noneValuation (.succ (.param 0)) = some k) := by
  refine ⟨⟨UniverseDecoderBoundary.source_admitted⟩, ⟨.nil⟩,
    ⟨UniverseDecoderBoundary.source_none_sort⟩, rfl, rfl,
    ValuationRel.refl _, .nil _ _, rfl, rfl, ?_⟩
  rintro ⟨k, hk⟩
  cases hk

/-- A proposed replacement of Option levels by Nat would need this even
on bounded admitted source sorts. It has an explicit counterexample for
every semantic model, since the empty paired context has no hypotheses. -/
def AllAdmittedSortLevelsFinite (M : AnnSemantics) : Prop :=
  ∀ E : ResolvedEnvA, EnvWfA (iotaIfaceA E) E →
    ∀ (n : Nat) (Γ : LCtxA) (A : ExprA) (u : Level),
      CtxWfA E (iotaIfaceA E) n Γ →
      HasTyA E (iotaIfaceA E) n Γ A (.sort u) →
      exprLevelsBoundedA n A = true → levelBounded n u = true →
      ∀ (ν μ : Valuation) (ρ σ : EnvI), ValuationRel ν μ →
        PairedRealises M ν μ Γ ρ σ → ∃ k : Nat, eval ν u = some k

theorem not_all_admitted_sort_levels_finite (M : AnnSemantics) :
    ¬ AllAdmittedSortLevelsFinite M := by
  intro h
  obtain ⟨k, hk⟩ := h emptyEnvA UniverseDecoderBoundary.source_admitted
    1 [] UniverseDecoderBoundary.noneSort (.succ (.param 0))
    .nil UniverseDecoderBoundary.source_none_sort rfl rfl
    UniverseDecoderBoundary.noneValuation UniverseDecoderBoundary.noneValuation
    EnvI.bot EnvI.bot (ValuationRel.refl _) (.nil _ _)
  cases hk

end Rcic.Declarative.Ann.LR3.OptionAdmittedLevels

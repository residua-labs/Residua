import rcic.RcicAnnLR3EnvironmentEvalComposition
import rcic.RcicAnnLR3InductiveCodes

/-!
# The environment-aware evaluator's actual dependent-product image

Finite native observations of the domain and codomain are aligned by the
proved finite-translation join theorem. The resulting exact value shape is
the product value already consumed by CodeI. This is an evaluator law, not
a universe construction or a source Ty_pi supplier. `closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.EnvironmentEval

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER

/-- The new evaluator produces the same native dependent-product value
shape used by CodeI, with its own actual domain image and body closure. -/
theorem denote_pi_value (E : ResolvedEnvA) (F : FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (A B : ExprA) (u v : Level) :
    ValueEq (denote E F ν ρ (.pi A u B v))
      (InductiveCodes.piValue (InductiveCodes.imaxLevel (eval ν u) (eval ν v))
        (denote E F ν ρ A) (denote E F ν ρ (.lam A u B))) := by
  rw [InductiveCodes.imaxLevel_eval]
  intro c
  constructor
  · rintro ⟨t, ht, hc⟩
    cases ht with
    | cut => exact Or.inl (cutTerm_only_bottom hc)
    | @pi _ _ _ _ A' B' hA hB =>
        have hp := (InductiveCodes.taggedValue_denI ρ (eval ν (.imax u v)) (.pi A' B') c).mpr hc
        rcases hp with hc | ⟨a, p, hc, ha, hp⟩
        · exact Or.inl hc
        · refine Or.inr ⟨a, p, hc, ha, ?_⟩
          rcases approxI_pi_inv hp with hp | ⟨a', g, hp, harg, hbody⟩
          · exact Or.inl hp
          · refine Or.inr ⟨a', g, hp, ⟨A', hA, harg⟩, ?_⟩
            intro s hs
            exact (denote_lambda_application E F ν ρ A B u (demand s.1) s.2).mpr
              ⟨B', hB, hbody s hs⟩
  · intro hc
    rcases hc with hc | ⟨a, p, hc, ha, hp⟩
    · cases hc
      exact denote_bot E F ν ρ _
    · rcases hp with hp | ⟨a', g, hp, hA, hg⟩
      · refine ⟨taggedTerm (eval ν (.imax u v)) (.pi cutTerm cutTerm),
          .pi (.cut A) (.cut B), ?_⟩
        apply (InductiveCodes.taggedValue_denI ρ (eval ν (.imax u v))
          (.pi cutTerm cutTerm) c).mp
        refine Or.inr ⟨a, p, hc, ha, ?_⟩
        cases hp
        exact .bot _ _
      · obtain ⟨A', htA, hA'⟩ := hA
        let observations : List (EnvI × CptI) :=
          g.map (fun s => (EnvI.cons (demand s.1) ρ, s.2))
        have hobs : ∀ q ∈ observations, denote E F ν q.1 B q.2 := by
          intro q hq
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
          exact (denote_lambda_application E F ν ρ A B u (demand s.1) s.2).mp (hg s hs)
        obtain ⟨B', htB, hB'⟩ := finite_observations observations hobs
        refine ⟨taggedTerm (eval ν (.imax u v)) (.pi A' B'), .pi htA htB, ?_⟩
        apply (InductiveCodes.taggedValue_denI ρ (eval ν (.imax u v)) (.pi A' B') c).mp
        refine Or.inr ⟨a, p, hc, ha, ?_⟩
        cases hp
        exact .pi hA' (fun s hs => hB' _ (List.mem_map.mpr ⟨s, hs, rfl⟩))


end Rcic.Declarative.Ann.LR3.EnvironmentEval

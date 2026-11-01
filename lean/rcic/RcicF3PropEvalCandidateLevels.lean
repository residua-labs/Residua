import rcic.RcicF3PropEvalCandidateParams
import rcic.RcicF3RawFamilyLevels

/-!
# The guarded constructor slice at the actual recursor valuation

The candidate guard compares valuations only below the family's arity.
Family-bounded syntax transports the same parameter tuple, dependent field
tuple and complete result key to the recursor's actual valuation. Entries
outside the family arity, including the motive universe, are unrestricted.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalCandidate
open Rcic.Declarative PiIndex RawFamilyRec RawFamily

/-- Full-key parameter slicing followed by bounded-family valuation transport. -/
theorem ctorAt_parameters_at (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (X : Frame) (ar : Nat) (hB : FamBounded fd ar)
    (vs : List Nat) (σ : Nat → Nat)
    (hσ : ∀ u, u < ar → σ u = σOf vs u)
    (i : Index.{4}) (z : PSet.{4}) (hc : CtorAt P μ fd X vs i z)
    (ps₀ : List PSet.{4}) (hkey : paramKey fd.params.length i = key ps₀)
    (h0 : evalTotal σ fd.resLevel = 0) :
    let M := mkM P (table P μ fd X)
    ∃ (j : Fin fd.ctors.length) (xs : List PSet.{4}),
      TelFits M σ fd.params ρ0 ps₀ ∧
      TelFits M σ (fd.ctors.get j).1 (push ps₀ ρ0) xs ∧
      i = key (ps₀ ++ (fd.ctors.get j).2.map
        (den M σ (push xs (push ps₀ ρ0)))) ∧
      Equiv z pempty := by
  dsimp only
  let M := mkM P (table P μ fd X)
  have h0vs : evalTotal (σOf vs) fd.resLevel = 0 :=
    (evalTotal_agree hσ fd.resLevel hB.res).symm.trans h0
  obtain ⟨j, xs, hps, hxs, hi, hz⟩ :=
    ctorAt_parameters P μ fd X vs i z hc ps₀ hkey h0vs
  have hj : fd.ctors[j.val]? = some (fd.ctors.get j) := by
    rw [List.getElem?_eq_getElem j.isLt]
    rfl
  have hctor := hB.ctors (fd.ctors.get j) (List.getElem?_mem hj)
  refine ⟨j, xs, (TelFits_levels M hσ fd.params hB.params ρ0 ps₀).mpr hps,
    (TelFits_levels M hσ (fd.ctors.get j).1 hctor.1 (push ps₀ ρ0) xs).mpr hxs,
    ?_, hz⟩
  rw [map_den_levels M hσ (fd.ctors.get j).2 hctor.2]
  exact hi

end Rcic.F3.PSet.PropEvalCandidate

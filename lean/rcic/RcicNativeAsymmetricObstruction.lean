import rcic.RcicNativeAsymmetricStrip
import rcic.RcicEtakMovingMinorSuccessor

/-!
Pin: 76f2d6fc6485f4a8bfa9b66a1db1760656516f8c.
COMPILED by the grok-rf lane (Lean 4.14.0): lake build green locally and
on the lean-w5 worker after fresh-olean rebuild; #print axioms ⊆
[propext, Quot.sound]. This theorem requires the explicit native
SortUnique assumption used by the moving-minor successor draft.
It does NOT construct SortUnique from EnvWfT and is not an unconditional
native countermodel. It connects that exact conditional obstruction to
the actual hereditary AsymmetricTile interface defined in this folder.
closure_claim = 0.
-/

namespace Rcic.Declarative.NativeAsymmetricStrip76

open NativeMovingMinor76

/-- The reverse ordering makes leftEnd the prescribed short side. -/
theorem noAsymmetricTile_of_SU (su : F8A2Support.SortUnique eqEnvT 2) :
    AsymmetricTile (E := eqEnvT) (n := 2) [] commonType → False := by
  intro S
  obtain ⟨d, left, right⟩ := S rightBranch rightBranchGood leftBranch leftBranchGood
  have hshort : leftEnd = d ∨
      Nonempty (NativeMovingMinor76.Step [] leftEnd d commonType) := by
    cases right with
    | stay h => exact .inl rfl
    | step s gs => exact .inr ⟨s⟩
  exact no_optional_against_star_of_SU su hshort left.erase

end Rcic.Declarative.NativeAsymmetricStrip76

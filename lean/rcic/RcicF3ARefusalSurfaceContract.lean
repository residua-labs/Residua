import rcic.RcicF3IndexedBoundNormalization
import rcic.RcicF3PropEvalSafeIndexAttack

/-!
# Composition for the measured refusal and separate indexed-bound repair

This component joins the exact AccP bound obstruction, safe-index
comparison, ordinary-row broadening, normalization, and adversarial
witnesses at one supplied Premises4. It does not assert check completeness
or a complete imported-Acc soundness-tier witness.
closure_claim = 0; scope_closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.ARefusalSurfaceContract

open Rcic.Declarative

/-- Every component uses the same P; their domains remain literal. -/
def Components (P : Premises4) : Prop :=
  AccBoundScopeAttack.Witness P ∧
  PropEvalSafeIndex.Witness P ∧
  IndexedFieldBounds.Witness P ∧
  IndexedBoundNormalization.Witness P ∧
  PropEvalSafeIndexAttack.Witness P

theorem components (P : Premises4) : Components P :=
  ⟨AccBoundScopeAttack.component_witness P,
    PropEvalSafeIndex.component_witness P,
    IndexedFieldBounds.component_witness P,
    IndexedBoundNormalization.component_witness P,
    PropEvalSafeIndexAttack.component_witness P⟩

/-- Exact row/normalization composition, without claiming a whole new tier. -/
def Target : Prop :=
  (∀ P : Premises4, Components P) ∧
  (∀ (K : Nat → Nat) {E : Rcic.Declarative.ResolvedEnv}
    (h : EnvWfT E), BoundG K h → IndexedFieldBounds.BoundGIndexed K h)

theorem target : Target :=
  ⟨components, IndexedFieldBounds.of_boundG⟩

theorem components_nonrefutable (P : Premises4) :
    ¬ (Components P → (Premises4 → False)) :=
  fun h => h (components P) P

theorem target_nonrefutable (P : Premises4) :
    ¬ (Target → (Premises4 → False)) :=
  fun h => h target P

end Rcic.F3.PSet.ARefusalSurfaceContract

#print axioms Rcic.F3.PSet.ARefusalSurfaceContract.components
#print axioms Rcic.F3.PSet.ARefusalSurfaceContract.target
#print axioms Rcic.F3.PSet.ARefusalSurfaceContract.components_nonrefutable
#print axioms Rcic.F3.PSet.ARefusalSurfaceContract.target_nonrefutable

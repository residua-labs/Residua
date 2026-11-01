import rcic.RcicF3IndexedBranchEvalAttack
import rcic.RcicF3IndexedWrapBoundBoundary

/-!
# Indexed Prop producers, inhabited recursive evaluation, and the old-iota boundary

The positive producer types are retained literally from AIndexedPropContract.
The Branch component supplies an actual inhabited depth-three recursive
child, candidate constructor production, evaluation and generated IH typing.
The Wrap component supplies a complete counterexample to the existing
unrestricted IotaAt/GInv interface on an admitted indexed-bound group.
The separate bound theorem places that fixture outside the unchanged
original BoundG domain at every K.

All components use the same explicit Premises4. This contract supplies no
unconditional inhabitant of Premises4, imported-Acc instance, modern iota,
universal plain-iota producer, or whole-tier closure. Old theorem statements,
root declarations and historical refutations are unchanged.
scope_closure_claim = 0. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.AIndexedPropBoundaryContract

open Rcic.Declarative

def Components (P : Premises4) : Prop :=
  AIndexedPropContract.Components P ∧
  IndexedBranchEvalAttack.Witness P ∧
  IndexedWrapIotaAttack.Witness P ∧
  ∀ K : Nat → Nat,
    IndexedFieldBounds.BoundGIndexed K IndexedWrapFixture.envWfT ∧
      ¬ BoundG K IndexedWrapFixture.envWfT

theorem components (P : Premises4) : Components P :=
  ⟨AIndexedPropContract.components P,
    IndexedBranchEvalAttack.component_witness P,
    IndexedWrapIotaAttack.component_witness P,
    IndexedWrapBoundBoundary.indexed_bound_strict_at_wrap P⟩

def Target : Prop :=
  AIndexedPropContract.CandidateConstructorProducer ∧
  AIndexedPropContract.LegacyGroupProducer ∧
  ∀ P : Premises4, Components P

theorem target : Target :=
  ⟨AIndexedPropContract.candidate_constructor_producer,
    AIndexedPropContract.legacy_group_producer, components⟩

theorem components_nonrefutable (P : Premises4) :
    ¬ (Components P → (Premises4 → False)) :=
  fun h => h (components P) P

theorem target_nonrefutable (P : Premises4) :
    ¬ (Target → (Premises4 → False)) :=
  fun h => h target P

end Rcic.F3.PSet.AIndexedPropBoundaryContract

#print axioms Rcic.F3.PSet.AIndexedPropBoundaryContract.components
#print axioms Rcic.F3.PSet.AIndexedPropBoundaryContract.target
#print axioms Rcic.F3.PSet.AIndexedPropBoundaryContract.components_nonrefutable
#print axioms Rcic.F3.PSet.AIndexedPropBoundaryContract.target_nonrefutable

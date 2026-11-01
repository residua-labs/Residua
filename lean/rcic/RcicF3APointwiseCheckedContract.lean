import rcic.RcicF3ABoundedFrameContract
import rcic.RcicF3PointwiseCheckedMigrationAttack

/-!
# Separate pointwise checked target and complete same-P composition

The original KernelSoundnessTierWDChecked is reached from exactly the
universal LocalCandidatesChecked input. That input retains the actual
selected DATA/PendA/check domain and each bounded-world faithful-table
instance; it is NOT produced here. Finite DATA, both Prop policies, plain
declarations, original W/D acceptance and the False finalizer have actual
producers in the imported migration.

The full previous component conjunction and every new actual-table witness
are composed under one Premises4. These components are produced without
the universal local-candidate input. Their relative non-refutability must
not be confused with non-refutability of CheckedTarget, whose latter
equivalence below records the still-unpaid production obligation.

CheckedTarget is explicitly separate from ABoundedFrameContract.Target.
The latter and every earlier NormRole/StepAG definition are unchanged; no
implication or equality between those universal targets is asserted.
Historical refutations keep their original targets. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.APointwiseCheckedContract

/-- The kernel consumer has exactly the new bounded local-existence
premise, with both original executable checks retained in its conclusion. -/
def LocalConsumer : Prop :=
  (∀ (P : Premises4) (K : Nat → Nat),
    PointwiseADataChecked.LocalCandidatesChecked P K) →
      Rcic.F3.StepWDApex.KernelSoundnessTierWDChecked

theorem local_consumer : LocalConsumer :=
  PointwiseADataChecked.kernelSoundnessTierWDChecked_of_localCandidates

/-- All preceding components and actual NEW-table witnesses use the same
P. No universal local-candidate producer is a conjunct. -/
def Components (P : Premises4) : Prop :=
  ABoundedFrameContract.Components P ∧
  PointwiseCheckedMigrationAttack.Witness P

theorem components (P : Premises4) : Components P :=
  ⟨ABoundedFrameContract.components P,
    PointwiseCheckedMigrationAttack.component_witness P⟩

theorem components_nonrefutable (P : Premises4) :
    ¬ (Components P → (Premises4 → False)) :=
  fun h => h (components P) P

/-- Explicit separate checked repair target. The universal local-frame
producer is retained literally, together with the unchanged kernel tier
and every produced component. -/
def CheckedTarget : Prop :=
  (∀ (P : Premises4) (K : Nat → Nat),
    PointwiseADataChecked.LocalCandidatesChecked P K) ∧
  Rcic.F3.StepWDApex.KernelSoundnessTierWDChecked ∧
  (∀ P, Components P)

theorem checked_target_of_localCandidates
    (hLocal : ∀ (P : Premises4) (K : Nat → Nat),
      PointwiseADataChecked.LocalCandidatesChecked P K) : CheckedTarget :=
  ⟨hLocal, local_consumer hLocal, components⟩

theorem checked_target_iff_localCandidates : CheckedTarget ↔
    ∀ (P : Premises4) (K : Nat → Nat),
      PointwiseADataChecked.LocalCandidatesChecked P K :=
  ⟨fun h => h.1, checked_target_of_localCandidates⟩

/-- This is an equivalence, not an assertion of either side. A universal
non-refutability claim would itself pay the remaining universal producer. -/
theorem checked_target_nonrefutable_iff (P : Premises4) :
    (¬ (CheckedTarget → (Premises4 → False))) ↔ CheckedTarget := by
  constructor
  · intro hn
    cases P.dec CheckedTarget with
    | isTrue h => exact h
    | isFalse h => exact False.elim (hn (fun ht _ => h ht))
  · intro ht h
    exact h ht P

end Rcic.F3.PSet.APointwiseCheckedContract

import rcic.RcicF3APointwiseCheckedContract
import rcic.RcicF3PointwiseCheckedApexAttack
import rcic.RcicF3ReaderDeltaAttack

/-!
# Produced checked target, reader composition and same-P non-refutability

The actual reader, bounded mask and local small-frame producers discharge
the earlier checked contract's literal universal LocalCandidatesChecked
input. Its unchanged checked kernel tier is produced by the new pointwise
interpretation, with both original executable checks and all original
environment antecedents retained.

Every earlier component, the new reader/mask witnesses, actual new-table
W and AccR witnesses, and the separate distinguished-False non-vacuity
certificate are composed under the SAME supplied Premises4. The checked
target itself is now supplied to the non-refutability proof; no universal
non-refutability premise is assumed.

The reader adversaries retain their actual auxiliary models; the delta
source uses an admitted transparent Id predecessor at its original zero
valuation. The installed pointwise group witnesses are separate conjuncts.

The old ABoundedFrameContract.Target and unchecked NormRole.StepAG remain
separate and unchanged. Their equivalences and the historical refutations
are not reinterpreted as statements about this checked target. This is a
source proof composition, not a compiled or computed Closed declaration.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.AReaderClosureContract

def Components (P : Premises4) : Prop :=
  APointwiseCheckedContract.Components P ∧
  PointwiseCheckedApexAttack.Witness P ∧
  ReaderDeltaAttack.Witness P

theorem components (P : Premises4) : Components P :=
  ⟨APointwiseCheckedContract.components P,
    PointwiseCheckedApexAttack.component_witness P,
    ReaderDeltaAttack.component_witness P⟩

theorem components_nonrefutable (P : Premises4) :
    ¬ (Components P → (Premises4 → False)) :=
  fun h => h (components P) P

/-- The earlier separate checked target is produced with its exact
universal local-candidate conjunct, not replaced by a fixture proposition. -/
theorem checked_target : APointwiseCheckedContract.CheckedTarget :=
  APointwiseCheckedContract.checked_target_of_localCandidates
    PointwiseLocalProducer.localCandidatesChecked

theorem checked_target_nonrefutable (P : Premises4) :
    ¬ (APointwiseCheckedContract.CheckedTarget → (Premises4 → False)) :=
  fun h => h checked_target P

/-- Final composition of the produced checked target and every complete
component witness. This does not include the old unchecked target. -/
def Target : Prop :=
  APointwiseCheckedContract.CheckedTarget ∧ (∀ P, Components P)

theorem target : Target := ⟨checked_target, components⟩

theorem target_nonrefutable (P : Premises4) :
    ¬ (Target → (Premises4 → False)) :=
  fun h => h target P

end Rcic.F3.PSet.AReaderClosureContract

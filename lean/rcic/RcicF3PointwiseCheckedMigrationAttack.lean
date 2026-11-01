import rcic.RcicF3PointwiseADataChecked
import rcic.RcicF3PointwiseDataFiniteAttack
import rcic.RcicF3PointwisePropGroupAttack
import rcic.RcicF3PointwisePropTree
import rcic.RcicF3PointwisePropPlainIotaAttack
import rcic.RcicF3PointwiseFalseNonvacuity
import rcic.RcicF3PointwiseDataTypedIotaAttack

/-!
# Same-P composition of the pointwise checked-consumer migration

The finite Nat producer, empty-child AccR instance, inhabited-domain
PropOnly tree, nonempty True iota, distinguished-False finalizer, and exact height-omega W
legacy-redex witness all use their actual new installed tables. Every
component uses the SAME supplied Premises4. The literal old AccR refutation
is retained inside its component, without transporting any old invariant.

The final checked-tier theorem remains conditional exactly on universal
bounded DATA local-candidate production. The implication is proved; that
universal premise and universal non-refutability are not supplied by these
fixtures. Original checks and final tier are unchanged. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseCheckedMigrationAttack

def Witness (P : Premises4) : Prop :=
  PointwiseDataFiniteAttack.Witness P ∧
  PointwisePropGroupAttack.Witness P ∧
  PointwisePropTree.Witness P ∧
  PointwisePropPlainIotaAttack.Witness P ∧
  (∀ K, PointwiseFalseNonvacuity.Witness P K) ∧
  PointwiseDataTypedIotaAttack.Witness P ∧
  (∀ K, PointwiseADataChecked.LocalCandidatesChecked P K →
    PointwiseADataChecked.StepADataChecked P K) ∧
  ((∀ (Q : Premises4) (K : Nat → Nat),
    PointwiseADataChecked.LocalCandidatesChecked Q K) →
      Rcic.F3.StepWDApex.KernelSoundnessTierWDChecked)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨PointwiseDataFiniteAttack.component_witness P,
    PointwisePropGroupAttack.component_witness P,
    PointwisePropTree.component_witness P,
    PointwisePropPlainIotaAttack.component_witness P,
    PointwiseFalseNonvacuity.component_witness P,
    PointwiseDataTypedIotaAttack.component_witness P,
    PointwiseADataChecked.stepADataChecked_of_localCandidates P,
    PointwiseADataChecked.kernelSoundnessTierWDChecked_of_localCandidates⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PointwiseCheckedMigrationAttack

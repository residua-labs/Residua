import rcic.RcicF3AFalseNonvacuityContract
import rcic.RcicF3NormADataChecked
import rcic.RcicF3NormPropTreeChecks
import rcic.RcicF3BoundedSubstAttack

/-!
# Complete checked Prop faces and the retained universal A target

The entire prior component conjunction is retained with actual inhabited
higher-order PropOnly composition and bounded beta/zeta telescope proofs.
Both Prop policies now have produced group consumers at the existing
checks. The unchanged checked apex therefore needs only the explicitly
stated positive-depth checked data producer.

That reduction does not produce or replace universal unchecked StepAG.
Target retains the full earlier universal A conjunction. No data producer
or universal non-refutability witness is asserted. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.APropCheckedContract

def DataConsumer : Prop :=
  (∀ P K, NormADataChecked.StepADataChecked P K) →
    Rcic.F3.StepWDApex.KernelSoundnessTierWDChecked

theorem data_consumer : DataConsumer :=
  NormADataChecked.kernelSoundnessTierWDChecked_of_AData

def Components (P : Premises4) : Prop :=
  AFalseNonvacuityContract.Components P ∧
  BoundedSubstAttack.Witness P ∧
  NormPropTreeChecks.Witness P ∧ DataConsumer

theorem components (P : Premises4) : Components P :=
  ⟨AFalseNonvacuityContract.components P, BoundedSubstAttack.component_witness P,
    NormPropTreeChecks.component_witness P, data_consumer⟩

theorem components_nonrefutable (P : Premises4) :
    ¬ (Components P → (Premises4 → False)) :=
  fun h => h (components P) P

def Target : Prop :=
  AFalseNonvacuityContract.Target ∧ (∀ P, Components P)

theorem target_of_stepAG (hA : ∀ P K, NormRole.StepAG P K) : Target :=
  ⟨AFalseNonvacuityContract.target_of_stepAG hA, components⟩

theorem target_iff_stepAG : Target ↔ ∀ P K, NormRole.StepAG P K :=
  ⟨fun h => h.1.1.1, target_of_stepAG⟩

theorem target_nonrefutable_iff (P : Premises4) :
    (¬ (Target → (Premises4 → False))) ↔ Target := by
  constructor
  · intro hn
    cases P.dec Target with
    | isTrue h => exact h
    | isFalse h => exact False.elim (hn (fun ht _ => h ht))
  · intro ht h
    exact h ht P

end Rcic.F3.PSet.APropCheckedContract

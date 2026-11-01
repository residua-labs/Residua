import rcic.RcicF3APropCheckedContract
import rcic.RcicF3NormDataGroupAttack
import rcic.RcicF3NormDataTypedIotaAttack
import rcic.RcicF3DataNotPiAttack

/-!
# Produced normalized DATA bridges and the remaining small-frame input

The entire prior component conjunction is retained. Actual constructor
typing, the bounded reader prefix, arbitrary-depth DATA recursion, stored
recursor membership and stable literal iota compose into GroupStepAt once
the actual normalized descriptor has a small closed candidate. The exact
W fixture supplies this candidate and exercises the new generic producer.
An actual typed legacy leaf redex exercises the new stable iota law.
The bounded fresh-head and arbitrary-Pi witnesses are retained together.

The checked apex still has the explicit universal small-frame input.
Neither that input nor the retained full unchecked A target is produced
or asserted non-refutable here. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ADataFrameContract

def FrameConsumer : Prop :=
  (∀ P K, NormAFrameChecked.FramesADataChecked P K) →
    Rcic.F3.StepWDApex.KernelSoundnessTierWDChecked

theorem frame_consumer : FrameConsumer :=
  NormAFrameChecked.kernelSoundnessTierWDChecked_of_frames

def Components (P : Premises4) : Prop :=
  APropCheckedContract.Components P ∧
  NormDataGroupAttack.Witness P ∧
  NormDataTypedIotaAttack.Witness P ∧
  DataNotPiAttack.Witness P ∧ FrameConsumer

theorem components (P : Premises4) : Components P :=
  ⟨APropCheckedContract.components P, NormDataGroupAttack.component_witness P,
    NormDataTypedIotaAttack.component_witness P,
    DataNotPiAttack.component_witness P, frame_consumer⟩

theorem components_nonrefutable (P : Premises4) :
    ¬ (Components P → (Premises4 → False)) :=
  fun h => h (components P) P

def Target : Prop :=
  APropCheckedContract.Target ∧ (∀ P, Components P)

theorem target_of_stepAG (hA : ∀ P K, NormRole.StepAG P K) : Target :=
  ⟨APropCheckedContract.target_of_stepAG hA, components⟩

theorem target_iff_stepAG : Target ↔ ∀ P K, NormRole.StepAG P K :=
  ⟨fun h => APropCheckedContract.target_iff_stepAG.mp h.1, target_of_stepAG⟩

theorem target_nonrefutable_iff (P : Premises4) :
    (¬ (Target → (Premises4 → False))) ↔ Target := by
  constructor
  · intro hn
    cases P.dec Target with
    | isTrue h => exact h
    | isFalse h => exact False.elim (hn (fun ht _ => h ht))
  · intro ht h
    exact h ht P

end Rcic.F3.PSet.ADataFrameContract

import rcic.RcicF3AWFixtureContract
import rcic.RcicF3NormWDChecked
import rcic.RcicF3NormDHiddenAttack
import rcic.RcicF3NormPropPlainIotaAttack
import rcic.RcicF3BoundedPiSpineAttack

/-!
# Checked W/D migration: composition and the remaining universal A producer

The new interpretation now produces the unchanged checked soundness tier
from universal normalized StepAG. The complete W fixture, bounded dependent
Pi witness, finite-family D witnesses and inhabited typed Prop/anySort iota
witness are retained in one literal component conjunction.

The conditional apex consumer is proved. Universal StepAG itself is still
an explicit argument of Target; universal non-refutability is equivalent
to producing that target, relative to the supplied Premises4 instance.
No fixture or conditional-consumer verdict closes the universal A target.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ACheckedMigrationContract

def ApexConsumer : Prop :=
  (∀ (P : Premises4) (K : Nat → Nat), NormRole.StepAG P K) →
    Rcic.F3.StepWDApex.KernelSoundnessTierWDChecked

theorem apex_consumer : ApexConsumer :=
  NormWDChecked.kernelSoundnessTierWDChecked_of_A

def Components (P : Premises4) : Prop :=
  AWFixtureContract.Components P ∧
  BoundedPiSpineAttack.Witness P ∧
  NormDHiddenAttack.Witness P ∧
  NormPropPlainIotaAttack.Witness P ∧
  ApexConsumer

/-- Every preceding component and every new concrete witness is retained
under one Premises4 instance, together with the proved conditional apex. -/
theorem components (P : Premises4) : Components P :=
  ⟨AWFixtureContract.components P, BoundedPiSpineAttack.component_witness P,
    NormDHiddenAttack.component_witness P,
    NormPropPlainIotaAttack.component_witness P, apex_consumer⟩

theorem components_nonrefutable (P : Premises4) :
    ¬ (Components P → (Premises4 → False)) :=
  fun h => h (components P) P

def Target : Prop :=
  (∀ (P : Premises4) (K : Nat → Nat), NormRole.StepAG P K) ∧
  Rcic.F3.StepWDApex.KernelSoundnessTierWDChecked ∧
  (∀ P, Components P)

theorem target_of_stepAG (hA : ∀ P K, NormRole.StepAG P K) : Target :=
  ⟨hA, apex_consumer hA, components⟩

theorem target_iff_stepAG : Target ↔ ∀ P K, NormRole.StepAG P K :=
  ⟨fun h => h.1, target_of_stepAG⟩

/-- This equivalence does not assert either side. It records precisely
why universal non-refutability cannot replace the unpaid producer. -/
theorem target_nonrefutable_iff (P : Premises4) :
    (¬ (Target → (Premises4 → False))) ↔ Target := by
  constructor
  · intro hn
    cases P.dec Target with
    | isTrue h => exact h
    | isFalse h => exact False.elim (hn (fun ht _ => h ht))
  · intro ht h
    exact h ht P

end Rcic.F3.PSet.ACheckedMigrationContract

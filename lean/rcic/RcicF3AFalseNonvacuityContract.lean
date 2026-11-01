import rcic.RcicF3ACheckedMigrationContract
import rcic.RcicF3NormFalseNonvacuity

/-!
# Nontrivial checked environment with the actual distinguished False prefix

The prior complete component conjunction is retained together with the
actual admitted False/Prop-definition model at every bound K. This pays
the environment antecedents of the unchanged checked tier and supplies
two distinct values in one installed fibre of that same model.

The universal normalized A producer remains an explicit Target conjunct.
This particular environment certificate does not produce that universal
premise, an imported Acc environment, or unconditional apex closure.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.AFalseNonvacuityContract

def Components (P : Premises4) : Prop :=
  ACheckedMigrationContract.Components P ∧
  (∀ K, NormFalseNonvacuity.Witness P K)

theorem components (P : Premises4) : Components P :=
  ⟨ACheckedMigrationContract.components P, NormFalseNonvacuity.component_witness P⟩

theorem components_nonrefutable (P : Premises4) :
    ¬ (Components P → (Premises4 → False)) :=
  fun h => h (components P) P

def Target : Prop :=
  ACheckedMigrationContract.Target ∧ (∀ P, Components P)

theorem target_of_stepAG (hA : ∀ P K, NormRole.StepAG P K) : Target :=
  ⟨ACheckedMigrationContract.target_of_stepAG hA, components⟩

theorem target_iff_stepAG : Target ↔ ∀ P K, NormRole.StepAG P K :=
  ⟨fun h => h.1.1, target_of_stepAG⟩

theorem target_nonrefutable_iff (P : Premises4) :
    (¬ (Target → (Premises4 → False))) ↔ Target := by
  constructor
  · intro hn
    cases P.dec Target with
    | isTrue h => exact h
    | isFalse h => exact False.elim (hn (fun ht _ => h ht))
  · intro ht h
    exact h ht P

end Rcic.F3.PSet.AFalseNonvacuityContract

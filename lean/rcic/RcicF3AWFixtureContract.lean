import rcic.RcicF3ADataKeyContract
import rcic.RcicF3NormPendAWSameTable

/-!
# The complete repaired W fixture and the retained universal A target

The entire previous component conjunction is retained. The new witness
produces the normalized Nat predecessor and exact PendA W invariant, the
complete literal recursor package, both whole-environment checks at
constant bounds, and distinct installed Nat values at the same W table
whose family contains the height-omega element.

This certificate is at the original admitted Nat/W fixture. Its environment
does not have the distinguished False prefix of the checked apex. The
universal normalized StepAG producer and interpretation migration through
the checked W/D apex remain unpaid. The target still quantifies over every
original PendA group, and the old literal refutations remain separate.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.AWFixtureContract

def Components (P : Premises4) : Prop :=
  ADataKeyContract.Components P ∧ NormPendAWSameTable.Witness P

/-- The previous suite and the complete same-table certificate compose
under the same Premises4 instance. -/
theorem components (P : Premises4) : Components P :=
  ⟨ADataKeyContract.components P, NormPendAWSameTable.component_witness P⟩

theorem components_nonrefutable (P : Premises4) :
    ¬ (Components P → (Premises4 → False)) :=
  fun h => h (components P) P

def Target : Prop :=
  (∀ P K, NormRole.StepAG P K) ∧ (∀ P, Components P)

theorem target_of_stepAG (hA : ∀ P K, NormRole.StepAG P K) : Target :=
  ⟨hA, components⟩

theorem target_iff_stepAG : Target ↔ ∀ P K, NormRole.StepAG P K :=
  ⟨fun h => h.1, target_of_stepAG⟩

end Rcic.F3.PSet.AWFixtureContract

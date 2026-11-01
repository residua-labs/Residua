import rcic.RcicF3ANormRoleContract
import rcic.RcicF3PiSmallKeyProducerAtAttack
import rcic.RcicF3FamilyBetaMirrorAttack
import rcic.RcicF3BoundedBVarAttack
import rcic.RcicF3NormPendAW
import rcic.RcicF3NormPendAWValue

/-!
# Exact-stage keyed data components and the retained universal A boundary

The complete previous component conjunction is retained. The added data
signature witness produces its literal closure and W4 1 data admissibility,
with dependent depth-three domains and both child and parent full keys
depending on actual reconstructed recursive fields. Its omega value is an
ordinary payload. The exact admitted PendA W group separately supplies a
small closed normalized frame and actual installed height-omega membership.
Its scalar production endpoint is also evaluated in the installed model;
this does not assert typing of the entire recursor input tuple.

The mirror component proves arbitrary-depth beta wrappers under admissible
candidate families. Bounded variable inversion extracts actual conversion
edges and composes them in the entire original fitting context. Neither
component asserts general mirror transport or local-context strengthening.

The universal NormRole.StepAG target still covers every PendA group and
remains an explicit input. No universal admitted-data signature, complete
data/propOnly recursor, W/D apex or overall check-passing witness is asserted.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ADataKeyContract

def Components (P : Premises4) : Prop :=
  ANormRoleContract.Components P ∧
    PiSmallKeyProducerAtAttack.Witness P ∧
    FamilyBetaMirrorAttack.Witness P ∧
    BoundedBVarAttack.Witness P ∧ NormPendAW.Witness P ∧
    NormPendAWValue.Witness P

/-- Composition retains all prior conjuncts, rather than projecting only
one fixture out of the previous checkpoint. -/
theorem components (P : Premises4) : Components P :=
  ⟨ANormRoleContract.components P,
    PiSmallKeyProducerAtAttack.component_witness P,
    FamilyBetaMirrorAttack.component_witness P,
    BoundedBVarAttack.component_witness P, NormPendAW.component_witness P,
    NormPendAWValue.component_witness P⟩

theorem components_nonrefutable (P : Premises4) :
    ¬ (Components P → (Premises4 → False)) :=
  fun h => h (components P) P

def Target : Prop :=
  (∀ P K, NormRole.StepAG P K) ∧ (∀ P, Components P)

theorem target_of_stepAG (hA : ∀ P K, NormRole.StepAG P K) : Target :=
  ⟨hA, components⟩

theorem target_iff_stepAG : Target ↔ ∀ P K, NormRole.StepAG P K :=
  ⟨fun h => h.1, target_of_stepAG⟩

end Rcic.F3.PSet.ADataKeyContract

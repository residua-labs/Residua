import rcic.RcicF3ADataFrameContract
import rcic.RcicF3RawFamilyGlobalSizeAttack
import rcic.RcicF3RecFieldConsumerAttack
import rcic.RcicF3BoundedBetaOriginAttack
import rcic.RcicF3PiGraphInversionAttack

/-!
# Small-signature assembly and bounded domain-erasure components

The complete previous DATA conjunction is retained. The new small
signature preserves actual recursive fields and full dependent keys.
Intersection over parameter representatives supplies an admissible frame;
the actual normalized cache supplies child inclusion and all-vector
canonicalization. Constructor closure still consumes ReachedMasks.
The exact admitted W fixture pays those masks and uses the new assembler.

The current global role also has a proved size-necessity law: even one
small DATA fibre requires a globally admissible closed candidate. The
composition retains its actual W instance. No role is changed here.

Bounded one-application erasure, converted-beta body provenance and reached
Pi conversion are separate produced components with actual W witnesses.
They do not supply the universal domain-mask induction or turn bounded
valuation hypotheses into all-vector closure. The checked small-frame
frontier and the full unchecked A target remain unpaid. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.AMaskAssemblyContract

def Components (P : Premises4) : Prop :=
  ADataFrameContract.Components P ∧
  RawFamilyGlobalSizeAttack.Witness P ∧
  RecFieldConsumerAttack.Witness P ∧
  BoundedBetaOriginAttack.Witness P ∧
  PiGraphInversionAttack.Witness P

theorem components (P : Premises4) : Components P :=
  ⟨ADataFrameContract.components P, RawFamilyGlobalSizeAttack.component_witness P,
    RecFieldConsumerAttack.component_witness P,
    BoundedBetaOriginAttack.component_witness P,
    PiGraphInversionAttack.component_witness P⟩

theorem components_nonrefutable (P : Premises4) :
    ¬ (Components P → (Premises4 → False)) :=
  fun h => h (components P) P

def Target : Prop :=
  ADataFrameContract.Target ∧ (∀ P, Components P)

theorem target_of_stepAG (hA : ∀ P K, NormRole.StepAG P K) : Target :=
  ⟨ADataFrameContract.target_of_stepAG hA, components⟩

theorem target_iff_stepAG : Target ↔ ∀ P K, NormRole.StepAG P K :=
  ⟨fun h => ADataFrameContract.target_iff_stepAG.mp h.1, target_of_stepAG⟩

theorem target_nonrefutable_iff (P : Premises4) :
    (¬ (Target → (Premises4 → False))) ↔ Target := by
  constructor
  · intro hn
    cases P.dec Target with
    | isTrue h => exact h
    | isFalse h => exact False.elim (hn (fun ht _ => h ht))
  · intro ht h
    exact h ht P

end Rcic.F3.PSet.AMaskAssemblyContract

import rcic.RcicF3AMaskAssemblyContract
import rcic.RcicF3NormFieldMaskContextAttack
import rcic.RcicF3ReaderSupportAttack
import rcic.RcicF3CheckedCtorWorldAttack

/-!
# Bounded recursive-field masking and a separate pointwise DATA role

The actual HasTyT induction produces the local masking relation. Actual
admitted constructor caches produce its Context, with both original Fits
and full family keys. The W witnesses retain nonempty recursive values,
height omega, beta/zeta conversion and dependent depth three. A further
reader witness proves that captured original assignments can differ;
agreement of an unused capture is not an admissible shortcut.

The separate pointwise DATA frame is globally admissible without assuming
global candidate inhabitation. Its local existence guard, original cases,
family reads and new installer are composed on the actual W fixture. The
recursor witness uses a family update of the concrete old W base; this is
explicitly distinct from the complete new installed table. Only the Nat
predecessor invariant is produced here. The unchanged selected D check
supplies the reached constructor world's recursor bound.

No complete reader-domain provenance, bounded local candidate producer,
universal pointwise group step or checked apex is asserted here. The
previous unchecked target remains literally equivalent to its previous
StepAG premise. All component witnesses use the same supplied Premises4.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ABoundedFrameContract

def Components (P : Premises4) : Prop :=
  AMaskAssemblyContract.Components P ∧
  NormFieldMaskContextAttack.Witness P ∧
  ReaderSupportAttack.Witness P ∧
  CheckedCtorWorldAttack.Witness P

theorem components (P : Premises4) : Components P :=
  ⟨AMaskAssemblyContract.components P,
    NormFieldMaskContextAttack.component_witness P,
    ReaderSupportAttack.component_witness P,
    CheckedCtorWorldAttack.component_witness P⟩

theorem components_nonrefutable (P : Premises4) :
    ¬ (Components P → (Premises4 → False)) :=
  fun h => h (components P) P

def Target : Prop :=
  AMaskAssemblyContract.Target ∧ (∀ P, Components P)

theorem target_of_stepAG (hA : ∀ P K, NormRole.StepAG P K) : Target :=
  ⟨AMaskAssemblyContract.target_of_stepAG hA, components⟩

theorem target_iff_stepAG : Target ↔ ∀ P K, NormRole.StepAG P K :=
  ⟨fun h => AMaskAssemblyContract.target_iff_stepAG.mp h.1, target_of_stepAG⟩

theorem target_nonrefutable_iff (P : Premises4) :
    (¬ (Target → (Premises4 → False))) ↔ Target := by
  constructor
  · intro hn
    cases P.dec Target with
    | isTrue h => exact h
    | isFalse h => exact False.elim (hn (fun ht _ => h ht))
  · intro ht h
    exact h ht P

end Rcic.F3.PSet.ABoundedFrameContract

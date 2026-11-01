import rcic.RcicF3EvalRoleDeltaAttack
import rcic.RcicF3EvalPropRecPkgAttack

/-!
# Composed normalized Prop producer checkpoint and exact open A target

The composition retains the complete actual installed AccR evaluation,
closure, stored recursor type and stable literal RecPkg, together with the
all-instance transparent-body witness. All earlier endpoint adversarial
and historical-refutation conjuncts remain inside the retained witness.

The universal raw-role StepAG target is unchanged and remains an explicit
input. The component producer does not imply it; the equivalence below
makes the boundary literal. The separate normalized-role migration and
small data construction are not assumed here. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.ANormalizedPropContract

def Components (P : Premises4) : Prop :=
  EvalRoleDeltaAttack.Witness P ∧ EvalPropRecPkgAttack.Witness P

theorem components (P : Premises4) : Components P :=
  ⟨EvalRoleDeltaAttack.component_witness P,
    EvalPropRecPkgAttack.component_witness P⟩

theorem components_nonrefutable (P : Premises4) :
    ¬ (Components P → (Premises4 → False)) :=
  fun h => h (components P) P

def Target : Prop :=
  (∀ P K, EvalRole.StepAG RawFamily.role P K) ∧
  (∀ P, Components P)

theorem target_of_stepAG
    (hA : ∀ P K, EvalRole.StepAG RawFamily.role P K) : Target :=
  ⟨hA, components⟩

theorem target_iff_stepAG :
    Target ↔ ∀ P K, EvalRole.StepAG RawFamily.role P K :=
  ⟨fun h => h.1, target_of_stepAG⟩

end Rcic.F3.PSet.ANormalizedPropContract

import rcic.RcicF3PropEvalCandidateSuite
import rcic.RcicF3EvalPlanAttack
import rcic.RcicF3PropEvalValueReadAttack
import rcic.RcicF3EvalPlanValueAttack
import rcic.RcicF3EvalInstalledAttack
import rcic.RcicF3EvalCandidateStepAttack

/-!
# Indexed endpoint checkpoint and its exact remaining universal target

The component conjunction retains the prior adversarial suite, actual
normalized plan, bounded value/read witness, production member application,
canonical installed-table witness with its own indexed IH, and candidate
producer under the new predecessor invariant. Every component is produced
relative to the same explicit Premises4 input.

The full target additionally requires universal EvalRole.StepAG at the raw
family role. target_of_stepAG exposes exactly that input as hA. It is an
assembly theorem, not a producer of hA. The old finite-stage and planned
refutations keep their old targets. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.EvalEndpointContract

/-- The literal component witnesses are preserved without dropping conjuncts. -/
def Components (P : Premises4) : Prop :=
  PropEvalCandidateSuite.Witness P ∧
  EvalPlanAttack.Witness ∧
  PropEvalValueReadAttack.Witness P ∧
  EvalPlanValueAttack.Witness P ∧
  EvalInstalledAttack.Witness P ∧
  EvalCandidateStepAttack.Witness P

/-- Checked composition of the produced components at one premise instance. -/
theorem components (P : Premises4) : Components P :=
  ⟨PropEvalCandidateSuite.component_witness P,
    EvalPlanAttack.component_witness,
    PropEvalValueReadAttack.component_witness P,
    EvalPlanValueAttack.component_witness P,
    EvalInstalledAttack.component_witness P,
    EvalCandidateStepAttack.component_witness P⟩

/-- Relative non-refutability covers the same complete component conjunction. -/
theorem components_nonrefutable (P : Premises4) :
    ¬ (Components P → (Premises4 → False)) :=
  fun h => h (components P) P

/-- The universal repaired A statement and the produced component checkpoint.
The first conjunct is not weakened to the AccR fixture or to faithfulness. -/
def Target : Prop :=
  (∀ (P : Premises4) (K : Nat → Nat),
    EvalRole.StepAG RawFamily.role P K) ∧
  (∀ P : Premises4, Components P)

/-- Declared-edge assembly: hA remains an explicit unproduced input. -/
theorem target_of_stepAG
    (hA : ∀ (P : Premises4) (K : Nat → Nat),
      EvalRole.StepAG RawFamily.role P K) : Target :=
  ⟨hA, components⟩

/-- Adding the produced checkpoint neither weakens nor strengthens universal A. -/
theorem target_iff_stepAG :
    Target ↔ ∀ (P : Premises4) (K : Nat → Nat),
      EvalRole.StepAG RawFamily.role P K :=
  ⟨fun h => h.1, target_of_stepAG⟩

end Rcic.F3.PSet.EvalEndpointContract

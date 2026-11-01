import rcic.RcicF3PropEvalCandidateStepAttack
import rcic.RcicF3CandidateScopeAttack
import rcic.RcicF3PropEvalCandidateLeafAttack
import rcic.RcicF3RawFamilyRecAtAttack

/-!
# Candidate-step composition and adversarial witness suite

The conjunction retains the literal refutation of the current planned raw
StepAG; the public candidate-step, closure and leastness composition at the
actual AccR group; beta/delta/zeta readers at relabelled depth-three dependent
indices; the auxiliary inhabited depth-three candidate field; and the actual
PendA W height-omega recursion component, including exclusion from famLim
and the independent motive valuation.

These are component witnesses under one Premises4 hypothesis. The reader
aliases remain reader fixtures, and the depth-three field remains auxiliary.
Universal raw-frame production and the production endpoint remain open.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalCandidateSuite
open Rcic.Declarative PiIndex

def Witness (P : Premises4) : Prop :=
  (¬ PlanRole.StepAG RawFamily.role P (fun _ => 1)) ∧
  PropEvalCandidateStepAttack.Witness P ∧
  CandidateScopeAttack.ReaderWitness ∧
  PropEvalCandidateLeafAttack.Witness P ∧
  (RecPlan.nodeCore (RawFamilyRecAtAttack.model P) PendAW.pNode [pempty, pempty]
      (fxZW P) ∈ (tv True : PSet.{4}) ∧
    fxZW P ∈ RawFamily.frame P (RawFamilyRecAtAttack.base P) PendAWBridge.fd []
      (key [tyv fxS]) ∧
    fxZW P ∉ El (fapps (famLim P (RawFamilyRecAtAttack.base P) PendAWBridge.fd [])
      [tyv fxS]) ∧
    RawFamilyRecAtAttack.σ 0 = 1 ∧ RawFamilyRecAtAttack.σ 0 ≠ σOf [] 0)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨PlanPropStepAttack.stepAG_false P,
    PropEvalCandidateStepAttack.component_witness P,
    CandidateScopeAttack.reader_witness,
    PropEvalCandidateLeafAttack.component_witness P,
    RawFamilyRecAtAttack.inhabited P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropEvalCandidateSuite

import Lean
import rcic.RcicF3EqStepDMin

/-!
# F3 stepD minimal-hypothesis seal

`closure_claim = 0`.

Bounded seal for `rcic.RcicF3EqStepDMin`. Every declaration listed below must
depend on no axiom outside `propext` and `Quot.sound`; the `run_cmd` refuses
otherwise. The named antecedents of the module — `PartitionStepsABW` (the
A/B1/W rows, other lanes' debts, field types verbatim), `StepDHyp` (the
D-arm of the group step at the granularity the fold consumes, at the group's
own `BoundG`/`BoundDG`), and the per-environment `DDispatch` guard inside
`TierF3UncondDD` (the A∧D and non-`GroupClassD` D-group corners, named) — are
hypotheses, not silently assumed proofs. The sealed theorems are: the
boundary refutation (§1), the rebuilt assembly and tier wrappers (§2), and
the non-vacuity/non-refutability witnesses (§3).
-/

namespace Rcic.F3.StepDMinSeal

open Lean

def sealedTheorems : List Name := [
  ``Rcic.F3.StepDMin.dr_not_pendA,
  ``Rcic.F3.StepDMin.dr_pendD,
  ``Rcic.F3.StepDMin.dr_not_recFieldsDirect,
  ``Rcic.F3.StepDMin.dr_not_nodeFieldRow,
  ``Rcic.F3.StepDMin.not_partitionSteps,
  ``Rcic.F3.StepDMin.not_partitionStepsABD,
  ``Rcic.F3.StepDMin.PartitionStepsABW,
  ``Rcic.F3.StepDMin.partitionStepsABW_of_steps,
  ``Rcic.F3.StepDMin.StepDHyp,
  ``Rcic.F3.StepDMin.DDispatch,
  ``Rcic.F3.StepDMin.nodeStepRow_of_abw,
  ``Rcic.F3.StepDMin.walkG_of_abwDD,
  ``Rcic.F3.StepDMin.gInvSteps_of_abw_hyp,
  ``Rcic.F3.StepDMin.tierF3Concl_of_abw_hyp,
  ``Rcic.F3.StepDMin.TierF3UncondDD,
  ``Rcic.F3.StepDMin.tierF3UncondDD_of_abw_hyp,
  ``Rcic.F3.StepDMin.PartitionStepsAB,
  ``Rcic.F3.StepDMin.partitionStepsAB_of_abw,
  ``Rcic.F3.StepDMin.partitionStepsAB_of_abd,
  ``Rcic.F3.StepDMin.tierF3UncondDD_of_ab_hyp,
  ``Rcic.F3.StepDMin.TierF3DD,
  ``Rcic.F3.StepDMin.tierF3DD_of_abw_hyp,
  ``Rcic.F3.StepDMin.KernelSoundnessTierDD,
  ``Rcic.F3.StepDMin.kernelSoundnessTierDD_of_abw_hyp,
  ``Rcic.F3.StepDMin.not_pendA_of_groupClassD,
  ``Rcic.F3.StepDMin.ddispatch_of_classGD,
  ``Rcic.F3.StepDMin.falseEnvU_classGD,
  ``Rcic.F3.StepDMin.tierF3Concl_falseEnvU,
  ``Rcic.F3.StepDMin.drEnvWfT_ddispatch,
  ``Rcic.F3.StepDMin.drEnvWfT_dArm_nonempty
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_stepd_min_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_stepd_min_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_stepd_min_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.StepDMinSeal

import Lean
import rcic.RcicF3TierGroup

/-!
# F3 tier group-granular record seal

`closure_claim = 0`.

Bounded seal for `rcic.RcicF3TierGroup`. Every declaration listed below must
depend on no axiom outside `propext` and `Quot.sound`; the `run_cmd` refuses
otherwise. Named open debts of the restated face: `StepAG`, `StepDG` (group
steps), `StepWField` (W row); the fixture remainder `DrRoleBridge`.
-/

namespace Rcic.F3.TierGroupSeal

open Lean

def sealedTheorems : List Name := [
  ``Rcic.F3.TierGroup.GroupStepAt,
  ``Rcic.F3.TierGroup.StepAG,
  ``Rcic.F3.TierGroup.StepDG,
  ``Rcic.F3.TierGroup.StepWField,
  ``Rcic.F3.TierGroup.PartitionStepsG,
  ``Rcic.F3.TierGroup.walkAgree_of_stepW,
  ``Rcic.F3.TierGroup.gInv_group_noAD,
  ``Rcic.F3.TierGroup.groupStepAt_of_noAD,
  ``Rcic.F3.TierGroup.groupStepAt_of_AD,
  ``Rcic.F3.TierGroup.walkG_of_stepW,
  ``Rcic.F3.TierGroup.gInvSteps_of_partitionStepsG,
  ``Rcic.F3.TierGroup.gInv_of_partitionStepsG,
  ``Rcic.F3.TierGroup.false_of_walkG_gInv,
  ``Rcic.F3.TierGroup.tierF3Uncond_of_partitionStepsG,
  ``Rcic.F3.TierGroup.partitionStepsG_of_hyp,
  ``Rcic.F3.TierGroup.tierF3Uncond_of_AD_W,
  ``Rcic.F3.TierGroup.tierF3_of_AD_W,
  ``Rcic.F3.TierGroup.kernelSoundnessTierUncond_of_AD_W,
  ``Rcic.F3.TierGroup.groupStepAt_of_partitionSteps,
  ``Rcic.F3.TierGroup.partitionStepsG_of_partitionSteps,
  ``Rcic.F3.TierGroup.stepDG_of_stepDHyp,
  ``Rcic.F3.TierGroup.stepAt_of_gInv,
  ``Rcic.F3.TierGroup.NoAD,
  ``Rcic.F3.TierGroup.gInv_of_noAD,
  ``Rcic.F3.TierGroup.consistent4_noAD,
  ``Rcic.F3.TierGroup.falseEnvU_noAD,
  ``Rcic.F3.TierGroup.tierConcl_falseEnvU_noAD,
  ``Rcic.F3.TierGroup.drGroup_dArm,
  ``Rcic.F3.TierGroup.gInv_drBase,
  ``Rcic.F3.TierGroup.drAgree,
  ``Rcic.F3.TierGroup.stepDAt_drEnv_iff,
  ``Rcic.F3.TierGroup.gInvD_drEnv,
  ``Rcic.F3.TierGroup.DrRoleBridge,
  ``Rcic.F3.TierGroup.stepDAt_drEnv_of_bridge,
  ``Rcic.F3.TierGroup.w_fieldShapes_generic,
  ``Rcic.F3.TierGroup.w_family,
  ``Rcic.F3.TierGroup.w_fields,
  ``Rcic.F3.TierGroup.w_shapes,
  ``Rcic.F3.TierGroup.w_pendA,
  ``Rcic.F3.TierGroup.wGroup_aArm,
  ``Rcic.F3.TierGroup.gInv_natEnvU,
  ``Rcic.F3.TierGroup.gInv_wEnv_of_stepAAt
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_tiergroup_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_tiergroup_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_tiergroup_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.TierGroupSeal

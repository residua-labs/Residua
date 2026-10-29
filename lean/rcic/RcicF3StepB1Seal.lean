import Lean
import rcic.RcicF3StepB1

/-!
# F3 stepB1 discharge seal

`closure_claim = 0`.

Bounded seal for `rcic.RcicF3StepB1`. Every declaration listed below must
depend on no axiom outside `propext` and `Quot.sound`; the `run_cmd` refuses
otherwise. No named hypothesis is introduced: `stepB1_proved` is the
`PartitionSteps.stepB1` field itself, and the tier wrappers take only the A/D
rows and glm's `StepWHyp`.
-/

namespace Rcic.F3.StepB1Seal

open Lean

def sealedTheorems : List Name := [
  ``Rcic.F3.PSet.posOf_some,
  ``Rcic.F3.PSet.LEq_of_getD,
  ``Rcic.F3.PSet.recon_getD,
  ``Rcic.F3.PSet.idx_pempty_of_ctorFits,
  ``Rcic.F3.PSet.recon_pempty,
  ``Rcic.F3.PSet.recon_of_ctorFits_propTel,
  ``Rcic.F3.PSet.iotaAgree_of_propTel,
  ``Rcic.F3.PSet.iota_at_propB,
  ``Rcic.F3.PSet.rec_member_sound_propB,
  ``Rcic.F3.PSet.recPkg_classB,
  ``Rcic.F3.StepB1.nodeFieldRow_of_notAD,
  ``Rcic.F3.StepB1.stepB1_proved,
  ``Rcic.F3.StepB1.PartitionStepsAD,
  ``Rcic.F3.StepB1.partitionStepsAD_of_ABD,
  ``Rcic.F3.StepB1.partitionStepsABD_of_AD,
  ``Rcic.F3.StepB1.partitionSteps_of_AD_hyp,
  ``Rcic.F3.StepB1.tierF3Uncond_of_AD_hyp,
  ``Rcic.F3.StepB1.kernelSoundnessTierUncond_of_AD_hyp
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_stepb1_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_stepb1_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_stepb1_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.StepB1Seal

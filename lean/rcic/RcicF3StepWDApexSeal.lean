import Lean
import rcic.RcicF3StepWDApex

/-!
# W/D-checked apex seal
Strict audit of local checks, admitted-prefix refusals, both check bridges and
selected-node refactors. A remains explicit; closure_claim = 0.
-/

namespace Rcic.F3.StepWDApexSeal

open Lean Elab Command

def sealedTheorems : List Name := [
  ``Rcic.F3.StepWDApex.groupCheck,
  ``Rcic.F3.StepWDApex.groupCheck_pass_iff,
  ``Rcic.F3.StepWDApex.groupStepAt_of_check,
  ``Rcic.F3.StepWDApex.EnvDChecked,
  ``Rcic.F3.StepWDApex.envCheck,
  ``Rcic.F3.StepWDApex.envCheck_pass_iff,
  ``Rcic.F3.StepWDApex.DCheckSound,
  ``Rcic.F3.StepWDApex.envCheck_sound,
  ``Rcic.F3.StepWDApex.EnvRefusal,
  ``Rcic.F3.StepWDApex.refusalCertificate,
  ``Rcic.F3.StepWDApex.EnvRefusal.side_fails,
  ``Rcic.F3.StepWDApex.envCheck_refusal_certified,
  ``Rcic.F3.StepWDApex.Outcome,
  ``Rcic.F3.StepWDApex.checkEnv,
  ``Rcic.F3.StepWDApex.steps_coveredWDChecked,
  ``Rcic.F3.StepWDApex.TierF3WDChecked,
  ``Rcic.F3.StepWDApex.KernelSoundnessTierWDChecked,
  ``Rcic.F3.StepWDApex.tierF3WDChecked_of_checked,
  ``Rcic.F3.StepWDApex.kernelSoundnessTierWDChecked_of_checked,
  ``Rcic.F3.StepWDApex.kernelSoundnessTierWDChecked_of_A,
  ``Rcic.F3.StepWDApex.wCheckedTier_of_D_complete,
  ``Rcic.F3.StepWDApex.dr_groupCheck_passes,
  ``Rcic.F3.StepWDApex.drKBad_envCheck_refuses,
  ``Rcic.F3.StepWDApex.not_all_envChecks,
  ``Rcic.F3.StepWDApex.EnvRefusal.node,
  ``Rcic.F3.StepWDApex.EnvRefusal.reason,
  ``Rcic.F3.StepWDApex.EnvRefusal.diagnosed,
  ``Rcic.F3.StepWDApex.EnvRefusal.failed,
  ``Rcic.F3.PSet.groupRecNode,
  ``Rcic.F3.PSet.group_rec_node,
  ``Rcic.F3.PSet.groupNode,
  ``Rcic.F3.PSet.group_node,
  ``Rcic.F3.StepDGOrder.gInv_groupRawD_atNode,
  ``Rcic.F3.StepDGOrder.gInv_groupRawD
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_stepwd_apex_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_stepwd_apex_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_stepwd_apex_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.StepWDApexSeal

import Lean
import rcic.RcicF3StepWMin

/-!
# F3 stepW minimal-hypothesis seal

`closure_claim = 0`.

Bounded seal for `rcic.RcicF3StepWMin`. Every declaration listed below must
depend on no axiom outside `propext` and `Quot.sound`; the `run_cmd` refuses
otherwise. `StepWHyp` is a named antecedent (the tier's W-debt guarded down to
the boundary theorem's open arm), not a silently assumed proof; the sealed
theorems are the composition with the landed assembly, the fixture discharge,
and the sort-uniqueness reduction.
-/

namespace Rcic.F3.StepWMinSeal

open Lean

def sealedTheorems : List Name := [
  ``Rcic.F3.StepWMin.uniformProp_or_uniformType,
  ``Rcic.F3.StepWMin.StepWHyp,
  ``Rcic.F3.StepWMin.stepW_of_hyp,
  ``Rcic.F3.StepWMin.hyp_of_steps,
  ``Rcic.F3.StepWMin.partitionSteps_of_hyp,
  ``Rcic.F3.StepWMin.partitionStepsABD_of_steps,
  ``Rcic.F3.StepWMin.tierF3Uncond_of_hyp,
  ``Rcic.F3.StepWMin.kernelSoundnessTierUncond_of_hyp,
  ``Rcic.F3.StepWMin.pwEnvWfT_inScope,
  ``Rcic.F3.StepWMin.stepW_pwEnv,
  ``Rcic.F3.StepWMin.stepW_of_sortUnique
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_stepw_min_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_stepw_min_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_stepw_min_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.StepWMinSeal

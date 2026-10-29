import Lean
import rcic.RcicF3StepWCheck

/-!
# F3 stepW checked side-condition seal

`closure_claim = 0`.

Bounded seal for `rcic.RcicF3StepWCheck`. Every declaration listed below must
depend on no axiom outside `propext` and `Quot.sound`; the `run_cmd` refuses
otherwise. The sealed content: the `StepWHyp` conjecture is replaced by a
decidable check the admission checker runs itself (`AgreeAtDec`,
`WalkAgree (AgreeAtDec np)`, both `Decidable` via `decForallLt` and the two
instances); the per-environment faces (`GroupWChecked`, `EnvWChecked`,
`StepsWAlong`, `stepsWAlong_of_envWChecked`) seal the check actually threaded
down an environment's structure, and `tierF3WChecked_of_abd` discharges
`TierF3WChecked` itself from the interim A/B1/D face alone, by threading
`Covered ∧ EnvWChecked` through the cover machinery's parameterized
`GInvSteps` (zero `StepWChecked` / `StepWHyp` premise); the PRIMARY faces
(`§CG`) target #8237's inhabitable group-granular record
`PartitionStepsG`: `tierF3WChecked_of_ADG` (per-environment, from
`StepAG`/`StepDG` + `EnvWChecked` alone) and
`tierF3Uncond_of_AD_checked` / `kernelSoundnessTierUncond_of_AD_checked`
(checked twins of `TierGroup.tierF3Uncond_of_AD_W`); the global-face
wrappers (`tierF3Uncond_of_checked`, `kernelSoundnessTierUncond_of_checked`)
seal as composition certificates under the strengthened global
`StepWChecked`. Completeness is unconditional too: the former
none-escape residue `[rcic-f3-stepw-leq-complete]` is retired by proof —
`LeqEscape` is empty (`leqEscape_not`), so `decLeN` decides `leN` outright
(`decLeN_complete` / `decLeN_iff`, `stepWChecked_of_hyp`). Expressiveness
untouched (nothing narrowed); the corpus cost is one closed evaluation at one gap position,
now run by `decide` itself (`stepWChecked_eqW`).
-/

namespace Rcic.F3.StepWCheckSeal

open Lean

def sealedTheorems : List Name := [
  ``Rcic.F3.StepWCheck.decLeN,
  ``Rcic.F3.StepWCheck.leN_of_decEqN_max,
  ``Rcic.F3.StepWCheck.decLeN_sound,
  ``Rcic.F3.StepWCheck.decLeN_closed_complete,
  ``Rcic.F3.StepWCheck.decLeN_can_refuse,
  ``Rcic.F3.StepWCheck.decLeN_eqW_gap,
  ``Rcic.F3.StepWCheck.LeqEscape,
  ``Rcic.F3.StepWCheck.leqEscape_of_leq_dec_false,
  ``Rcic.F3.StepWCheck.eqN_max_of_leN,
  ``Rcic.F3.StepWCheck.leqEscape_not,
  ``Rcic.F3.StepWCheck.decLeN_complete,
  ``Rcic.F3.StepWCheck.decLeN_iff,
  ``Rcic.F3.StepWCheck.AgreeAtDec,
  ``Rcic.F3.StepWCheck.decForallLt,
  ``Rcic.F3.StepWCheck.instDecidableAgreeAtDec,
  ``Rcic.F3.StepWCheck.instDecidableWalkAgree,
  ``Rcic.F3.StepWCheck.agreeAt_of_agreeAtDec,
  ``Rcic.F3.StepWCheck.GapLevelsClosed,
  ``Rcic.F3.StepWCheck.agreeAtDec_of_agreeAt_closed,
  ``Rcic.F3.StepWCheck.walkAgree_congr,
  ``Rcic.F3.StepWCheck.GroupWChecked,
  ``Rcic.F3.StepWCheck.EnvWChecked,
  ``Rcic.F3.StepWCheck.stepW_of_groupWChecked,
  ``Rcic.F3.StepWCheck.stepW_of_checked,
  ``Rcic.F3.StepWCheck.StepsWAlong,
  ``Rcic.F3.StepWCheck.stepsWAlong_of_envWChecked,
  ``Rcic.F3.StepWCheck.StepWChecked,
  ``Rcic.F3.StepWCheck.partitionSteps_of_checked,
  ``Rcic.F3.StepWCheck.TierF3WChecked,
  ``Rcic.F3.StepWCheck.nodeStepRow_of_groupWChecked,
  ``Rcic.F3.StepWCheck.walkG_of_coveredWChecked,
  ``Rcic.F3.StepWCheck.steps_coveredWChecked,
  ``Rcic.F3.StepWCheck.tierF3WChecked_of_abd,
  ``Rcic.F3.StepWCheck.walkAgree_of_groupWChecked,
  ``Rcic.F3.StepWCheck.walkG_of_envWChecked,
  ``Rcic.F3.StepWCheck.steps_coveredWChecked_G,
  ``Rcic.F3.StepWCheck.tierF3WChecked_of_ADG,
  ``Rcic.F3.StepWCheck.partitionStepsG_of_checked,
  ``Rcic.F3.StepWCheck.tierF3Uncond_of_AD_checked,
  ``Rcic.F3.StepWCheck.tierF3_of_AD_checked,
  ``Rcic.F3.StepWCheck.kernelSoundnessTierUncond_of_AD_checked,
  ``Rcic.F3.StepWCheck.tierF3Uncond_of_checked,
  ``Rcic.F3.StepWCheck.kernelSoundnessTierUncond_of_checked,
  ``Rcic.F3.StepWCheck.StepWHypClosed,
  ``Rcic.F3.StepWCheck.walkAgreeDec_of_walkAgree,
  ``Rcic.F3.StepWCheck.stepWChecked_of_hyp_closed,
  ``Rcic.F3.StepWCheck.agreeAtDec_of_agreeAt,
  ``Rcic.F3.StepWCheck.walkAgreeDec_of_walkAgree_gen,
  ``Rcic.F3.StepWCheck.stepWChecked_of_hyp,
  ``Rcic.F3.StepWCheck.stepWChecked_eqW
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_stepw_check_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_stepw_check_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_stepw_check_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.StepWCheckSeal

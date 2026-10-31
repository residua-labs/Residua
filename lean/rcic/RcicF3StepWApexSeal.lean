import Lean
import rcic.RcicF3StepWApex

/-!
# W-checked apex seal
Every environment check, refusal certificate, soundness bridge and completeness
statement is audited under the strict policy. A/D debts remain; closure_claim = 0.
-/

namespace Rcic.F3.StepWApexSeal

open Lean Elab Command

def sealedTheorems : List Name := [
  ``Rcic.F3.StepWApex.envCheck,
  ``Rcic.F3.StepWApex.envCheck_pass_iff,
  ``Rcic.F3.StepWApex.EnvCheckSound,
  ``Rcic.F3.StepWApex.envCheck_sound,
  ``Rcic.F3.StepWApex.EnvRefusal,
  ``Rcic.F3.StepWApex.EnvRefusal.reason,
  ``Rcic.F3.StepWApex.refusalCertificate,
  ``Rcic.F3.StepWApex.envCheck_refusal_certified,
  ``Rcic.F3.StepWApex.Outcome,
  ``Rcic.F3.StepWApex.checkEnv,
  ``Rcic.F3.StepWApex.envCheck_complete,
  ``Rcic.F3.StepWApex.all_envChecks_iff_hyp,
  ``Rcic.F3.StepWApex.EnvRefusal.refutes_hyp,
  ``Rcic.F3.StepWApex.TierF3WChecked,
  ``Rcic.F3.StepWApex.KernelSoundnessTierWChecked,
  ``Rcic.F3.StepWApex.tierF3WChecked_of_AD,
  ``Rcic.F3.StepWApex.kernelSoundnessTierWChecked_of_checked,
  ``Rcic.F3.StepWApex.kernelSoundnessTierWChecked_of_AD,
  ``Rcic.F3.StepWApex.uncheckedTier_of_complete
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_stepw_apex_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_stepw_apex_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_stepw_apex_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.StepWApexSeal

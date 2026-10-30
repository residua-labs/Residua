import Lean
import rcic.RcicF3StepWRefusal

/-!
# Exact W diagnostic seal
Audits the local decision interface and its conditional global adapter.
No theorem that all checks pass is supplied. closure_claim = 0.
-/

namespace Rcic.F3.StepWRefusalSeal

open Lean Elab Command

def sealedTheorems : List Name := [
  ``Rcic.F3.StepWRefusal.Refusal,
  ``Rcic.F3.StepWRefusal.instDecidableEqRefusal,
  ``Rcic.F3.StepWRefusal.instReprRefusal,
  ``Rcic.F3.StepWRefusal.Refusal.residue,
  ``Rcic.F3.StepWRefusal.refusalOf,
  ``Rcic.F3.StepWRefusal.refusalOf_none_iff,
  ``Rcic.F3.StepWRefusal.refusalOf_gapSortBound_iff,
  ``Rcic.F3.StepWRefusal.agrees_of_none,
  ``Rcic.F3.StepWRefusal.checked_of_agrees,
  ``Rcic.F3.StepWRefusal.openArm_none_iff,
  ``Rcic.F3.StepWRefusal.openArm_refusal_iff,
  ``Rcic.F3.StepWRefusal.refusal_refutes_hyp,
  ``Rcic.F3.StepWRefusal.all_checks_iff_hyp,
  ``Rcic.F3.StepWRefusal.stepWChecked_of_all_checks,
  ``Rcic.F3.StepWRefusal.eqW_no_refusal
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_stepw_refusal_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_stepw_refusal_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_stepw_refusal_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.StepWRefusalSeal

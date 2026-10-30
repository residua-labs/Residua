import Lean
import rcic.RcicF3StepWGroup

/-!
# Exact group W decision seal
Audits the original GroupWChecked decision and its named refusal interface.
Global W remains an explicit premise. closure_claim = 0.
-/

namespace Rcic.F3.StepWGroupSeal

open Lean Elab Command

def sealedTheorems : List Name := [
  ``Rcic.F3.StepWGroup.recursorResult_head,
  ``Rcic.F3.StepWGroup.recursorCut_unique,
  ``Rcic.F3.StepWGroup.nodeCut_unique,
  ``Rcic.F3.StepWGroup.nodeResult_unique,
  ``Rcic.F3.StepWGroup.groupRefusal,
  ``Rcic.F3.StepWGroup.groupRefusal_none_iff,
  ``Rcic.F3.StepWGroup.decideGroup,
  ``Rcic.F3.StepWGroup.groupRefusal_cases,
  ``Rcic.F3.StepWGroup.groupRefusal_refusal_iff,
  ``Rcic.F3.StepWGroup.AllGroupChecks,
  ``Rcic.F3.StepWGroup.all_groupChecks_iff_checked,
  ``Rcic.F3.StepWGroup.all_groupChecks_iff_hyp,
  ``Rcic.F3.StepWGroup.stepWChecked_of_all_groupChecks,
  ``Rcic.F3.StepWGroup.groupRefusal_refutes_hyp,
  ``Rcic.F3.StepWGroup.eqW_group_no_refusal,
  ``Rcic.F3.StepWGroup.BadSortPair,
  ``Rcic.F3.StepWGroup.refusal_has_badSortPair
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_stepw_group_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_stepw_group_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_stepw_group_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.StepWGroupSeal

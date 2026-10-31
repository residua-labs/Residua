import Lean
import rcic.RcicF3StepWOpen

/-!
# StepW local non-vacuity and global-equivalence seal

Every public declaration below is audited against {propext, Quot.sound}.
No global W producer or global consistency result is asserted.
closure_claim = 0.
-/

namespace Rcic.F3.StepWOpenSeal

open Lean Elab Command

def sealedTheorems : List Name := [
  ``Rcic.F3.StepWOpen.OpenArm,
  ``Rcic.F3.StepWOpen.OpenArm.Agrees,
  ``Rcic.F3.StepWOpen.OpenArm.Checked,
  ``Rcic.F3.StepWOpen.eqWOpenArm,
  ``Rcic.F3.StepWOpen.openArm_nonempty,
  ``Rcic.F3.StepWOpen.eqWOpenArm_agrees,
  ``Rcic.F3.StepWOpen.eqWOpenArm_not_refutation,
  ``Rcic.F3.StepWOpen.hyp_of_stepWChecked,
  ``Rcic.F3.StepWOpen.stepWChecked_iff_hyp,
  ``Rcic.F3.StepWOpen.hyp_iff_all_openArm,
  ``Rcic.F3.StepWOpen.global_nonvacuity_iff,
  ``Rcic.F3.StepWOpen.Counterexample,
  ``Rcic.F3.StepWOpen.counterexample_refutes_hyp,
  ``Rcic.F3.StepWOpen.diagonal_sortExcursion,
  ``Rcic.F3.StepWOpen.noExcursion_refuted,
  ``Rcic.F3.StepWOpen.ctorEnvironment_before_rec,
  ``Rcic.F3.StepWOpen.walk_entry_double_typed_before_rec,
  ``Rcic.F3.StepWOpen.prefix_iota_members_old,
  ``Rcic.F3.StepWOpen.derivedIota_before_rec_iff,
  ``Rcic.F3.StepWOpen.freshFamily_typing_does_not_restrict
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_stepw_open_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_stepw_open_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_stepw_open_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.StepWOpenSeal

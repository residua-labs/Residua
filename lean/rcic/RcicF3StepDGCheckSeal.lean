import Lean
import rcic.RcicF3StepDGCheck

/-!
# F3 StepDG check seal

`closure_claim = 0`.

Bounded seal for `rcic.RcicF3StepDGCheck`. Every declaration listed
below must depend on no axiom outside `propext` and `Quot.sound`; the
`run_cmd` refuses otherwise. The module delivers the per-node checked
side condition (`ctorParamsEqB`/`propCornerB`/`ctorsBelowRecB` and the
packaged `stepDGSideB` with exact iffs), the named refusal
(`StepDGRefusal`/`stepDGRefusalOf`), the domain-guarded checked face
(`StepDGChecked` → `stepDG_of_checked`), the `accP` refusal tooth, and
the δ-fixture measurements (`drSide_iff`, `drKBad_*`,
`gInv_drEnv_of_stepDG`), per the module header.
-/

namespace Rcic.F3.StepDGCheckSeal

open Lean

def sealedTheorems : List Name := [
  ``Rcic.F3.StepDGCheck.allFin,
  ``Rcic.F3.StepDGCheck.allFin_iff,
  ``Rcic.F3.StepDGCheck.finSearch,
  ``Rcic.F3.StepDGCheck.allFin_false_iff,
  ``Rcic.F3.StepDGCheck.listAll_false_iff,
  ``Rcic.F3.StepDGCheck.bnot_true,
  ``Rcic.F3.StepDGCheck.bnot_false,
  ``Rcic.F3.StepDGCheck.bool_not_true,
  ``Rcic.F3.StepDGCheck.bool_not_false,
  ``Rcic.F3.StepDGCheck.ctorParamsEqB,
  ``Rcic.F3.StepDGCheck.ctorParamsEqB_iff,
  ``Rcic.F3.StepDGCheck.ctorParamsEq_dec,
  ``Rcic.F3.StepDGCheck.fieldsFreeB,
  ``Rcic.F3.StepDGCheck.fieldsFreeB_iff,
  ``Rcic.F3.StepDGCheck.fieldsFreeB_false_iff,
  ``Rcic.F3.StepDGCheck.unrevealedB,
  ``Rcic.F3.StepDGCheck.unrevealedB_iff,
  ``Rcic.F3.StepDGCheck.unrevealedB_false_iff,
  ``Rcic.F3.StepDGCheck.cornerConsequentB,
  ``Rcic.F3.StepDGCheck.cornerConsequentB_iff,
  ``Rcic.F3.StepDGCheck.propCornerB,
  ``Rcic.F3.StepDGCheck.propCornerB_iff,
  ``Rcic.F3.StepDGCheck.propCornerB_false_iff,
  ``Rcic.F3.StepDGCheck.propCorner_dec,
  ``Rcic.F3.StepDGCheck.stepDGSideB,
  ``Rcic.F3.StepDGCheck.stepDGSideB_iff,
  ``Rcic.F3.StepDGCheck.stepDGSide_dec,
  ``Rcic.F3.StepDGCheck.StepDGRefusal,
  ``Rcic.F3.StepDGCheck.stepDGRefusalOf,
  ``Rcic.F3.StepDGCheck.stepDGRefusalOf_none_iff,
  ``Rcic.F3.StepDGCheck.stepDGRefusalOf_some_iff,
  ``Rcic.F3.StepDGCheck.StepDGChecked,
  ``Rcic.F3.StepDGCheck.stepDG_of_checked,
  ``Rcic.F3.StepDGCheck.stepDGChecked_complete,
  ``Rcic.F3.StepDGCheck.ctorsBelowRec_eq_of_recBelow,
  ``Rcic.F3.StepDGCheck.accPNode,
  ``Rcic.F3.StepDGCheck.accP_pendA,
  ``Rcic.F3.StepDGCheck.accP_pendC,
  ``Rcic.F3.StepDGCheck.accP_propCorner_refuses,
  ``Rcic.F3.StepDGCheck.accP_propCorner_refuses_of_pendC,
  ``Rcic.F3.StepDGCheck.accP_ctorParamsEq,
  ``Rcic.F3.StepDGCheck.accP_stepDGSide_refuses,
  ``Rcic.F3.StepDGCheck.accP_refusal_named,
  ``Rcic.F3.StepDGCheck.accP_domain_guard_fails,
  ``Rcic.F3.StepDGCheck.accP_sideG_vacuous,
  ``Rcic.F3.StepDGCheck.drSide_iff,
  ``Rcic.F3.StepDGCheck.drKBad,
  ``Rcic.F3.StepDGCheck.drKBad_boundG,
  ``Rcic.F3.StepDGCheck.drKBad_boundDG,
  ``Rcic.F3.StepDGCheck.drKBad_recBelowCtors,
  ``Rcic.F3.StepDGCheck.drKBad_refuses,
  ``Rcic.F3.StepDGCheck.drKBad_side_fails,
  ``Rcic.F3.StepDGCheck.gInv_drEnv_of_stepDG,
  ``Rcic.F3.StepDGCheck.gInv_drEnv_of_stepDG_flat,
  ``Rcic.F3.StepDGCheck.drEnv_check_fires
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_stepdg_check_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_stepdg_check_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_stepdg_check_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.StepDGCheckSeal

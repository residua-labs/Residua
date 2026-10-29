import Lean
import rcic.RcicF3StepDGRec

/-!
# F3 StepDG rec seal

`closure_claim = 0`.

Bounded seal for `rcic.RcicF3StepDGRec`. Every declaration listed below
must depend on no axiom outside `propext` and `Quot.sound`; the `run_cmd`
refuses otherwise. The module delivers the bounded recursor chain in the
raw roles (`rec_stepDB`/`rec_stageDB`/`rec_fields_okDB`/`minor_ok_groupDB`/
`recVal_mem_recDB`/`recVal_mem_recPDB`), the bounded constructor soundness
(`ctor_member_soundB`), the checked order `CtorsBelowRec`, the raw-role
group step (`gInv_groupRawD`), and `StepDG` under the checked side
condition (`stepDG_under`), per the module header.
-/

namespace Rcic.F3.StepDGRecSeal

open Lean

def sealedTheorems : List Name := [
  ``Rcic.F3.StepDGOrder.noFunRec_of_not_pendA,
  ``Rcic.F3.StepDGOrder.canonL_bounded,
  ``Rcic.F3.StepDGOrder.canonL_length,
  ``Rcic.F3.StepDGOrder.upd_self,
  ``Rcic.F3.StepDGOrder.limB,
  ``Rcic.F3.StepDGOrder.den_self_recApp,
  ``Rcic.F3.StepDGOrder.ed_self_of_lim,
  ``Rcic.F3.StepDGOrder.ed_lim_of_self,
  ``Rcic.F3.StepDGOrder.famLE_lim_self,
  ``Rcic.F3.StepDGOrder.famμ_of_limDB,
  ``Rcic.F3.StepDGOrder.rec_stepDB,
  ``Rcic.F3.StepDGOrder.rec_stageDB,
  ``Rcic.F3.StepDGOrder.rec_fields_okDB,
  ``Rcic.F3.StepDGOrder.minor_ok_groupDB,
  ``Rcic.F3.StepDGOrder.recVal_mem_recDB,
  ``Rcic.F3.StepDGOrder.recVal_mem_recPDB,
  ``Rcic.F3.StepDGOrder.ctor_member_soundB,
  ``Rcic.F3.StepDGOrder.CtorsBelowRec,
  ``Rcic.F3.StepDGOrder.ctorsBelowRecB,
  ``Rcic.F3.StepDGOrder.ctorsBelowRecB_true,
  ``Rcic.F3.StepDGOrder.ctorsBelowRecB_eq_true,
  ``Rcic.F3.StepDGOrder.ctorsBelowRec_dec,
  ``Rcic.F3.StepDGOrder.gInv_groupRawD,
  ``Rcic.F3.StepDGOrder.StepDGSide,
  ``Rcic.F3.StepDGOrder.StepDGSideG,
  ``Rcic.F3.StepDGOrder.stepDG_at,
  ``Rcic.F3.StepDGOrder.stepDG_under
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_stepdg_rec_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_stepdg_rec_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_stepdg_rec_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.StepDGRecSeal

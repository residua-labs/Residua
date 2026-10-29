import Lean
import rcic.RcicF3EqDRoleBridge

/-!
# F3 D role bridge seal

`closure_claim = 0`.

Bounded seal for `rcic.RcicF3EqDRoleBridge`. Every declaration listed below
must depend on no axiom outside `propext` and `Quot.sound`; the `run_cmd`
refuses otherwise. This module closes the fixture remainder named by
`RcicF3TierGroupSeal` (`DrRoleBridge`): the general `StepDG` beyond the
fixture remains owed, with the measured boundary recorded in §7 of the
module.
-/

namespace Rcic.F3.TierGroupSeal.DRoleBridge

open Lean

def sealedTheorems : List Name := [
  ``Rcic.F3.TierGroup.drRawFam,
  ``Rcic.F3.TierGroup.drRawFam_shape,
  ``Rcic.F3.TierGroup.drField_norm_cases,
  ``Rcic.F3.TierGroup.drNormFam,
  ``Rcic.F3.TierGroup.drNormFam_shape,
  ``Rcic.F3.TierGroup.drIdVal,
  ``Rcic.F3.TierGroup.drId_fapp,
  ``Rcic.F3.TierGroup.DrFamShape,
  ``Rcic.F3.TierGroup.drRawFam_DrFamShape,
  ``Rcic.F3.TierGroup.drNormFam_DrFamShape,
  ``Rcic.F3.TierGroup.drFamType,
  ``Rcic.F3.TierGroup.drFibre_field,
  ``Rcic.F3.TierGroup.drTabIter_zero_base,
  ``Rcic.F3.TierGroup.drTabIter_zero_entry,
  ``Rcic.F3.TierGroup.drTabIter_succ_entry,
  ``Rcic.F3.TierGroup.drTabIter_entry_code,
  ``Rcic.F3.TierGroup.drFieldRaw_step,
  ``Rcic.F3.TierGroup.drFieldNorm_step,
  ``Rcic.F3.TierGroup.drIter_empty,
  ``Rcic.F3.TierGroup.drFamLim_empty,
  ``Rcic.F3.TierGroup.drFamLim_eq,
  ``Rcic.F3.TierGroup.DrDataAgree,
  ``Rcic.F3.TierGroup.DrDataAgree.get,
  ``Rcic.F3.TierGroup.DrDataAgree.get_none,
  ``Rcic.F3.TierGroup.DrDataAgree.ihArgs_eq,
  ``Rcic.F3.TierGroup.DrDataAgree.nfOf_agree,
  ``Rcic.F3.TierGroup.DrDataAgree.recBody_eq,
  ``Rcic.F3.TierGroup.DrDataAgree.recCore_eq,
  ``Rcic.F3.TierGroup.DrDataAgree.ctorEnd_eq,
  ``Rcic.F3.TierGroup.DrDataAgree.recEnd_eq,
  ``Rcic.F3.TierGroup.drDataAgree,
  ``Rcic.F3.TierGroup.drEnv_members,
  ``Rcic.F3.TierGroup.drFaithfulD,
  ``Rcic.F3.TierGroup.drRoleBridge,
  ``Rcic.F3.TierGroup.stepDAt_drEnv_uncond,
  ``Rcic.F3.TierGroup.RoleBridgeEnv,
  ``Rcic.F3.TierGroup.gInv_of_roleBridgeEnv,
  ``Rcic.F3.TierGroup.roleBridgeEnv_drEnv
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_eq_drolebridge_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_eq_drolebridge_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_eq_drolebridge_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.TierGroupSeal.DRoleBridge

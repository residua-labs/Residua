import Lean
import rcic.RcicF3StepAObstr

/-!
# F3 `StepAG` obstruction-side seal

`closure_claim = 0`.

Bounded seal for `rcic.RcicF3StepAObstr`. Every declaration listed below
must depend on no axiom outside `propext` and `Quot.sound`; the `run_cmd`
refuses otherwise. Named open debts of this face: the famfix cell
(`FamKTBridge`, residue `[rcic-f3-stepa-famfix]` — the producer lane's
lfp-agreement target) and the KT recursor package (membership at the KT
table); ι at the `wEnv` fixture is EMPTY (`iotaAt_wEnv_vacuous`), and the
checked side condition is `CtorWitOK` (residue
`[rcic-f3-stepa-witness-shapes]`).
-/

namespace Rcic.F3.StepAObstrSeal

open Lean

def sealedTheorems : List Name := [
  ``Rcic.F3.StepAObstr.WitDirect,
  ``Rcic.F3.StepAObstr.CtorWitOK,
  ``Rcic.F3.StepAObstr.iota_at_of_witDirect,
  ``Rcic.F3.StepAObstr.noWitness_wEnv,
  ``Rcic.F3.StepAObstr.iotaAt_wEnv_vacuous,
  ``Rcic.F3.StepAObstr.FamFixW,
  ``Rcic.F3.StepAObstr.FamKTBridge,
  ``Rcic.F3.StepAObstr.famFixW_of_bridge,
  ``Rcic.F3.StepAObstr.RecStepCtxA,
  ``Rcic.F3.StepAObstr.gInv_group_ofAt_A,
  ``Rcic.F3.StepAObstr.stepAAt_of_A,
  ``Rcic.F3.StepAObstr.stepAG_of_cells
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_stepa_obstr_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_stepa_obstr_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_stepa_obstr_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.StepAObstrSeal

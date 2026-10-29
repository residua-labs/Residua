import Lean
import rcic.RcicF3StepDGOrder

/-!
# F3 StepDG order seal

`closure_claim = 0`.

Bounded seal for `rcic.RcicF3StepDGOrder`. Every declaration listed below
must depend on no axiom outside `propext` and `Quot.sound`; the `run_cmd`
refuses otherwise. The module breaks the stage-table / `EnvSound` cycle named
by `RcicF3EqDRoleBridge` §7 by an order (base invariant at every stage table,
the family member by membership, no fixed point assumed) and delivers the raw
D chain's control at every instance within the recursor's bound
(`famLim_raw_norm`, `famB_raw`, `groupFaithB_raw`). The unguarded `StepDG`
itself is not claimed here (the recursor/constructor assembly and the
instances above the recursor's bound remain, per the module header).
-/

namespace Rcic.F3.StepDGOrderSeal

open Lean

def sealedTheorems : List Name := [
  ``Rcic.F3.StepDGOrder.envCtx_freshT,
  ``Rcic.F3.StepDGOrder.readsOKAlong_envCtxT,
  ``Rcic.F3.StepDGOrder.readsClosed_envCtx,
  ``Rcic.F3.StepDGOrder.faithfulR_upd_fresh,
  ``Rcic.F3.StepDGOrder.famType_refs_ne,
  ``Rcic.F3.StepDGOrder.den_famType_upd,
  ``Rcic.F3.StepDGOrder.famZero_mem,
  ``Rcic.F3.StepDGOrder.famIter_mem,
  ``Rcic.F3.StepDGOrder.famLim_mem,
  ``Rcic.F3.StepDGOrder.fam_member_sound_of_mem,
  ``Rcic.F3.StepDGOrder.canonL_map_σOf,
  ``Rcic.F3.StepDGOrder.famEnd_upd_equiv,
  ``Rcic.F3.StepDGOrder.small_recApp_of_equiv,
  ``Rcic.F3.StepDGOrder.DStage,
  ``Rcic.F3.StepDGOrder.canon_eq_of_length,
  ``Rcic.F3.StepDGOrder.famIter_raw_norm,
  ``Rcic.F3.StepDGOrder.famLim_raw_norm,
  ``Rcic.F3.StepDGOrder.famB_raw,
  ``Rcic.F3.StepDGOrder.dStage_of,
  ``Rcic.F3.StepDGOrder.fam_member_sound_raw,
  ``Rcic.F3.StepDGOrder.groupFaithB_raw
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_stepdg_order_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_stepdg_order_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_stepdg_order_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.StepDGOrderSeal

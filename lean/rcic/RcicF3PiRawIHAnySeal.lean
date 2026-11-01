import Lean
import rcic.RcicF3PiRawIHAnyAttack
/-! Strict arbitrary-sort raw IH component seal. No universal A closure.
`closure_claim = 0`. -/
namespace Rcic.F3.PiRawIHAnySeal
open Lean Elab Command

def sealedTheorems : List Name := [
  ``Rcic.F3.PSet.PiRawMotiveAny.carrier,
  ``Rcic.F3.PSet.PiRawMotiveAny.elements,
  ``Rcic.F3.PSet.PiRawMotiveAny.guarded,
  ``Rcic.F3.PSet.PiRawMotiveAny.guarded_dich,
  ``Rcic.F3.PSet.PiRawMotiveAny.mem_carrier,
  ``Rcic.F3.PSet.PiRawMotiveAny.elements_key,
  ``Rcic.F3.PSet.PiRawMotiveAny.guarded_key,
  ``Rcic.F3.PSet.PiRawMotiveAny.guarded_resp,
  ``Rcic.F3.PSet.PiRawMotiveAny.guarded_unused,
  ``Rcic.F3.PSet.PiRawMotiveAny.motive_mem_U,
  ``Rcic.F3.PSet.PiRawMotiveAny.policy_key,
  ``Rcic.F3.PSet.PiRawIHAny.normalized_spec,
  ``Rcic.F3.PSet.PiRawIHAny.builder_spec,
  ``Rcic.F3.PSet.PiRawIHAny.builder_original,
  ``Rcic.F3.PSet.PiRawIHAny.rawFamily_spec,
  ``Rcic.F3.PSet.PiRawIHAny.rawFamily_builder_original,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.datum,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.domain,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.σ,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.v,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.domain_dich,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.type_mem,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.motive,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.assignment,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.motive_mem,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.motive_apply,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.field_mem,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.leaf,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.inhabited,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.unused_arity,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.invalid_index_guard,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.used_key,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.complete_key_required,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.hidden_data_builders,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.indexed_data_insertion,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.param_motive,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.param_before,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.param_value,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.param_context,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.original_data_builder,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.type_not_prop,
  ``Rcic.F3.PSet.PiRawIHAnyAttack.old_guard_refuted
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[pi_raw_ih_any_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[pi_raw_ih_any_seal] {t} depends on {ax}"
  logInfo m!"[pi_raw_ih_any_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"
end Rcic.F3.PiRawIHAnySeal

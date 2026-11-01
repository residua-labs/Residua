import Lean
import rcic.RcicF3AReaderClosureSeal
import rcic.RcicF3AccBoundScopeAttack
import rcic.RcicF3PropEvalSafeIndex
import rcic.RcicF3IndexedFieldBounds
import rcic.RcicF3IndexedBoundNormalization
import rcic.RcicF3PropEvalSafeIndexAttack
import rcic.RcicF3ARefusalSurfaceContract

/-!
Exact inventory for the AccP bound obstruction, safe-index comparison,
ordinary-row broadening, normalization and same-P adversarial composition.
Every private and compiler-generated declaration is included.
closure_claim = 0; scope_closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.ARefusalSurfaceSeal
open Lean Elab Command

def sealedModules : List Name := [
  `rcic.RcicF3AccBoundScopeAttack,
  `rcic.RcicF3PropEvalSafeIndex,
  `rcic.RcicF3IndexedFieldBounds,
  `rcic.RcicF3IndexedBoundNormalization,
  `rcic.RcicF3PropEvalSafeIndexAttack,
  `rcic.RcicF3ARefusalSurfaceContract
]

def sealedTheoremsRaw : String := " ".intercalate [
  "Rcic.F3.PSet.AccBoundScopeAttack.prefixTable._cstage1",
  "Rcic.F3.PSet.AccBoundScopeAttack.prefixTable._lambda_1._closed_1._cstage2",
  "Rcic.F3.PSet.AccBoundScopeAttack.component_witness",
  "Rcic.F3.PSet.AccBoundScopeAttack.boundG_refuted",
  "Rcic.F3.PSet.AccBoundScopeAttack.no_bounded_prop_sort",
  "Rcic.F3.PSet.AccBoundScopeAttack.boundG_index_obligation",
  "Rcic.F3.PSet.AccBoundScopeAttack.family_value",
  "Rcic.F3.PSet.AccBoundScopeAttack.prefixTable._closed_4._cstage2",
  "Rcic.F3.PSet.AccBoundScopeAttack.zeroTable._cstage1",
  "Rcic.F3.PSet.AccBoundScopeAttack.prefixTable",
  "Rcic.F3.PSet.AccBoundScopeAttack.prefixTable._cstage2",
  "Rcic.F3.PSet.AccBoundScopeAttack.prefix_sound",
  "Rcic.F3.PSet.AccBoundScopeAttack.boundG_index_obligation.match_1",
  "Rcic.F3.PSet.AccBoundScopeAttack.prefixTable._closed_3._cstage2",
  "Rcic.F3.PSet.AccBoundScopeAttack.prefix_member_cases",
  "Rcic.F3.PSet.AccBoundScopeAttack.prop_universe_not_prop",
  "Rcic.F3.PSet.AccBoundScopeAttack.relation_sound",
  "Rcic.F3.PSet.AccBoundScopeAttack.zeroTable",
  "Rcic.F3.PSet.AccBoundScopeAttack.prefixTable._closed_2._cstage2",
  "Rcic.F3.PSet.AccBoundScopeAttack.prefixTable._lambda_1._cstage2",
  "Rcic.F3.PSet.AccBoundScopeAttack.relation_value",
  "Rcic.F3.PSet.AccBoundScopeAttack.prefix_no_constructor",
  "Rcic.F3.PSet.AccBoundScopeAttack.prefix_allSound",
  "Rcic.F3.PSet.AccBoundScopeAttack.Witness",
  "Rcic.F3.PSet.AccBoundScopeAttack.component_nonrefutable",
  "Rcic.F3.PSet.AccBoundScopeAttack.prefixTable._closed_1._cstage2",
  "Rcic.F3.PSet.AccBoundScopeAttack.family_sound",
  "Rcic.F3.PSet.AccBoundScopeAttack.zeroTable._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndex.witnessFields._cstage1",
  "Rcic.F3.PSet.PropEvalSafeIndex.witnessFields.eq_1",
  "Rcic.F3.PSet.PropEvalSafeIndex.witnessFields._closed_1._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndex.trueCode._cstage1",
  "Rcic.F3.PSet.PropEvalSafeIndex.leq_of_getD.match_1",
  "Rcic.F3.PSet.PropEvalSafeIndex.leq_after_prefix",
  "Rcic.F3.PSet.PropEvalSafeIndex.false_fits",
  "Rcic.F3.PSet.PropEvalSafeIndex.distinct_codes",
  "Rcic.F3.PSet.PropEvalSafeIndex.witnessIndices._closed_1._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndex.trueCode",
  "Rcic.F3.PSet.PropEvalSafeIndex.component_nonrefutable",
  "Rcic.F3.PSet.PropEvalSafeIndex.witness_prefix_sound.match_1",
  "Rcic.F3.PSet.PropEvalSafeIndex.falseCode",
  "Rcic.F3.PSet.PropEvalSafeIndex.plain_result_at_fields_of_bounds",
  "Rcic.F3.PSet.PropEvalSafeIndex.falseCode._closed_1._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndex.true_fits",
  "Rcic.F3.PSet.PropEvalSafeIndex.witnessIndices._closed_2._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndex.leq_map_member.match_1",
  "Rcic.F3.PSet.PropEvalSafeIndex.UnrevealedBounds",
  "Rcic.F3.PSet.PropEvalSafeIndex.leq_of_getD",
  "Rcic.F3.PSet.PropEvalSafeIndex.falseCode._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndex.field_equiv_of_key",
  "Rcic.F3.PSet.PropEvalSafeIndex.field_equiv_pempty_of_typing",
  "Rcic.F3.PSet.PropEvalSafeIndex.witnessFields._closed_2._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndex.selected_fields_safe",
  "Rcic.F3.PSet.PropEvalSafeIndex.trueCode._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndex.witnessFields",
  "Rcic.F3.PSet.PropEvalSafeIndex.witnessTable",
  "Rcic.F3.PSet.PropEvalSafeIndex.functional_of_normalized_bounds",
  "Rcic.F3.PSet.PropEvalSafeIndex.witnessTable._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndex.false_code_not_proof",
  "Rcic.F3.PSet.PropEvalSafeIndex.witness_comparison",
  "Rcic.F3.PSet.PropEvalSafeIndex.witnessIndices._cstage1",
  "Rcic.F3.PSet.PropEvalSafeIndex.UnrevealedBounds.proof_1",
  "Rcic.F3.PSet.PropEvalSafeIndex.functional_of_bounds",
  "Rcic.F3.PSet.PropEvalSafeIndex.witnessFields._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndex.component_witness",
  "Rcic.F3.PSet.PropEvalSafeIndex.bare_field_read",
  "Rcic.F3.PSet.PropEvalSafeIndex.bounds_of_policy",
  "Rcic.F3.PSet.PropEvalSafeIndex.fields_equiv_of_bounds",
  "Rcic.F3.PSet.PropEvalSafeIndex.witnessIndices",
  "Rcic.F3.PSet.PropEvalSafeIndex.fields_equiv_of_normalized_bounds",
  "Rcic.F3.PSet.PropEvalSafeIndex.trueCode._closed_1._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndex.witness_prefix_sound",
  "Rcic.F3.PSet.PropEvalSafeIndex.falseCode._cstage1",
  "Rcic.F3.PSet.PropEvalSafeIndex.trueCode._closed_2._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndex.leq_map_member",
  "Rcic.F3.PSet.PropEvalSafeIndex.UnrevealedBounds.of_all",
  "Rcic.F3.PSet.PropEvalSafeIndex.witness_bounds",
  "Rcic.F3.PSet.PropEvalSafeIndex.Witness",
  "Rcic.F3.PSet.PropEvalSafeIndex.witnessTable._cstage1",
  "Rcic.F3.PSet.PropEvalSafeIndex.witnessIndices._cstage2",
  "Rcic.F3.PSet.IndexedFieldBounds.AllPropRows.proof_1",
  "Rcic.F3.PSet.IndexedFieldBounds.Rows.rec",
  "Rcic.F3.PSet.IndexedFieldBounds.Rows.recOn",
  "Rcic.F3.PSet.IndexedFieldBounds.BoundGIndexed.proof_1",
  "Rcic.F3.PSet.IndexedFieldBounds.accP_recursive_row_bound.match_1",
  "Rcic.F3.PSet.IndexedFieldBounds.OrdinaryBounds",
  "Rcic.F3.PSet.IndexedFieldBounds.Rows.unrevealed",
  "Rcic.F3.PSet.IndexedFieldBounds.Rows.noConfusion",
  "Rcic.F3.PSet.IndexedFieldBounds.BoundGIndexed.proof_3",
  "Rcic.F3.PSet.IndexedFieldBounds.OrdinaryBounds.proof_1",
  "Rcic.F3.PSet.IndexedFieldBounds.BoundGIndexed.proof_4",
  "Rcic.F3.PSet.IndexedFieldBounds.component_nonrefutable",
  "Rcic.F3.PSet.IndexedFieldBounds.of_boundG.match_1",
  "Rcic.F3.PSet.IndexedFieldBounds.Witness",
  "Rcic.F3.PSet.IndexedFieldBounds.Rows.instOK",
  "Rcic.F3.PSet.IndexedFieldBounds.functional_of_boundIndexed",
  "Rcic.F3.PSet.IndexedFieldBounds.Rows",
  "Rcic.F3.PSet.IndexedFieldBounds.Rows.casesOn",
  "Rcic.F3.PSet.IndexedFieldBounds.accP_recursive_row_bound",
  "Rcic.F3.PSet.IndexedFieldBounds.Rows.mk",
  "Rcic.F3.PSet.IndexedFieldBounds.BoundGIndexed._sunfold",
  "Rcic.F3.PSet.IndexedFieldBounds.accP_allProp_refuted",
  "Rcic.F3.PSet.IndexedFieldBounds.BoundGIndexed._unsafe_rec",
  "Rcic.F3.PSet.IndexedFieldBounds.Rows.noConfusionType",
  "Rcic.F3.PSet.IndexedFieldBounds.component_witness",
  "Rcic.F3.PSet.IndexedFieldBounds.accP_rows.match_1",
  "Rcic.F3.PSet.IndexedFieldBounds.Rows.of_allProp",
  "Rcic.F3.PSet.IndexedFieldBounds.envBound",
  "Rcic.F3.PSet.IndexedFieldBounds.accP_rows_at_node",
  "Rcic.F3.PSet.IndexedFieldBounds.AllPropRows",
  "Rcic.F3.PSet.IndexedFieldBounds.BoundGIndexed",
  "Rcic.F3.PSet.IndexedFieldBounds.BoundGIndexed.proof_2",
  "Rcic.F3.PSet.IndexedFieldBounds.of_boundG",
  "Rcic.F3.PSet.IndexedFieldBounds.accP_rows.match_2",
  "Rcic.F3.PSet.IndexedFieldBounds.BoundGIndexed.match_1._cstage1",
  "Rcic.F3.PSet.IndexedFieldBounds.falseEnv_bound",
  "Rcic.F3.PSet.IndexedFieldBounds.accP_rows",
  "Rcic.F3.PSet.IndexedFieldBounds.Rows.ordinary",
  "Rcic.F3.PSet.IndexedFieldBounds.Rows.compare",
  "Rcic.F3.PSet.IndexedFieldBounds.envBound.match_1",
  "Rcic.F3.PSet.IndexedFieldBounds.BoundGIndexed.match_1",
  "Rcic.F3.PSet.IndexedBoundNormalization.original_field_normalized",
  "Rcic.F3.PSet.IndexedBoundNormalization.sort_row_normalizes",
  "Rcic.F3.PSet.IndexedBoundNormalization.bodies_conditions",
  "Rcic.F3.PSet.IndexedBoundNormalization.transparent_facts",
  "Rcic.F3.PSet.IndexedBoundNormalization.den_piTelescope",
  "Rcic.F3.PSet.IndexedBoundNormalization.family_prefix_bodies",
  "Rcic.F3.PSet.IndexedBoundNormalization.sort_row_normalizes.match_1",
  "Rcic.F3.PSet.IndexedBoundNormalization.transparent_facts.match_1",
  "Rcic.F3.PSet.IndexedBoundNormalization.fields_to_raw_of_guarded",
  "Rcic.F3.PSet.IndexedBoundNormalization.Witness",
  "Rcic.F3.PSet.IndexedBoundNormalization.component_nonrefutable",
  "Rcic.F3.PSet.IndexedBoundNormalization.component_witness",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixed_comparison",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixedIndices",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixed_comparison_at_tuple",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixed_witness",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixed_tuple_fits",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixedFields",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.MixedWitness",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixedFields._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixedParameters._closed_2._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixed_bounds",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.revealed_value_not_proof",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixedIndices._cstage1",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.indicesKey",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.full_key_separates_parameters",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixedParameters._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixedIndices._closed_2._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixedFields._closed_1._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.component_nonrefutable",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixedParameters._closed_1._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.indices_only_alias",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixedFields._cstage1",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixedFields.eq_1",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.parameters_true_fit",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.component_witness",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixedParameters._cstage1",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.proof_row_unrevealed",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.fullKey",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixedFields._closed_2._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixedFields._closed_3._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixedIndices._closed_1._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixedIndices._cstage2",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.proofRow.proof_1",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.parameters_false_fit",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixedParameters",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.Witness",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.mixed_not_all_proofs",
  "Rcic.F3.PSet.PropEvalSafeIndexAttack.proofRow",
  "Rcic.F3.PSet.ARefusalSurfaceContract.target",
  "Rcic.F3.PSet.ARefusalSurfaceContract.components_nonrefutable",
  "Rcic.F3.PSet.ARefusalSurfaceContract.target_nonrefutable",
  "Rcic.F3.PSet.ARefusalSurfaceContract.Target",
  "Rcic.F3.PSet.ARefusalSurfaceContract.components",
  "Rcic.F3.PSet.ARefusalSurfaceContract.Components"
]

def sealedTheorems : List Name :=
  (sealedTheoremsRaw.split (· == ' ') |>.map String.toName)

def allowedAxioms : List Name := [``propext, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let mut actual : Array Name := #[]
  for m in sealedModules do
    let some idx := env.getModuleIdx? m
      | throwError "[a_refusal_surface_seal] module {m} is not imported"
    actual := actual ++ env.header.moduleData[idx.toNat]!.constNames
  unless actual.size == sealedTheorems.length do
    throwError "[a_refusal_surface_seal] inventory size {sealedTheorems.length} differs from {actual.size}"
  for n in actual do
    unless sealedTheorems.contains n do
      throwError "[a_refusal_surface_seal] uncovered declaration {n}"
  for n in sealedTheorems do
    unless actual.contains n && env.contains n do
      throwError "[a_refusal_surface_seal] stale or foreign declaration {n}"
  let (_, s) := ((do
    for n in sealedTheorems do CollectAxioms.collect n).run env).run {}
  let bad := s.axioms.filter (fun ax => !allowedAxioms.contains ax)
  unless bad.isEmpty do
    for n in sealedTheorems do
      let (_, st) := ((CollectAxioms.collect n).run env).run {}
      for ax in st.axioms do
        unless allowedAxioms.contains ax do
          throwError "[a_refusal_surface_seal] {n} depends on {ax}"
  logInfo m!"[a_refusal_surface_seal] {sealedTheorems.length} declarations in {sealedModules.length} modules; exact coverage; axioms ⊆ {allowedAxioms}; closure_claim = 0"

end Rcic.F3.ARefusalSurfaceSeal

import Lean
import rcic.RcicNativeTypedModelCovVSeal
import rcic.RcicNativeTypedModelCovWAligned
import rcic.RcicNativeTypedModelCovWArity
import rcic.RcicNativeTypedModelCovWBasicK
import rcic.RcicNativeTypedModelCovWCallBoundary
import rcic.RcicNativeTypedModelCovWControls
import rcic.RcicNativeTypedModelCovWFixtures
import rcic.RcicNativeTypedModelCovWRawAdequacy
import rcic.RcicNativeTypedModelCovWRealized
import rcic.RcicNativeTypedModelCovWRevealed
import rcic.RcicNativeTypedModelCovWValueActions

/-!
# Bounded seal: actual-call K and strict raw value adequacy

All authored CovW public roots are checked below. The Eq free bypass is
excluded by the old fragment; the new raw grammar has no Prop-recursion
constructor. Saturated K observations require the actual native certificates.
Strict raw observations supply matching sort/Pi heads and exact spine fields.
The revealed-field observation bridge has a fully inhabited counterexample,
whose untyped distinguishing demand and normal native reduct are measured.
The full guarded realized matching-head and interpretation bridges stay open.

Eight prior bounded seals and the exact external #7776 replay are checked
separately. Neither full Foundation root is imported. closure_claim = 0.
-/

private def covWRoots : Array Lean.Name := #[
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.ApproxTW,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.ApproxTKW,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.approxTW_forget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.approxTKW_forget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWPropRecIndexed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_raw_of_indexed_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_guarded_of_indexed_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_k_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWMemberArity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWConstsArity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_consts_arity_natExpand_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_hasTy_consts_arity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWMemberArity.mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_consts_arity_mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_consts_arity_levels,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_group_body_arities,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_body_consts_arity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_schema_consts_arity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_trueK_index,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_trueK_common,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_trueK_native_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_trueK_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_trueK_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWAndCanonWitness,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_canon,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_canon_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_index,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_common,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_rhs_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_native_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_read,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_normal_redR_eq,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_indexed_occurrence_not_free,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_indexed_rec_spine_not_free,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_indexed_delta_not_free,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_indexed_schema_not_free,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_indexed_eligible_spine_not_free,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_eligible_indexed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_prefix_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_prefix_no_lambda,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_prefix_observation_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_apart_raw_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_apart_prefix_raw_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWEqApartWitness,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_apart_guard_rejected,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_apart_raw_guarded_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_apart_normal_iff_no_native,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_apart_normal_consequences,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_sort_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_rigid_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_neutral_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_K_eqGap_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_K_apart_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_K_eta_guard_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_K_prefix_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_identity_tower_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_identity_uniform_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_proof_total_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_trueIntro_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_abelCoquand_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_proof_demand_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_proof_demand_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_nat_rec_instance_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_ineligible_prop_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWHo_repaired_instance,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_approxTKW_proj_ctor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWFixtureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_of_indexed_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_natSucc_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_alias_in_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_polyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_alias_extension,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_nat_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_nat_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_eq_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_nat_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_normal_reduct_after_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_normal_reduct_forward,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_forward,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListDemands.append,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_envT_pushArgs_ge,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_demands_push_lookup,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_demands_instPrefix_images,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_raw_actions,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_raw_typed_actions,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_raw_closed_actions,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_raw_closed_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_raw_closed_sort_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_raw_closed_pi_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_raw_closed_ctor_fields,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_prop_indexed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_nat_prop_indexed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_empty_prop_indexed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_from_old,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_forget_old,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.ApproxTKWStage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.ApproxTKWStage.mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_stage_of_indexed_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWRealized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWRealized.forget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_realized_of_indexed_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_realized_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_revealed_projField,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevFam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevCtor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMotTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMinTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevRecTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevRec,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevFamEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevCtorEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevField,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMajor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevFamily,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMotive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMinor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevEnv_wf,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevW,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevP_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevIndex_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevField_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_field_index_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevFamily_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMajor_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_family_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMajor_at_index,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMotive_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMinor_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevCall_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_index_guard,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_common,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_is_revealed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_identity_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_field_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_index_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_field_not_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_not_typed_demand,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_field_normal_readback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_revealed_field_boundary,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListRealizes,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListRealizes.length_eq,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListRealizes.getD,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListRealizes.of_getD,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListRealizes.append,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListRealizes.append_right,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListDemands,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListDemands.length_eq,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListDemands.append_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListDemands.snoc_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fields_of_demand_vectors,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWValueAction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_spine_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_backward,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_lambda,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_app,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_app_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_rigid_const,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_normal_reduct_unique,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_ctor_demand_actual_fields,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_legacy_schema_family_eq,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_nonprop_no_native_k,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_iota_action_instance,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_redR_recMajor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_recursor_call,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_curry,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_recursor
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound]
  for root in covWRoots do
    if !env.contains root then
      throwError "CovW seal: missing declaration {root}"
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "CovW seal: {root} has forbidden axioms {forbidden}"
  logInfo m!"CovW seal: {covWRoots.size} public roots checked; allowed axioms = {allowed}"

#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.ApproxTW
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.ApproxTKW
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.approxTW_forget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.approxTKW_forget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWPropRecIndexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_raw_of_indexed_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_guarded_of_indexed_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_k_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWMemberArity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWConstsArity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_consts_arity_natExpand_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_hasTy_consts_arity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWMemberArity.mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_consts_arity_mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_consts_arity_levels
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_group_body_arities
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_body_consts_arity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_schema_consts_arity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_trueK_index
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_trueK_common
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_trueK_native_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_trueK_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_trueK_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWAndCanonWitness
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_canon
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_canon_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_index
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_common
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_rhs_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_native_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_read
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_andK_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_normal_redR_eq
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_indexed_occurrence_not_free
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_indexed_rec_spine_not_free
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_indexed_delta_not_free
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_indexed_schema_not_free
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_indexed_eligible_spine_not_free
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_eligible_indexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_prefix_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_prefix_no_lambda
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_prefix_observation_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_apart_raw_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_apart_prefix_raw_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWEqApartWitness
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_apart_guard_rejected
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_apart_raw_guarded_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_apart_normal_iff_no_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_apart_normal_consequences
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_sort_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_rigid_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_neutral_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_K_eqGap_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_K_apart_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_K_eta_guard_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_K_prefix_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_identity_tower_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_identity_uniform_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_proof_total_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_trueIntro_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_abelCoquand_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_proof_demand_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_proof_demand_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_nat_rec_instance_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_ineligible_prop_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWHo_repaired_instance
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_approxTKW_proj_ctor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWFixtureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_of_indexed_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_natSucc_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_alias_in_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_polyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_alias_extension
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_nat_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_nat_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_eq_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fixture_nat_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_normal_reduct_after_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_normal_reduct_forward
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_forward
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListDemands.append
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_envT_pushArgs_ge
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_demands_push_lookup
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_demands_instPrefix_images
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_raw_actions
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_raw_typed_actions
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_raw_closed_actions
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_raw_closed_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_raw_closed_sort_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_raw_closed_pi_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_raw_closed_ctor_fields
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_eq_prop_indexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_nat_prop_indexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_empty_prop_indexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_from_old
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_forget_old
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.ApproxTKWStage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.ApproxTKWStage.mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_stage_of_indexed_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWRealized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWRealized.forget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_realized_of_indexed_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_realized_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_revealed_projField
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevFam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevCtor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMotTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMinTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevRecTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevRec
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevFamEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevCtorEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevField
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMajor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevFamily
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMotive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMinor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevEnv_wf
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevW
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevP_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevIndex_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevField_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_field_index_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevFamily_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMajor_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_family_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMajor_at_index
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMotive_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevMinor_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRevCall_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_index_guard
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_common
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_is_revealed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_identity_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_field_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_index_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_field_not_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_not_typed_demand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covWRev_field_normal_readback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_revealed_field_boundary
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListRealizes
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListRealizes.length_eq
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListRealizes.getD
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListRealizes.of_getD
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListRealizes.append
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListRealizes.append_right
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListDemands
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListDemands.length_eq
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListDemands.append_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWListDemands.snoc_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_fields_of_demand_vectors
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.CovWValueAction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_spine_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_backward
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_lambda
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_app
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_app_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_rigid_const
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_normal_reduct_unique
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_ctor_demand_actual_fields
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_legacy_schema_family_eq
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_nonprop_no_native_k
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_iota_action_instance
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_redR_recMajor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_recursor_call
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_curry
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWAudit.covW_value_action_recursor

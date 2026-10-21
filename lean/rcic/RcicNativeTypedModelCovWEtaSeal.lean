import Lean
import rcic.RcicNativeTypedModelCovWTypedSeal
import rcic.RcicNativeTypedModelCovWEtaActions
import rcic.RcicNativeTypedModelCovWEtaAliasControl
import rcic.RcicNativeTypedModelCovWEtaAligned
import rcic.RcicNativeTypedModelCovWEtaBoundary
import rcic.RcicNativeTypedModelCovWEtaControls
import rcic.RcicNativeTypedModelCovWEtaExpansionBoundary
import rcic.RcicNativeTypedModelCovWEtaHoControl
import rcic.RcicNativeTypedModelCovWEtaInverseBoundary
import rcic.RcicNativeTypedModelCovWEtaKGuardControl
import rcic.RcicNativeTypedModelCovWEtaNat
import rcic.RcicNativeTypedModelCovWEtaNatAdequacy

/-!
# Bounded seal: typed eta saturation and the proof-field expansion boundary

The old Nat eta/beta/let mismatch is repaired by actual new observations.
The finite typed eta grammar retains per-call K, positive fixtures and the
ineligible-Prop exclusion. An admitted proof-indexed family supplies the
remaining typed inverse-substitution and direct beta/let expansion failures.
Actual compact typing, native typings and reductions, and realized valuations
are supplied. The general interpreter and fundamental assembler remain open.

All new public roots are listed below. The preceding bounded seals and exact
external replay are checked independently. Neither full Foundation root is
imported. closure_claim = 0.
-/

private def covWEtaRoots : Array Lean.Name := #[
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRawActionCore,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaRawAction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_action_typing,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_action_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_action_app,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_core_of_value,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_action_of_value,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_closed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_instantiated,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_closed_row,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_sort_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_pi_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_spine_fields,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_closed_sort_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_closed_pi_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_demands_of_value,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_closed_ctor_fields,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_empty_app,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_empty_lam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_eta_empty_row,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_type_sort_row,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_empty_graph_typed_sort_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_beta_apply_alias,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_beta_apply_alias_not_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.ApproxTKWEta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_of_old,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.ApproxTKWEtaStage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.ApproxTKWEtaStage.mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_stage_of_old,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaRealized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_realized_of_old,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_realized_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNatFn,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNatExpand,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNatArrow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNatGraph,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNatArrowCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNatFn_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNatExpand_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNatArrow_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_contract,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_expand_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_fn_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_expand_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_arrow_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_fn_guarded,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_expand_guarded,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_arrow_guarded,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_arrow_not_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_graph_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_graph_nonbottom,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_old_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_old_no_lambda,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_raw_no_lambda,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_guarded_no_lambda,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_no_rec_occurrence,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaNatFailureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaNatFailureAt.refutes,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_raw_failure,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_guarded_failure,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_no_raw_conversion_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_no_guarded_conversion_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_same_stage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaFixtureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_of_old,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_natSucc_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_alias_in_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_polyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_alias_extension,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_nat_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_nat_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_eq_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_nat_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_sort_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_rigid_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_neutral_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_K_eqGap_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_trueK_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_andK_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_identity_tower_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_identity_uniform_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_proof_total_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_trueIntro_supply,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_abelCoquand_supply,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_proof_demand_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_proof_demand_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_nat_rec_instance_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvFn,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_source_clean,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_source_not_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_let_not_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_source_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_let_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_beta_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_let_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_step_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_red_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_conversion_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_let_conversion_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_coarse_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_rec_occurrence,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_ineligible_prop_head_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_ineligible_prop_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaHo_type_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaHo_type_observation_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaHo_repaired_instance,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaRigidTerm,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaRigidTerm.lift,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaRigidTerm.foldApps_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaClean,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaCleanEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_clean_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_cleanEnv_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_cleanEnv_cons,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_clean_appSpine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_raw_clean,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_observation_clean,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvBody,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvTarget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvCompact,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvSource,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvLet,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_P_demands_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_body_clean,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_compact_not_clean,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_typed_factor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvBody_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvLetBody_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvTarget_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvSource_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvLet_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_beta_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_let_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_beta_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_let_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_normal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_subst,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_P_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_arg_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_target_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_result_type_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_compact_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_compact_nonbottom,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_proof_demand_rejected,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_untyped_factor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_typed_inverseAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_typed_inverse,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_same_stage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaGuard_fresh_not_uniform,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaEqObservationGate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_eq_observation_gate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_apart_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_etaIndex_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_apart_observation_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_etaIndex_observation_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_K_apart_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_K_eta_guard_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_fn_graph,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_expand_graph,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_shared_graph,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_beta_source,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_let_source,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_beta_let_repaired,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_same_stage_repaired,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_fn_graph_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_expand_graph_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_graph_zero_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_beta_source_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_let_source_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_local_guarded_actions
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound]
  for root in covWEtaRoots do
    if !env.contains root then
      throwError "CovWEta seal: missing declaration {root}"
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "CovWEta seal: {root} has forbidden axioms {forbidden}"
  logInfo m!"CovWEta seal: {covWEtaRoots.size} public roots checked; allowed axioms = {allowed}"

#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRawActionCore
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaRawAction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_action_typing
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_action_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_action_app
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_core_of_value
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_action_of_value
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_closed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_instantiated
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_closed_row
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_sort_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_pi_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_spine_fields
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_closed_sort_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_closed_pi_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_demands_of_value
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaRaw_closed_ctor_fields
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_empty_app
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_empty_lam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_eta_empty_row
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_type_sort_row
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_empty_graph_typed_sort_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_beta_apply_alias
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_beta_apply_alias_not_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.ApproxTKWEta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_of_old
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.ApproxTKWEtaStage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.ApproxTKWEtaStage.mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_stage_of_old
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaRealized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_realized_of_old
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_realized_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNatFn
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNatExpand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNatArrow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNatGraph
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNatArrowCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNatFn_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNatExpand_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNatArrow_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_contract
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_expand_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_fn_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_expand_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_arrow_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_fn_guarded
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_expand_guarded
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_arrow_guarded
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_arrow_not_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_graph_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_graph_nonbottom
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_old_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_old_no_lambda
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_raw_no_lambda
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_guarded_no_lambda
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_no_rec_occurrence
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaNatFailureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaNatFailureAt.refutes
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_raw_failure
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_guarded_failure
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_no_raw_conversion_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_no_guarded_conversion_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_same_stage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaFixtureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_of_old
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_natSucc_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_alias_in_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_polyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_alias_extension
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_nat_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_nat_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_eq_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_fixture_nat_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_sort_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_rigid_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_neutral_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_K_eqGap_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_trueK_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_andK_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_identity_tower_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_identity_uniform_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_proof_total_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_trueIntro_supply
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_abelCoquand_supply
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_proof_demand_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_proof_demand_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_nat_rec_instance_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvFn
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_source_clean
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_source_not_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_let_not_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_source_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_let_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_beta_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_let_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_step_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_red_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_conversion_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_let_conversion_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_coarse_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_rec_occurrence
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_ineligible_prop_head_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_ineligible_prop_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaHo_type_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaHo_type_observation_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaHo_repaired_instance
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaRigidTerm
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaRigidTerm.lift
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaRigidTerm.foldApps_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaClean
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaCleanEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_clean_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_cleanEnv_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_cleanEnv_cons
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_clean_appSpine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_raw_clean
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_observation_clean
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvBody
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvTarget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvCompact
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvSource
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvLet
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_P_demands_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_body_clean
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_compact_not_clean
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_typed_factor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvBody_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvLetBody_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvTarget_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvSource_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInvLet_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_beta_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_let_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_beta_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_let_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_normal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_subst
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_P_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_arg_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_target_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_result_type_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_compact_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_compact_nonbottom
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_proof_demand_rejected
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_untyped_factor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_typed_inverseAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_no_typed_inverse
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaInv_same_stage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaGuard_fresh_not_uniform
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.CovWEtaEqObservationGate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_eq_observation_gate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_apart_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_etaIndex_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_apart_observation_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_etaIndex_observation_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_K_apart_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEta_K_eta_guard_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_fn_graph
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_expand_graph
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_shared_graph
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_beta_source
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_let_source
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_beta_let_repaired
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_same_stage_repaired
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_fn_graph_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_expand_graph_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_graph_zero_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_beta_source_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_let_source_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit.covWEtaNat_local_guarded_actions

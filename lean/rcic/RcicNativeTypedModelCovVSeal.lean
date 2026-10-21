import Lean
import rcic.RcicNativeTypedModelCovUSeal
import rcic.RcicNativeTypedModelW6Iota
import rcic.RcicNativeTypedModelCovVAligned
import rcic.RcicNativeTypedModelCovVBasicK
import rcic.RcicNativeTypedModelCovVControls
import rcic.RcicNativeTypedModelCovVFixtures
import rcic.RcicNativeTypedModelCovVHeadActions
import rcic.RcicNativeTypedModelCovVHo
import rcic.RcicNativeTypedModelCovVNativeHeads
import rcic.RcicNativeTypedModelCovVProjection
import rcic.RcicNativeTypedModelCovVRealized
import rcic.RcicNativeTypedModelCovVRestriction

/-!
# Bounded seal for native-K-aligned observations

The old higher-order Prop observation is excluded, while every retained
control has an actual aligned supply. General projection-to-field observation
transport is one-way and restricted to non-revealed fields. Native head
soundness is supplied only for the explicit literal fragment, plus body-free
rigid constants and recursor prefixes with bottom outputs. The fully saturated
nonbottom recursor action remains open. No general interpreter or fundamental
supplier is asserted. The imported W6 module is the exact landed parallel result.

All authored CovV public roots are checked below. Seven prior bounded seals
and the pinned #7776 replay are checked separately. Neither full Foundation
root is imported into this closure. `closure_claim = 0`.
-/

private def covVRoots : Array Lean.Name := #[
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVPropHeadsNative,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.ApproxTN,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.ApproxTKN,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.approxTN_forget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxT_of_native_heads,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.approxTKN_forget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.approxTKN_forgetN,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxTK_of_native_heads,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.approxTKN_iff_approxTN_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_k_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVTrueWitness,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVAndWitness,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_trueK_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_trueK_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_andK_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_andK_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_sort_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_rigid_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_neutral_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_K_eqGap_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_K_apart_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_K_eta_guard_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_K_prefix_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_identity_tower_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_identity_uniform_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_proof_total_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_trueIntro_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_abelCoquand_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_proof_demand_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_proof_demand_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_nat_rec_instance_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVFixtureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_of_native_heads,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_natSucc_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_alias_in_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_polyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_alias_extension,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_nat_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_nat_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_eq_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_nat_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVNativeHead,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVActionRealization,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_native_head_backward,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_native_head_after_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_native_head_forward,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_redR_foldApps,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_backward,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_forward,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_lambda,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_app,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_app_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_body_free_spine_normal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_rigid_const,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_curry_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_recursor_bottom,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVLambdaFragment,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_lambda_fragment_actions,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_lambda_fragment_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_realized_lambda_fragment_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVHo_rec_family_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVHo_const_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_app_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVHo_foldApps_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVHo_type_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVHo_type_guarded_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVHo_type_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVHo_type_observation_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVHo_repaired_instance,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_eq_native_heads,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_true_native_heads,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_and_native_heads,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_nat_native_heads,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_empty_native_heads,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxT_beta_forward,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxT_lamTel_bvar,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_iotaS_legacy_data,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxT_prop_major_indep,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxT_iota_legacy_prop_forward,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxT_iota_prop_anyMajor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxT_projField_anyMajor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxT_projField_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxTK_proj_ctor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxTN_proj_ctor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxTKN_proj_ctor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_proj_ctor_native_and_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.ApproxTKNStage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.ApproxTKNStage.mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.approxTKNStage_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_stage_of_native_heads,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxTN_lift_intro,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVRealized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVRealized.mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxTN_substT_up,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxTN_substT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVRealized.approxTN,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVRealized.approxTKN_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVRealized.stage_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_realized_bot_of_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_realized_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_realized_of_native_heads,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVRealized.forget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_ineligible_prop_const_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_foldApps_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_ineligible_prop_spine
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound]
  for root in covVRoots do
    if !env.contains root then
      throwError "CovV seal: missing declaration {root}"
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "CovV seal: {root} has forbidden axioms {forbidden}"
  logInfo m!"CovV seal: {covVRoots.size} public roots checked; allowed axioms = {allowed}"

#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVPropHeadsNative
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.ApproxTN
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.ApproxTKN
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.approxTN_forget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxT_of_native_heads
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.approxTKN_forget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.approxTKN_forgetN
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxTK_of_native_heads
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.approxTKN_iff_approxTN_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_k_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVTrueWitness
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVAndWitness
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_trueK_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_trueK_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_andK_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_andK_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_sort_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_rigid_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_neutral_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_K_eqGap_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_K_apart_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_K_eta_guard_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_K_prefix_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_identity_tower_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_identity_uniform_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_proof_total_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_trueIntro_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_abelCoquand_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_proof_demand_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_proof_demand_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_nat_rec_instance_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVFixtureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_of_native_heads
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_natSucc_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_alias_in_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_polyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_alias_extension
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_nat_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_nat_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_eq_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_fixture_nat_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVNativeHead
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVActionRealization
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_native_head_backward
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_native_head_after_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_native_head_forward
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_redR_foldApps
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_backward
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_forward
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_lambda
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_app
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_app_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_body_free_spine_normal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_rigid_const
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_curry_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_action_recursor_bottom
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVLambdaFragment
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_lambda_fragment_actions
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_lambda_fragment_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_realized_lambda_fragment_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVHo_rec_family_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVHo_const_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_app_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVHo_foldApps_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVHo_type_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVHo_type_guarded_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVHo_type_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVHo_type_observation_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covVHo_repaired_instance
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_eq_native_heads
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_true_native_heads
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_and_native_heads
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_nat_native_heads
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_empty_native_heads
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxT_beta_forward
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxT_lamTel_bvar
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_iotaS_legacy_data
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxT_prop_major_indep
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxT_iota_legacy_prop_forward
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxT_iota_prop_anyMajor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxT_projField_anyMajor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxT_projField_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxTK_proj_ctor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxTN_proj_ctor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxTKN_proj_ctor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_proj_ctor_native_and_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.ApproxTKNStage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.ApproxTKNStage.mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.approxTKNStage_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_stage_of_native_heads
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxTN_lift_intro
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVRealized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVRealized.mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxTN_substT_up
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_approxTN_substT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVRealized.approxTN
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVRealized.approxTKN_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVRealized.stage_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_realized_bot_of_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_realized_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_realized_of_native_heads
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.CovVRealized.forget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_ineligible_prop_const_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_foldApps_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovVAudit.covV_ineligible_prop_spine

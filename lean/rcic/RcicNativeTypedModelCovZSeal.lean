import Lean
import rcic.RcicNativeTypedModelCovZContract
import rcic.RcicNativeTypedModelCovZFixtures
import rcic.RcicNativeTypedModelCovZIdSynthesisBoundary
import rcic.RcicNativeTypedModelCovZMeasure
import rcic.RcicNativeTypedModelCovZNeutralBody
import rcic.RcicNativeTypedModelCovZOrder
import rcic.RcicNativeTypedModelCovZOrderMeet
import rcic.RcicNativeTypedModelCovZOrderUp
import rcic.RcicNativeTypedModelCovZRigidId
import rcic.RcicNativeTypedModelCovZRigidPoly
import rcic.RcicNativeTypedModelCovZSynthesisBoundary
import rcic.RcicNativeTypedModelCovZWall4
import rcic.RcicNativeTypedModelCovZWall4Control

/-!
# Bounded seal for code synthesis and common-code measurements

The unchanged joint CoreY/H/H synthesis target is kernel-refuted even at an
inhabited polymorphic identity declaration. All eight prior fixtures have
actual positive code witnesses. Literal common-row intersection fails; the
general amalgamation question for two already realized edges remains open.
The relevant-function pattern and its demanded action are supplied positively.

All authored public declarations in this round are checked below. No global
fundamental assembler is instantiated. Neither Foundation build root is
imported. `closure_claim = 0`.
-/

private def covZRoots : Array Lean.Name := #[
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.CovZJointCodeAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.CovZTypedJointSynthesis,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.CovZClosedCodeOfSpec,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_no_codeOf_of_no_realization,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_not_typedJoint_of_no_realization,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.CovZInhabitedJointAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_fixture_natSucc_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_fixture_alias_in_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_fixture_polyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_fixture_alias_extension,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_fixture_nat_coverage_and_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_fixture_eq_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_fixture_nat_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.fundTyCodeAtCovY_covZRigidId,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.fundTyAtCovY_covZRigidId,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.not_covZ_rigidId_joint_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.not_covZ_typedJointSynthesis_rigidId,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.not_covZ_closedCodeOf_rigidId,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZ_sizeOf_lam_demand_lt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZ_sizeOf_lam_output_lt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZ_sizeOf_spine_argument_lt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZ_not_spine_application_decreases,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZ_natSucc_action_measure_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_hereditary_normal_bot_only,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_hereditary_bvar_bot_only,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_not_hereditary_empty_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_not_hereditary_poly_result_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZMatchedNatCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZMatchedNatCode_not_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.approxTK_covZMatchedNatCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_matched_code_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_matched_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_matched_related,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_matched_realized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.not_covZ_natSucc_standard_realized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_row_deletion_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.not_covZ_core_downward_of_row_inclusion,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_standard_rows_subset_matched,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.not_covZ_core_downward_row_subset,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_core_rows_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_realization_rows_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZBottomRowNatCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZBottomRowNatCode_not_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.approxTK_covZBottomRowNatCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_bottomRow_code_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_bottomRow_covers,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_bottomRow_reflects,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_bottomRow_related,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_bottomRow_realized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_exact_common_nat_rows,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_nat_common_rows_failure,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZBottomNatCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZWrongNatCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZBottomNatCode_not_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.approxTK_covZBottomNatCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_bottom_code_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_bottom_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_bottom_related,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_bottom_realized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.not_covZ_natSucc_wrong_code_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.not_covZ_natSucc_wrong_related,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_domain_raise_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.not_covZ_core_upward_of_domain_raise,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_eq_prop_sort_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.not_covZ_realization_upward_prop_sort,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZ_polyId_body_observed_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdMember,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdTy_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdEnvWfT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdHead_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdHead_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdHead_not_propCtor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdHead_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidId_pi_gate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidId_application_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidId_no_pi_gate_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.not_covZRigidId_core_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdHead_related_leaf,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.not_covZRigidId_hereditary_any_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidId_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidId_full_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyMember,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyHead,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyTy_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyEnvWfT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyHead_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyHead_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyHead_not_propCtor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyHead_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyHead_normal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyHead_old_related,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyHead_related_leaf,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.not_covZRigidPoly_hereditary_any_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPoly_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.fundTyCodeAtCovY_covZRigidPoly,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.fundTyAtCovY_covZRigidPoly,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.not_covZ_rigidPoly_joint_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.not_covZ_typedJointSynthesis,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.not_covZ_closedCodeOf,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_rigidPoly_boundary,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZPropArrowCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZRelevantAppCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_relevant_demand_typing,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_relevant_app_typing,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.hereditaryCovRealizationYAt_relevant_domain,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.hereditaryCovRealizationYAt_relevant_app,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.lrSCoreCovY_relevant_app,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_relevant_app_joint,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_relevant_argument_native,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_relevant_argument_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.lrSCoreCovY_relevant_argument,
  ``Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_relevant_argument_control
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound]
  for root in covZRoots do
    if !env.contains root then
      throwError "CovZ seal: missing declaration {root}"
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "CovZ seal: {root} has forbidden axioms {forbidden}"
  logInfo m!"CovZ seal: {covZRoots.size} public roots checked; allowed axioms = {allowed}"

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Z_SEAL_ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.CovZJointCodeAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.CovZTypedJointSynthesis
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.CovZClosedCodeOfSpec
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_no_codeOf_of_no_realization
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_not_typedJoint_of_no_realization
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.CovZInhabitedJointAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_fixture_natSucc_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_fixture_alias_in_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_fixture_polyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_fixture_alias_extension
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_fixture_nat_coverage_and_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_fixture_eq_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_fixture_nat_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.fundTyCodeAtCovY_covZRigidId
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.fundTyAtCovY_covZRigidId
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.not_covZ_rigidId_joint_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.not_covZ_typedJointSynthesis_rigidId
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.not_covZ_closedCodeOf_rigidId
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZ_sizeOf_lam_demand_lt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZ_sizeOf_lam_output_lt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZ_sizeOf_spine_argument_lt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZ_not_spine_application_decreases
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZ_natSucc_action_measure_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_hereditary_normal_bot_only
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_hereditary_bvar_bot_only
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_not_hereditary_empty_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_not_hereditary_poly_result_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZMatchedNatCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZMatchedNatCode_not_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.approxTK_covZMatchedNatCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_matched_code_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_matched_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_matched_related
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_matched_realized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.not_covZ_natSucc_standard_realized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_row_deletion_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.not_covZ_core_downward_of_row_inclusion
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_standard_rows_subset_matched
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.not_covZ_core_downward_row_subset
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_core_rows_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_realization_rows_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZBottomRowNatCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZBottomRowNatCode_not_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.approxTK_covZBottomRowNatCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_bottomRow_code_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_bottomRow_covers
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_bottomRow_reflects
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_bottomRow_related
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_bottomRow_realized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_exact_common_nat_rows
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_nat_common_rows_failure
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZBottomNatCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZWrongNatCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZBottomNatCode_not_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.approxTK_covZBottomNatCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_bottom_code_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_bottom_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_bottom_related
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_bottom_realized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.not_covZ_natSucc_wrong_code_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.not_covZ_natSucc_wrong_related
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_natSucc_domain_raise_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.not_covZ_core_upward_of_domain_raise
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.covZ_eq_prop_sort_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit.not_covZ_realization_upward_prop_sort
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZ_polyId_body_observed_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdMember
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdTy_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdEnvWfT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdHead_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdHead_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdHead_not_propCtor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdHead_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidId_pi_gate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidId_application_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidId_no_pi_gate_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.not_covZRigidId_core_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidIdHead_related_leaf
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.not_covZRigidId_hereditary_any_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidId_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidId_full_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyMember
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyHead
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyTy_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyEnvWfT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyHead_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyHead_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyHead_not_propCtor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyHead_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyHead_normal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyHead_old_related
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPolyHead_related_leaf
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.not_covZRigidPoly_hereditary_any_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit.covZRigidPoly_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.fundTyCodeAtCovY_covZRigidPoly
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.fundTyAtCovY_covZRigidPoly
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.not_covZ_rigidPoly_joint_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.not_covZ_typedJointSynthesis
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.not_covZ_closedCodeOf
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_rigidPoly_boundary
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZPropArrowCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZRelevantAppCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_relevant_demand_typing
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_relevant_app_typing
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.hereditaryCovRealizationYAt_relevant_domain
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.hereditaryCovRealizationYAt_relevant_app
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.lrSCoreCovY_relevant_app
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_relevant_app_joint
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_relevant_argument_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_relevant_argument_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.lrSCoreCovY_relevant_argument
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovZAudit.covZ_relevant_argument_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Z_SEAL_ROOTS

import Lean
import rcic.RcicNativeTypedModelCovWEtaSeal
import rcic.RcicNativeTypedModelCovWIrrelAliasControl
import rcic.RcicNativeTypedModelCovWIrrelAligned
import rcic.RcicNativeTypedModelCovWIrrelBoundary
import rcic.RcicNativeTypedModelCovWIrrelCompact
import rcic.RcicNativeTypedModelCovWIrrelControls
import rcic.RcicNativeTypedModelCovWIrrelFixtures
import rcic.RcicNativeTypedModelCovWIrrelFullProofEquality
import rcic.RcicNativeTypedModelCovWIrrelFunctionBoundary
import rcic.RcicNativeTypedModelCovWIrrelFunctionRawBoundary
import rcic.RcicNativeTypedModelCovWIrrelFunctionRepairBoundary
import rcic.RcicNativeTypedModelCovWIrrelKControls
import rcic.RcicNativeTypedModelCovWIrrelNat
import rcic.RcicNativeTypedModelCovWIrrelNatAdequacy
import rcic.RcicNativeTypedModelCovWIrrelNativeEtaBody
import rcic.RcicNativeTypedModelCovWIrrelNativePositions
import rcic.RcicNativeTypedModelCovWIrrelPositionPins
import rcic.RcicNativeTypedModelCovWIrrelPositions
import rcic.RcicNativeTypedModelCovWIrrelProofDemand
import rcic.RcicNativeTypedModelCovWIrrelProofSupplies
import rcic.RcicNativeTypedModelCovWIrrelRecControl
import rcic.RcicNativeTypedModelCovWIrrelRepair
import rcic.RcicNativeTypedModelCovWIrrelScope
import rcic.RcicNativeTypedModelCovWIrrelShape

/-!
# Bounded seal: native proof-field erasure and relevant-function expansion

The old independent proof-field irr violation is inhabited. New raw and
guarded grammars retain actual universe provenance and emit bottom at
native proof positions. Public observations erase provenance. Fresh positive
supplies repair proof-field beta/let transport and retain the controls.
The relevant-function field example gives a further inhabited eta-congruence
and typed-expansion boundary. No general interpreter or assembler is built.

The preceding bounded seals and the pinned external replay are checked
independently. Neither full Foundation root is imported. closure_claim = 0.
-/

private def covWIrrelRoots : Array Lean.Name := #[
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_empty_app,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_empty_lam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_eta_empty_row,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_type_sort_row,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_empty_graph_typed_sort_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_beta_apply_alias,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_beta_apply_alias_not_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_sort_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.ApproxTWIrrel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.ApproxTKWIrrel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_raw_forget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_guarded_forget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRaw_closed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_raw_appSpine_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_guarded_appSpine_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.ApproxTKWIrrelStage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.ApproxTKWIrrelStage.mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelRealized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_realized_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelObservation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelRawObservation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_observation_of,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_observation_forget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRaw_observation_closed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelQMember,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelFamilyMember,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelFamilyEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProp,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelP,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelQ,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelFamily,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelFamilyType,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelLeft,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRight,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelFine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelOtherFine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelFamilyEnv_wf,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelEnv_wf,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_prop_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_p_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_q_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_left_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_right_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_pq_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_conv_rev,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_prop_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_p_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_q_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_prop_not_propCtor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_p_not_propCtor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_q_not_propCtor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_not_propCtor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_prop_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_p_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_q_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_left_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_right_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_result_type_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fine_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fine_nonbottom,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_other_fine_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_other_fine_nonbottom,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_right_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_right_clean,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fine_not_clean,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_right_fine_absent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_endpoints_normal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_no_rec_occurrence,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_old_observations_differ,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelOldFailureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_old_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_old_no_conversion_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_old_same_stage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CptWIrrel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelErase,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelEraseRows,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelEraseArgs,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_erase_args,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_erase_rows,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRowErase,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_erase_bot_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.sortCodeWIrrel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_erase_sortCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.EnvWIrrel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.EnvWIrrel.bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.EnvWIrrel.cons,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.demandWIrrel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.EnvWIrrel.pushArgs,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelEnvErase,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_env_erase_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_env_erase_cons,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_env_erase_push,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.curryStepWIrrel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.fieldDemandVectorsWIrrel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.ctorDemandWIrrel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_erase_curry,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_erase_vectors,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_erase_ctorDemand,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_identity_tower_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_identity_uniform_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proof_total_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_trueIntro_supply,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_abelCoquand_supply,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_rigid_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_neutral_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_pi_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_nat_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_succ_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNatArrowCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natArrow_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natEta_empty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_aliasIdentity_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelPolyPropCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_poly_type_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_poly_value_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_eq_realized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelFixtureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_pack,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_natSucc_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_alias_in_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_polyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_alias_extension,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_nat_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_nat_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_eq_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_nat_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelFamilyResult,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelFamilyShape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelFamilySource,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_raw_family_applied_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelFamilyEtaStep,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_shape_of_native,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_applied_all_shape_of_native,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_all_observations_equal_of_native,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_all_public_observations_equal_of_native,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_eta_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_applied_all_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_all_observations_equal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_all_public_observations_equal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_closed_observations_equal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_closed_public_observations_equal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_raw_family_all_observations_equal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_raw_family_all_public_observations_equal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionArrow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionGType,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionGMember,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionG,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionSucc,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionEta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionTarget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionEtaSource,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionBody,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionFn,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionBetaSource,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionAtom,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionFine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionArrowCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionEnv_wf,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_nat_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_arrow_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_g_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_succ_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_eta_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_target_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_eta_source_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_body_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_beta_source_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_eta_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_beta_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_beta_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_nat_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_succ_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_g_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_nat_not_propCtor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_succ_not_propCtor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_g_not_propCtor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_succ_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_g_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_target_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_result_type_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_fine_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_fine_nonbottom,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_arrow_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_nat_not_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_arrow_not_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_pi_demand_no_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWFunctionClean,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_fine_not_clean,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_eta_source_clean,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_eta_source_absent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_arrow_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_beta_source_clean,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_beta_source_absent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_target_normal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_eta_source_normal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_no_rec_occurrence,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWFunctionOldFailureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_old_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_old_no_eta_conversion_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_old_no_beta_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_old_same_stage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_target,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_type,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_arrow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_target_observation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_type_observation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_eta_absent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_beta_absent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_let_absent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_all_fine_decorations_absent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_realized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWFunctionRawFailureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_same_stage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionAtomR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionFineR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionArrowCodeR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionGraphR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionLetSource,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_let_body_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_let_source_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_let_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_let_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_let_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_fine_erases,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionEnv_inScope,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_g_position,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_arrow_native_nonproof,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_g_nonproof_position,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_nat_observedR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_succ_observedR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_g_observedR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_target_observedR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_result_type_observedR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_arrow_observedR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_succ_graphR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_eta_graphR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_graph_typedR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_fine_typedR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_fine_nonbottomR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_eta_source_absentR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_beta_source_absentR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_let_source_absentR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_no_typed_factor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_coarseR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_let_coarseR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWFunctionRepairedFailureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_transportAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_no_conversion_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_no_beta_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_no_step_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_no_let_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_no_let_conversion_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_inverseAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_no_typed_inverse,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_same_stage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_let_source_absent_old,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_target_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_type_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_eta_absent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_beta_absent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_let_absent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_all_fine_decorations_absent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWFunctionErasedFailureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_transportAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_no_conversion_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_no_beta_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_no_step_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_no_let_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_no_let_conversion_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_K_eqGap_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_trueK_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_andK_rhs_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_andK_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_K_eqGap_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_trueK_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_andK_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_K_erased_positive_controls,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_apart_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_etaIndex_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_apart_observation_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_etaIndex_observation_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_K_apart_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_K_eta_guard_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_ineligible_prop_head_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_ineligible_prop_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelHo_type_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelHo_type_observation_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelHo_repaired_instance,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNatGraph,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNatGraphType,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNatResult,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_type_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_fn_graph,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_expand_graph,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_graph_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_shared_graph,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_beta_source,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_let_source,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_beta_let_repaired,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_same_stage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_graph_zero_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_local_guarded_actions,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_erased_guarded_actions,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_eta_body,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_native_sort_separation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_nat_notProp,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natArrow_notProp,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natSucc_nonproof,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natArrowPosition_nonproof,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_position,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_proof_position,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_erases,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_proofs_same_field,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_position,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_proof_position,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_erases,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_position_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natRec_zeroMinor_position,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natRec_zeroMinor_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natRec_zeroMinor_ctx,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natRec_zeroMinor_proof_of_eqZero,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natRec_zeroMinor_proof_zero,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natRec_zeroMinor_proof_imax,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natRec_zeroMinor_universe_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_const_type_chain,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_pi_type_chain,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_nat_notProp_of_sortSeparation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natArrow_notProp_of_sortSeparation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_position_nonproof_of_notProp,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natSucc_position,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natSucc_nonproof_of_sortSeparation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natArrowPosition_nonproof_of_sortSeparation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelTelCtx,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelPosition,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelProofPosition,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_position_length,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_position_unique,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofPosition_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelSlot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_slot_proof,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_slot_nonproof,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_slot_bot_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_slot_deterministic,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_slot_exists_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_raw_origin_boundary,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_raw_levels_boundary,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelOldAvoidTerm,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelOldAvoidTerm.lift,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelOldAvoidTerm.foldApps_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelOldClean,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelOldCleanEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelOld_clean_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelOld_cleanEnv_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelOld_cleanEnv_cons,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelOld_clean_appSpine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelOld_raw_clean,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelOld_observation_clean,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProofDemand_intro_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProofDemand_intro_avoids,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProofDemand_full_not_clean,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProofDemand_intro_full_excluded,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProofDemand_full_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProofDemand_old_typed_transport_no,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProofDemand_old_irr_violation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_family_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_family_not_propCtor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_position,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_proof_position,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_family_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_body_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_source_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_let_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_target_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_source_new,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_let_new,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_target_new,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_type_new,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_coarse_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_typed_sources,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_typed_factor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_erased_sources,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelProofSuppliesAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proof_supplies_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProofDemandCoarse,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_head_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_head_new,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_left_new,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_right_new,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_coarse_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_typed_equal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_erased_equal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_proofs_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_left_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_right_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_apps_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_bottom_demand,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_composed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelProofDemandSupplyAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_supply_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecMinorCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecMajorCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRec_minor_code_erase,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRec_major_code_erase,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRec_ctor_demand,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecMinor_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRec_schema_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRec_const_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRec_call_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecTypeAt_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecTypeAt_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecMajor_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecMajor_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecEnv_realized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecInstance_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecInstance_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecInstance_erased,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_nat_rec_instance_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelHeadTerm,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelHeadTerm.lift_one,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelHeadTerm.headConst,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelHeadShape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_raw_head_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_guarded_head_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proof_field_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelCoarse,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_new,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_left_new,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_right_new,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_typed_observations_equal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelEnv_inScope,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_native_not_sort_and_pi
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  for root in covWIrrelRoots do
    if !env.contains root then
      throwError "CovWIrrel seal: missing declaration {root}"
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "CovWIrrel seal: {root} has forbidden axioms {forbidden}"
  logInfo m!"CovWIrrel seal: {covWIrrelRoots.size} public roots checked; allowed axioms = {allowed}"

#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_empty_app
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_empty_lam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_eta_empty_row
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_type_sort_row
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_empty_graph_typed_sort_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_beta_apply_alias
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_beta_apply_alias_not_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_sort_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.ApproxTWIrrel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.ApproxTKWIrrel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_raw_forget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_guarded_forget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRaw_closed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_raw_appSpine_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_guarded_appSpine_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.ApproxTKWIrrelStage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.ApproxTKWIrrelStage.mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelRealized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_realized_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelObservation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelRawObservation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_observation_of
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_observation_forget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRaw_observation_closed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelQMember
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelFamilyMember
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelFamilyEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProp
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelP
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelQ
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelFamily
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelFamilyType
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelLeft
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRight
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelFine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelOtherFine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelFamilyEnv_wf
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelEnv_wf
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_prop_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_p_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_q_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_left_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_right_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_pq_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_conv_rev
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_prop_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_p_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_q_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_prop_not_propCtor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_p_not_propCtor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_q_not_propCtor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_not_propCtor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_prop_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_p_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_q_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_left_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_right_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_result_type_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fine_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fine_nonbottom
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_other_fine_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_other_fine_nonbottom
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_right_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_right_clean
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fine_not_clean
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_right_fine_absent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_endpoints_normal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_no_rec_occurrence
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_old_observations_differ
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelOldFailureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_old_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_old_no_conversion_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_old_same_stage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CptWIrrel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelErase
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelEraseRows
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelEraseArgs
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_erase_args
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_erase_rows
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRowErase
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_erase_bot_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.sortCodeWIrrel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_erase_sortCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.EnvWIrrel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.EnvWIrrel.bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.EnvWIrrel.cons
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.demandWIrrel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.EnvWIrrel.pushArgs
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelEnvErase
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_env_erase_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_env_erase_cons
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_env_erase_push
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.curryStepWIrrel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.fieldDemandVectorsWIrrel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.ctorDemandWIrrel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_erase_curry
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_erase_vectors
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_erase_ctorDemand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_identity_tower_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_identity_uniform_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proof_total_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_trueIntro_supply
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_abelCoquand_supply
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_rigid_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_neutral_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_pi_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_nat_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_succ_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNatArrowCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natArrow_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natEta_empty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_aliasIdentity_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelPolyPropCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_poly_type_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_poly_value_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_eq_realized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelFixtureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_pack
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_natSucc_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_alias_in_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_polyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_alias_extension
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_nat_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_nat_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_eq_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_fixture_nat_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelFamilyResult
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelFamilyShape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelFamilySource
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_raw_family_applied_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelFamilyEtaStep
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_shape_of_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_applied_all_shape_of_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_all_observations_equal_of_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_all_public_observations_equal_of_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_eta_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_applied_all_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_all_observations_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_all_public_observations_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_closed_observations_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_closed_public_observations_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_raw_family_all_observations_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_raw_family_all_public_observations_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionArrow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionGType
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionGMember
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionG
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionSucc
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionEta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionTarget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionEtaSource
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionBody
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionFn
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionBetaSource
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionAtom
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionFine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionArrowCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionEnv_wf
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_nat_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_arrow_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_g_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_succ_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_eta_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_target_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_eta_source_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_body_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_beta_source_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_eta_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_beta_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_beta_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_nat_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_succ_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_g_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_nat_not_propCtor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_succ_not_propCtor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_g_not_propCtor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_succ_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_g_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_target_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_result_type_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_fine_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_fine_nonbottom
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_arrow_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_nat_not_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_arrow_not_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_pi_demand_no_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWFunctionClean
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_fine_not_clean
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_eta_source_clean
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_eta_source_absent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_arrow_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_beta_source_clean
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_beta_source_absent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_target_normal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_eta_source_normal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_no_rec_occurrence
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWFunctionOldFailureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_old_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_old_no_eta_conversion_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_old_no_beta_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_old_same_stage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_target
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_type
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_arrow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_target_observation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_type_observation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_eta_absent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_beta_absent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_let_absent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_all_fine_decorations_absent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_realized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWFunctionRawFailureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_raw_same_stage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionAtomR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionFineR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionArrowCodeR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionGraphR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionLetSource
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_let_body_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_let_source_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_let_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_let_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_let_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_fine_erases
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunctionEnv_inScope
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_g_position
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_arrow_native_nonproof
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_g_nonproof_position
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_nat_observedR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_succ_observedR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_g_observedR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_target_observedR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_result_type_observedR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_arrow_observedR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_succ_graphR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_eta_graphR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_graph_typedR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_fine_typedR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_fine_nonbottomR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_eta_source_absentR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_beta_source_absentR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_let_source_absentR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_no_typed_factor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_coarseR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_let_coarseR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWFunctionRepairedFailureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_transportAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_no_conversion_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_no_beta_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_no_step_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_no_let_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_no_let_conversion_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_inverseAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_no_typed_inverse
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_repaired_same_stage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_let_source_absent_old
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_target_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_type_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_eta_absent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_beta_absent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_let_absent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_all_fine_decorations_absent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWFunctionErasedFailureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_transportAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_no_conversion_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_no_beta_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_no_step_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_no_let_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWFunction_erased_no_let_conversion_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_K_eqGap_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_trueK_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_andK_rhs_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_andK_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_K_eqGap_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_trueK_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_andK_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_K_erased_positive_controls
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_apart_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_etaIndex_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_apart_observation_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_etaIndex_observation_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_K_apart_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_K_eta_guard_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_ineligible_prop_head_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_ineligible_prop_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelHo_type_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelHo_type_observation_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelHo_repaired_instance
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNatGraph
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNatGraphType
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNatResult
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_type_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_fn_graph
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_expand_graph
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_graph_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_shared_graph
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_beta_source
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_let_source
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_beta_let_repaired
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_same_stage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_graph_zero_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_local_guarded_actions
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelNat_erased_guarded_actions
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_eta_body
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_native_sort_separation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_nat_notProp
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natArrow_notProp
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natSucc_nonproof
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natArrowPosition_nonproof
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_position
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_proof_position
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_erases
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_proofs_same_field
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_position
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_proof_position
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_erases
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_position_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natRec_zeroMinor_position
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natRec_zeroMinor_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natRec_zeroMinor_ctx
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natRec_zeroMinor_proof_of_eqZero
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natRec_zeroMinor_proof_zero
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natRec_zeroMinor_proof_imax
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natRec_zeroMinor_universe_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_const_type_chain
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_pi_type_chain
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_nat_notProp_of_sortSeparation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natArrow_notProp_of_sortSeparation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_position_nonproof_of_notProp
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natSucc_position
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natSucc_nonproof_of_sortSeparation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_natArrowPosition_nonproof_of_sortSeparation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelTelCtx
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelPosition
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelProofPosition
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_position_length
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_position_unique
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofPosition_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelSlot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_slot_proof
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_slot_nonproof
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_slot_bot_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_slot_deterministic
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_slot_exists_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_raw_origin_boundary
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_raw_levels_boundary
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelOldAvoidTerm
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelOldAvoidTerm.lift
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelOldAvoidTerm.foldApps_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelOldClean
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelOldCleanEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelOld_clean_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelOld_cleanEnv_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelOld_cleanEnv_cons
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelOld_clean_appSpine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelOld_raw_clean
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelOld_observation_clean
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProofDemand_intro_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProofDemand_intro_avoids
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProofDemand_full_not_clean
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProofDemand_intro_full_excluded
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProofDemand_full_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProofDemand_old_typed_transport_no
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProofDemand_old_irr_violation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_family_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_family_not_propCtor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_position
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_proof_position
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_family_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_body_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_source_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_let_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_target_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_source_new
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_let_new
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_target_new
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_type_new
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_coarse_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_typed_sources
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_typed_factor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_inv_erased_sources
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelProofSuppliesAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proof_supplies_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelProofDemandCoarse
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_head_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_head_new
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_left_new
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_right_new
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_coarse_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_typed_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_erased_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_proofs_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_left_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_right_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_apps_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_bottom_demand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_composed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelProofDemandSupplyAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proofDemand_supply_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecMinorCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecMajorCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRec_minor_code_erase
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRec_major_code_erase
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRec_ctor_demand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecMinor_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRec_schema_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRec_const_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRec_call_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecTypeAt_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecTypeAt_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecMajor_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecMajor_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecEnv_realized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecInstance_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecInstance_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelRecInstance_erased
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_nat_rec_instance_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelHeadTerm
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelHeadTerm.lift_one
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelHeadTerm.headConst
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.CovWIrrelHeadShape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_raw_head_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_guarded_head_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_proof_field_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelCoarse
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_new
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_left_new
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_right_new
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_family_typed_observations_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrelEnv_inScope
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit.covWIrrel_native_not_sort_and_pi

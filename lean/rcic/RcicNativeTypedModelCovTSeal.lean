import Lean
import rcic.RcicNativeTypedModelCovSSeal
import rcic.RcicNativeTypedModelCovTData
import rcic.RcicNativeTypedModelCovTRecursor
import rcic.RcicNativeTypedModelCovTRecursorView
import rcic.RcicNativeTypedModelCovTSpine
import rcic.RcicNativeTypedModelCovTStage
import rcic.RcicNativeTypedModelCovTSubstitution
import rcic.RcicNativeTypedModelCovTView
import rcic.RcicNativeTypedModelCovTViewFixtures

/-!
# Bounded seal for provenance views and first-gate controls

Actual inductive views, source-spine provenance, fixed-argument
admissibility and K-free forward observation substitution are supplied.
The native-neutral recursor refutes compact-to-literal-sort alignment and
its inert rigid leaf, not general head or view supply. The general supply
port is open. No interpreter, semantic substitution iff, conversion or
fundamental-theorem case is claimed. `closure_claim = 0`.

This seal covers every authored public CovT declaration. The prior five
seals and the exact external #7776 replay are checked separately. Neither
full Foundation root is imported or built by this bounded audit.
-/

private def covTRoots : Array Lean.Name := #[
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTProbe,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTLambdaArg,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRigidType,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRigidTypeCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTWrappedType,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTWrappedTypeCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTProbe_nonbot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTLambdaArg_nonbot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRigidTypeCode_nonbot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTWrappedTypeCode_nonbot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTProbe_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_indexId_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_indexId_normal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_eq_head_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_eq_head_not_propCtor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_eq_head_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRigidType_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRigidType_normal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRigidType_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRigidTypeCode_positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTWrappedType_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTWrappedType_normal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTWrappedType_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTWrappedTypeCode_not_positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_nil_env_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_nil_ctx_coherent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_rigid_lambda_data,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_wrapped_lambda_data,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMotive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMinorTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMinor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecTypeAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMinorCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMajorCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecCtx,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecExtCtx,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecExtEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMotive_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMotive_beta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecProp_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMinor_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecTypeAt_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecCtx_wf,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecExtCtx_wf,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecExt_y_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMinor_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_const_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecTypeAt_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_no_native,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecTypeAt_normal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecTypeAt_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecTypeAt_no_sort_read,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMajorCode_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_env_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_ctx_coherent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_ext_env_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_ext_ctx_coherent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_ext_y_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_rigid_rejects,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_unknown_accepts,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_prop_leaf_accepts,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_type_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_rigid_leaf_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_minor_stage3,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_major_stage3,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_type_stage3,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_y_stage3,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_args_stage3,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_view_stage3,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_unknown_view_stage3,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_view_universe,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_view_not_positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_motive_admissible,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_zero_admissible,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_minor_admissible,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_major_admissible,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTRecStage3Control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_stage3_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTPropObservationSortReadback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_no_prop_observation_sort_readback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTViewedPropSortReadback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_no_viewed_prop_sort_readback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTSpineProvenance,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTSpineProvenance.observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_spine_provenance_of_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTObservationBudget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTObservationBudget_zero_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.ApproxTKStage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.ApproxTKStage.forget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.ApproxTKStage.mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.approxTKStage_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.approxTKStage_zero,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.approxTKStage_at_budget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.approxTK_iff_exists_stage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.approxTKStage_common,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_approxTK_subst0_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_approxTK_subst0_of_no_indexed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_approxTK_subst0_nat,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_approxTKStage_subst0_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_admissible_subst0_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_argument_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_deep_result,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTSubstitutionBeta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTSubstitutionBetaTable,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_beta_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_beta_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_beta_read,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_beta_function_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_beta_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_native_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_staged_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_prop_not_admissible_sort,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_prop_admissible_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_prop_demand_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTAdmissible,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.TyObsArgs,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.TyObsView,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.TyObsArgs.length_eq,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.TyObsView.universe,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.TyObsView.typing,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.TyObsView.observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.TyObsView.positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.TyObsView.positive_typing,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_view_pi_domain_decreases,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_view_pi_output_decreases,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTViewSupply,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTFixtureStage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_sort_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_sort_bot_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_pi_nil_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_nat_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_nat_bot_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_natArrow_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_idPiProp_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_polyProp_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_propArrow_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_relevant_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_alias_sort_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_aliasPi_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTTypeFixtureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_typeFixture_of_S,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_bot_env_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_nil_coherent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_natSucc_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_alias_in_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_polyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_alias_extension,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_nat_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_nat_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_eq_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_nat_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_origin_var0_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_origin_var1_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_origin_literal_domain_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_origin_variable_domain_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_origin_sort_bot_domain_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_origin_nat_bot_domain_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_origin_variable_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_origin_sort_level_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_rigid_lambda_args,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_rigid_lambda_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_wrapped_lambda_view
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound]
  for root in covTRoots do
    if !env.contains root then
      throwError "CovT seal: missing declaration {root}"
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "CovT seal: {root} has forbidden axioms {forbidden}"
  logInfo m!"CovT seal: {covTRoots.size} public roots checked; allowed axioms = {allowed}"

#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTProbe
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTLambdaArg
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRigidType
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRigidTypeCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTWrappedType
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTWrappedTypeCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTProbe_nonbot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTLambdaArg_nonbot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRigidTypeCode_nonbot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTWrappedTypeCode_nonbot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTProbe_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_indexId_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_indexId_normal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_eq_head_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_eq_head_not_propCtor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_eq_head_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRigidType_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRigidType_normal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRigidType_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRigidTypeCode_positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTWrappedType_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTWrappedType_normal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTWrappedType_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTWrappedTypeCode_not_positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_nil_env_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_nil_ctx_coherent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_rigid_lambda_data
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_wrapped_lambda_data
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMotive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMinorTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMinor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecTypeAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMinorCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMajorCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecCtx
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecExtCtx
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecExtEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMotive_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMotive_beta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecProp_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMinor_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecTypeAt_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecCtx_wf
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecExtCtx_wf
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecExt_y_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMinor_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_const_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecTypeAt_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_no_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecTypeAt_normal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecTypeAt_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecTypeAt_no_sort_read
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRecMajorCode_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_env_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_ctx_coherent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_ext_env_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_ext_ctx_coherent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_ext_y_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_rigid_rejects
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_unknown_accepts
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_prop_leaf_accepts
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_type_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_rigid_leaf_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_minor_stage3
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_major_stage3
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_type_stage3
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_y_stage3
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_args_stage3
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_view_stage3
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_unknown_view_stage3
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_view_universe
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_view_not_positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_motive_admissible
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_zero_admissible
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_minor_admissible
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_major_admissible
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTRecStage3Control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTRec_stage3_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTPropObservationSortReadback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_no_prop_observation_sort_readback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTViewedPropSortReadback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_no_viewed_prop_sort_readback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTSpineProvenance
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTSpineProvenance.observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_spine_provenance_of_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTObservationBudget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTObservationBudget_zero_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.ApproxTKStage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.ApproxTKStage.forget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.ApproxTKStage.mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.approxTKStage_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.approxTKStage_zero
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.approxTKStage_at_budget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.approxTK_iff_exists_stage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.approxTKStage_common
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_approxTK_subst0_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_approxTK_subst0_of_no_indexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_approxTK_subst0_nat
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_approxTKStage_subst0_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_admissible_subst0_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_argument_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_deep_result
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTSubstitutionBeta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTSubstitutionBetaTable
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_beta_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_beta_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_beta_read
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_beta_function_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_beta_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_native_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_substitution_staged_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_prop_not_admissible_sort
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_prop_admissible_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_prop_demand_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTAdmissible
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.TyObsArgs
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.TyObsView
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.TyObsArgs.length_eq
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.TyObsView.universe
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.TyObsView.typing
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.TyObsView.observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.TyObsView.positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.TyObsView.positive_typing
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_view_pi_domain_decreases
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_view_pi_output_decreases
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTViewSupply
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covTFixtureStage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_sort_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_sort_bot_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_pi_nil_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_nat_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_nat_bot_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_natArrow_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_idPiProp_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_polyProp_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_propArrow_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_relevant_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_alias_sort_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_aliasPi_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTTypeFixtureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_typeFixture_of_S
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_bot_env_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_nil_coherent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_natSucc_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_alias_in_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_polyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_alias_extension
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_nat_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_nat_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_eq_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_fixture_nat_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_origin_var0_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_origin_var1_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_origin_literal_domain_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_origin_variable_domain_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_origin_sort_bot_domain_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_origin_nat_bot_domain_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_origin_variable_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_origin_sort_level_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_rigid_lambda_args
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_rigid_lambda_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covT_wrapped_lambda_view

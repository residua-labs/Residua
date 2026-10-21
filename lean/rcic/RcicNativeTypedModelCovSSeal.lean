import Lean
import rcic.RcicNativeTypedModelCovRSeal
import rcic.RcicNativeTypedModelCovSCandidate
import rcic.RcicNativeTypedModelCovSCoherence
import rcic.RcicNativeTypedModelCovSFixtures
import rcic.RcicNativeTypedModelCovSInterpret
import rcic.RcicNativeTypedModelCovSKControls
import rcic.RcicNativeTypedModelCovSObsCoherence
import rcic.RcicNativeTypedModelCovSOperators
import rcic.RcicNativeTypedModelCovSOrigin
import rcic.RcicNativeTypedModelCovSProofAction
import rcic.RcicNativeTypedModelCovSProofControls
import rcic.RcicNativeTypedModelCovSSubstitutionBoundary
import rcic.RcicNativeTypedModelCovSSubstitutionData
import rcic.RcicNativeTypedModelCovSTemplate
import rcic.RcicNativeTypedModelCovSWall4

/-!
# Bounded seal for observed-template interpretation and total Prop

The finite raw-compact decoder and every resulting candidate are supplied.
Native variable/binder origins cannot be recovered from the raw carrier;
actual independently observed substitution and forward-inclusion controls
remain negative. Positive proof observations and a nonbottom proof-demand
application are supplied. Eight selected-observation fixtures retain their
stronger lexical controls; two raw aliases have explicit total fallbacks.
No general native bridge or fundamental-theorem case is claimed.
`closure_claim = 0`.

This seal covers every authored public S declaration. Prior Z/P/Q/R seals
and the exact external #7776 replay are checked separately. Neither full
Foundation root is imported or built by this bounded audit.
-/

private def covSRoots : Array Lean.Name := #[
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSRel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CandidateCovS,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CandidateCovS.readback_right,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CandidateCovS.readback_both,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CandidateCovS.self_left,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CandidateCovS.self_right,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CandidateCovS.positive_iff_true,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSTotalRel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSTotal_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.candidateCovS_of_R_false,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.candidateCovR_of_S_false,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSMeet,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSMeet_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CandidateCovS.positive_eq_total,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSRelIncl,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRelIncl_refl,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRelIncl_trans,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRelIncl_total,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_forward_mono_forces_total,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_no_forward_mono_at_nontotal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_total_not_included_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_no_forward_mono_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_total_R_false,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_opaque_mixed_variance,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_opaque_domain_antitone,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_opaque_codomain_mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSCoherence_idSort1_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSCoherence_idSort1Ty_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSCoherence_idSort1_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSCoherence_idSort1Ty_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_opaque_prop_identity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_opaque_total_rejects_identity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_opaque_domain_not_covariant,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_opaque_variance_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_strict_total_identity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_strict_prop_rejects_identity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_strict_domain_not_antitone,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSFixtureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSFixture_reframe,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRows_singleton_relation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRows_nil_relation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_nat_arrow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_nat_arrow_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_nat_arrow_succ,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSPolyPropCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSPolyPropCode_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_polyProp,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_polyProp_lam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_fixture_natSucc_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_fixture_alias_in_pi_fallback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_fixture_polyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDemandSubstAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_alias_demand_substitution_fallback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_fixture_alias_extension_fallback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_fixture_nat_coverage_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_fixture_eq_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_fixture_nat_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSBuildRows,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_template_pair_snd_lt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.interpretObsTemplate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSBaseVal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSNativeInterp,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSNativeInterp_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_sort,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_unknownPi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_unknown_accepts_all,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSJoint,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSJoint_of_related,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSJoint_trans,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_congr_template,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSJoint_reindex_template,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSJoint_symm,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSJoint_trans_templates,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_K_eqGap_readback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_K_eqGap_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_K_apart_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_K_eta_observation_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_K_eta_guard_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_K_prefix_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObs_arrow_codomain_mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObs_forall_body_mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObs_ordinary_codomain_mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObs_allProp_body_mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObs_allSort_body_mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObs_build_rows_intro,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObs_build_rows_antitone,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsRows,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsRows_antitone,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_pi_eq,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_pi_rows_antitone,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_to_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_bot_not_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixedCtx,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixedEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixedCtx_wf,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixed_type_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixed_term_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixed_env_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixed_ctx_coherent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixed_observations,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixed_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSInput,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSInput_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSForall,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSForall_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSForall_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSForall_intro,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSForall_apply,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate.total,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate.prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate.sort,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRigidRel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRigid_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate.rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate.rows,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate.ordinary,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate.allProp,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate.allSort,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_nonzero_level_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOriginCtx,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOriginEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOriginCtx_wf,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_lookup,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_env_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_ctx_coherent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_var0_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_var1_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_var0_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_var1_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_no_variable_decoder_generic,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_no_variable_decoder,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_variable_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOriginNatArrow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOriginNatArrow_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_pi_observations,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_no_pi_decoder_generic,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_no_pi_decoder,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_pi_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOriginVarArrow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOriginVarArrow_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_prop_domain_observations,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_no_prop_domain_decoder_generic,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_no_prop_domain_decoder,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_prop_domain_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_sort_level_observations,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_no_sort_level_decoder,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_sort_level_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFnTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFnMember,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFnEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFnEnvWfT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_neutral,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_argument_neutral,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_true_positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_argument_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_intro_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_neutral_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_application_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_demand_not_bottom,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_positive_argument_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFnArrow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFnArrow_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFnArrow_member,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_nonbottom_demand_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProof_head_total,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProof_total_no_old_typing,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProof_total_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_trueIntro_all_observations,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_trueIntro_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_polyIdProof_all_observations,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_polyIdProof_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_abelCoquand_all_observations,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_abelCoquand_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_domain_template,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_codomain_template,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_deep_template,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_rows_elim,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_allSort_rejects_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_deep_rejects_identity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_sort_nil_accepts,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitutionVal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_observed_not_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_bot_not_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSIndependentVariableSubstitution,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_no_independent_bridge,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_observed_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitutionDeep,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitutionDeep_tyCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_argument_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_deep_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitutionCtx,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitutionEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitutionCtx_wf,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_body_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_env_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_ctx_coherent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_body_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_argument_observes_valuation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_native_inst,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_result_shallow_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_result_sort_nil_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSSubstitutionNativeData,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_native_data,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSObsSyntax,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_pi_domain_size_lt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_pi_output_size_lt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.templateOfObs,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.templateOfObs_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.templateOfObs_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.templateOfObs_sort,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.templateOfObs_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.templateOfObs_lam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.templateOfObs_empty_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.templateOfObs_ne_var,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRelevantCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSPropArrowCode_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRelevantCode_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_prop_arrow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_relevant,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_relevant_argument_membership,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_relevant_app_membership,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_relevant_app_joint,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_relevant_argument_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_relevant_app_replay
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound]
  for root in covSRoots do
    if !env.contains root then
      throwError "CovS seal: missing declaration {root}"
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "CovS seal: {root} has forbidden axioms {forbidden}"
  logInfo m!"CovS seal: {covSRoots.size} public roots checked; allowed axioms = {allowed}"

#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSRel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CandidateCovS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CandidateCovS.readback_right
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CandidateCovS.readback_both
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CandidateCovS.self_left
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CandidateCovS.self_right
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CandidateCovS.positive_iff_true
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSTotalRel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSTotal_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.candidateCovS_of_R_false
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.candidateCovR_of_S_false
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSMeet
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSMeet_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CandidateCovS.positive_eq_total
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSRelIncl
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRelIncl_refl
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRelIncl_trans
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRelIncl_total
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_forward_mono_forces_total
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_no_forward_mono_at_nontotal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_total_not_included_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_no_forward_mono_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_total_R_false
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_opaque_mixed_variance
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_opaque_domain_antitone
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_opaque_codomain_mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSCoherence_idSort1_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSCoherence_idSort1Ty_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSCoherence_idSort1_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSCoherence_idSort1Ty_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_opaque_prop_identity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_opaque_total_rejects_identity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_opaque_domain_not_covariant
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_opaque_variance_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_strict_total_identity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_strict_prop_rejects_identity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_strict_domain_not_antitone
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSFixtureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSFixture_reframe
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRows_singleton_relation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRows_nil_relation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_nat_arrow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_nat_arrow_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_nat_arrow_succ
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSPolyPropCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSPolyPropCode_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_polyProp
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_polyProp_lam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_fixture_natSucc_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_fixture_alias_in_pi_fallback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_fixture_polyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDemandSubstAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_alias_demand_substitution_fallback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_fixture_alias_extension_fallback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_fixture_nat_coverage_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_fixture_eq_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_fixture_nat_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSBuildRows
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_template_pair_snd_lt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.interpretObsTemplate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSBaseVal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSNativeInterp
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSNativeInterp_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_sort
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_unknownPi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_unknown_accepts_all
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSJoint
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSJoint_of_related
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSJoint_trans
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_congr_template
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSJoint_reindex_template
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSJoint_symm
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSJoint_trans_templates
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_K_eqGap_readback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_K_eqGap_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_K_apart_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_K_eta_observation_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_K_eta_guard_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_K_prefix_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObs_arrow_codomain_mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObs_forall_body_mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObs_ordinary_codomain_mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObs_allProp_body_mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObs_allSort_body_mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObs_build_rows_intro
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObs_build_rows_antitone
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsRows
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsRows_antitone
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_pi_eq
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_pi_rows_antitone
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_to_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_bot_not_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixedCtx
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixedEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixedCtx_wf
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixed_type_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixed_term_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixed_env_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixed_ctx_coherent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixed_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsMixed_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSInput
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSInput_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSForall
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSForall_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSForall_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSForall_intro
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSForall_apply
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate.total
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate.prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate.sort
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRigidRel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRigid_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate.rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate.rows
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate.ordinary
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate.allProp
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSDataCandidate.allSort
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_nonzero_level_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOriginCtx
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOriginEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOriginCtx_wf
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_lookup
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_env_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_ctx_coherent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_var0_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_var1_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_var0_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_var1_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_no_variable_decoder_generic
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_no_variable_decoder
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_variable_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOriginNatArrow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOriginNatArrow_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_pi_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_no_pi_decoder_generic
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_no_pi_decoder
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_pi_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOriginVarArrow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOriginVarArrow_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_prop_domain_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_no_prop_domain_decoder_generic
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_no_prop_domain_decoder
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_prop_domain_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_sort_level_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_no_sort_level_decoder
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSOrigin_sort_level_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFnTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFnMember
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFnEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFnEnvWfT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_neutral
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_argument_neutral
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_true_positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_argument_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_intro_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_neutral_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_application_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_demand_not_bottom
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_positive_argument_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFnArrow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFnArrow_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFnArrow_member
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProofFn_nonbottom_demand_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProof_head_total
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProof_total_no_old_typing
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSProof_total_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_trueIntro_all_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_trueIntro_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_polyIdProof_all_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_polyIdProof_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_abelCoquand_all_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_abelCoquand_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_domain_template
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_codomain_template
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_deep_template
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_rows_elim
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_allSort_rejects_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_deep_rejects_identity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_sort_nil_accepts
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitutionVal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_observed_not_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_bot_not_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSIndependentVariableSubstitution
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_no_independent_bridge
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_observed_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitutionDeep
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitutionDeep_tyCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_argument_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_deep_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitutionCtx
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitutionEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitutionCtx_wf
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_body_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_env_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_ctx_coherent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_body_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_argument_observes_valuation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_native_inst
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_result_shallow_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_result_sort_nil_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSSubstitutionNativeData
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSSubstitution_native_data
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.CovSObsSyntax
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_pi_domain_size_lt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_pi_output_size_lt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.templateOfObs
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.templateOfObs_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.templateOfObs_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.templateOfObs_sort
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.templateOfObs_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.templateOfObs_lam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.templateOfObs_empty_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.templateOfObs_ne_var
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRelevantCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSPropArrowCode_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSRelevantCode_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_prop_arrow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covSObsInterp_relevant
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_relevant_argument_membership
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_relevant_app_membership
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_relevant_app_joint
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_relevant_argument_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovSAudit.covS_relevant_app_replay

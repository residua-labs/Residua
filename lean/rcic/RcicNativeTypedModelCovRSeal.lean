import Lean
import rcic.RcicNativeTypedModelCovZSeal
import rcic.RcicNativeTypedModelCovPSeal
import rcic.RcicNativeTypedModelCovQSeal
import rcic.RcicNativeTypedModelCovRArrow
import rcic.RcicNativeTypedModelCovRCandidate
import rcic.RcicNativeTypedModelCovRFixtureSyntax
import rcic.RcicNativeTypedModelCovRFixtures
import rcic.RcicNativeTypedModelCovRForall
import rcic.RcicNativeTypedModelCovRIdentity
import rcic.RcicNativeTypedModelCovRImpredicative
import rcic.RcicNativeTypedModelCovRLambdaBoundary
import rcic.RcicNativeTypedModelCovROpaqueArrow
import rcic.RcicNativeTypedModelCovRProofControls
import rcic.RcicNativeTypedModelCovRReadback
import rcic.RcicNativeTypedModelCovRReadbackView
import rcic.RcicNativeTypedModelCovRSubstitutionBoundary
import rcic.RcicNativeTypedModelCovRSyntax
import rcic.RcicNativeTypedModelCovRWall4

/-!
# Bounded seal for lexical candidate interpretation

Candidate quantification is Prop-valued. Every represented fixed template
has candidate closure; one code-free rigid identity witness supplies all
native finite tower applications. Eight lexical fixtures and the actual
lambda identity are positive under the new result gate. Typed raw-size
readback growth and unconditional semantic-substitution mismatch are
separate inhabited boundaries. General native observation adequacy and
reindexing remain open; closure_claim = 0.

The seal checks all 253 new public declarations. Imported Z/P/Q seals and
the exact external #7776 replay are checked separately. Neither full
Foundation root is imported or built by this bounded audit.
-/

private def covRRoots : Array Lean.Name := #[
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSupport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSupport_intro,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSupport_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRArrowCoverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRArrowAction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRFunctionShape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRLambdaRows,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_intro,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_rows,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_singleton_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_apply,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_neutral,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_rigidProp_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRRel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CandidateCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CandidateCov.readback_right,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CandidateCov.readback_both,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CandidateCov.self_left,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CandidateCov.self_right,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CandidateCov.positive_iff_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.candidateAll,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.candidateAll_elim,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRCompactRel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRCandidate_compact,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPositiveRel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPositive_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRCodeRel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRCodeRel_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRProp_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSort_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSpine_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPositiveCode_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRProp_rejects_lam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSort_rejects_lam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSpine_rejects_lam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSort_accepts_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRCandidate_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.candidateMeet,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.candidateMeet_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.candidateIntersection,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.candidateIntersection_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.candidateIntersection_elim,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.coreRAt_symm,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.coreRAt_trans,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRInterpretedFixtureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRInterpretedFixture_reframe,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_lam_compact,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNatSyntax,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNatArrowSyntax,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPropArrowSyntax,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyPropSyntax,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRRelevantSyntax,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNatSyntax_native_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNatArrowSyntax_native_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPropSyntax_native_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPropArrowSyntax_native_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyPropSyntax_native_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRRelevantSyntax_native_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPropArrowSyntax_lam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyPropSyntax_lam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_fixture_natSucc_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_fixture_alias_in_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_fixture_polyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_fixture_alias_extension,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_fixture_nat_coverage_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_fixture_eq_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_fixture_nat_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_relevant_argument_membership,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_relevant_app_membership,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_relevant_app_core,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_relevant_argument_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CoreRAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRFixtureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_lam_compact,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRProp_pi_bot_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNat_not_positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNat_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNat_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNatArrowRel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNatArrow_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNatArrow_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNatArrow_succ,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRAliasArrowRel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRAliasArrow_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRAliasArrow_identity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyPropArrowRel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyPropArrow_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyPropArrow_lam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRDemandSubstAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_alias_demand_substitution,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_fixture_natSucc_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_fixture_alias_in_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_fixture_polyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_fixture_alias_extension,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_fixture_nat_coverage_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_fixture_eq_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_fixture_nat_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRForallBody,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRForallBodyCandidates,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_intro,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_apply,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_neutral,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_readback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_positive_iff_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_prop_argument_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_apply_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_variable_body,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRIdentitySyntax,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRIdentitySyntax_native,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRIdentitySyntax_wellFormed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRIdentityRelation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRIdentity_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_lambdaIdentity_realization,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_lambdaIdentity_joint,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_lambdaIdentity_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_rigidIdentity_realization,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_rigidIdentity_instance,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRTowerSyntax,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRTowerSyntax_tag,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRTowerSyntax_native,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRTowerSyntax_wellFormed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRTowerRelation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRTower_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_identity_tower_realization,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_identity_tower_joint,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_identity_native_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_tower_native_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_identity_uniform_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_identity_universe_joint,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRQuantifyCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRQuantifyCandidate_true,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRStrictIdentityBody,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRStrictIdentityBody_candidates,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRProp_support_not_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRStrictIdentityBody_rejects_polyIdOut0,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyIdCpt0_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_strict_identity_rejects_polyIdCpt0,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRLambdaIdentity_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRLambdaIdentity_strict_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRLambdaIdentity_no_strict_supplier,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_intro,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_singleton_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_apply,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_neutral,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_identity_readback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_identity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRIdentityRows_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_polyIdOut0_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_polyIdOut0,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_cexPolyId_readback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_cexPolyId_two_beta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_polyIdCpt0_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_cexPolyId,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_cexPolyId_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRTrueIntro_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_trueIntro_all_observations,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_trueIntro_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyIdProofRelation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyIdProof_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_polyIdProof_all_observations,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_polyIdProof_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_abelCoquand_all_observations,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_abelCoquand_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRProof_head_no_positive_candidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRProof_positive_boundary_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRProof_no_positive_observation_supply,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackArgument,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackSource,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackTarget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackArgument_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackBody_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackSource_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackTarget_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_substitution,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_native_beta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_ck2_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_ck2_readback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_target_normal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_size_grows,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_source_ne_target,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_not_raw_type_step_size_descent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_not_normal_type_readback_size_descent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackSmallSyntax,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackArgumentSyntax,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackSyntax,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackSyntax_native,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackSyntax_wellFormed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_actual_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_candidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_candidate_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_opaque_identity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_strict_rejects_identity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_identity_not_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_arrow_predicates_ne,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_identity_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_native_application_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_native_beta_readback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_identity_not_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_forall_rejects_identity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_lexical_native,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_lexical_views,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_lexical_identity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_lexical_rejects_identity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_lexical_not_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_lexical_predicates_ne,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_lexical_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRSyntax,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRVal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRCons,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRVal.cons,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRTag,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNative,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRValValid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRVal_cons_valid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRDomainOpaque,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrowAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrowAt_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRInterpret,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRInterpret_var,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRInterpret_bound_var,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRInterpret_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRBaseVal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRBaseVal_valid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRJoint,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRJoint_of_related,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRJoint_trans,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRTemplateWellFormed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRNativeView,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPropArrowRel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPropArrow_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_relevant_argument_membership,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRRelevantAppRel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRRelevantApp_isCandidate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_relevant_app_membership,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_relevant_app_core,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_relevant_argument_control
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound]
  for root in covRRoots do
    if !env.contains root then
      throwError "CovR seal: missing declaration {root}"
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "CovR seal: {root} has forbidden axioms {forbidden}"
  logInfo m!"CovR seal: {covRRoots.size} public roots checked; allowed axioms = {allowed}"

#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSupport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSupport_intro
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSupport_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRArrowCoverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRArrowAction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRFunctionShape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRLambdaRows
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_intro
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_rows
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_singleton_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_apply
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_neutral
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_rigidProp_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRRel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CandidateCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CandidateCov.readback_right
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CandidateCov.readback_both
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CandidateCov.self_left
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CandidateCov.self_right
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CandidateCov.positive_iff_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.candidateAll
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.candidateAll_elim
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRCompactRel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRCandidate_compact
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPositiveRel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPositive_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRCodeRel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRCodeRel_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRProp_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSort_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSpine_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPositiveCode_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRProp_rejects_lam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSort_rejects_lam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSpine_rejects_lam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSort_accepts_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRCandidate_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.candidateMeet
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.candidateMeet_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.candidateIntersection
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.candidateIntersection_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.candidateIntersection_elim
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.coreRAt_symm
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.coreRAt_trans
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRInterpretedFixtureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRInterpretedFixture_reframe
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_lam_compact
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNatSyntax
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNatArrowSyntax
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPropArrowSyntax
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyPropSyntax
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRRelevantSyntax
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNatSyntax_native_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNatArrowSyntax_native_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPropSyntax_native_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPropArrowSyntax_native_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyPropSyntax_native_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRRelevantSyntax_native_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPropArrowSyntax_lam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyPropSyntax_lam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_fixture_natSucc_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_fixture_alias_in_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_fixture_polyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_fixture_alias_extension
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_fixture_nat_coverage_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_fixture_eq_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_fixture_nat_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_relevant_argument_membership
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_relevant_app_membership
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_relevant_app_core
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_syntax_relevant_argument_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CoreRAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRFixtureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrow_lam_compact
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRProp_pi_bot_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNat_not_positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNat_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNat_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNatArrowRel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNatArrow_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNatArrow_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNatArrow_succ
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRAliasArrowRel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRAliasArrow_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRAliasArrow_identity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyPropArrowRel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyPropArrow_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyPropArrow_lam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRDemandSubstAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_alias_demand_substitution
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_fixture_natSucc_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_fixture_alias_in_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_fixture_polyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_fixture_alias_extension
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_fixture_nat_coverage_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_fixture_eq_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_fixture_nat_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRForallBody
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRForallBodyCandidates
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_intro
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_apply
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_neutral
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_readback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_positive_iff_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_prop_argument_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_apply_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_variable_body
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRIdentitySyntax
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRIdentitySyntax_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRIdentitySyntax_wellFormed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRIdentityRelation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRIdentity_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_lambdaIdentity_realization
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_lambdaIdentity_joint
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_lambdaIdentity_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_rigidIdentity_realization
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_rigidIdentity_instance
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRTowerSyntax
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRTowerSyntax_tag
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRTowerSyntax_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRTowerSyntax_wellFormed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRTowerRelation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRTower_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_identity_tower_realization
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_identity_tower_joint
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_identity_native_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_tower_native_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_identity_uniform_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_identity_universe_joint
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRQuantifyCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRQuantifyCandidate_true
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRStrictIdentityBody
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRStrictIdentityBody_candidates
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRProp_support_not_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRStrictIdentityBody_rejects_polyIdOut0
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyIdCpt0_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRForall_strict_identity_rejects_polyIdCpt0
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRLambdaIdentity_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRLambdaIdentity_strict_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRLambdaIdentity_no_strict_supplier
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_intro
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_singleton_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_apply
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_neutral
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_identity_readback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_identity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRIdentityRows_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_polyIdOut0_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_polyIdOut0
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_cexPolyId_readback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_cexPolyId_two_beta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_polyIdCpt0_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_cexPolyId
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covROpaqueArrow_cexPolyId_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRTrueIntro_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_trueIntro_all_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_trueIntro_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyIdProofRelation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPolyIdProof_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_polyIdProof_all_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_polyIdProof_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_abelCoquand_all_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_abelCoquand_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRProof_head_no_positive_candidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRProof_positive_boundary_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRProof_no_positive_observation_supply
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackArgument
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackSource
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackTarget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackArgument_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackBody_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackSource_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackTarget_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_substitution
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_native_beta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_ck2_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_ck2_readback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_target_normal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_size_grows
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_source_ne_target
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_not_raw_type_step_size_descent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_not_normal_type_readback_size_descent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackSmallSyntax
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackArgumentSyntax
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackSyntax
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackSyntax_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadbackSyntax_wellFormed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_actual_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_candidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRReadback_candidate_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_opaque_identity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_strict_rejects_identity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_identity_not_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_arrow_predicates_ne
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_identity_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_native_application_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_native_beta_readback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_identity_not_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_forall_rejects_identity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_lexical_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_lexical_views
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_lexical_identity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_lexical_rejects_identity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_lexical_not_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_lexical_predicates_ne
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRSubstitution_lexical_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRSyntax
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRVal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRCons
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRVal.cons
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRTag
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRNative
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRValValid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRVal_cons_valid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRDomainOpaque
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrowAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRArrowAt_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRInterpret
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRInterpret_var
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRInterpret_bound_var
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRInterpret_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRBaseVal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRBaseVal_valid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRJoint
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRJoint_of_related
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRJoint_trans
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRTemplateWellFormed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.CovRNativeView
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPropArrowRel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRPropArrow_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_relevant_argument_membership
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRRelevantAppRel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covRRelevantApp_isCandidate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_relevant_app_membership
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_relevant_app_core
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRAudit.covR_relevant_argument_control

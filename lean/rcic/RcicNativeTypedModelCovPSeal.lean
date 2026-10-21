import Lean
import rcic.RcicNativeTypedModelCovPFixtures
import rcic.RcicNativeTypedModelCovPIdentity
import rcic.RcicNativeTypedModelCovPNeutral
import rcic.RcicNativeTypedModelCovPOuterIdentity
import rcic.RcicNativeTypedModelCovPPositive
import rcic.RcicNativeTypedModelCovPProofCollapse
import rcic.RcicNativeTypedModelCovPRealization
import rcic.RcicNativeTypedModelCovPReflection
import rcic.RcicNativeTypedModelCovPReplay
import rcic.RcicNativeTypedModelCovPStrict
import rcic.RcicNativeTypedModelCovPStrictBoundary
import rcic.RcicNativeTypedModelCovPStrictFixtures
import rcic.RcicNativeTypedModelCovPStrictK
import rcic.RcicNativeTypedModelCovPStrictRealization
import rcic.RcicNativeTypedModelCovPTransport
import rcic.RcicNativeTypedModelCovPTyping
import rcic.RcicNativeTypedModelCovPWall4

/-!
# Bounded seal for positive proposition evidence and neutral reflection

The positive predicate and both compact typings supply all declared fields.
The rigid identity acquires outer coverage but remains impossible at every
hereditary code; the same exact-leaf boundary survives the strict observation
filter while actions are unchanged. Genuine proof irrelevance has an inhabited
rigid-proof obstruction, while the Abel--Coquand delta pin still collapses.
All eight displayed codes and the guarded K controls are remeasured.

Only the new public declarations listed below are sealed. No global assembler,
common-code order, or Foundation build root is instantiated. The external
#7776 replay imports its pinned unlanded source outside this bounded closure.
`closure_claim = 0`.
-/

private def covPRoots : Array Lean.Name := #[
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_sort,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_natArrow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_aliasCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_polyPropCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPJointAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_joint_of_Y,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPFixtureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_fixture_of_Y,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_fixture_natSucc_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_fixture_alias_in_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_fixture_polyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_fixture_alias_extension,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_fixture_nat_coverage_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_fixture_eq_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_fixture_nat_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPPropArrow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPPropArrowId,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPPropArrow_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPPropArrowId_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_identity_arguments_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_not_hereditary_identity_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_rigidId_two_application_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_rigidId_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_hereditary_normal_bot_only,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_hereditary_bvar_bot_only,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_not_hereditary_empty_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_hereditary_pi_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_hereditary_sort_zero_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_not_hereditary_sort_pi_same_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_hereditary_empty_pi_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_not_hereditary_poly_result_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPIdentityOuterCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPIdentityOuterCode_not_positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.approxT_covPIdentityOuterCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPIdentity_outer_gate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPIdentity_outer_output_gate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPIdentity_outer_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPIdentity_b_only_repairs_outer,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_rigid_empty_rows_no_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPIdentity_output_typed_not_covered,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.IsPropCTP,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.isPropCT_of_isPropCTP,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.not_isPropCTP_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.not_isPropCTP_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.not_isPropCTP_sort,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.not_isPropCTP_lam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.not_isPropCTP_pi_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.not_isPropCTP_pi_bot_outputs,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.not_isPropCTP_emptyEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.isPropCTP_spine_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.prop_universe_seed_incompatible,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_proofCollapse_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_proofCollapse_of_positive_typing,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_true_positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_true_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_prop_universe_seed_no,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_prop_universe_seed_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_trueIntro_collapse,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_trueIntro_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProofMember,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProofEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProofEnvWfT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_true_positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_head_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_head_not_propCtor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_true_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_true_not_propCtor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_head_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_true_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_approxT_rigid_propCtor_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_intro_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_irr_contract_no,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_no_observed_type_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_collapse_no,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_native_irr_counterexample,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_approxT_app_bot_of_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_abelCoquand_bot_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_abelCoquand_top_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_abelCoquand_delta_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_abelCoquand_delta_collapse,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPAbelCoquandId,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPAbelCoquandId_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_abelCoquand_id_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_abelCoquand_distinct_proofs_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_abelCoquand_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_abelCoquand_irr_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPDemandRelation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPSelectedRow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPActionCoverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.HereditaryCovRealizationPAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_typing,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_of_Y,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationYAt_of_P,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_old_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_constructor_pi_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_positive_excludes_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPIdentity_neutral_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPReflectionCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPReflectionCode_type,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPReflectionCode_not_positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_reflection_extra_gate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_no_extra_gate_without_reflection,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.old_prop_bot_incompatible,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.reflection_universe_guard_necessary,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_identity_b_or_br_no_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_neutral_b_or_br_no_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_identity_b_or_br_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_identity_b_or_br_no_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPNeutralTypeSlot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPStrictCompact,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ApproxTKStrictP,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctxModelT_approxTKStrictP,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.approxTKStrictP_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_neutral_bottom_rejected,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_rigidId_type_slot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_rigidId_action_no,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_rigidId_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_constructor_not_type_slot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.approxTKStrictP_recursorPropK,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_model_contract,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_model_mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_strict_forget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_not_hereditary_strict_identity_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_not_hereditary_strict_poly_result_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_rigidId_head_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_identity_boundary_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_spine_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_natSucc_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_nat_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_natArrow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_alias_compact,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_alias_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_polyProp_compact,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_polyProp_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_eq_compact,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_prop_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_wall4_compact,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_wall4_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPStrictFixtureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_fixture_of_certificates,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_fixture_natSucc_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_fixture_alias_in_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_fixture_polyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_fixture_alias_extension,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_fixture_nat_coverage_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_fixture_eq_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_fixture_nat_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.approxTKStrictP_eqGap_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.approxTKStrictP_apartRec_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_K_positive_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_K_apart_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_strict,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationYAt_strict,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_joint_of_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPCodeTransport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_from_Y,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.NeutralHeadP,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.neutralHeadP_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.neutralHeadP_not_constructor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.RigidPiGateP,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CTyCovP2,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CTyCovP2.bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CTyCovP2.univProp,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CTyCovP2.univType,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CTyCovP2.lam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CTyCovP2.rigidPi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CTyCovP2.reflectedPi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CTyCovP2.spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovTypingP,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_bot_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_prop_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_sort_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_lam_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_spine_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_pi_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_prop_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.C2P,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_of_ctyCov2,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_of_ctyS,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_prop_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_sort_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_spine_iff_ctyCov2,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.positive_prop_inv_incompatible,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.reflection_at_all_nonprop_incompatible,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.reflection_at_all_nonbot_nonprop_incompatible,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_propArrow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_hereditary_sort_zero,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_relevant_app_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_relevant_app_hereditary,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_relevant_app_joint
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound]
  for root in covPRoots do
    if !env.contains root then
      throwError "CovP seal: missing declaration {root}"
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "CovP seal: {root} has forbidden axioms {forbidden}"
  logInfo m!"CovP seal: {covPRoots.size} public roots checked; allowed axioms = {allowed}"

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_SEAL_ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_sort
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_natArrow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_aliasCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_polyPropCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPJointAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_joint_of_Y
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPFixtureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_fixture_of_Y
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_fixture_natSucc_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_fixture_alias_in_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_fixture_polyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_fixture_alias_extension
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_fixture_nat_coverage_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_fixture_eq_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_fixture_nat_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPPropArrow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPPropArrowId
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPPropArrow_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPPropArrowId_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_identity_arguments_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_not_hereditary_identity_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_rigidId_two_application_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_rigidId_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_hereditary_normal_bot_only
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_hereditary_bvar_bot_only
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_not_hereditary_empty_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_hereditary_pi_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_hereditary_sort_zero_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_not_hereditary_sort_pi_same_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_hereditary_empty_pi_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_not_hereditary_poly_result_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPIdentityOuterCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPIdentityOuterCode_not_positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.approxT_covPIdentityOuterCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPIdentity_outer_gate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPIdentity_outer_output_gate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPIdentity_outer_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPIdentity_b_only_repairs_outer
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_rigid_empty_rows_no_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPIdentity_output_typed_not_covered
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.IsPropCTP
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.isPropCT_of_isPropCTP
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.not_isPropCTP_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.not_isPropCTP_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.not_isPropCTP_sort
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.not_isPropCTP_lam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.not_isPropCTP_pi_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.not_isPropCTP_pi_bot_outputs
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.not_isPropCTP_emptyEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.isPropCTP_spine_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.prop_universe_seed_incompatible
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_proofCollapse_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_proofCollapse_of_positive_typing
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_true_positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_true_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_prop_universe_seed_no
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_prop_universe_seed_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_trueIntro_collapse
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_trueIntro_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProofMember
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProofEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProofEnvWfT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_true_positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_head_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_head_not_propCtor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_true_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_true_not_propCtor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_head_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_true_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_approxT_rigid_propCtor_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_intro_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_irr_contract_no
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_no_observed_type_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_collapse_no
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPProof_native_irr_counterexample
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_approxT_app_bot_of_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_abelCoquand_bot_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_abelCoquand_top_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_abelCoquand_delta_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_abelCoquand_delta_collapse
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPAbelCoquandId
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPAbelCoquandId_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_abelCoquand_id_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_abelCoquand_distinct_proofs_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_abelCoquand_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_abelCoquand_irr_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPDemandRelation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPSelectedRow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPActionCoverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.HereditaryCovRealizationPAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_typing
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_of_Y
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationYAt_of_P
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_old_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_constructor_pi_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_positive_excludes_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPIdentity_neutral_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPReflectionCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPReflectionCode_type
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covPReflectionCode_not_positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_reflection_extra_gate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_no_extra_gate_without_reflection
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.old_prop_bot_incompatible
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.reflection_universe_guard_necessary
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_identity_b_or_br_no_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_neutral_b_or_br_no_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_identity_b_or_br_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_identity_b_or_br_no_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPNeutralTypeSlot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPStrictCompact
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ApproxTKStrictP
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctxModelT_approxTKStrictP
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.approxTKStrictP_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_neutral_bottom_rejected
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_rigidId_type_slot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_rigidId_action_no
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_rigidId_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_constructor_not_type_slot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.approxTKStrictP_recursorPropK
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_model_contract
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_model_mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_strict_forget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_not_hereditary_strict_identity_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_not_hereditary_strict_poly_result_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_rigidId_head_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_identity_boundary_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_spine_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_natSucc_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_nat_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_natArrow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_alias_compact
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_alias_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_polyProp_compact
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_polyProp_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_eq_compact
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_prop_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_wall4_compact
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_wall4_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPStrictFixtureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_fixture_of_certificates
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_fixture_natSucc_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_fixture_alias_in_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_fixture_polyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_fixture_alias_extension
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_fixture_nat_coverage_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_fixture_eq_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_fixture_nat_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.approxTKStrictP_eqGap_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.approxTKStrictP_apartRec_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_K_positive_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_K_apart_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_strict
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationYAt_strict
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_strict_joint_of_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovPCodeTransport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.hereditaryCovRealizationPAt_from_Y
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.NeutralHeadP
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.neutralHeadP_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.neutralHeadP_not_constructor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.RigidPiGateP
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CTyCovP2
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CTyCovP2.bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CTyCovP2.univProp
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CTyCovP2.univType
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CTyCovP2.lam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CTyCovP2.rigidPi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CTyCovP2.reflectedPi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CTyCovP2.spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.CovTypingP
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_bot_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_prop_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_sort_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_lam_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_spine_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_pi_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_prop_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.C2P
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_of_ctyCov2
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_of_ctyS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_prop_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_sort_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.ctyCovP2_spine_iff_ctyCov2
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.positive_prop_inv_incompatible
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.reflection_at_all_nonprop_incompatible
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.reflection_at_all_nonbot_nonprop_incompatible
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_transport_propArrow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_hereditary_sort_zero
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_relevant_app_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_relevant_app_hereditary
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPAudit.covP_relevant_app_joint
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_SEAL_ROOTS

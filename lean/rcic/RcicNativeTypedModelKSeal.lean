import Lean
import rcic.RcicNativeTypedModelKReport

/-!
# Bounded seal for the ApproxTK measurement

Every explicitly introduced public declaration, constructor and structure
projection in this batch is a named root below.  The audit traverses each
root's actual transitive proof dependencies and rejects every axiom outside
propext and Quot.sound.  It does not import or build RcicFoundationSeal.

CK2 and KIndexConvAt are imported from #7749, never redefined in this batch.
The report states the bounded positive controls and the refuted interfaces;
this seal certifies those statements, not a global model closure claim.
`closure_claim = 0`.
-/

private def approxTKSealedRoots : List Lean.Name := [
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.ModelAgreementAtT,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.ValueAgreementT,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.TypeAgreementT,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.modelAgreementAtT_refl,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.modelAgreementAtT_symm,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.modelAgreementAtT_trans,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.valueAgreementT_of_no_values,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.relSubstAtT_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.relSubstIdT_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.fundTyAt_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.fundConvAt_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.tyValidAt_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.ctxValidAt_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.envTypedAtT_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.relSubstTypedAtT_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.typingAt_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.modelConvSoundAt_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.hybridSeed_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.ctxModelT_eq_of_agreement,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.ctxModelTLaws_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.ctxModelTLaws'_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.modelBetaExpandT_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.typingLemmaEnvT_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.fundamentalSAtT_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.fundCases_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.ihBelow_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.IndexedPropRecT,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.indexedPropRecT_eqRec,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.not_indexedPropRecT_natEnvU,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.not_indexedPropRecT_trueRec,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.TypedCompactWitnessT,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.typedCompactWitnessT_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.eqControl_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.eq_typed_compact_control,
  ``Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.nat_typed_compact_control,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.KFreeSetT,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.KFreeSetT.mk,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.KFreeSetT.noIndexed,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.KFreeSetT.delta,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.KFreeSetT.schema,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.KFreeT,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeSetT_empty,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeSetT_union,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_of_no_occurs,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_bvar,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_sort,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_support,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_app,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_lam,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_app_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_pi_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_lam_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_letE_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_const_not_indexed,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_delta,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_schema,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_foldApps_head,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_rigid_const,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_of_no_indexed,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_natEnvU,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.not_kFreeT_eqRec,
  ``Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.not_kFreeT_eqRec_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.IndexAgreementDI,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.KIndexGuardAt,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.kIndexGuardAt_native,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.kNativeHead_of_guard,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.eq_indexAgreementDI,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.eqKGuard_of_indexConv,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.not_indexAgreementDI_apart,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.not_kIndexGuardAt_apart,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.kIndexGuardAt_eqGap,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.guarded_kNativeHead_eqGap,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.indexBinderBeta_agreementDI,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.deltaIndex_agreementDI,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.deltaBinderIndex_agreementDI,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.kIndexGuardAt_binder,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.kIndexGuardAt_delta,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.kIndexGuardAt_delta_under_binder,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.guarded_native_binder_control,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.guarded_native_delta_control,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.guarded_native_delta_under_binder_control,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.not_uniform_agreementDI_distinct_bvars,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.not_agreementDI_etaIndex,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.not_indexAgreementDI_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.not_kIndexGuardAt_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.NativeKIndexComplete,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.kIndexGuardAt_of_native_complete,
  ``Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.not_nativeKIndexComplete_eqEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.bot,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.free,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.pi,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.lam,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.app,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.appSpine,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.delta,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.letE,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.lit,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.iota,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.recursorPropK,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_forget,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_iff_approxT_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.ctxModelT_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.modelAgreementAtT_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_k_head,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_bvar_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_bvar_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_sort_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_sort_code,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_pi_bot_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_pi_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_lam_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_letE_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.SaturatedComputationTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_of_saturated,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_app_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.ElTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.elTK_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.elTK_forget,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.elTK_iff_elT_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_mono_env,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_nat_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_modelBetaExpandT_of_minimal_inversions,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_modelBetaExpandT_of_approxT_projection,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_modelBetaExpandT_approxT,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_raw_app_inv_of_bot_function,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_ctxModelTLaws_of_bot_function,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.apartPrefix,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.apartRec_eq_app_prefix,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.apartPrefix_model,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.apartPrefix_native_control,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_raw_app_intro_of_apartPrefix,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_appCpt_reconstruction_of_apartPrefix,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_fundTyAt_of_normal_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_fundamentalSAtT_of_normal_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.apartCtx_identity_model,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_fundamentalSAtT_of_raw_app_prefix,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.discardApartRec,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.discardApartRec_beta,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_modelConvSoundAt_discardApartRec,
  ``Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_global_model_conv_sound_of_discardApartRec,
  ``Rcic.Declarative.NativeValleys.TypedModelKControlAudit.approxTK_eqRec_prefix_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelKControlAudit.approxTK_eqRec_fold_prefix_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelKControlAudit.approxTK_eqRec_const_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelKControlAudit.approxTK_eqRec_bvar_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelKControlAudit.approxTK_apartRec_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelKControlAudit.not_approxTK_apartRec_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelKControlAudit.approxTK_eqGap_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.not_modelBetaExpandT_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.eqGapPrefix,
  ``Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.eqGapRedex_eq_app_prefix,
  ``Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.approxTK_eqGapPrefix_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.not_ctxModelTLaws_approxTK_eqGap,
  ``Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.not_ctxModelTLaws'_approxTK_eqGap,
  ``Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.not_saturatedComputationTK_of_nonconst_head,
  ``Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.approxTK_app_bot_of_function_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.approxTK_identity_app_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.eqGapAlias,
  ``Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.approxTK_eqGapAlias_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.native_identity_beta,
  ``Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.eqGapAlias_native_beta_control,
  ``Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.not_native_conversion_sound_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.ArgTypedTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.ModelBetaExpandTypedTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.eqGapPrefix_argTypedTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.no_eqGap_typed_beta_factorization,
  ``Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.eqGapDirectAlias,
  ``Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.eqGapDirectAlias_contractum,
  ``Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.not_approxTK_eqGapDirectAlias_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.not_modelBetaExpandTypedTK_eqEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.eqGapDirectAlias_native_beta_control,
  ``Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.envTypedAtT_approxTK_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.eqGap_typed_identity_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.true_rec_metadata,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.not_indexedPropRecT_trueEnvU,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.and_rec_metadata,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.not_indexedPropRecT_andEnvU,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.kFreeT_trueEnvU,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.kFreeT_andEnvU,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.approxTK_true_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.approxTK_and_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.kFreeT_lift,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.approxTK_cons_lift0_iff_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.KFreeValuesT,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.KFreeTypesT,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.valueAgreementT_approxTK_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.typeAgreementT_approxTK_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.relSubstAtT_approxTK_iff_of_kFree_values,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.relSubstIdT_approxTK_iff_of_kFree_values,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.fundTyAt_approxTK_iff_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.fundConvAt_approxTK_iff_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.tyValidAt_approxTK_iff_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxValidAt_approxTK_iff_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.envTypedAtT_approxTK_iff_of_kFree_types,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.relSubstTypedAtT_approxTK_iff_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.typingAt_approxTK_iff_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.modelConvSoundAt_approxTK_iff_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.hybridSeed_approxTK_iff_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.modelAgreementAtT_approxTK_of_no_indexed,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelT_approxTK_eq_approxT_of_no_indexed,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelTLaws_approxTK_of_no_indexed,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelTLaws'_approxTK_of_no_indexed,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.fundamentalSAtT_approxTK_iff_of_no_indexed,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.typingLemmaEnvT_approxTK_iff_of_no_indexed,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.fundCases_approxTK_iff_of_no_indexed,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.modelBetaExpandT_approxTK_iff_of_no_indexed,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelTLaws_approxTK_natEnvU,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelTLaws'_approxTK_natEnvU,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelTLaws_approxTK_trueEnvU,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelTLaws'_approxTK_trueEnvU,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelTLaws_approxTK_andEnvU,
  ``Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelTLaws'_approxTK_andEnvU,
  ``Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.approxTK_eq_sort_minor,
  ``Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.approxTK_binder_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.approxTK_delta_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.approxTK_delta_under_binder_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.approxTK_etaIndexRedex_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.typed_eta_model_boundary,
  ``Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.not_native_eta_model_sound,
  ``Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.TypedNativeKForwardTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.not_typedNativeKForwardTK_eqEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.eq_typed_compact_controlTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.nat_typed_compact_controlTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.eqGap_typed_compact_controlTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.kFreeT_cexTerm,
  ``Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.kFreeT_cexType,
  ``Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.kFreeT_closed_beta_cex,
  ``Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.envTypedAtT_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.not_typingLemmaEnvT_of_cex_agreement,
  ``Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.not_typingLemmaEnvT_of_kFree_agreement,
  ``Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.approxTK_cexTerm,
  ``Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.not_typingLemmaEnvT_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.closed_cex_control_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.not_modelConvSoundAt_of_closed_beta_agreement,
  ``Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.not_modelConvSoundAt_approxTK_closed_beta,
  ``Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.not_fundCases_approxTK_natEnvU,
  ``Rcic.Declarative.NativeValleys.TypedModelKReportAudit.approxTK_checked_boundary
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Quot.sound]
  for root in approxTKSealedRoots do
    let (_, state) := ((CollectAxioms.collect root).run env).run {}
    for ax in state.axioms do
      unless allowed.contains ax do
        throwError "ApproxTK seal: {root} depends on disallowed axiom {ax}"
  logInfo m!"ApproxTK seal: {approxTKSealedRoots.length} roots checked; allowed axioms = {allowed}"

-- BEGIN RCIC_NATIVE_TYPED_MODEL_K_SEAL_ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.ModelAgreementAtT
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.ValueAgreementT
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.TypeAgreementT
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.modelAgreementAtT_refl
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.modelAgreementAtT_symm
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.modelAgreementAtT_trans
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.valueAgreementT_of_no_values
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.relSubstAtT_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.relSubstIdT_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.fundTyAt_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.fundConvAt_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.tyValidAt_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.ctxValidAt_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.envTypedAtT_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.relSubstTypedAtT_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.typingAt_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.modelConvSoundAt_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.hybridSeed_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.ctxModelT_eq_of_agreement
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.ctxModelTLaws_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.ctxModelTLaws'_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.modelBetaExpandT_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.typingLemmaEnvT_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.fundamentalSAtT_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.fundCases_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.ihBelow_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.IndexedPropRecT
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.indexedPropRecT_eqRec
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.not_indexedPropRecT_natEnvU
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.not_indexedPropRecT_trueRec
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.TypedCompactWitnessT
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.typedCompactWitnessT_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.eqControl_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.eq_typed_compact_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTransportAudit.nat_typed_compact_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.KFreeSetT
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.KFreeSetT.mk
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.KFreeSetT.noIndexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.KFreeSetT.delta
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.KFreeSetT.schema
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.KFreeT
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeSetT_empty
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeSetT_union
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_of_no_occurs
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_bvar
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_sort
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_support
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_app
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_lam
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_app_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_pi_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_lam_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_letE_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_const_not_indexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_delta
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_schema
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_foldApps_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_rigid_const
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_of_no_indexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.kFreeT_natEnvU
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.not_kFreeT_eqRec
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit.not_kFreeT_eqRec_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.IndexAgreementDI
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.KIndexGuardAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.kIndexGuardAt_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.kNativeHead_of_guard
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.eq_indexAgreementDI
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.eqKGuard_of_indexConv
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.not_indexAgreementDI_apart
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.not_kIndexGuardAt_apart
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.kIndexGuardAt_eqGap
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.guarded_kNativeHead_eqGap
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.indexBinderBeta_agreementDI
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.deltaIndex_agreementDI
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.deltaBinderIndex_agreementDI
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.kIndexGuardAt_binder
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.kIndexGuardAt_delta
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.kIndexGuardAt_delta_under_binder
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.guarded_native_binder_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.guarded_native_delta_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.guarded_native_delta_under_binder_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.not_uniform_agreementDI_distinct_bvars
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.not_agreementDI_etaIndex
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.not_indexAgreementDI_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.not_kIndexGuardAt_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.NativeKIndexComplete
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.kIndexGuardAt_of_native_complete
#print axioms Rcic.Declarative.NativeValleys.TypedModelKGuardAudit.not_nativeKIndexComplete_eqEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.free
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.lam
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.app
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.appSpine
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.delta
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.letE
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.lit
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.iota
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.ApproxTK.recursorPropK
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_forget
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_iff_approxT_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.ctxModelT_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.modelAgreementAtT_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_k_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_bvar_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_bvar_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_sort_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_sort_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_pi_bot_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_pi_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_lam_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_letE_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.SaturatedComputationTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_of_saturated
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_app_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.ElTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.elTK_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.elTK_forget
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.elTK_iff_elT_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_mono_env
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.approxTK_nat_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_modelBetaExpandT_of_minimal_inversions
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_modelBetaExpandT_of_approxT_projection
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_modelBetaExpandT_approxT
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_raw_app_inv_of_bot_function
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_ctxModelTLaws_of_bot_function
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.apartPrefix
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.apartRec_eq_app_prefix
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.apartPrefix_model
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.apartPrefix_native_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_raw_app_intro_of_apartPrefix
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_appCpt_reconstruction_of_apartPrefix
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_fundTyAt_of_normal_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_fundamentalSAtT_of_normal_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.apartCtx_identity_model
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_fundamentalSAtT_of_raw_app_prefix
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.discardApartRec
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.discardApartRec_beta
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_modelConvSoundAt_discardApartRec
#print axioms Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit.not_global_model_conv_sound_of_discardApartRec
#print axioms Rcic.Declarative.NativeValleys.TypedModelKControlAudit.approxTK_eqRec_prefix_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelKControlAudit.approxTK_eqRec_fold_prefix_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelKControlAudit.approxTK_eqRec_const_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelKControlAudit.approxTK_eqRec_bvar_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelKControlAudit.approxTK_apartRec_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelKControlAudit.not_approxTK_apartRec_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelKControlAudit.approxTK_eqGap_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.not_modelBetaExpandT_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.eqGapPrefix
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.eqGapRedex_eq_app_prefix
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.approxTK_eqGapPrefix_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.not_ctxModelTLaws_approxTK_eqGap
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.not_ctxModelTLaws'_approxTK_eqGap
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.not_saturatedComputationTK_of_nonconst_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.approxTK_app_bot_of_function_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.approxTK_identity_app_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.eqGapAlias
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.approxTK_eqGapAlias_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.native_identity_beta
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.eqGapAlias_native_beta_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelKFailureAudit.not_native_conversion_sound_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.ArgTypedTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.ModelBetaExpandTypedTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.eqGapPrefix_argTypedTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.no_eqGap_typed_beta_factorization
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.eqGapDirectAlias
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.eqGapDirectAlias_contractum
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.not_approxTK_eqGapDirectAlias_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.not_modelBetaExpandTypedTK_eqEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.eqGapDirectAlias_native_beta_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.envTypedAtT_approxTK_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit.eqGap_typed_identity_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.true_rec_metadata
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.not_indexedPropRecT_trueEnvU
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.and_rec_metadata
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.not_indexedPropRecT_andEnvU
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.kFreeT_trueEnvU
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.kFreeT_andEnvU
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.approxTK_true_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.approxTK_and_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.kFreeT_lift
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.approxTK_cons_lift0_iff_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.KFreeValuesT
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.KFreeTypesT
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.valueAgreementT_approxTK_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.typeAgreementT_approxTK_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.relSubstAtT_approxTK_iff_of_kFree_values
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.relSubstIdT_approxTK_iff_of_kFree_values
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.fundTyAt_approxTK_iff_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.fundConvAt_approxTK_iff_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.tyValidAt_approxTK_iff_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxValidAt_approxTK_iff_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.envTypedAtT_approxTK_iff_of_kFree_types
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.relSubstTypedAtT_approxTK_iff_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.typingAt_approxTK_iff_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.modelConvSoundAt_approxTK_iff_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.hybridSeed_approxTK_iff_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.modelAgreementAtT_approxTK_of_no_indexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelT_approxTK_eq_approxT_of_no_indexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelTLaws_approxTK_of_no_indexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelTLaws'_approxTK_of_no_indexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.fundamentalSAtT_approxTK_iff_of_no_indexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.typingLemmaEnvT_approxTK_iff_of_no_indexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.fundCases_approxTK_iff_of_no_indexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.modelBetaExpandT_approxTK_iff_of_no_indexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelTLaws_approxTK_natEnvU
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelTLaws'_approxTK_natEnvU
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelTLaws_approxTK_trueEnvU
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelTLaws'_approxTK_trueEnvU
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelTLaws_approxTK_andEnvU
#print axioms Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit.ctxModelTLaws'_approxTK_andEnvU
#print axioms Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.approxTK_eq_sort_minor
#print axioms Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.approxTK_binder_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.approxTK_delta_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.approxTK_delta_under_binder_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.approxTK_etaIndexRedex_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.typed_eta_model_boundary
#print axioms Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.not_native_eta_model_sound
#print axioms Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.TypedNativeKForwardTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.not_typedNativeKForwardTK_eqEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.eq_typed_compact_controlTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.nat_typed_compact_controlTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit.eqGap_typed_compact_controlTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.kFreeT_cexTerm
#print axioms Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.kFreeT_cexType
#print axioms Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.kFreeT_closed_beta_cex
#print axioms Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.envTypedAtT_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.not_typingLemmaEnvT_of_cex_agreement
#print axioms Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.not_typingLemmaEnvT_of_kFree_agreement
#print axioms Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.approxTK_cexTerm
#print axioms Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.not_typingLemmaEnvT_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.closed_cex_control_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.not_modelConvSoundAt_of_closed_beta_agreement
#print axioms Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.not_modelConvSoundAt_approxTK_closed_beta
#print axioms Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit.not_fundCases_approxTK_natEnvU
#print axioms Rcic.Declarative.NativeValleys.TypedModelKReportAudit.approxTK_checked_boundary
-- END RCIC_NATIVE_TYPED_MODEL_K_SEAL_ROOTS

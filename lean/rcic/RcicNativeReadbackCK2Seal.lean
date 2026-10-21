import Lean
import rcic.RcicNativeReadbackCK2Conv
import rcic.RcicNativeReadbackCK2
import rcic.RcicNativeReadbackCK2Index
import rcic.RcicNativeReadbackCK2NativeControls
import rcic.RcicNativeReadbackCK2IndexDet
import rcic.RcicNativeReadbackCK2Inputs
import rcic.RcicNativeReadbackCK2ModelObstruction
import rcic.RcicNativeReadbackCK2Measurement
import rcic.RcicNativeReadbackCK2Gap

/-!
# Bounded CK2 repair and obstruction seal

All 314 explicitly named public declarations and inductive constructors
of the nine new leaves are queried below.  Every leaf is compiled from
its current source; dependency sources and cached objects are byte-audited
against current main.  Neither aggregate Foundation target is built.

Both complete readback cores satisfy DetR, NormalUniqueR and ReadbackLaws.
Both fail the unchanged global FundamentalSAtT input on the admitted Eq
environment.  The original local gap motives are exactly equivalent to
the explicit, still-unsupplied native EqGapTypedCtorArity port.
`closure_claim = 0`.
-/

/-- The exact project registration list, checked in this bounded module. -/
private def ck2SealedRoots : List Lean.Name := [
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.majorFamily,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.computedFamily,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.KIndexConvAt,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.KCommonAt,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.kCommonAt_irr,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.kCommonAt_of_conv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.KCanonW,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.iotaRhsOf_kcanon_eq,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.fields_length_eq_of_same_rec,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.kFreeRec_not_kProjRec,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.not_kProjRec_eqEnv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.KNativeHead,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.KNativeHead.intro,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.KNativeHead.kStar,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.KNativeHead.kProj,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.detR_kNativeHead,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.kNativeHead_ck_det,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.kIndexConvAt_eqGap,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.kCommonAt_eqGap,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.kNativeHead_eqGap,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.ExtendsEqEnv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.eqConvW,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.eqRefl_applyTel,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.eqConvW_computedFamily,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.eqKCanon_families,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.eqFamilyPartialTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.eqReflApplyTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.eqKGate_of_indexConv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.kNativeHead_eq_of_indexConv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.WhStepCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.WhStepCK2.ctx,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.WhStepCK2.native,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.WhStepCK2.recMajor,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.WhStepCK2.appHead,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.SaturatedRecSource,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.saturatedRecSource_app,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.whStepCK2_ctx_or_saturated,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.saturatedRecSource_is_app,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.saturatedRecSource_spine,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalR_sortCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalR_piCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalR_lamCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalR_bvarCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalR_famAppCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalR_ctorSpineCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalR_recPrefixCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.readbackLaws_whStepCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.whStepCtx_app_cases,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.whStepCtx_recCall_ctor,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.whStepCK2_ctx_det,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.recCall_const_inj,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.kNativeHead_whStepCK2_det,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.detR_whStepCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalUniqueR_whStepCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalR_kRec_of_no_native,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.whStepCK2_eqGap,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2Audit.redR_whStepCK2_eqGap,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.FirstWhnfMismatch,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.FirstWhnfMismatch.here,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.FirstWhnfMismatch.there,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.firstWhnfMismatch_det,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.firstWhnfMismatch_false_of_normal,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.FirstWhnfMismatchStar,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.FirstWhnfMismatchStar.refl,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.FirstWhnfMismatchStar.step,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.firstWhnfMismatchStar_eq_of_normal,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.firstWhnfMismatch_eqGap,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eqGap_indexConv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eqWitnessIndexCut,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.indexFn,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.indexId,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.indexBinderBeta,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.indexFnTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.indexIdTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.indexBinderBetaTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.indexBinderBetaConv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderEqCtx,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderEqCtxWf,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binder_indices_normal,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binder_index_schedule_stuck,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binder_index_control,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaEqCtx,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndex,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaEqCtxWf,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexConv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eta_indices_normal,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eta_index_schedule_stuck,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eta_index_control,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.deltaEqMember,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.deltaEqEnv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.deltaEqEnvWf,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.deltaIndexConv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.delta_index_schedule,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.deltaBinderIndex,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.deltaBinderIndexConv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.delta_binder_schedule_stuck,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.delta_index_control,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.computedBetaIndex,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.computedBetaIndexTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.computedBetaIndexConv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.computedBetaEqCtx,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.computedBetaEqCtxWf,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.computed_beta_schedule_stuck,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.computed_beta_index_control,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.WhnfIndexComplete,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.not_whnfIndexComplete_eqEnvT,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binder_index_no_alignment,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eta_index_no_alignment,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.scheduledCanonIdx,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.WhStepIndexCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.WhStepIndexCK2.ck,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.WhStepIndexCK2.index,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.WhStepIndexCK2.recMajor,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.WhStepIndexCK2.appHead,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.indexEqGapAlignedW,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.redR_whStepIndexCK2_eqGap,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.ScheduledRecSource,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.scheduledRecSource_app,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.whStepIndexCK2_ck_or_saturated,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.scheduledRecSource_is_app,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.scheduledRecSource_spine,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.normalR_sortIndexCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.normalR_piIndexCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.normalR_lamIndexCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.normalR_ctorIndexCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.normalR_famAppIndexCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.readbackLaws_whStepIndexCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.whStepIndexCK2_recPrefix_false_aux,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eqIndexW,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eqFnIndexW,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eqIndexRedex,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eqFnIndexRedex,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eqWitnessCtorData,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.whStepCK_eqIndex_false_aux,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.whStepCK_eqFnIndex_false_aux,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.whStepIndexCK2_eqIndex_false_aux,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.whStepIndexCK2_eqFnIndex_false_aux,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.normalR_whStepIndexCK2_eqIndex,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.normalR_whStepIndexCK2_eqFnIndex,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexMot,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexMot,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexRedex,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexRedex,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexRedex_normal,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexRedex_normal,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexRedex_not_sort,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexRedex_not_sort,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexFamily,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexCtor,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexFamilyTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexCtorTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexMotBodyTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexMotTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexMotAtConv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexRecTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexRedexConv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexFamily,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexCtor,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexParamTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexFamilyTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexCtorTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexMotBodyTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexMotTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexMotAtConv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexRecTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexRedexConv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binder_readback_countermodel,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eta_readback_countermodel,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.not_fundamentalLRST_whStepIndexCK2_binder,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.not_fundamentalLRST_whStepIndexCK2_eta,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.relSubstIdT_bot_of_noValue,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.not_lrSCoreS_index_binder_sort,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.not_fundConvAt_whStepIndexCK2_binder,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.not_lrSCoreS_index_eta_sort,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.not_fundConvAt_whStepIndexCK2_eta,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.not_fundamentalSAtT_whStepIndexCK2_eqEnvT,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.kNativeHead_binder,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.kNativeHead_eta,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.native_binder_control,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.native_eta_control,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaEqExtends,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaConstTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaBinderTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaFamilyTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaCtorTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaMotTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaMotAtConv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaRecTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaRedex,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaRedexConv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaHeadEqCtx,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaUnderBinderEqCtx,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaHeadEqCtxWf,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaUnderBinderEqCtxWf,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.kNativeHead_delta,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.kNativeHead_delta_under_binder,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.native_delta_control,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.native_delta_under_binder_control,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.firstWhnfMismatch_ne,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.indexSchedule_data_eq,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.IndexHead,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.IndexHead.intro,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.IndexHead.toStep,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.detR_indexHead,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.indexHead_ck_false,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.ck_app_cases_index,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.ck_recMajor_cases_index,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.whStepIndexCK2_ck_det,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.indexHead_whStepIndexCK2_det,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.detR_whStepIndexCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.normalUniqueR_whStepIndexCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.eqRec_structured_exists,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.eqRec_model_schema,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.eqRec_model_minor_forward,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.eqRec_model_minor_backward,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.eqRec_model_minor,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.eqGap_model_shape,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.EqGapUniformReadCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.eqGapFundConvAt_iff_uniformRead,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.eqGap_uniformRead_identity,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.not_fundTyAt_of_normal_prop_compact,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.not_fundamentalSAtT_of_normal_prop_compact,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartEqAt,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRight,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartCtx,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartMot,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRec,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartLeft_ty,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartCtx_wf,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRec_typed,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartCtx_identity,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartCtx_ctxEnv_eq_bot,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartCtx_identity_canonical,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartCtx_typed_identity,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRec_model,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRec_typed_model_seed,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRec_argTyped,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRight_model,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apart_separating_compacts_typed,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.not_apart_index_conv_of_fundamental,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.not_apart_family_conv_of_fundamental,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.not_apart_native_head_of_fundamental,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.not_fundamental_of_apart_head_normality,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.not_fundamentalSAtT_whStepCK2_eqEnv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.kNativeHead_apartRec_target,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.whStepCK2_apartRec_target,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.redR_whStepCK2_apartRec_cases,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRec_probeRealizedCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRec_normalIndex,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.not_fundTyAt_whStepIndexCK2_apartRec,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.not_fundamentalSAtT_whStepIndexCK2_eqEnv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRec_probeRealizedIndex,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.native_core_contract,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.index_core_contract,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.native_controls_readback,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.index_delta_readback,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.eqGap_actual_reads,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.eqGap_realized_of_read,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.eqGap_realized_both,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.probeEquiv_of_stepCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.probeEquiv_ctxCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.native_iota_probeCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.actionFnType,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.actionFn,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.actionExpandedFn,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.actionFnTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.actionHeadConv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.action_headCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.action_argCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.action_mixedCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.action_nonvacuityCK2,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.neither_original_fundamental,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapBetaIndex,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCall,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.substT_eqGapRedex,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapBetaIndexTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapBetaIndexConv,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqGap_typedSubst_data,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.redR_eqGap_subst_nonCtor_native,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.redR_gapCall_nonCtor_index,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.redR_eqGap_subst_nonCtor_index,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqEnv_ctorMember,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.isCtorSpine_eq_iff,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqMajor_cases,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCtorW,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.whStepCtx_gapCall_refl,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.whStepCtx_gapCall_ctor_two,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCall_iota_arity,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.whStepCtx_gapCall_arity,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.whStepCK_gapCall_ctor_arity,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.whStepCK2_gapCall_ctor_arity,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.whStepIndexCK2_gapCall_ctor_arity,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.redR_gapCall_ctor_arity_native,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.redR_gapCall_ctor_arity_index,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.normalR_gapCall_ctor_badarity_native,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.normalR_gapCall_ctor_badarity_index,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.EqGapRelatedCtorArity,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.EqGapTypedCtorArity,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.relSubstAtT_eqGap_bot_diagonal,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqGapRelatedCtorArity_iff_typed,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqGapUniformRead_native_iff_relatedCtorArity,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqGapUniformRead_index_iff_relatedCtorArity,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqGapFundConvAt_native_iff_typedCtorArity,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqGapFundConvAt_index_iff_typedCtorArity,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqGapFundConvAt_native_iff_index,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCanonicalMajor,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCanonicalSubst,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCanonicalMajorTy,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCanonicalSubst_typed,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCanonicalSubst_related,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCanonical_control,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCanonical_readbacks,
  ``Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapIdentity_control
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Quot.sound]
  for root in ck2SealedRoots do
    let (_, state) := ((CollectAxioms.collect root).run env).run {}
    for ax in state.axioms do
      unless allowed.contains ax do
        throwError "[rcic_ck2_seal] {root} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_ck2_seal] {ck2SealedRoots.length} public roots sealed; axioms ⊆ {allowed}"


-- BEGIN RCIC_NATIVE_READBACK_CK2_ROOTS
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.majorFamily
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.computedFamily
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.KIndexConvAt
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.KCommonAt
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.kCommonAt_irr
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.kCommonAt_of_conv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.KCanonW
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.iotaRhsOf_kcanon_eq
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.fields_length_eq_of_same_rec
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.kFreeRec_not_kProjRec
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.not_kProjRec_eqEnv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.KNativeHead
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.KNativeHead.intro
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.KNativeHead.kStar
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.KNativeHead.kProj
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.detR_kNativeHead
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.kNativeHead_ck_det
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.kIndexConvAt_eqGap
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.kCommonAt_eqGap
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.kNativeHead_eqGap
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.ExtendsEqEnv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.eqConvW
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.eqRefl_applyTel
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.eqConvW_computedFamily
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.eqKCanon_families
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.eqFamilyPartialTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.eqReflApplyTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.eqKGate_of_indexConv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit.kNativeHead_eq_of_indexConv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.WhStepCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.WhStepCK2.ctx
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.WhStepCK2.native
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.WhStepCK2.recMajor
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.WhStepCK2.appHead
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.SaturatedRecSource
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.saturatedRecSource_app
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.whStepCK2_ctx_or_saturated
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.saturatedRecSource_is_app
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.saturatedRecSource_spine
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalR_sortCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalR_piCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalR_lamCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalR_bvarCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalR_famAppCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalR_ctorSpineCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalR_recPrefixCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.readbackLaws_whStepCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.whStepCtx_app_cases
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.whStepCtx_recCall_ctor
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.whStepCK2_ctx_det
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.recCall_const_inj
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.kNativeHead_whStepCK2_det
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.detR_whStepCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalUniqueR_whStepCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.normalR_kRec_of_no_native
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.whStepCK2_eqGap
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2Audit.redR_whStepCK2_eqGap
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.FirstWhnfMismatch
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.FirstWhnfMismatch.here
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.FirstWhnfMismatch.there
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.firstWhnfMismatch_det
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.firstWhnfMismatch_false_of_normal
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.FirstWhnfMismatchStar
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.FirstWhnfMismatchStar.refl
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.FirstWhnfMismatchStar.step
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.firstWhnfMismatchStar_eq_of_normal
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.firstWhnfMismatch_eqGap
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eqGap_indexConv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eqWitnessIndexCut
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.indexFn
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.indexId
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.indexBinderBeta
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.indexFnTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.indexIdTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.indexBinderBetaTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.indexBinderBetaConv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderEqCtx
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderEqCtxWf
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binder_indices_normal
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binder_index_schedule_stuck
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binder_index_control
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaEqCtx
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndex
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaEqCtxWf
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexConv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eta_indices_normal
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eta_index_schedule_stuck
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eta_index_control
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.deltaEqMember
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.deltaEqEnv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.deltaEqEnvWf
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.deltaIndexConv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.delta_index_schedule
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.deltaBinderIndex
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.deltaBinderIndexConv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.delta_binder_schedule_stuck
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.delta_index_control
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.computedBetaIndex
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.computedBetaIndexTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.computedBetaIndexConv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.computedBetaEqCtx
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.computedBetaEqCtxWf
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.computed_beta_schedule_stuck
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.computed_beta_index_control
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.WhnfIndexComplete
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.not_whnfIndexComplete_eqEnvT
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binder_index_no_alignment
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eta_index_no_alignment
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.scheduledCanonIdx
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.WhStepIndexCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.WhStepIndexCK2.ck
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.WhStepIndexCK2.index
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.WhStepIndexCK2.recMajor
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.WhStepIndexCK2.appHead
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.indexEqGapAlignedW
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.redR_whStepIndexCK2_eqGap
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.ScheduledRecSource
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.scheduledRecSource_app
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.whStepIndexCK2_ck_or_saturated
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.scheduledRecSource_is_app
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.scheduledRecSource_spine
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.normalR_sortIndexCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.normalR_piIndexCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.normalR_lamIndexCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.normalR_ctorIndexCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.normalR_famAppIndexCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.readbackLaws_whStepIndexCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.whStepIndexCK2_recPrefix_false_aux
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eqIndexW
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eqFnIndexW
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eqIndexRedex
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eqFnIndexRedex
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eqWitnessCtorData
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.whStepCK_eqIndex_false_aux
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.whStepCK_eqFnIndex_false_aux
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.whStepIndexCK2_eqIndex_false_aux
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.whStepIndexCK2_eqFnIndex_false_aux
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.normalR_whStepIndexCK2_eqIndex
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.normalR_whStepIndexCK2_eqFnIndex
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexMot
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexMot
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexRedex
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexRedex
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexRedex_normal
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexRedex_normal
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexRedex_not_sort
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexRedex_not_sort
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexFamily
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexCtor
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexFamilyTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexCtorTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexMotBodyTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexMotTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexMotAtConv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexRecTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binderIndexRedexConv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexFamily
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexCtor
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexParamTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexFamilyTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexCtorTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexMotBodyTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexMotTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexMotAtConv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexRecTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.etaIndexRedexConv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.binder_readback_countermodel
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.eta_readback_countermodel
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.not_fundamentalLRST_whStepIndexCK2_binder
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.not_fundamentalLRST_whStepIndexCK2_eta
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.relSubstIdT_bot_of_noValue
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.not_lrSCoreS_index_binder_sort
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.not_fundConvAt_whStepIndexCK2_binder
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.not_lrSCoreS_index_eta_sort
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.not_fundConvAt_whStepIndexCK2_eta
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit.not_fundamentalSAtT_whStepIndexCK2_eqEnvT
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.kNativeHead_binder
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.kNativeHead_eta
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.native_binder_control
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.native_eta_control
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaEqExtends
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaConstTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaBinderTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaFamilyTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaCtorTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaMotTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaMotAtConv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaRecTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaRedex
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaRedexConv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaHeadEqCtx
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaUnderBinderEqCtx
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaHeadEqCtxWf
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.deltaUnderBinderEqCtxWf
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.kNativeHead_delta
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.kNativeHead_delta_under_binder
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.native_delta_control
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit.native_delta_under_binder_control
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.firstWhnfMismatch_ne
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.indexSchedule_data_eq
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.IndexHead
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.IndexHead.intro
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.IndexHead.toStep
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.detR_indexHead
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.indexHead_ck_false
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.ck_app_cases_index
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.ck_recMajor_cases_index
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.whStepIndexCK2_ck_det
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.indexHead_whStepIndexCK2_det
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.detR_whStepIndexCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit.normalUniqueR_whStepIndexCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.eqRec_structured_exists
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.eqRec_model_schema
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.eqRec_model_minor_forward
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.eqRec_model_minor_backward
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.eqRec_model_minor
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.eqGap_model_shape
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.EqGapUniformReadCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.eqGapFundConvAt_iff_uniformRead
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.eqGap_uniformRead_identity
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.not_fundTyAt_of_normal_prop_compact
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit.not_fundamentalSAtT_of_normal_prop_compact
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartEqAt
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRight
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartCtx
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartMot
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRec
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartLeft_ty
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartCtx_wf
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRec_typed
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartCtx_identity
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartCtx_ctxEnv_eq_bot
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartCtx_identity_canonical
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartCtx_typed_identity
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRec_model
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRec_typed_model_seed
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRec_argTyped
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRight_model
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apart_separating_compacts_typed
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.not_apart_index_conv_of_fundamental
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.not_apart_family_conv_of_fundamental
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.not_apart_native_head_of_fundamental
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.not_fundamental_of_apart_head_normality
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.not_fundamentalSAtT_whStepCK2_eqEnv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.kNativeHead_apartRec_target
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.whStepCK2_apartRec_target
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.redR_whStepCK2_apartRec_cases
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRec_probeRealizedCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRec_normalIndex
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.not_fundTyAt_whStepIndexCK2_apartRec
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.not_fundamentalSAtT_whStepIndexCK2_eqEnv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit.apartRec_probeRealizedIndex
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.native_core_contract
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.index_core_contract
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.native_controls_readback
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.index_delta_readback
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.eqGap_actual_reads
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.eqGap_realized_of_read
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.eqGap_realized_both
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.probeEquiv_of_stepCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.probeEquiv_ctxCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.native_iota_probeCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.actionFnType
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.actionFn
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.actionExpandedFn
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.actionFnTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.actionHeadConv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.action_headCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.action_argCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.action_mixedCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.action_nonvacuityCK2
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit.neither_original_fundamental
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapBetaIndex
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCall
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.substT_eqGapRedex
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapBetaIndexTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapBetaIndexConv
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqGap_typedSubst_data
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.redR_eqGap_subst_nonCtor_native
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.redR_gapCall_nonCtor_index
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.redR_eqGap_subst_nonCtor_index
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqEnv_ctorMember
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.isCtorSpine_eq_iff
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqMajor_cases
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCtorW
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.whStepCtx_gapCall_refl
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.whStepCtx_gapCall_ctor_two
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCall_iota_arity
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.whStepCtx_gapCall_arity
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.whStepCK_gapCall_ctor_arity
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.whStepCK2_gapCall_ctor_arity
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.whStepIndexCK2_gapCall_ctor_arity
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.redR_gapCall_ctor_arity_native
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.redR_gapCall_ctor_arity_index
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.normalR_gapCall_ctor_badarity_native
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.normalR_gapCall_ctor_badarity_index
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.EqGapRelatedCtorArity
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.EqGapTypedCtorArity
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.relSubstAtT_eqGap_bot_diagonal
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqGapRelatedCtorArity_iff_typed
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqGapUniformRead_native_iff_relatedCtorArity
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqGapUniformRead_index_iff_relatedCtorArity
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqGapFundConvAt_native_iff_typedCtorArity
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqGapFundConvAt_index_iff_typedCtorArity
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.eqGapFundConvAt_native_iff_index
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCanonicalMajor
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCanonicalSubst
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCanonicalMajorTy
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCanonicalSubst_typed
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCanonicalSubst_related
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCanonical_control
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapCanonical_readbacks
#print axioms Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit.gapIdentity_control
-- END RCIC_NATIVE_READBACK_CK2_ROOTS

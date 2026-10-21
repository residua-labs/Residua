import Lean
import rcic.RcicNativeTypedModelCovRelAgreement
import rcic.RcicNativeTypedModelCovRelApp
import rcic.RcicNativeTypedModelCovRelCore
import rcic.RcicNativeTypedModelCovRelEqGap
import rcic.RcicNativeTypedModelCovRelEscape
import rcic.RcicNativeTypedModelCovRelExpansion
import rcic.RcicNativeTypedModelCovRelFund
import rcic.RcicNativeTypedModelCovRelFundApp
import rcic.RcicNativeTypedModelCovRelPER
import rcic.RcicNativeTypedModelCovRelPERControl
import rcic.RcicNativeTypedModelCovRelRealization
import rcic.RcicNativeTypedModelCovRelSubst
import rcic.RcicNativeTypedModelCovRelSubstAgreement
import rcic.RcicNativeTypedModelCovRelWitness

/-!
# Bounded seal for the typing-parametric covariant recursive relation

Every public declaration of the composition leaves is registered below.
This seal checks existence and actual transitive axiom dependencies. The
raw type escape and raw global typing statements have explicit kernel
refutations. The fundamental assembler and the complete Eq target remain
conditional at the exact named native inputs described in their leaves.

Only this bounded seal is built. `closure_claim = 0`.
-/

private def covRelRoots : List Lean.Name := [
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovGateAgreement,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_sort,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_pi_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_pi_bot_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_lam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_pi_of_ctyS_rows,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_polyIdCpt01,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_polyIdTyCpt01,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_iff_coreS,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrsCov_iff_lrss,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_app,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_app_diagonal_arg,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_app_diagonal_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovLamTyping,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovTyping,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covTypingCTyCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovTypingIncludesS,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covTypingCTyCov_includesS,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.LRSCoreCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.LRSCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_prop_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_sort_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_prop_iff_sort,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_spine_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_sortIdx_irrel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_spine_irrel_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.IrrelAtCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.SymmTmAtCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.TransTmAtCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.SymmTyAtCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.TransTyAtCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.eqGap_subst_read_of_typedCtorArity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.eqGapFundTyAt_approxTK_iff_typedCtorArity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.not_eqGapFundTyAt_approxTK_of_typed_badarity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.eqGapDirectAlias_fundConvAt_of_typedCtorArity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.relSubstAtCov_eqGap_bot_diagonal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.eqGapFundTyAtCov_approxTK_iff_typedCtorArity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.eqGapFundTyAtCov_approxTK_iff_old,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.eqGapDirectAlias_fundConvAtCov_of_typedCtorArity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.eqGapDirectAlias_fundConvAtCov_iff_typedCtorArity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.eqGapCanonical_cov_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.eqGapAlias_type_read,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.envTypedCovAtP_eqGap_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.idPiProp_covRel_at_alias,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.not_elTCovP_at_eqGapAlias,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.alias_type_escape_counterexample,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.RawCovEscape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.not_rawCovEscape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.GuardedCovTyping,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.not_guardedCovTyping,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.not_alias_covTyping_of_observations,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.not_typingLemmaEnvCovM_approxTK_eqEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.not_raw_covTypedEnvelope_escape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_expand_red_both,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_expand_red,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_expand_red_right,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_expand,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_expand_right,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.FundTyAtCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.FundConvAtCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.FundamentalCovAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.TyValidAtCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CtxValidAtCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.FundTyAtCov.modelMap,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundTyAtCov_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.FundConvAtCov.modelMap,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundConvAtCov_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundTyAtCov_approxTK_iff_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundConvAtCov_approxTK_iff_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovSubstGateFor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovObservationGateFor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundTyAtCov_of_old,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundConvAtCov_of_old,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundTyAtCov_approxTK_of_old_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundConvAtCov_approxTK_of_old_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovAtomicModelLaws,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covAtomicModelLaws_of_old,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covAtomicModelLaws_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_bvar,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_bvar_via_old,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_sort,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_refl,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_sorts,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_zetaLocal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_refl_via_old,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundConvAtCov_of_model_contract,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundConvAtCov_beta_of_model_contract,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundConvAtCov_beta_via_old,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.approxTK_app_elim_cov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovAppArms,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_app_approxTK_of_arms,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.IHBelowFundCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.FundTyCovStep,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.FundConvCovStep,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.FundCovCases,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_strong,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundamentalCovAt_of_cases,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundamentalCovAt_approxTK_of_cases,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.ctxValidAtCov_of_fundamental,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_app_via_old_cases,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.RelSubstAtCov.nativeInstances,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovAppResiduals,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covAppArms_of_native_motives,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_app_approxTK_of_residuals,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_app_step_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.TurnAtCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covPERKernel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.typedPERCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_irrel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_symm,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_trans,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_symm_tm,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_trans_tm,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelPERControlAudit.typedPERCov_whStepCK2_emptyEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelPERControlAudit.lrSCoreCov_idSort1Ty_polyIdDom1,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelPERControlAudit.idSort1_cov_per_control_emptyEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.NormalizedCovRealization,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.normalizedCovRealization_iff_at_normal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.normalizedCovRealization_eqGapAlias,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.normalizedCovRealization_eqGapAlias_ctyCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.alias_raw_and_normalized_realization,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.eqGapAlias_normalized_envelope,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.not_normalizedCovRealization_natSucc,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.NormalizedCovEscape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.not_normalizedCovEscape_ctyCov_nat,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.ElTCovP,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.EnvTypedCovAtP,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.elTCovP_ctyCov_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.envTypedCovAtP_ctyCov_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.envTypedCovAtP_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.envTypedCovAtP_bot_of_no_values,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.elTCovP_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.ctxEnvM_cov_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.envTypedCovAtP_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.envTypedCovAtP_approxTK_iff_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.RelSubstAtCov,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.RelSubstAtCov.ctxEnvs,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.relSubstAtCov_bot_diagonal_of_no_values,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.RelSubstAtCov.modelMap,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.relSubstAtCov_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.relSubstAtCov_approxTK_iff_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.relSubstAtCov_iff_old_of_relation_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.envTypedCovAtP_zetaLocalSortCtx_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.relSubstAtCov_zetaLocalSortCtx_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.zetaLocalSortCtx_cov_related_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovSubstGateAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.RelSubstAtCov.toOld,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.RelSubstAtCov.ofOld,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.relSubstAtCov_iff_old_of_gate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovSubstGateAt.modelMap,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covSubstGateAt_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covSubstGateAt_approxTK_iff_of_kFree_values,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.RelSubstAtCov.diagL,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.RelSubstAtCov.diagR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovSubstGateAt.diagL,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovSubstGateAt.diagR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covSubstGateAt_zetaLocalSortCtx_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.relSubstAtCov_zetaLocalSortCtx_toOld,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.lrSCoreCov_identity_row,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.lrSCoreCov_polyId_cpt01,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.polyId_covRel_control_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.lrSCoreCov_natSucc_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.natSucc_covRel_nonEscape_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.approxTK_natRec_good_call,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.redR_natRec_good_call,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.lrSCoreCov_natRec_good_call,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.natRec_covRel_control_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.eqGapDirectAlias_lrsCoreCov_prop
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Quot.sound]
  for root in covRelRoots do
    unless env.contains root do
      throwError "Covariant recursive relation seal: missing root {root}"
    let (_, state) := ((CollectAxioms.collect root).run env).run {}
    for ax in state.axioms do
      unless allowed.contains ax do
        throwError "Covariant recursive relation seal: {root} uses disallowed axiom {ax}"
  logInfo m!"Covariant recursive relation seal: {covRelRoots.length} roots checked; allowed axioms = {allowed}"

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_REL_SEAL_ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovGateAgreement
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_sort
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_pi_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_pi_bot_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_lam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_pi_of_ctyS_rows
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_polyIdCpt01
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covGateAgreement_polyIdTyCpt01
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_iff_coreS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrsCov_iff_lrss
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_app
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_app_diagonal_arg
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_app_diagonal_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovLamTyping
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovTyping
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covTypingCTyCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovTypingIncludesS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covTypingCTyCov_includesS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.LRSCoreCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.LRSCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_prop_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_sort_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_prop_iff_sort
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_spine_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_sortIdx_irrel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_spine_irrel_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.IrrelAtCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.SymmTmAtCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.TransTmAtCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.SymmTyAtCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.TransTyAtCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.eqGap_subst_read_of_typedCtorArity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.eqGapFundTyAt_approxTK_iff_typedCtorArity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.not_eqGapFundTyAt_approxTK_of_typed_badarity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.eqGapDirectAlias_fundConvAt_of_typedCtorArity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.relSubstAtCov_eqGap_bot_diagonal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.eqGapFundTyAtCov_approxTK_iff_typedCtorArity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.eqGapFundTyAtCov_approxTK_iff_old
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.eqGapDirectAlias_fundConvAtCov_of_typedCtorArity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.eqGapDirectAlias_fundConvAtCov_iff_typedCtorArity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEqGapAudit.eqGapCanonical_cov_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.eqGapAlias_type_read
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.envTypedCovAtP_eqGap_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.idPiProp_covRel_at_alias
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.not_elTCovP_at_eqGapAlias
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.alias_type_escape_counterexample
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.RawCovEscape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.not_rawCovEscape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.GuardedCovTyping
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.not_guardedCovTyping
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.not_alias_covTyping_of_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.not_typingLemmaEnvCovM_approxTK_eqEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit.not_raw_covTypedEnvelope_escape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_expand_red_both
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_expand_red
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_expand_red_right
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_expand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_expand_right
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.FundTyAtCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.FundConvAtCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.FundamentalCovAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.TyValidAtCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CtxValidAtCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.FundTyAtCov.modelMap
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundTyAtCov_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.FundConvAtCov.modelMap
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundConvAtCov_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundTyAtCov_approxTK_iff_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundConvAtCov_approxTK_iff_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovSubstGateFor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovObservationGateFor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundTyAtCov_of_old
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundConvAtCov_of_old
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundTyAtCov_approxTK_of_old_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundConvAtCov_approxTK_of_old_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovAtomicModelLaws
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covAtomicModelLaws_of_old
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covAtomicModelLaws_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_bvar
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_bvar_via_old
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_sort
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_refl
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_sorts
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_zetaLocal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_refl_via_old
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundConvAtCov_of_model_contract
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundConvAtCov_beta_of_model_contract
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundConvAtCov_beta_via_old
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.approxTK_app_elim_cov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovAppArms
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_app_approxTK_of_arms
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.IHBelowFundCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.FundTyCovStep
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.FundConvCovStep
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.FundCovCases
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_strong
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundamentalCovAt_of_cases
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundamentalCovAt_approxTK_of_cases
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.ctxValidAtCov_of_fundamental
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_app_via_old_cases
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.RelSubstAtCov.nativeInstances
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovAppResiduals
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covAppArms_of_native_motives
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_app_approxTK_of_residuals
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.fundCov_app_step_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.TurnAtCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covPERKernel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.typedPERCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_irrel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_symm
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_trans
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_symm_tm
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.lrSCoreCov_trans_tm
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelPERControlAudit.typedPERCov_whStepCK2_emptyEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelPERControlAudit.lrSCoreCov_idSort1Ty_polyIdDom1
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelPERControlAudit.idSort1_cov_per_control_emptyEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.NormalizedCovRealization
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.normalizedCovRealization_iff_at_normal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.normalizedCovRealization_eqGapAlias
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.normalizedCovRealization_eqGapAlias_ctyCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.alias_raw_and_normalized_realization
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.eqGapAlias_normalized_envelope
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.not_normalizedCovRealization_natSucc
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.NormalizedCovEscape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit.not_normalizedCovEscape_ctyCov_nat
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.ElTCovP
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.EnvTypedCovAtP
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.elTCovP_ctyCov_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.envTypedCovAtP_ctyCov_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.envTypedCovAtP_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.envTypedCovAtP_bot_of_no_values
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.elTCovP_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.ctxEnvM_cov_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.envTypedCovAtP_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.envTypedCovAtP_approxTK_iff_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.RelSubstAtCov
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.RelSubstAtCov.ctxEnvs
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.relSubstAtCov_bot_diagonal_of_no_values
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.RelSubstAtCov.modelMap
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.relSubstAtCov_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.relSubstAtCov_approxTK_iff_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.relSubstAtCov_iff_old_of_relation_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.envTypedCovAtP_zetaLocalSortCtx_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.relSubstAtCov_zetaLocalSortCtx_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.zetaLocalSortCtx_cov_related_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovSubstGateAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.RelSubstAtCov.toOld
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.RelSubstAtCov.ofOld
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.relSubstAtCov_iff_old_of_gate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovSubstGateAt.modelMap
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covSubstGateAt_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covSubstGateAt_approxTK_iff_of_kFree_values
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.RelSubstAtCov.diagL
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.RelSubstAtCov.diagR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovSubstGateAt.diagL
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.CovSubstGateAt.diagR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.covSubstGateAt_zetaLocalSortCtx_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelAudit.relSubstAtCov_zetaLocalSortCtx_toOld
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.lrSCoreCov_identity_row
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.lrSCoreCov_polyId_cpt01
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.polyId_covRel_control_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.lrSCoreCov_natSucc_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.natSucc_covRel_nonEscape_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.approxTK_natRec_good_call
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.redR_natRec_good_call
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.lrSCoreCov_natRec_good_call
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.natRec_covRel_control_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit.eqGapDirectAlias_lrsCoreCov_prop
-- END RCIC_NATIVE_TYPED_MODEL_COV_REL_SEAL_ROOTS

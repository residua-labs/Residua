import Lean
import rcic.RcicNativeTypedModelCovKGuard
import rcic.RcicNativeTypedModelCovRelBoundary
import rcic.RcicNativeTypedModelCovAdapterWitness

/-!
# Bounded seal for the covariant ApproxTK measurement

All public declarations of the five composition leaves are roots below.
The seal checks their actual transitive axiom dependencies.  The imported
CTyCov, KG, ApproxTK, CK2 and native fixtures are not redefined here.

The local closed counterexample is covariantly typed.  Global covariant
typing, native completeness of KG, and unconditional return to CTyS have
separate kernel refutations.  The beta relation adapter has explicit forward
model preservation and contractum diagonal inputs.  The covariant envelope
does not constitute the missing covariant recursive escape relation.

Only this bounded seal is built.  `closure_claim = 0`.
-/

private def covKRoots : List Lean.Name := [
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.ElTCovM,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.EnvTypedCovAtM,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.CovTypingAtM,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.TypingLemmaEnvCovM,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.elTCovM_approxT_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.envTypedCovAtM_approxT_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.typingLemmaEnvCovM_approxT_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.envTypedCovAtM_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.envTypedCovAtM_of_envTypedAtT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.elTCovM_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.covTyping_cexTerm,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.covTyping_cexType,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.covTyping_cexTerm_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.covTyping_cexType_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.closed_cex_cov_control_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.closed_cex_cov_eq_nat_controls,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.not_cov_global_of_natSucc_observations,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.not_typingLemmaEnvCovM_approxTK_natEnvU,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKAudit.nat_succ_cov_obstruction_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit.kg_six_agreement_controls,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit.kg_six_native_conjunction_controls,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit.kg_six_native_typing_controls,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit.kg_deltaBinder_native_obstruction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit.kg_and_strict_guard_cross_controls,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit.kg_deltaConst_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit.KGDeltaEtaCompositionAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit.not_kgDeltaEtaCompositionAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit.fundConvAt_of_model_contractT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit.fundConvAt_beta_of_model_contractT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit.approxTK_function_variable_beta_contract,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit.no_eqGap_realized_beta_factorization,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit.approxTK_eqGapDirectAlias_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit.eqGapDirectAlias_lrsCoreS_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit.eqGapDirectAlias_beta_route_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.ctyCov_strict_polyId,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.NativeCovToSReentryM,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.polyId_cov_reentry_control_approxT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.polyId_cov_reentry_control_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.not_nativeCovToSReentryM_approxT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.not_nativeCovToSReentryM_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.CovTypedEnvelopeT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.covTypedEnvelopeT_expand_red,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.envTypedCovAtM_eqGap_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.eqGapDirectAlias_cov_envelope_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovAdapterWitnessAudit.sortBetaSrc,
  ``Rcic.Declarative.NativeValleys.TypedModelCovAdapterWitnessAudit.approxTK_sortBeta_contract,
  ``Rcic.Declarative.NativeValleys.TypedModelCovAdapterWitnessAudit.SortBetaAdapterWitnessT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovAdapterWitnessAudit.sortBetaAdapterWitnessT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovAdapterWitnessAudit.eq_nat_sortBetaAdapterWitnessT
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Quot.sound]
  for root in covKRoots do
    let (_, state) := ((CollectAxioms.collect root).run env).run {}
    for ax in state.axioms do
      unless allowed.contains ax do
        throwError "Covariant ApproxTK seal: {root} uses disallowed axiom {ax}"
  logInfo m!"Covariant ApproxTK seal: {covKRoots.length} roots checked; allowed axioms = {allowed}"

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_K_SEAL_ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.ElTCovM
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.EnvTypedCovAtM
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.CovTypingAtM
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.TypingLemmaEnvCovM
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.elTCovM_approxT_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.envTypedCovAtM_approxT_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.typingLemmaEnvCovM_approxT_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.envTypedCovAtM_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.envTypedCovAtM_of_envTypedAtT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.elTCovM_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.covTyping_cexTerm
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.covTyping_cexType
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.covTyping_cexTerm_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.covTyping_cexType_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.closed_cex_cov_control_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.closed_cex_cov_eq_nat_controls
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.not_cov_global_of_natSucc_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.not_typingLemmaEnvCovM_approxTK_natEnvU
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKAudit.nat_succ_cov_obstruction_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit.kg_six_agreement_controls
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit.kg_six_native_conjunction_controls
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit.kg_six_native_typing_controls
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit.kg_deltaBinder_native_obstruction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit.kg_and_strict_guard_cross_controls
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit.kg_deltaConst_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit.KGDeltaEtaCompositionAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit.not_kgDeltaEtaCompositionAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit.fundConvAt_of_model_contractT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit.fundConvAt_beta_of_model_contractT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit.approxTK_function_variable_beta_contract
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit.no_eqGap_realized_beta_factorization
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit.approxTK_eqGapDirectAlias_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit.eqGapDirectAlias_lrsCoreS_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit.eqGapDirectAlias_beta_route_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.ctyCov_strict_polyId
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.NativeCovToSReentryM
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.polyId_cov_reentry_control_approxT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.polyId_cov_reentry_control_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.not_nativeCovToSReentryM_approxT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.not_nativeCovToSReentryM_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.CovTypedEnvelopeT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.covTypedEnvelopeT_expand_red
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.envTypedCovAtM_eqGap_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit.eqGapDirectAlias_cov_envelope_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovAdapterWitnessAudit.sortBetaSrc
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovAdapterWitnessAudit.approxTK_sortBeta_contract
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovAdapterWitnessAudit.SortBetaAdapterWitnessT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovAdapterWitnessAudit.sortBetaAdapterWitnessT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovAdapterWitnessAudit.eq_nat_sortBetaAdapterWitnessT
-- END RCIC_NATIVE_TYPED_MODEL_COV_K_SEAL_ROOTS

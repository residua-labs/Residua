import Lean
import rcic.RcicNativeTypedModelCovXActions
import rcic.RcicNativeTypedModelCovXBoundary
import rcic.RcicNativeTypedModelCovXCasePorts
import rcic.RcicNativeTypedModelCovXCoherence
import rcic.RcicNativeTypedModelCovXCore
import rcic.RcicNativeTypedModelCovXEnvBoundary
import rcic.RcicNativeTypedModelCovXEta
import rcic.RcicNativeTypedModelCovXEtaBoundary
import rcic.RcicNativeTypedModelCovXEtaControl
import rcic.RcicNativeTypedModelCovXEtaFactor
import rcic.RcicNativeTypedModelCovXEtaFund
import rcic.RcicNativeTypedModelCovXEtaObserved
import rcic.RcicNativeTypedModelCovXExpansion
import rcic.RcicNativeTypedModelCovXInterface
import rcic.RcicNativeTypedModelCovXLetControl
import rcic.RcicNativeTypedModelCovXPER
import rcic.RcicNativeTypedModelCovXRealization
import rcic.RcicNativeTypedModelCovXRealizationNat
import rcic.RcicNativeTypedModelCovXRealizationPorts
import rcic.RcicNativeTypedModelCovXSubstLaws
import rcic.RcicNativeTypedModelCovXTypePosition

/-!
# Bounded seal: extensional Pi and hereditary realization measurements

The complete Nat.succ eta motive and the alias-Pi hereditary target are
positive. Eager finite views are refuted at the impredicative proposition;
the full lambda/eta motives inherit that obstruction. A second independent
counterexample refutes raw covariant environment extension from hereditary
realization. No global fundamental supplier is asserted.

Every authored public declaration in the imported CovX leaves is registered
below. This seal composes Lean's axiom collector and checks the exact allowed
set. It does not import RcicFoundation or RcicFoundationSeal as a build root.
`closure_claim = 0`.
-/

private def covXRoots : Array Lean.Name := #[
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_app_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_of_old_sort,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_base_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundCovX_sort,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundCovX_sorts,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundConvAtCovX_of_model_contract,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundConvAtCovX_beta_of_model_contract,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXTypeView_has_normal_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXTypedViews,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXTypedViews_implies_type_normalization,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXTypeView_impredicative_false,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.not_covXTypeView_idPiProp_eq,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.not_covXTypedViews_eqEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.not_covXTypeView_pi_idPiProp,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXPolyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXPolyPropLamTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXPolyPropLam_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXPolyPropLam_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.not_lrSCoreCovX_polyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covX_eager_view_typed_counterexample,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.not_fundTyAtCovX_polyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.not_fundamentalCovXAt_eqEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXPolyPropLam_piGate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXPolyPropLam_one_layer_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXPolyPropLam_typed_action_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXTypeTransportAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXTypeTransportAt_of_readback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXTypeTransportAt_eqGapAlias,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXTypeTransportAt_eqGapAlias_native_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXTypeTransportFor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXTypeTransportFor_refl,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXMiddleObservationFor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXMiddleObservationFor_refl,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundTyAtCovX_type_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundConvAtCovX_type_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundConvAtCovX_symm_of_ports,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundConvAtCovX_trans_of_middle,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covX_sort_ports_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_view_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXNormalHeadAgreement,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXNormalHeadAgreement_of_red,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXTypeView.reindex,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_reindex_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.LRSCoreCovX,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_of_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_iff_at_view,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_type_heads_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_type_readback_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXTypeView,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXPiGate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXCompactAction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.LRSCoreCovXAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXUniverseCompatibility,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXPiGate_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covX_spine_application_grows,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_pi_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEnvBoundaryAudit.approxTK_lift_eqGapPrefix_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEnvBoundaryAudit.approxTK_lift_eqGapDirectAlias_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEnvBoundaryAudit.not_envTypedCovAtP_alias_cons,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEnvBoundaryAudit.not_relSubstAtCovX_alias_cons,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEnvBoundaryAudit.CovXRawAssumptionExtension,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEnvBoundaryAudit.covX_alias_raw_extension_counterexample,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEnvBoundaryAudit.not_covXRawAssumptionExtension_eqGap,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_eta_app_readback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_eta_action_of_beta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_native_port,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_spine_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_spine_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_not_approxTK_lam_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.CovXModelEtaObservationAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_not_modelEtaObservation_natSucc,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_eta_observation_boundary,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covXPolyPropLam_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.not_lrSCoreCovX_eta_polyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.not_fundConvAtCovX_eta_polyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_eta_eager_view_counterexample,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covXNatView,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covXNatArrowView,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_pi_gate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natArrow_spine_of_action,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natArrow_lam_of_rows,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_at_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natZero_related,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.CovXCompactActionCovers,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.CovXEtaActionFactorAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.lrSCoreCovXAt_pi_of_action_covers,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_eta_left_of_action_factor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_action_covers,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_action_factor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_eta_actions_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_eta_action_factor_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covXNatEtaEmptyRow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_empty_row_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_factor_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.fundTyAtCovX_natSucc,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.fundConvAtCovX_eta_natSucc,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_motive_changed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_fund_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_app_observation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_observation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covXNatRows,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covXNatRows_not_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_nat_annotation_demands,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_pi_gate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_type_observation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_expand_red_both,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_expand_red,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_expand_red_right,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_eta_left,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_eta_right,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_symm,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_trans,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_expand_red_both,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXSquare,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXSquare.swap,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.RelSubstAtCovX,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.RelSubstAtCovX.ctxEnvs,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.relSubstAtCovX_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.RelSubstAtCovX.swap,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.FundTyAtCovX,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.FundConvAtCovX,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.FundamentalCovXAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundCovX_bvar,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundCovX_refl,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundCovX_zetaLocal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXLetAudit.relSubstAtCovX_zetaLocalSortCtx_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXLetAudit.covX_zetaLocalSortCtx_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXFixedPER,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_PER,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_symm,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_trans,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.HereditaryCovRealizationXAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.hereditaryCovRealizationXAt_sort_of_related,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.hereditaryCovRealizationXAt_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.covXAliasPiView,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.covXAliasIdentity_piGate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.covXAliasIdentity_related,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.hereditaryCovRealizationXAt_covNormAliasPi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.covXAlias_hereditary_native_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.hereditary_alias_does_not_supply_raw_type_port,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationNatAudit.covX_base_related_compact_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationNatAudit.covX_nat_spine_realization,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationNatAudit.covX_nat_realization_of_related,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationNatAudit.covX_natSucc_hereditary_realization,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationNatAudit.covX_eq_and_nat_hereditary_controls,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationPortsAudit.CovXHereditarySupplyAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationPortsAudit.hereditaryCovRealizationXAt_of_supply,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationPortsAudit.hereditaryCovRealizationXAt_escape_pair,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationPortsAudit.covXHereditarySupplyAt_nat,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationPortsAudit.covXHereditarySupplyAt_natSucc,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationPortsAudit.covXHereditarySupplyAt_alias,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXRealizationPortsAudit.covXHereditarySupplyAt_alias_native_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.RelSubstAtCovX.diagL,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.RelSubstAtCovX.envs,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.RelSubstAtCovX.modelMap,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.relSubstAtCovX_congr,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.relSubstAtCovX_approxTK_iff_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundTyAtCovX_approxTK_iff_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundConvAtCovX_approxTK_iff_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.TypeReadbackObservationTK,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.TypePositionReadbackAtTK,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.typeReadbackObservationTK_iff_at_normal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.typePositionReadbackAtTK_of_normal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.typePositionReadbackAtTK_sort_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.typeReadbackObservationTK_eqGapAlias,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.not_typePositionReadbackAtTK_eqGapAlias,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.typePositionReadback_alias_native_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.typeReadback_alias_and_apart_guard,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.typeReadbackObservationTK_apart_prop_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.typeReadbackObservationTK_apart_bot_of_no_sort
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound]
  for root in covXRoots do
    if !env.contains root then
      throwError "CovX seal: missing declaration {root}"
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "CovX seal: {root} has forbidden axioms {forbidden}"
  logInfo m!"CovX seal: {covXRoots.size} public roots checked; allowed axioms = {allowed}"

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_SEAL_ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_app_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_of_old_sort
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_base_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundCovX_sort
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundCovX_sorts
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundConvAtCovX_of_model_contract
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundConvAtCovX_beta_of_model_contract
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXTypeView_has_normal_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXTypedViews
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXTypedViews_implies_type_normalization
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXTypeView_impredicative_false
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.not_covXTypeView_idPiProp_eq
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.not_covXTypedViews_eqEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.not_covXTypeView_pi_idPiProp
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXPolyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXPolyPropLamTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXPolyPropLam_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXPolyPropLam_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.not_lrSCoreCovX_polyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covX_eager_view_typed_counterexample
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.not_fundTyAtCovX_polyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.not_fundamentalCovXAt_eqEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXPolyPropLam_piGate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXPolyPropLam_one_layer_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXPolyPropLam_typed_action_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXTypeTransportAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXTypeTransportAt_of_readback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXTypeTransportAt_eqGapAlias
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXTypeTransportAt_eqGapAlias_native_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXTypeTransportFor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXTypeTransportFor_refl
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXMiddleObservationFor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXMiddleObservationFor_refl
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundTyAtCovX_type_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundConvAtCovX_type_transport
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundConvAtCovX_symm_of_ports
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundConvAtCovX_trans_of_middle
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covX_sort_ports_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_view_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXNormalHeadAgreement
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXNormalHeadAgreement_of_red
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXTypeView.reindex
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_reindex_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.LRSCoreCovX
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_of_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_iff_at_view
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_type_heads_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_type_readback_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXTypeView
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXPiGate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXCompactAction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.LRSCoreCovXAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXUniverseCompatibility
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covXPiGate_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.covX_spine_application_grows
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_pi_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEnvBoundaryAudit.approxTK_lift_eqGapPrefix_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEnvBoundaryAudit.approxTK_lift_eqGapDirectAlias_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEnvBoundaryAudit.not_envTypedCovAtP_alias_cons
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEnvBoundaryAudit.not_relSubstAtCovX_alias_cons
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEnvBoundaryAudit.CovXRawAssumptionExtension
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEnvBoundaryAudit.covX_alias_raw_extension_counterexample
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEnvBoundaryAudit.not_covXRawAssumptionExtension_eqGap
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_eta_app_readback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_eta_action_of_beta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_native_port
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_spine_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_spine_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_not_approxTK_lam_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.CovXModelEtaObservationAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_not_modelEtaObservation_natSucc
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_eta_observation_boundary
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covXPolyPropLam_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.not_lrSCoreCovX_eta_polyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.not_fundConvAtCovX_eta_polyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_eta_eager_view_counterexample
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covXNatView
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covXNatArrowView
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_pi_gate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natArrow_spine_of_action
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natArrow_lam_of_rows
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_at_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natZero_related
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.CovXCompactActionCovers
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.CovXEtaActionFactorAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.lrSCoreCovXAt_pi_of_action_covers
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_eta_left_of_action_factor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_action_covers
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_action_factor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_eta_actions_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_eta_action_factor_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covXNatEtaEmptyRow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_empty_row_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_factor_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.fundTyAtCovX_natSucc
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.fundConvAtCovX_eta_natSucc
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_motive_changed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_fund_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_app_observation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_observation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covXNatRows
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covXNatRows_not_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_nat_annotation_demands
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_pi_gate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit.covX_natSucc_eta_type_observation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_expand_red_both
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_expand_red
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_expand_red_right
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_eta_left
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_eta_right
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_symm
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_trans
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovX_expand_red_both
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXSquare
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXSquare.swap
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.RelSubstAtCovX
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.RelSubstAtCovX.ctxEnvs
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.relSubstAtCovX_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.RelSubstAtCovX.swap
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.FundTyAtCovX
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.FundConvAtCovX
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.FundamentalCovXAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundCovX_bvar
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundCovX_refl
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundCovX_zetaLocal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXLetAudit.relSubstAtCovX_zetaLocalSortCtx_approxTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXLetAudit.covX_zetaLocalSortCtx_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.CovXFixedPER
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_PER
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_symm
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.lrSCoreCovXAt_trans
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.HereditaryCovRealizationXAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.hereditaryCovRealizationXAt_sort_of_related
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.hereditaryCovRealizationXAt_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.covXAliasPiView
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.covXAliasIdentity_piGate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.covXAliasIdentity_related
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.hereditaryCovRealizationXAt_covNormAliasPi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.covXAlias_hereditary_native_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationAudit.hereditary_alias_does_not_supply_raw_type_port
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationNatAudit.covX_base_related_compact_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationNatAudit.covX_nat_spine_realization
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationNatAudit.covX_nat_realization_of_related
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationNatAudit.covX_natSucc_hereditary_realization
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationNatAudit.covX_eq_and_nat_hereditary_controls
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationPortsAudit.CovXHereditarySupplyAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationPortsAudit.hereditaryCovRealizationXAt_of_supply
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationPortsAudit.hereditaryCovRealizationXAt_escape_pair
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationPortsAudit.covXHereditarySupplyAt_nat
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationPortsAudit.covXHereditarySupplyAt_natSucc
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationPortsAudit.covXHereditarySupplyAt_alias
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXRealizationPortsAudit.covXHereditarySupplyAt_alias_native_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.RelSubstAtCovX.diagL
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.RelSubstAtCovX.envs
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.RelSubstAtCovX.modelMap
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.relSubstAtCovX_congr
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.relSubstAtCovX_approxTK_iff_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundTyAtCovX_approxTK_iff_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXAudit.fundConvAtCovX_approxTK_iff_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.TypeReadbackObservationTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.TypePositionReadbackAtTK
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.typeReadbackObservationTK_iff_at_normal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.typePositionReadbackAtTK_of_normal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.typePositionReadbackAtTK_sort_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.typeReadbackObservationTK_eqGapAlias
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.not_typePositionReadbackAtTK_eqGapAlias
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.typePositionReadback_alias_native_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.typeReadback_alias_and_apart_guard
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.typeReadbackObservationTK_apart_prop_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit.typeReadbackObservationTK_apart_bot_of_no_sort
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_SEAL_ROOTS

import Lean
import rcic.RcicNativeTypedModelCovWRigidCore
import rcic.RcicNativeTypedModelCovWRigidLocal
import rcic.RcicNativeTypedModelCovWRigidSpines
import rcic.RcicNativeTypedModelCovWRigidTransport
import rcic.RcicNativeTypedModelCovWRigidLegacy
import rcic.RcicNativeTypedModelCovWRigidTypingBoundary
import rcic.RcicNativeTypedModelCovWRigidPiTrans
import rcic.RcicNativeTypedModelCovWRigidMShape

/-! Bounded CovWRigid axiom audit. closure_claim = 0. No global completeness claim. -/

#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidRecursor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidHeadReady
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_headReady_app
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_headReady_const
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_no_legacy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.ApproxTKWRigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidObservation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_observation_of
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidTypedInvariant
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.ApproxTKWRigidStage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.ApproxTKWRigidStage.mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidCodesDetermineTypes
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidLegacyNeutralCompleteness
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_expand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_contract
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_raw_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_typed_invariant
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidLocal_variable_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidLocal_all_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidLocal_cell_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_local_value_from_earlier_tail
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_app_spine_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_typed_head_bot_fields
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_recursor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidHoDemandR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidHoDemand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_demand_nonbottom
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_ctor_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_divergent_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_bohm_call_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_empty_lam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_empty_app
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_beta_fn_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_beta_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_zeta_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_cells_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidLocalFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_localFree_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_localFree_cons
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_of_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_to_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_observations_of_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_empty_no_recursors
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_empty_observations_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_sort_complete
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_pi_sort_complete
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_eq_no_recursors
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_eq_observations_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_etaEq_localFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_trueVar_localFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_mixAnd_localFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_trueIota_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_trueK_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_eqIota_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_etaIndex_K_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_andIota_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_andK_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_M_shared_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_spine_not_universe
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_demand_not_sort_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_typing_boundary_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTransLevel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTransMiddle
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTrans_middle_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTrans_middle_beta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTrans_left_leg
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTrans_right_leg
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTrans_conversion
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTrans_middle_not_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTrans_nativeValley
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTrans_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvMCodeSafe
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvMShape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvMShape.Matches
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvMRecShape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvMTerm
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvMShapeCons
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_matches_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_matches_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_term_lift
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_eq_call_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_term_const_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_term_const_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_legacy_eq_rhs
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_shape_sound
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_eq_call_safe
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_safe_typed_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_eq_call_typed_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_at_sort_one
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_M_typed_equality
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWRigid_M_typed_equality

private def covWRigidPublicRoots : Array Lean.Name := #[
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidRecursor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidHeadReady,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_headReady_app,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_headReady_const,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_no_legacy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.ApproxTKWRigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidObservation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_observation_of,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidTypedInvariant,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.ApproxTKWRigidStage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.ApproxTKWRigidStage.mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidCodesDetermineTypes,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidLegacyNeutralCompleteness,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_expand,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_contract,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_raw_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_observations,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_typed_invariant,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_native,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidLocal_variable_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidLocal_all_observations,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidLocal_cell_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_local_value_from_earlier_tail,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_app_spine_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_typed_head_bot_fields,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_recursor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidHoDemandR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidHoDemand,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_demand_nonbottom,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_ctor_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_divergent_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_bohm_call_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_empty_lam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_empty_app,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_beta_fn_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_beta_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_zeta_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_cells_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.CovWRigidLocalFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_localFree_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_localFree_cons,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_of_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_to_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_observations_of_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_empty_no_recursors,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_empty_observations_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_sort_complete,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_pi_sort_complete,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_eq_no_recursors,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_eq_observations_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_etaEq_localFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_trueVar_localFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_mixAnd_localFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_trueIota_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_trueK_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_eqIota_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_etaIndex_K_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_andIota_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_andK_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_M_shared_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_spine_not_universe,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_demand_not_sort_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_typing_boundary_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTransLevel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTransMiddle,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTrans_middle_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTrans_middle_beta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTrans_left_leg,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTrans_right_leg,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTrans_conversion,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTrans_middle_not_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTrans_nativeValley,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidPiTrans_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvMCodeSafe,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvMShape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvMShape.Matches,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvMRecShape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvMTerm,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvMShapeCons,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_matches_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_matches_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_term_lift,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_eq_call_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_term_const_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_term_const_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_legacy_eq_rhs,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_shape_sound,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_eq_call_safe,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_safe_typed_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_eq_call_typed_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_at_sort_one,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_M_typed_equality,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWRigid_M_typed_equality
]

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Quot.sound]
  for root in covWRigidPublicRoots do
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "CovWRigid: {root} has forbidden axioms {forbidden}"
  logInfo m!"CovWRigid: {covWRigidPublicRoots.size} public roots checked"

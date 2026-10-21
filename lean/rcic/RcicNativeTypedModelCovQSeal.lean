import Lean
import rcic.RcicNativeTypedModelCovPSeal
import rcic.RcicNativeTypedModelCovQBoundary
import rcic.RcicNativeTypedModelCovQFinite
import rcic.RcicNativeTypedModelCovQFixtures
import rcic.RcicNativeTypedModelCovQReindex
import rcic.RcicNativeTypedModelCovQTower
import rcic.RcicNativeTypedModelCovQUniverse

/-!
# Bounded seal for neutral universe membership and finite instance codes

Every fixed finite Prop-arrow instance has an explicitly computed code and
full P-shaped hereditary realization. The weaker instance-first interface
still refutes one finite code for the polymorphic identity: empty actions
consume strict finite code size, while actual native arguments have unbounded
arrow depth. The unchanged CoreY and proof-collapse integration boundaries
remain explicit. Eight retained fixtures use the weaker Q predicate.

This seal checks only the 80 new public declarations below. The imported P
seal is freshly checked separately. No code order, global assembler, or full
Foundation root is built. The pinned external #7776 replay stays outside this
bounded import closure. `closure_claim = 0`.
-/

private def covQRoots : Array Lean.Name := #[
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_realized_tower_lower_bound,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_no_uniform_tower_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_pointwise_not_uniform_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQProof_no_observed_type_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowCode_type,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowCode_not_positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_neutral_arrowCode_typing,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_neutral_arrowCode_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_neutral_arrowTower_realization,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQIdentityTowerApp,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQIdentityTowerApp_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQIdentityTowerApp_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQIdentityTowerApp_realization,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQIdentityTower_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQIdentity_two_instance_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.CovQJointAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_hereditary_from_P,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_joint_of_P,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.CovQFixtureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_fixture_of_P,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_fixture_natSucc_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_fixture_alias_in_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_fixture_polyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_fixture_alias_extension,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_fixture_nat_coverage_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_fixture_eq_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_fixture_nat_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_relevant_app_joint,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_rigidId_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.HereditaryCovRealizationQAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.hereditaryCovRealizationQAt_typing,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.hereditaryCovRealizationQAt_from_P,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.hereditaryCovRealizationQAt_of_P,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_hereditary_pi_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_hereditary_emptyStep,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_instance_first_identity_no_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowTower,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowTowerWitness,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowTower_lift,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowTower_instantiate,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowTower_instantiate0,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowTower_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowTowerWitness_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowTower_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_body_inst,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_tower_application_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.CovQRealization,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.CovQEmptyStep,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_tower_code_lower_bound,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_no_finite_descending_identity,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_spine_not_old_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_spine_no_P_universe,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_spine_no_P_sort_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_universe_P_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_spine_no_old_core_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.CTyCovQ,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_of_P,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_of_C2,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_of_S,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_univNeutral,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_univProp,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_univType,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_reflectedPi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_nonprop_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_positive_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_bot_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_prop_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_prop_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_sort_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_lam_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_spine_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_pi_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_positive_excludes_spine,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_old_prop_inv_fails,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_hereditary_sort_zero,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_universe_realized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_universe_no_old_joint,
  ``Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_universe_control
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound]
  for root in covQRoots do
    if !env.contains root then
      throwError "CovQ seal: missing declaration {root}"
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "CovQ seal: {root} has forbidden axioms {forbidden}"
  logInfo m!"CovQ seal: {covQRoots.size} public roots checked; allowed axioms = {allowed}"

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Q_SEAL_ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_realized_tower_lower_bound
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_no_uniform_tower_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_pointwise_not_uniform_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQProof_no_observed_type_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowCode_type
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowCode_not_positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_neutral_arrowCode_typing
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_neutral_arrowCode_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_neutral_arrowTower_realization
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQIdentityTowerApp
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQIdentityTowerApp_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQIdentityTowerApp_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQIdentityTowerApp_realization
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQIdentityTower_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQIdentity_two_instance_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.CovQJointAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_hereditary_from_P
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_joint_of_P
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.CovQFixtureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_fixture_of_P
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_fixture_natSucc_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_fixture_alias_in_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_fixture_polyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_fixture_alias_extension
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_fixture_nat_coverage_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_fixture_eq_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_fixture_nat_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_relevant_app_joint
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_rigidId_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.HereditaryCovRealizationQAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.hereditaryCovRealizationQAt_typing
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.hereditaryCovRealizationQAt_from_P
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.hereditaryCovRealizationQAt_of_P
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_hereditary_pi_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_hereditary_emptyStep
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_instance_first_identity_no_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowTower
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowTowerWitness
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowTower_lift
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowTower_instantiate
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowTower_instantiate0
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowTower_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowTowerWitness_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQArrowTower_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_body_inst
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_tower_application_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.CovQRealization
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.CovQEmptyStep
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_tower_code_lower_bound
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_no_finite_descending_identity
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_spine_not_old_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_spine_no_P_universe
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_spine_no_P_sort_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_universe_P_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_spine_no_old_core_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.CTyCovQ
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_of_P
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_of_C2
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_of_S
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_univNeutral
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_univProp
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_univType
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_reflectedPi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_nonprop_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_positive_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_bot_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_prop_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_prop_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_sort_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_lam_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_spine_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_pi_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.ctyCovQ_positive_excludes_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_old_prop_inv_fails
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_hereditary_sort_zero
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_universe_realized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_universe_no_old_joint
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovQAudit.covQ_identity_universe_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Q_SEAL_ROOTS

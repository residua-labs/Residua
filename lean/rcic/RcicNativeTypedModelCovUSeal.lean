import Lean
import rcic.RcicNativeTypedModelCovTSeal
import rcic.RcicNativeTypedModelCovUCycle
import rcic.RcicNativeTypedModelCovUFixtures
import rcic.RcicNativeTypedModelCovUOmegaCore
import rcic.RcicNativeTypedModelCovUProjection
import rcic.RcicNativeTypedModelCovURealized
import rcic.RcicNativeTypedModelCovURecInstance
import rcic.RcicNativeTypedModelCovUSoundness
import rcic.RcicNativeTypedModelCovUSoundnessEnv

/-!
# Bounded seal for realized valuations and the native-head boundary

Explicit native substitutions realize the retained finite fixtures and repair
the open Nat-recursion control. Old-model simultaneous substitution preserves
the exact compact, with a K-free introduction to ApproxTK.

The admitted higher-order Prop singleton supplies a closed type at Sort 1
with a stage-one Prop observation and no native normal readback. Its precise
failed rule is ApproxT.recursorProp, admitted through ApproxTK.free. The
necessary realized head-supply port is kernel-refuted with inhabited premises.
The separate constructor-projection iff fails in the field-to-projection
direction. No interpreter or general fundamental supplier follows this gate.

All authored public CovU declarations are sealed below. Six prior bounded
seals and the pinned external #7776 replay are checked separately. Both full
Foundation roots are excluded from this audit. `closure_claim = 0`.
-/

private def covURoots : Array Lean.Name := #[
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycleBody,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycleIhLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycleMinor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycleF,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycleX,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycleX_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycleWitness,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycle_conversion,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycleX_closed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycle_omega_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovURealizedFixtureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_fixture_natSucc_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_fixture_alias_in_pi,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_fixture_polyPropLam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_fixture_alias_extension,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_fixture_nat_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_fixture_nat_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_fixture_eq_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_fixture_nat_anchor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUOmegaDelta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUOmega,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUOmega_hasTy_of_cycle,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUOmega_self_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_redR_of_self_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_no_normal_readback_of_self_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjPMember,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjPEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjProofMember,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjPEnvWfT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjEnvWfT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjP,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjProof,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjPairType,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjPair,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjMotive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjMinor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjTerm,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjP_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjProof_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjPairType_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjPair_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_P_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_proof_rigid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_proof_not_propCtor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_proof_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_P_observation_positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_minor_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_app_bot_of_function_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_rec_schema,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_term_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_term_only_bottom,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjMotive_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjMinor_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjTerm_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjW,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_is_projection,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_native_readback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covU_proj_ctor_observation_boundary,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTRealized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTRealized.mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_approxT_substT_up,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_approxT_substT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTRealized.approxT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTRealized.approxTK_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTRealized.stage_of_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_realized_bot_of_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_realized_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecMajor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecSubst,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecMajor_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecMajor_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecSubst_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecEnv_realized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecInstance,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecInstance_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecInstance_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecWitness,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecInstance_read,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecInstance_head_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUOriginSubst,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUOriginEnv_realized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUEqProof,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUEqSubst,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUEqProof_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUEqSubst_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUEqEnv_realized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUSubstitutionSubst,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUSubstitutionEnv_realized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecZero,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecZero_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecZero_motive_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecMinorBody_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecMinorZero_beta,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecRhs_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecInstance_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecExtSubst,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecExtY_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecExtY_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecExtSubst_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecExtEnv_realized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMotive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoIhTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMinor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMajor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMajor_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoWitness,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHo_no_legacy_witness,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHo_not_kFreeRec,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHo_not_kProjRec,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_self_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_no_normal_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHo_no_indexed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMinorCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMinor_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_approxT,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_observed_stage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_obs_sound_head_boundary,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovURealizedHeadSupply,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_no_realized_head_supply,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoFam,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoField,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoCtor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMotTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMinTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoRecTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoRec,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoFamEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoCtorEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoGroupEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoParameter,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoEnv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoEnv_members,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoGroup_wf,
  ``Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoEnv_wf
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound]
  for root in covURoots do
    if !env.contains root then
      throwError "CovU seal: missing declaration {root}"
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "CovU seal: {root} has forbidden axioms {forbidden}"
  logInfo m!"CovU seal: {covURoots.size} public roots checked; allowed axioms = {allowed}"

#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycleBody
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycleIhLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycleMinor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycleF
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycleX
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycleX_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycleWitness
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycle_conversion
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycleX_closed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUCycle_omega_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovURealizedFixtureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_fixture_natSucc_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_fixture_alias_in_pi
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_fixture_polyPropLam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_fixture_alias_extension
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_fixture_nat_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_fixture_nat_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_fixture_eq_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_fixture_nat_anchor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUOmegaDelta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUOmega
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUOmega_hasTy_of_cycle
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUOmega_self_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_redR_of_self_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_no_normal_readback_of_self_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjPMember
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjPEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjProofMember
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjPEnvWfT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjEnvWfT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjP
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjProof
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjPairType
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjPair
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjMotive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjMinor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjTerm
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjP_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjProof_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjPairType_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjPair_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_P_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_proof_rigid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_proof_not_propCtor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_proof_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_P_observation_positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_minor_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_app_bot_of_function_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_rec_schema
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_term_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_term_only_bottom
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjMotive_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjMinor_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjTerm_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProjW
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_is_projection
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covUProj_native_readback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovUAudit.covU_proj_ctor_observation_boundary
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTRealized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTRealized.mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_approxT_substT_up
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_approxT_substT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTRealized.approxT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTRealized.approxTK_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovTRealized.stage_of_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_realized_bot_of_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_realized_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecMajor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecSubst
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecMajor_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecMajor_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecSubst_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecEnv_realized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecInstance
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecInstance_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecInstance_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecWitness
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecInstance_read
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecInstance_head_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUOriginSubst
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUOriginEnv_realized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUEqProof
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUEqSubst
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUEqProof_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUEqSubst_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUEqEnv_realized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUSubstitutionSubst
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUSubstitutionEnv_realized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecZero
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecZero_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecZero_motive_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecMinorBody_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecMinorZero_beta
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecRhs_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecInstance_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecExtSubst
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecExtY_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecExtY_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecExtSubst_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covURecExtEnv_realized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMotive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoIhTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMinor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMajor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMajor_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoWitness
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHo_no_legacy_witness
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHo_not_kFreeRec
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHo_not_kProjRec
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_self_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_no_normal_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHo_no_indexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMinorCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMinor_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_approxT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_observed_stage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_obs_sound_head_boundary
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovURealizedHeadSupply
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_no_realized_head_supply
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoFam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoField
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoCtor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMotTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMinTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoRecTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoRec
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoFamEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoCtorEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoGroupEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoParameter
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoEnv_members
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoGroup_wf
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoEnv_wf

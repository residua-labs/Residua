import Lean
import rcic.RcicF3ABoundedFrameSeal
import rcic.RcicF3PointwiseDataLocal
import rcic.RcicF3PointwiseDataCtor
import rcic.RcicF3PointwiseRoleEquations
import rcic.RcicF3PointwiseGroupFacts
import rcic.RcicF3PointwiseDataPrefix
import rcic.RcicF3PointwiseDataPrefixAttack
import rcic.RcicF3PointwiseDataValue
import rcic.RcicF3PointwiseDataRecMem
import rcic.RcicF3PointwiseDataIotaCases
import rcic.RcicF3PointwiseDataIota
import rcic.RcicF3PointwiseDataMember
import rcic.RcicF3PointwiseDataRecPkg
import rcic.RcicF3PointwiseDataGroup
import rcic.RcicF3PointwiseDataGroupAttack
import rcic.RcicF3PointwiseDataTypedIotaAttack
import rcic.RcicF3PointwiseDataFinite
import rcic.RcicF3PointwisePropPrefix
import rcic.RcicF3PointwisePropCtor
import rcic.RcicF3PointwisePropEvalStep
import rcic.RcicF3PointwisePropEvalTotal
import rcic.RcicF3PointwisePropEvalValue
import rcic.RcicF3PointwisePropParamEvalStep
import rcic.RcicF3PointwisePropParamEvalTotal
import rcic.RcicF3PointwisePropParamEvalValue
import rcic.RcicF3PointwisePropRecMem
import rcic.RcicF3PointwisePropParamRecMem
import rcic.RcicF3PointwisePropRecPkg
import rcic.RcicF3PointwisePropOnlyIota
import rcic.RcicF3PointwisePropPlainValue
import rcic.RcicF3PointwisePropPlainIota
import rcic.RcicF3PointwisePropGroup
import rcic.RcicF3PointwisePropParamGroup
import rcic.RcicF3PointwisePropPlainGroup
import rcic.RcicF3PointwiseRoleConsumer
import rcic.RcicF3PointwiseADataChecked
import rcic.RcicF3PointwiseDataFiniteAttack
import rcic.RcicF3PointwisePropGroupAttack
import rcic.RcicF3PointwisePropTree
import rcic.RcicF3PointwisePropPlainIotaAttack
import rcic.RcicF3PointwiseFalseNonvacuity
import rcic.RcicF3PointwiseCheckedMigrationAttack
import rcic.RcicF3APointwiseCheckedContract

/-!
Exact inventory for the actual pointwise DATA constructor/recursor package,
new-table W typed iota, finite DATA and both Prop-policy consumers,
admission fold, False finalizer, and complete same-P composition.
Private and generated declarations are included. The universal bounded
local-candidate producer remains explicit and unpaid in this checkpoint.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.APointwiseCheckedSeal
open Lean Elab Command

def sealedModules : List Name := [
  `rcic.RcicF3PointwiseDataLocal,
  `rcic.RcicF3PointwiseDataCtor,
  `rcic.RcicF3PointwiseRoleEquations,
  `rcic.RcicF3PointwiseGroupFacts,
  `rcic.RcicF3PointwiseDataPrefix,
  `rcic.RcicF3PointwiseDataPrefixAttack,
  `rcic.RcicF3PointwiseDataValue,
  `rcic.RcicF3PointwiseDataRecMem,
  `rcic.RcicF3PointwiseDataIotaCases,
  `rcic.RcicF3PointwiseDataIota,
  `rcic.RcicF3PointwiseDataMember,
  `rcic.RcicF3PointwiseDataRecPkg,
  `rcic.RcicF3PointwiseDataGroup,
  `rcic.RcicF3PointwiseDataGroupAttack,
  `rcic.RcicF3PointwiseDataTypedIotaAttack,
  `rcic.RcicF3PointwiseDataFinite,
  `rcic.RcicF3PointwisePropPrefix,
  `rcic.RcicF3PointwisePropCtor,
  `rcic.RcicF3PointwisePropEvalStep,
  `rcic.RcicF3PointwisePropEvalTotal,
  `rcic.RcicF3PointwisePropEvalValue,
  `rcic.RcicF3PointwisePropParamEvalStep,
  `rcic.RcicF3PointwisePropParamEvalTotal,
  `rcic.RcicF3PointwisePropParamEvalValue,
  `rcic.RcicF3PointwisePropRecMem,
  `rcic.RcicF3PointwisePropParamRecMem,
  `rcic.RcicF3PointwisePropRecPkg,
  `rcic.RcicF3PointwisePropOnlyIota,
  `rcic.RcicF3PointwisePropPlainValue,
  `rcic.RcicF3PointwisePropPlainIota,
  `rcic.RcicF3PointwisePropGroup,
  `rcic.RcicF3PointwisePropParamGroup,
  `rcic.RcicF3PointwisePropPlainGroup,
  `rcic.RcicF3PointwiseRoleConsumer,
  `rcic.RcicF3PointwiseADataChecked,
  `rcic.RcicF3PointwiseDataFiniteAttack,
  `rcic.RcicF3PointwisePropGroupAttack,
  `rcic.RcicF3PointwisePropTree,
  `rcic.RcicF3PointwisePropPlainIotaAttack,
  `rcic.RcicF3PointwiseFalseNonvacuity,
  `rcic.RcicF3PointwiseCheckedMigrationAttack,
  `rcic.RcicF3APointwiseCheckedContract
]

def sealedTheoremsRaw : String := " ".intercalate [
  "Rcic.F3.PSet.PointwiseDataLocal.frame",
  "Rcic.F3.PSet.PointwiseDataLocal.LocalCandidates",
  "Rcic.F3.PSet.PointwiseDataLocal.admissible",
  "Rcic.F3.PSet.PointwiseDataLocal.of_global_candidate",
  "Rcic.F3.PSet.PointwiseDataLocal.closed_at",
  "Rcic.F3.PSet.PointwiseDataCtor.member_sound_of_inputs",
  "Rcic.F3.PSet.PointwiseDataCtor.ctor_end_mem_at",
  "Rcic.F3.PSet.PointwiseDataCtor.value_mem",
  "Rcic.F3.PSet.PointwiseDataCtor.constructor_at_walk",
  "Rcic.F3.PSet.PointwiseRoleEquations.body_eq_of_faithful",
  "Rcic.F3.PSet.PointwiseRoleEquations.recursor_value_of_group",
  "_private.rcic.RcicF3PointwiseRoleEquations.0.Rcic.F3.PSet.PointwiseRoleEquations.node_new_bodyless",
  "Rcic.F3.PSet.PointwiseRoleEquations.bodyEquations_at_node",
  "Rcic.F3.PSet.PointwiseRoleEquations.bodyEquations_of_faithful",
  "Rcic.F3.PSet.PointwiseRoleEquations.family_equation_of_group",
  "Rcic.F3.PSet.PointwiseRoleEquations.constructor_value_of_group",
  "Rcic.F3.PSet.PointwiseGroupFacts.group_facts",
  "Rcic.F3.PSet.PointwiseGroupFacts.canonical_group_facts",
  "Rcic.F3.PSet.PointwiseDataPrefix.sound_of_local_candidates",
  "Rcic.F3.PSet.PointwiseDataPrefixAttack.leaf_sound",
  "Rcic.F3.PSet.PointwiseDataPrefixAttack.Witness",
  "Rcic.F3.PSet.PointwiseDataPrefixAttack.component_nonrefutable",
  "Rcic.F3.PSet.PointwiseDataPrefixAttack.component_witness",
  "Rcic.F3.PSet.PointwiseDataPrefixAttack.node_sound",
  "Rcic.F3.PSet.PointwiseDataPrefixAttack.local_candidates",
  "Rcic.F3.PSet.PointwiseDataPrefixAttack.produced",
  "Rcic.F3.PSet.PointwiseDataValue.nodeCore_mem",
  "Rcic.F3.PSet.PointwiseDataRecMem.memberValue_mem",
  "_private.rcic.RcicF3PointwiseDataRecMem.0.Rcic.Declarative.policyMotiveLevel.match_1.splitter._cstage2",
  "_private.rcic.RcicF3PointwiseDataRecMem.0.Rcic.Declarative.policyMotiveLevel.match_1.eq_1",
  "Rcic.F3.PSet.PointwiseDataRecMem.member_sound",
  "_private.rcic.RcicF3PointwiseDataRecMem.0.Rcic.Declarative.policyMotiveLevel.match_1.splitter",
  "_private.rcic.RcicF3PointwiseDataRecMem.0.Rcic.Declarative.policyMotiveLevel.match_1.splitter._rarg._cstage2",
  "_private.rcic.RcicF3PointwiseDataRecMem.0.Rcic.Declarative.policyMotiveLevel.match_1.splitter._cstage1",
  "Rcic.F3.PSet.PointwiseDataRecMem.memberValue_mem.match_1",
  "_private.rcic.RcicF3PointwiseDataRecMem.0.Rcic.Declarative.policyMotiveLevel.match_1.eq_2",
  "Rcic.Declarative.policyMotiveLevel.eq_1",
  "Rcic.Declarative.policyMotiveLevel.eq_2",
  "Rcic.F3.PSet.PointwiseDataIotaCases.original_cases_at",
  "Rcic.F3.PSet.PointwiseDataIota.iota_eq",
  "Rcic.F3.PSet.PointwiseDataMember.sound_of_local_candidates",
  "Rcic.F3.PSet.PointwiseDataMember.member_sound_of_local_candidates",
  "Rcic.F3.PSet.PointwiseDataRecPkg.rec_pkg",
  "Rcic.F3.PSet.PointwiseDataRecPkg.iota_at",
  "Rcic.F3.PSet.PointwiseDataGroup.GroupStepAt",
  "Rcic.F3.PSet.PointwiseRole.envSound_of_gInv",
  "Rcic.F3.PSet.PointwiseDataGroup.LocalCandidatesAt",
  "Rcic.F3.PSet.PointwiseDataGroup.group_step_of_check",
  "Rcic.F3.PSet.PointwiseDataGroupAttack.all_sound",
  "Rcic.F3.PSet.PointwiseDataGroupAttack.group_step",
  "Rcic.F3.PSet.PointwiseDataGroupAttack.Witness.proof_2",
  "Rcic.F3.PSet.PointwiseDataGroupAttack.local_candidates_at",
  "Rcic.F3.PSet.PointwiseDataGroupAttack.invariant",
  "Rcic.F3.PSet.PointwiseDataGroupAttack.component_nonrefutable",
  "Rcic.F3.PSet.PointwiseDataGroupAttack.rec_pkg",
  "Rcic.F3.PSet.PointwiseDataGroupAttack.env_sound",
  "Rcic.F3.PSet.PointwiseDataGroupAttack.component_witness",
  "Rcic.F3.PSet.PointwiseDataGroupAttack.Witness.proof_1",
  "Rcic.F3.PSet.PointwiseDataGroupAttack.Witness",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.motive",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.major_mem",
  "_private.rcic.RcicF3PointwiseDataTypedIotaAttack.0.Rcic.F3.PSet.PointwiseDataTypedIotaAttack.recStored._closed_2._cstage2",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.parameter_fit",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.node_mem",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.motive_apply",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.application_result",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.rhs_mem",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.recursor_value",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.result_not_empty",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.arguments",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.context_fits",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.prefixValues",
  "_private.rcic.RcicF3PointwiseDataTypedIotaAttack.0.Rcic.F3.PSet.PointwiseDataTypedIotaAttack.recStored._cstage1",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.prefix_fit",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.redex_equiv",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.\u03c1",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.result",
  "_private.rcic.RcicF3PointwiseDataTypedIotaAttack.0.Rcic.F3.PSet.PointwiseDataTypedIotaAttack.recStored",
  "_private.rcic.RcicF3PointwiseDataTypedIotaAttack.0.Rcic.F3.PSet.PointwiseDataTypedIotaAttack.recStored._closed_1._cstage2",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.lhs_hsound",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.arguments_fit",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.result_equiv",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.target_type",
  "_private.rcic.RcicF3PointwiseDataTypedIotaAttack.0.Rcic.F3.PSet.PointwiseDataTypedIotaAttack.hsound_bvar",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.Witness",
  "_private.rcic.RcicF3PointwiseDataTypedIotaAttack.0.Rcic.F3.PSet.PointwiseDataTypedIotaAttack.recStored._cstage2",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.omega_in_motive",
  "_private.rcic.RcicF3PointwiseDataTypedIotaAttack.0.Rcic.F3.PSet.PointwiseDataTypedIotaAttack.rec_present",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.motive_mem",
  "_private.rcic.RcicF3PointwiseDataTypedIotaAttack.0.Rcic.F3.PSet.PointwiseDataTypedIotaAttack.hsound_app",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.second_mem",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.target",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.second",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.rhs_hsound",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.component_nonrefutable",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.major",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.lhs_mem",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.recursor_role",
  "Rcic.F3.PSet.PointwiseDataTypedIotaAttack.component_witness",
  "Rcic.F3.PSet.PointwiseDataFinite.local_candidates",
  "Rcic.F3.PSet.PointwiseDataFinite.group_step_of_check",
  "Rcic.F3.PSet.PointwisePropPrefix.family_equation_of_group",
  "Rcic.F3.PSet.PointwisePropPrefix.canonical_group_facts",
  "Rcic.F3.PSet.PointwisePropCtor.member_sound",
  "Rcic.F3.PSet.PointwisePropEval.constructor_step",
  "Rcic.F3.PSet.PointwisePropEval.normalized_evaluates",
  "Rcic.F3.PSet.PointwisePropEval.candidate_closed",
  "Rcic.F3.PSet.PointwisePropEval.result_spec",
  "Rcic.F3.PSet.PointwisePropParamEval.constructor_step",
  "Rcic.F3.PSet.PointwisePropParamEval.normalized_evaluates",
  "Rcic.F3.PSet.PointwisePropParamEval.candidate_closed",
  "Rcic.F3.PSet.PointwisePropParamEval.empty_mem",
  "Rcic.F3.PSet.PointwisePropRecMem.member_sound",
  "Rcic.F3.PSet.PointwisePropRecMem.memberValue_mem.match_1",
  "Rcic.F3.PSet.PointwisePropRecMem.memberValue_mem",
  "Rcic.F3.PSet.PointwisePropParamRecMem.memberValue_mem.match_1",
  "Rcic.F3.PSet.PointwisePropParamRecMem.member_sound",
  "Rcic.F3.PSet.PointwisePropParamRecMem.memberValue_mem",
  "Rcic.F3.PSet.PointwisePropRecPkg.rec_pkg",
  "Rcic.F3.PSet.PointwisePropOnlyIota.iota_at",
  "Rcic.F3.PSet.PointwisePropOnlyIota.installed_empty",
  "Rcic.F3.PSet.PointwisePropOnlyIota.rec_pkg",
  "Rcic.F3.PSet.PointwisePropEval.endValue_plain",
  "Rcic.F3.PSet.PointwisePropEval.result_plain",
  "Rcic.F3.PSet.PointwisePropPlainIota.iota_at",
  "Rcic.F3.PSet.PointwisePropPlainIota.rec_pkg",
  "Rcic.F3.PSet.PointwisePropPlainIota.iota_eq",
  "Rcic.F3.PSet.PointwisePropGroup.group_step",
  "Rcic.F3.PSet.PointwisePropParamGroup.group_step_no_parameters",
  "Rcic.F3.PSet.PointwisePropParamGroup.group_step",
  "Rcic.F3.PSet.PointwisePropParamGroup.group_step_of_check",
  "Rcic.F3.PSet.PointwisePropPlainGroup.group_step",
  "Rcic.F3.PSet.PointwiseRole.GInvSteps.casesOn",
  "Rcic.F3.PSet.PointwiseRole.false_of_gInv",
  "Rcic.F3.PSet.PointwiseRole.GInvSteps.noConfusionType",
  "Rcic.F3.PSet.PointwiseRole.GInvSteps.stepGrp",
  "Rcic.F3.PSet.PointwiseRole.GInvSteps.mk",
  "Rcic.F3.PSet.PointwiseRole.GInvSteps.stepThm",
  "Rcic.F3.PSet.PointwiseRole.GInvSteps.stepDef",
  "Rcic.F3.PSet.PointwiseRole.gInv_singleW",
  "Rcic.F3.PSet.PointwiseRole.GInvSteps.stepOpq",
  "Rcic.F3.PSet.PointwiseRole.GInvSteps.noConfusion",
  "Rcic.F3.PSet.PointwiseRole.gInv_of_steps",
  "Rcic.F3.PSet.PointwiseRole.GInvSteps.recOn",
  "Rcic.F3.PSet.PointwiseRole.GInvSteps.rec",
  "Rcic.F3.PSet.PointwiseRole.gInv_of_steps.match_1",
  "Rcic.F3.PSet.PointwiseRole.GInvSteps",
  "Rcic.F3.PSet.PointwiseADataChecked.kernelSoundnessTierWDChecked_of_localCandidates",
  "Rcic.F3.PSet.PointwiseADataChecked.kernelSoundnessTierWDChecked_of_AData",
  "Rcic.F3.PSet.PointwiseADataChecked.LocalCandidatesChecked",
  "Rcic.F3.PSet.PointwiseADataChecked.tierF3WDChecked_of_AData",
  "Rcic.F3.PSet.PointwiseADataChecked.StepADataChecked",
  "Rcic.F3.PSet.PointwiseADataChecked.steps_coveredWDChecked",
  "Rcic.F3.PSet.PointwiseADataChecked.invariant_of_checks",
  "Rcic.F3.PSet.PointwiseADataChecked.stepADataChecked_of_localCandidates",
  "Rcic.F3.PSet.PointwiseADataChecked.group_step_of_check",
  "Rcic.F3.PSet.PointwiseADataChecked.envSound_of_checks",
  "Rcic.F3.PSet.PointwiseDataFiniteAttack.Witness",
  "Rcic.F3.PSet.PointwiseDataFiniteAttack.uniform_type",
  "Rcic.F3.PSet.PointwiseDataFiniteAttack.group_check",
  "Rcic.F3.PSet.PointwiseDataFiniteAttack.component_witness",
  "Rcic.F3.PSet.PointwiseDataFiniteAttack.table",
  "Rcic.F3.PSet.PointwiseDataFiniteAttack.local_candidates",
  "Rcic.F3.PSet.PointwiseDataFiniteAttack.env_sound",
  "Rcic.F3.PSet.PointwiseDataFiniteAttack.component_nonrefutable",
  "Rcic.F3.PSet.PointwiseDataFiniteAttack.family_value",
  "Rcic.F3.PSet.PointwiseDataFiniteAttack.group_step",
  "Rcic.F3.PSet.PointwiseDataFiniteAttack.Witness.proof_2",
  "Rcic.F3.PSet.PointwiseDataFiniteAttack.installed_numeral",
  "Rcic.F3.PSet.PointwiseDataFiniteAttack.faithful",
  "Rcic.F3.PSet.PointwiseDataFiniteAttack.invariant",
  "Rcic.F3.PSet.PointwiseDataFiniteAttack.Witness.proof_1",
  "Rcic.F3.PSet.PointwisePropGroupAttack.table",
  "Rcic.F3.PSet.PointwisePropGroupAttack.arguments_fit",
  "Rcic.F3.PSet.PointwisePropGroupAttack.component_witness",
  "Rcic.F3.PSet.PointwisePropGroupAttack.ctorClasses",
  "Rcic.F3.PSet.PointwisePropGroupAttack.all_sound",
  "Rcic.F3.PSet.PointwisePropGroupAttack.uniform_prop",
  "Rcic.F3.PSet.PointwisePropGroupAttack.package",
  "Rcic.F3.PSet.PointwisePropGroupAttack.constructor_mem",
  "Rcic.F3.PSet.PointwisePropGroupAttack.Witness",
  "Rcic.F3.PSet.PointwisePropGroupAttack.policy",
  "Rcic.F3.PSet.PointwisePropGroupAttack.canonical_plan",
  "Rcic.F3.PSet.PointwisePropGroupAttack.faithful",
  "Rcic.F3.PSet.PointwisePropGroupAttack.component_nonrefutable",
  "Rcic.F3.PSet.PointwisePropGroupAttack.package.match_1",
  "Rcic.F3.PSet.PointwisePropGroupAttack.produced_gInv",
  "Rcic.F3.PSet.PointwisePropTree.branch_mem",
  "Rcic.F3.PSet.PointwisePropTree.Witness",
  "Rcic.F3.PSet.PointwisePropTree.member_sound",
  "Rcic.F3.PSet.PointwisePropTree.family_mem",
  "Rcic.F3.PSet.PointwisePropTree.component_nonrefutable",
  "Rcic.F3.PSet.PointwisePropTree.env_sound",
  "Rcic.F3.PSet.PointwisePropTree.table",
  "Rcic.F3.PSet.PointwisePropTree.invariant",
  "Rcic.F3.PSet.PointwisePropTree.group_step",
  "Rcic.F3.PSet.PointwisePropTree.leaf_mem",
  "Rcic.F3.PSet.PointwisePropTree.branch_application",
  "Rcic.F3.PSet.PointwisePropTree.checked_group_step",
  "Rcic.F3.PSet.PointwisePropTree.node_mem",
  "Rcic.F3.PSet.PointwisePropTree.component_witness",
  "Rcic.F3.PSet.PointwisePropTree.package",
  "Rcic.F3.PSet.PointwisePropTree.faithful",
  "Rcic.F3.PSet.PointwisePropTree.Witness.proof_1",
  "Rcic.F3.PSet.PointwisePropTree.Witness.proof_2",
  "Rcic.F3.PSet.PointwisePropTree.package.match_1",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.uniform_prop",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.motive_mem",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.lhs_application",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.result_mem",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.Witness",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.table",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.arguments_fit",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.result_equiv",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.result_ne_empty",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.\u03c1",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.result",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.motive_at_intro",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.redex_equiv",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.redex_equiv.match_1",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.package.match_1",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.arguments",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.inhabited_family",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.package",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.recursor_value",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.application_result",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.motive",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.component_witness",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.constructor_sound",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.faithful",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.application_mem",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.minor_mem",
  "Rcic.F3.PSet.PointwisePropPlainIotaAttack.component_nonrefutable",
  "Rcic.F3.PSet.PointwiseFalseNonvacuity.component_witness",
  "Rcic.F3.PSet.PointwiseFalseNonvacuity.base_step",
  "Rcic.F3.PSet.PointwiseFalseNonvacuity.env_sound",
  "Rcic.F3.PSet.PointwiseFalseNonvacuity.base_invariant",
  "Rcic.F3.PSet.PointwiseFalseNonvacuity.true_inhabited",
  "Rcic.F3.PSet.PointwiseFalseNonvacuity.distinct",
  "Rcic.F3.PSet.PointwiseFalseNonvacuity.consistent",
  "Rcic.F3.PSet.PointwiseFalseNonvacuity.prop_value",
  "Rcic.F3.PSet.PointwiseFalseNonvacuity.true_mem",
  "Rcic.F3.PSet.PointwiseFalseNonvacuity.false_empty",
  "Rcic.F3.PSet.PointwiseFalseNonvacuity.table",
  "Rcic.F3.PSet.PointwiseFalseNonvacuity.faithful",
  "Rcic.F3.PSet.PointwiseFalseNonvacuity.component_nonrefutable",
  "Rcic.F3.PSet.PointwiseFalseNonvacuity.invariant",
  "Rcic.F3.PSet.PointwiseFalseNonvacuity.false_mem",
  "Rcic.F3.PSet.PointwiseFalseNonvacuity.Witness",
  "Rcic.F3.PSet.PointwiseCheckedMigrationAttack.component_nonrefutable",
  "Rcic.F3.PSet.PointwiseCheckedMigrationAttack.component_witness",
  "Rcic.F3.PSet.PointwiseCheckedMigrationAttack.Witness",
  "Rcic.F3.PSet.APointwiseCheckedContract.components",
  "Rcic.F3.PSet.APointwiseCheckedContract.local_consumer",
  "Rcic.F3.PSet.APointwiseCheckedContract.checked_target_iff_localCandidates",
  "Rcic.F3.PSet.APointwiseCheckedContract.Components",
  "Rcic.F3.PSet.APointwiseCheckedContract.checked_target_nonrefutable_iff",
  "Rcic.F3.PSet.APointwiseCheckedContract.CheckedTarget",
  "Rcic.F3.PSet.APointwiseCheckedContract.components_nonrefutable",
  "Rcic.F3.PSet.APointwiseCheckedContract.checked_target_of_localCandidates",
  "Rcic.F3.PSet.APointwiseCheckedContract.LocalConsumer"
]

def sealedTheorems : List Name :=
  (sealedTheoremsRaw.split (· == ' ') |>.map String.toName)

def allowedAxioms : List Name := [``propext, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let mut actual : Array Name := #[]
  for m in sealedModules do
    let some idx := env.getModuleIdx? m
      | throwError "[a_pointwise_checked_seal] module {m} is not imported"
    actual := actual ++ env.header.moduleData[idx.toNat]!.constNames
  unless actual.size == sealedTheorems.length do
    throwError "[a_pointwise_checked_seal] inventory size {sealedTheorems.length} differs from {actual.size}"
  for t in actual do
    unless sealedTheorems.contains t do
      throwError "[a_pointwise_checked_seal] uncovered declaration {t}"
  for t in sealedTheorems do
    unless actual.contains t && env.contains t do
      throwError "[a_pointwise_checked_seal] stale or foreign declaration {t}"
  let (_, s) := ((do
    for t in sealedTheorems do CollectAxioms.collect t).run env).run {}
  let bad := s.axioms.filter (fun ax => !allowedAxioms.contains ax)
  unless bad.isEmpty do
    for t in sealedTheorems do
      let (_, st) := ((CollectAxioms.collect t).run env).run {}
      for ax in st.axioms do
        unless allowedAxioms.contains ax do
          throwError "[a_pointwise_checked_seal] {t} depends on {ax}"
  logInfo m!"[a_pointwise_checked_seal] {sealedTheorems.length} declarations in {sealedModules.length} modules; exact coverage; axioms ⊆ {allowedAxioms}; closure_claim = 0"


end Rcic.F3.APointwiseCheckedSeal

import Lean
import rcic.RcicF3ANormalizedPropSeal
import rcic.RcicF3NormRole
import rcic.RcicF3NormRoleReads
import rcic.RcicF3NormRoleDelta
import rcic.RcicF3NormRoleTable
import rcic.RcicF3NormRoleTableAttack
import rcic.RcicF3NormCandidatePrefix
import rcic.RcicF3NormPropCtor
import rcic.RcicF3NormPropCtorAttack
import rcic.RcicF3NormPropCtorUniform
import rcic.RcicF3NormPropCtorUniformAttack
import rcic.RcicF3NormPropEvalInputs
import rcic.RcicF3NormPropEvalStep
import rcic.RcicF3NormPropEvalTotal
import rcic.RcicF3NormPropEvalValue
import rcic.RcicF3NormPropRecMem
import rcic.RcicF3NormPropRecPkg
import rcic.RcicF3NormPropGroup
import rcic.RcicF3NormPropGroupAttack
import rcic.RcicF3NormPropEvalAttack
import rcic.RcicF3PiSmallTuple
import rcic.RcicF3PiSmallTupleAttack
import rcic.RcicF3PiSmallRecursive
import rcic.RcicF3PiSmallRecursiveAttack
import rcic.RcicF3RawNonIRHiddenAttack
import rcic.RcicF3ANormRoleContract

/-!
# Exact axiom seal for the normalized-role group producer

All private and compiler-generated declarations in these 25 producer and
witness modules are sealed. The four inherited exact seals remain imported.
The complete Prop/anySort group-step face is produced; universal data frames,
propOnly recursor, W/D migration and the apex remain unpaid. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.ANormRoleSeal
open Lean Elab Command

def sealedModules : List Name := [
  `rcic.RcicF3NormRole,
  `rcic.RcicF3NormRoleReads,
  `rcic.RcicF3NormRoleDelta,
  `rcic.RcicF3NormRoleTable,
  `rcic.RcicF3NormRoleTableAttack,
  `rcic.RcicF3NormCandidatePrefix,
  `rcic.RcicF3NormPropCtor,
  `rcic.RcicF3NormPropCtorAttack,
  `rcic.RcicF3NormPropCtorUniform,
  `rcic.RcicF3NormPropCtorUniformAttack,
  `rcic.RcicF3NormPropEvalInputs,
  `rcic.RcicF3NormPropEvalStep,
  `rcic.RcicF3NormPropEvalTotal,
  `rcic.RcicF3NormPropEvalValue,
  `rcic.RcicF3NormPropRecMem,
  `rcic.RcicF3NormPropRecPkg,
  `rcic.RcicF3NormPropGroup,
  `rcic.RcicF3NormPropGroupAttack,
  `rcic.RcicF3NormPropEvalAttack,
  `rcic.RcicF3PiSmallTuple,
  `rcic.RcicF3PiSmallTupleAttack,
  `rcic.RcicF3PiSmallRecursive,
  `rcic.RcicF3PiSmallRecursiveAttack,
  `rcic.RcicF3RawNonIRHiddenAttack,
  `rcic.RcicF3ANormRoleContract
]

def sealedTheoremsRaw : String := " ".intercalate [
  "Rcic.F3.PSet.NormRole.envCtx_group_stable",
  "Rcic.F3.PSet.NormRole.GInv",
  "Rcic.F3.PSet.NormRole.envCtx_group",
  "Rcic.F3.PSet.groupRoles.eq_1",
  "Rcic.F3.PSet.NormRole.StepAG",
  "Rcic.F3.PSet.NormRole.envCtx_fresh.match_2",
  "Rcic.F3.PSet.NormRole.envCtx.match_1._cstage1",
  "Rcic.F3.PSet.NormRole.GroupStepAt",
  "Rcic.F3.PSet.NormRole.envCtx_fresh.match_1",
  "Rcic.F3.PSet.NormRole.envCtx",
  "Rcic.F3.PSet.NormRole.gInv_empty",
  "Rcic.F3.PSet.NormRole.gInv_empty.match_1",
  "Rcic.F3.PSet.NormRole.envCtx._sunfold",
  "Rcic.F3.PSet.NormRole.envCtx.match_1",
  "Rcic.F3.PSet.NormRole.envCtx_fresh",
  "Rcic.F3.PSet.NormRole.readsOKAlong_envCtxT",
  "Rcic.F3.PSet.NormRole.famReads_normal",
  "Rcic.F3.PSet.NormRole.fields_reads",
  "Rcic.F3.PSet.NormRole.field_reads",
  "Rcic.F3.PSet.NormRole.readsOKAlong_envCtxT.match_1",
  "Rcic.F3.PSet.NormRole.planReadsOKAlong",
  "Rcic.F3.PSet.NormRole.bodies_read_in_base",
  "Rcic.F3.PSet.NormRoleDelta.bodyEquations_update_at_node",
  "Rcic.F3.PSet.NormRoleDelta.body_eq_of_faithful",
  "_private.rcic.RcicF3NormRoleDelta.0.Rcic.F3.PSet.NormRoleDelta.node_new_bodyless",
  "Rcic.F3.PSet.NormRoleDelta.bodyEquations_of_faithful",
  "Rcic.F3.PSet.NormRoleDelta.bodyEquations_at_node",
  "Rcic.F3.PSet.NormRoleDelta.body_plain",
  "Rcic.F3.PSet.NormRoleDelta.body_plain.match_1",
  "Rcic.F3.PSet.NormRole.table",
  "Rcic.F3.PSet.NormRole.table_exists",
  "Rcic.F3.PSet.NormRole.table_spec",
  "Rcic.F3.PSet.NormRole.table_nonrefutable",
  "Rcic.F3.PSet.NormRoleTableAttack.component_witness",
  "Rcic.F3.PSet.NormRoleTableAttack.table",
  "Rcic.F3.PSet.NormRoleTableAttack.component_nonrefutable",
  "Rcic.F3.PSet.NormRoleTableAttack.Witness",
  "Rcic.F3.PSet.NormCandidatePrefix.target_facts",
  "Rcic.F3.PSet.NormCandidatePrefix.prior_at_frame",
  "Rcic.F3.PSet.NormCandidatePrefix.canonical_group_facts",
  "Rcic.F3.PSet.NormCandidatePrefix.frame_prefix_envSound",
  "Rcic.F3.PSet.NormCandidatePrefix.group_facts",
  "Rcic.F3.PSet.NormCandidatePrefix.family_equation_of_group",
  "Rcic.F3.PSet.NormCandidatePrefix.candidate_prefix_envSound",
  "Rcic.F3.PSet.NormPropCtor.member_sound",
  "Rcic.F3.PSet.NormPropCtor.field_count",
  "Rcic.F3.PSet.NormPropCtor.value_mem",
  "Rcic.F3.PSet.NormPropCtorAttack.Witness",
  "Rcic.F3.PSet.NormPropCtorAttack.component_witness",
  "Rcic.F3.PSet.NormPropCtorAttack.component_nonrefutable",
  "Rcic.F3.PSet.NormPropCtorUniform.normalized_closed",
  "Rcic.F3.PSet.NormPropCtorUniform.member_sound",
  "Rcic.F3.PSet.NormPropCtorUniformAttack.component_nonrefutable",
  "Rcic.F3.PSet.NormPropCtorUniformAttack.Witness",
  "Rcic.F3.PSet.NormPropCtorUniformAttack.component_witness",
  "Rcic.F3.PSet.NormPropEval.frame_inputs",
  "Rcic.F3.PSet.NormPropEval.base",
  "Rcic.F3.PSet.NormPropEval.constructor_step",
  "Rcic.F3.PSet.NormPropEval.candidate",
  "Rcic.F3.PSet.NormPropEval.candidate_closed",
  "Rcic.F3.PSet.NormPropEval.normalized_evaluates",
  "Rcic.F3.PSet.NormPropEval.result_spec",
  "Rcic.F3.PSet.NormPropEval.major_at_frame",
  "Rcic.F3.PSet.NormPropRecMem.memberValue_mem.match_1",
  "Rcic.F3.PSet.NormPropRecMem.member_sound",
  "Rcic.F3.PSet.NormPropRecMem.memberValue_mem",
  "Rcic.F3.PSet.NormPropRecPkg.rec_pkg",
  "Rcic.F3.PSet.NormPropGroup.group_step",
  "Rcic.F3.PSet.NormPropGroupAttack.component_witness",
  "Rcic.F3.PSet.NormPropGroupAttack.produced_gInv",
  "Rcic.F3.PSet.NormPropGroupAttack.component_nonrefutable",
  "Rcic.F3.PSet.NormPropGroupAttack.Witness",
  "Rcic.F3.PSet.NormPropGroupAttack.invariant_nonrefutable",
  "Rcic.F3.PSet.NormPropEvalAttack.role_context_eq",
  "Rcic.F3.PSet.NormPropEvalAttack.installed_iota",
  "Rcic.F3.PSet.NormPropEvalAttack.component_nonrefutable",
  "Rcic.F3.PSet.NormPropEvalAttack.old_table_eq",
  "Rcic.F3.PSet.NormPropEvalAttack.descriptor_eq",
  "_private.rcic.RcicF3NormPropEvalAttack.0.Rcic.F3.PSet.NormPropEvalAttack.constructor_fields",
  "Rcic.F3.PSet.NormPropEvalAttack.ihValue",
  "Rcic.F3.PSet.NormPropEvalAttack.ih_typed",
  "Rcic.F3.PSet.NormPropEvalAttack.no_children",
  "_private.rcic.RcicF3NormPropEvalAttack.0.Rcic.F3.PSet.NormPropEvalAttack.singleton_fields",
  "Rcic.F3.PSet.NormPropEvalAttack.value_same",
  "Rcic.F3.PSet.NormPropEvalAttack.μ",
  "Rcic.F3.PSet.NormPropEvalAttack.Witness",
  "Rcic.F3.PSet.NormPropEvalAttack.component_witness.match_1",
  "Rcic.F3.PSet.NormPropEvalAttack.arguments_fit",
  "_private.rcic.RcicF3NormPropEvalAttack.0.Rcic.F3.PSet.NormPropEvalAttack.recursive_field",
  "Rcic.F3.PSet.NormPropEvalAttack.endpoint_eq",
  "Rcic.F3.PSet.NormPropEvalAttack.application_result",
  "Rcic.F3.PSet.NormPropEvalAttack.result",
  "Rcic.F3.PSet.NormPropEvalAttack.ih_eq",
  "Rcic.F3.PSet.NormPropEvalAttack.invalid_key",
  "Rcic.F3.PSet.NormPropEvalAttack.C",
  "Rcic.F3.PSet.NormPropEvalAttack.component_witness",
  "Rcic.F3.PSet.NormPropEvalAttack.X",
  "Rcic.F3.PSet.NormPropEvalAttack.evaluation_context_eq",
  "Rcic.F3.PSet.NormPropEvalAttack.old_endpoint_rejected",
  "Rcic.F3.PSet.PiSmallTuple.values.match_1._cstage1",
  "Rcic.F3.PSet.PiSmallTuple.complete_congr.match_1",
  "Rcic.F3.PSet.PiSmallTuple.complete_stage_one",
  "Rcic.F3.PSet.PiSmallTuple.values",
  "Rcic.F3.PSet.PiSmallTuple.complete_stage_three",
  "Rcic.F3.PSet.PiSmallTuple.complete_congr",
  "Rcic.F3.PSet.PiSmallTuple.Space.match_1._cstage1",
  "Rcic.F3.PSet.PiSmallTuple.values_length.match_1",
  "Rcic.F3.PSet.PiSmallTuple.sound",
  "Rcic.F3.PSet.PiSmallTuple.complete_with_result",
  "Rcic.F3.PSet.PiSmallTuple.rep",
  "Rcic.F3.PSet.PiSmallTuple.small_of_rep_mem",
  "Rcic.F3.PSet.PiSmallTuple.complete",
  "Rcic.F3.PSet.PiSmallTuple.values.match_1",
  "Rcic.F3.PSet.PiSmallTuple.Space",
  "Rcic.F3.PSet.PiSmallTuple.complete_stage_four_plus",
  "Rcic.F3.PSet.PiSmallTuple.complete_stage_two",
  "Rcic.F3.PSet.PiSmallTuple.values._sunfold",
  "Rcic.F3.PSet.PiSmallTuple.Space._sunfold",
  "Rcic.F3.PSet.PiSmallTuple.values_length",
  "Rcic.F3.PSet.PiSmallTuple.rep_spec",
  "Rcic.F3.PSet.PiSmallTuple.Space.match_1",
  "Rcic.F3.PSet.PiSmallTupleAttack.result",
  "Rcic.F3.PSet.PiSmallTupleAttack.alternatives_dich",
  "Rcic.F3.PSet.PiSmallTupleAttack.data_represented",
  "Rcic.F3.PSet.PiSmallTupleAttack.fields._closed_2._cstage2",
  "Rcic.F3.PSet.PiSmallTupleAttack.component_witness",
  "Rcic.F3.PSet.PiSmallTupleAttack.omega_stage_one",
  "Rcic.F3.PSet.PiSmallTupleAttack.result._cstage1",
  "Rcic.F3.PSet.PiSmallTupleAttack.proof_represented",
  "Rcic.F3.PSet.PiSmallTupleAttack.result._closed_2._cstage2",
  "Rcic.F3.PSet.PiSmallTupleAttack.proofType_stage_one",
  "Rcic.F3.PSet.PiSmallTupleAttack.data_fits",
  "Rcic.F3.PSet.PiSmallTupleAttack.fields._closed_5._cstage2",
  "Rcic.F3.PSet.PiSmallTupleAttack.result._closed_3._cstage2",
  "Rcic.F3.PSet.PiSmallTupleAttack.dataType_stage_one",
  "Rcic.F3.PSet.PiSmallTupleAttack.data_small",
  "Rcic.F3.PSet.PiSmallTupleAttack.fields._cstage1",
  "Rcic.F3.PSet.PiSmallTupleAttack.dataType",
  "Rcic.F3.PSet.PiSmallTupleAttack.proofType",
  "Rcic.F3.PSet.PiSmallTupleAttack.result._closed_4._cstage2",
  "Rcic.F3.PSet.PiSmallTupleAttack.dataTuple",
  "Rcic.F3.PSet.PiSmallTupleAttack.fields",
  "Rcic.F3.PSet.PiSmallTupleAttack.fields._closed_1._cstage2",
  "Rcic.F3.PSet.PiSmallTupleAttack.table",
  "Rcic.F3.PSet.PiSmallTupleAttack.alternatives",
  "Rcic.F3.PSet.PiSmallTupleAttack.σ",
  "Rcic.F3.PSet.PiSmallTupleAttack.σ._cstage2",
  "Rcic.F3.PSet.PiSmallTupleAttack.proof_fits",
  "Rcic.F3.PSet.PiSmallTupleAttack.singleton_dich",
  "Rcic.F3.PSet.PiSmallTupleAttack.fields._closed_6._cstage2",
  "Rcic.F3.PSet.PiSmallTupleAttack.proof_small",
  "Rcic.F3.PSet.PiSmallTupleAttack.Represented",
  "Rcic.F3.PSet.PiSmallTupleAttack.fields._cstage2",
  "Rcic.F3.PSet.PiSmallTupleAttack.model",
  "Rcic.F3.PSet.PiSmallTupleAttack.result._closed_1._cstage2",
  "Rcic.F3.PSet.PiSmallTupleAttack.Witness",
  "Rcic.F3.PSet.PiSmallTupleAttack.result._cstage2",
  "Rcic.F3.PSet.PiSmallTupleAttack.component_nonrefutable",
  "Rcic.F3.PSet.PiSmallTupleAttack.fields._closed_4._cstage2",
  "Rcic.F3.PSet.PiSmallTupleAttack.fields._closed_3._cstage2",
  "Rcic.F3.PSet.PiSmallTupleAttack.proofTuple",
  "Rcic.F3.PSet.PiSmallTupleAttack.omega_not_empty",
  "Rcic.F3.PSet.PiSmallTupleAttack.σ._cstage1",
  "Rcic.F3.PSet.PiSmallTupleAttack.result._closed_5._cstage2",
  "Rcic.F3.PSet.PiSmallRecursive.result_fits",
  "Rcic.F3.PSet.PiSmallRecursive.compile._sunfold",
  "Rcic.F3.PSet.PiSmallRecursive.normalized_mem",
  "Rcic.F3.PSet.PiSmallRecursive.normalized_mem_stage_four_plus",
  "Rcic.F3.PSet.PiSmallRecursive.compile_domains",
  "Rcic.F3.PSet.PiSmallRecursive.compile.match_1",
  "Rcic.F3.PSet.PiSmallRecursive.classValue_lift",
  "Rcic.F3.PSet.PiSmallRecursive.compile_mem",
  "Rcic.F3.PSet.PiSmallRecursive.widen._sunfold",
  "Rcic.F3.PSet.PiSmallRecursive.lifted_rep_dich",
  "Rcic.F3.PSet.PiSmallRecursive.compile_domains.match_1",
  "Rcic.F3.PSet.PiSmallRecursive.normalized_mem_stage_two",
  "Rcic.F3.PSet.PiSmallRecursive.widen",
  "Rcic.F3.PSet.PiSmallRecursive.normalized_mem_stage_one",
  "Rcic.F3.PSet.PiSmallRecursive.widen.match_1._cstage1",
  "Rcic.F3.PSet.PiSmallRecursive.normalized_mem_stage_three",
  "Rcic.F3.PSet.PiSmallRecursive.compile.match_1._cstage1",
  "Rcic.F3.PSet.PiSmallRecursive.widen.match_1",
  "Rcic.F3.PSet.PiSmallRecursive.compile",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.leaf._cstage1",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.leaf._closed_1._cstage2",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.field",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.data_apply",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.leaf_member",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.field._cstage2",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.proof_apply",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.leaf_read",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.original_stage_one",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.field_read",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.smallTel",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.labels",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.field._cstage1",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.alternative_domain_stage",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.leaf",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.field._closed_1._cstage2",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.empty_body_equations",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.leaf._cstage2",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.original_equiv",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.compressed_member",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.Witness",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.compressed_result",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.original_domains_stage",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.fibres",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.fibres_dich",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.value",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.value_member",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.component_nonrefutable",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.originalTel",
  "Rcic.F3.PSet.PiSmallRecursiveAttack.component_witness",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.rawFields",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.family_typed.proof_2",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.hidden_typed",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.rawFields._cstage1",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.family_typed.proof_1",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.member._closed_1._cstage2",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.hidden_typed.proof_1",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.family_typed.proof_3",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.hidden._closed_1._cstage2",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.member._closed_2._cstage2",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.hidden._cstage2",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.normalFields._cstage1",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.normal_nonIR",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.normalFields",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.nonrefutable",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.hidden",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.family._cstage1",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.raw_not_nonIR",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.member._cstage1",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.context_typed",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.member._closed_3._cstage2",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.hidden._cstage1",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.Witness",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.member",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.env",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.normalFields._cstage2",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.rawFields._cstage2",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.read_and_scan",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.family",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.family_typed",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.family._cstage2",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.member._cstage2",
  "Rcic.F3.PSet.RawNonIRHiddenAttack.component_witness",
  "Rcic.F3.PSet.ANormRoleContract.components",
  "Rcic.F3.PSet.ANormRoleContract.PropFace",
  "Rcic.F3.PSet.ANormRoleContract.target_of_stepAG",
  "Rcic.F3.PSet.ANormRoleContract.components_nonrefutable",
  "Rcic.F3.PSet.ANormRoleContract.Target",
  "Rcic.F3.PSet.ANormRoleContract.target_iff_stepAG",
  "Rcic.F3.PSet.ANormRoleContract.Components",
  "Rcic.F3.PSet.ANormRoleContract.prop_face_nonrefutable",
  "Rcic.F3.PSet.ANormRoleContract.prop_face"
]

def sealedTheorems : List Name :=
  (sealedTheoremsRaw.split (· == ' ') |>.map String.toName)

def allowedAxioms : List Name := [``propext, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let mut actual : Array Name := #[]
  for m in sealedModules do
    let some idx := env.getModuleIdx? m
      | throwError "[a_norm_role_seal] module {m} is not imported"
    actual := actual ++ env.header.moduleData[idx.toNat]!.constNames
  unless actual.size == sealedTheorems.length do
    throwError "[a_norm_role_seal] inventory size {sealedTheorems.length} differs from {actual.size}"
  for t in actual do
    unless sealedTheorems.contains t do
      throwError "[a_norm_role_seal] uncovered declaration {t}"
  for t in sealedTheorems do
    unless actual.contains t && env.contains t do
      throwError "[a_norm_role_seal] stale or foreign declaration {t}"
  let (_, s) := ((do
    for t in sealedTheorems do CollectAxioms.collect t).run env).run {}
  let bad := s.axioms.filter (fun ax => !allowedAxioms.contains ax)
  unless bad.isEmpty do
    for t in sealedTheorems do
      let (_, st) := ((CollectAxioms.collect t).run env).run {}
      for ax in st.axioms do
        unless allowedAxioms.contains ax do
          throwError "[a_norm_role_seal] {t} depends on {ax}"
  logInfo m!"[a_norm_role_seal] {sealedTheorems.length} declarations in {sealedModules.length} modules; exact coverage; axioms ⊆ {allowedAxioms}; closure_claim = 0"


end Rcic.F3.ANormRoleSeal

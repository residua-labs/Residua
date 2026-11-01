import Lean
import rcic.RcicF3AAxisBridgeSeal
import rcic.RcicF3CandidateBoundFields
import rcic.RcicF3CandidateBoundTuple
import rcic.RcicF3CandidateFieldAdmission
import rcic.RcicF3CandidateFields
import rcic.RcicF3CandidatePrefixFromGroup
import rcic.RcicF3CandidatePrefixFromGroupAttack
import rcic.RcicF3CandidateScope
import rcic.RcicF3CandidateScopeAttack
import rcic.RcicF3CandidateTupleAttack
import rcic.RcicF3PiCleanViews
import rcic.RcicF3PropEvalAdmittedInputs
import rcic.RcicF3PropEvalAdmittedInputsAttack
import rcic.RcicF3PropEvalCandidate
import rcic.RcicF3PropEvalCandidateAttack
import rcic.RcicF3PropEvalCandidateInputs
import rcic.RcicF3PropEvalCandidateLeafAttack
import rcic.RcicF3PropEvalCandidateLevels
import rcic.RcicF3PropEvalCandidateLevelsAttack
import rcic.RcicF3PropEvalCandidateParams
import rcic.RcicF3PropEvalCandidateParamsAttack
import rcic.RcicF3PropEvalCandidateStep
import rcic.RcicF3PropEvalCandidateStepAttack
import rcic.RcicF3PropEvalCandidateSuite
import rcic.RcicF3PropEvalInputs
import rcic.RcicF3PropEvalMotiveGuard
import rcic.RcicF3PropEvalMotiveGuardAttack
import rcic.RcicF3PropEvalPacket
import rcic.RcicF3PropEvalRawFamily
import rcic.RcicF3PropEvalRawFamilyAttack

/-!
# Exact axiom seal for the candidate constructor step

The inventory includes every declaration (including generated and private
declarations) in the 29 new component and attack modules. The previous
515-declaration bridge seal remains imported. This seal asserts the axiom
policy and exact inventory only; universal StepAG and RCC closure remain
open. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.ACandidateStepSeal
open Lean Elab Command

def sealedModules : List Name := [
  `rcic.RcicF3CandidateBoundFields,
  `rcic.RcicF3CandidateBoundTuple,
  `rcic.RcicF3CandidateFieldAdmission,
  `rcic.RcicF3CandidateFields,
  `rcic.RcicF3CandidatePrefixFromGroup,
  `rcic.RcicF3CandidatePrefixFromGroupAttack,
  `rcic.RcicF3CandidateScope,
  `rcic.RcicF3CandidateScopeAttack,
  `rcic.RcicF3CandidateTupleAttack,
  `rcic.RcicF3PiCleanViews,
  `rcic.RcicF3PropEvalAdmittedInputs,
  `rcic.RcicF3PropEvalAdmittedInputsAttack,
  `rcic.RcicF3PropEvalCandidate,
  `rcic.RcicF3PropEvalCandidateAttack,
  `rcic.RcicF3PropEvalCandidateInputs,
  `rcic.RcicF3PropEvalCandidateLeafAttack,
  `rcic.RcicF3PropEvalCandidateLevels,
  `rcic.RcicF3PropEvalCandidateLevelsAttack,
  `rcic.RcicF3PropEvalCandidateParams,
  `rcic.RcicF3PropEvalCandidateParamsAttack,
  `rcic.RcicF3PropEvalCandidateStep,
  `rcic.RcicF3PropEvalCandidateStepAttack,
  `rcic.RcicF3PropEvalCandidateSuite,
  `rcic.RcicF3PropEvalInputs,
  `rcic.RcicF3PropEvalMotiveGuard,
  `rcic.RcicF3PropEvalMotiveGuardAttack,
  `rcic.RcicF3PropEvalPacket,
  `rcic.RcicF3PropEvalRawFamily,
  `rcic.RcicF3PropEvalRawFamilyAttack
]

def sealedTheoremsRaw : String := " ".intercalate [
  "Rcic.F3.PSet.CandidateScope.fits_original_prefix",
  "Rcic.F3.PSet.CandidateScope.original_field_normalized",
  "Rcic.F3.PSet.CandidateBoundFields.family_prefix_bodiesOK",
  "Rcic.F3.PSet.CandidateBoundFields.field_tuple_raw",
  "Rcic.F3.PSet.CandidateBoundFields.original_fields_instOK",
  "Rcic.F3.PSet.CandidateFieldAdmission.certificates_of_fields",
  "Rcic.F3.PSet.CandidateFieldAdmission.of_fields",
  "Rcic.F3.PSet.CandidateFieldAdmission.clean_at",
  "Rcic.F3.PSet.CandidateFields.normalized_sub",
  "Rcic.F3.PSet.CandidateFields.telFits_mono_prefix",
  "Rcic.F3.PSet.CandidateFields.original_field_sub",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.group_facts",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.GroupPrefixFacts.rawEnv",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.GroupPrefixFacts.rec",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.raw_prefix_envSound",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.GroupPrefixFacts.noConfusion",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.GroupPrefixFacts.candidateEnv",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.GroupPrefixFacts.casesOn",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.GroupPrefixFacts.bounded",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.GroupPrefixFacts.free",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.GroupPrefixFacts.noConfusionType",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.GroupPrefixFacts.familyType",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.GroupPrefixFacts.mk",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.syntax_facts",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.GroupPrefixFacts.prior",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.GroupPrefixFacts.facts",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.GroupPrefixFacts.closedReader",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.GroupPrefixFacts.familyMember",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.GroupPrefixFacts",
  "Rcic.F3.PSet.CandidatePrefixFromGroup.GroupPrefixFacts.recOn",
  "Rcic.F3.PSet.CandidatePrefixFromGroupAttack.component_witness",
  "Rcic.F3.PSet.CandidatePrefixFromGroupAttack.Witness",
  "Rcic.F3.PSet.CandidatePrefixFromGroupAttack.facts",
  "Rcic.F3.PSet.CandidatePrefixFromGroupAttack.component_nonrefutable",
  "Rcic.F3.PSet.CandidatePrefixFromGroupAttack.facts.match_1",
  "Rcic.F3.PSet.CandidateScope.recNode_den_piTelescope",
  "_private.rcic.RcicF3CandidateScope.0.Rcic.Declarative.transparentBody.match_1.eq_2",
  "Rcic.F3.PSet.CandidateScope.piTelescopeFuel_of_transparentBody_eq.match_1",
  "Rcic.F3.PSet.CandidateScope.transparentBody_eq_of_bodyless_extension",
  "Rcic.F3.PSet.CandidateScope.piTelescopeFuel_of_transparentBody_eq",
  "Rcic.F3.PSet.CandidateScope.recNode_read",
  "_private.rcic.RcicF3CandidateScope.0.Rcic.Declarative.transparentBody.match_1.eq_1",
  "_private.rcic.RcicF3CandidateScope.0.Rcic.Declarative.transparentBody.match_1.splitter._rarg._cstage2",
  "Rcic.F3.PSet.CandidateScope.piTelescopeFuel_of_transparentBody_eq.match_1._cstage1",
  "_private.rcic.RcicF3CandidateScope.0.Rcic.Declarative.transparentBody.match_1.splitter._cstage2",
  "_private.rcic.RcicF3CandidateScope.0.Rcic.Declarative.transparentBody.match_1.splitter",
  "Rcic.F3.PSet.CandidateScope.recNode_transparentBody_prefix",
  "_private.rcic.RcicF3CandidateScope.0.Rcic.Declarative.transparentBody.match_1.splitter._cstage1",
  "Rcic.F3.PSet.CandidateScopeAttack.hidden_reads",
  "Rcic.F3.PSet.CandidateScopeAttack.acc_normalized_mem",
  "Rcic.F3.PSet.CandidateScopeAttack.accσ",
  "Rcic.F3.PSet.CandidateScopeAttack.acc_read",
  "Rcic.F3.PSet.CandidateScopeAttack.shadowed",
  "Rcic.F3.PSet.CandidateScopeAttack.accρ",
  "Rcic.F3.PSet.CandidateScopeAttack.accρ._closed_1._cstage2",
  "Rcic.F3.PSet.CandidateScopeAttack.accσ._cstage2",
  "Rcic.F3.PSet.CandidateScopeAttack.bodyless._closed_1._cstage2",
  "Rcic.F3.PSet.CandidateScopeAttack.hidden_scans",
  "Rcic.F3.PSet.CandidateScopeAttack.acc_nonrefutable",
  "Rcic.F3.PSet.CandidateScopeAttack.bodyless",
  "Rcic.F3.PSet.CandidateScopeAttack.bodyless._cstage2",
  "Rcic.F3.PSet.CandidateScopeAttack.extended",
  "Rcic.F3.PSet.CandidateScopeAttack.ReaderWitness",
  "Rcic.F3.PSet.CandidateScopeAttack.acc_witness",
  "Rcic.F3.PSet.CandidateScopeAttack.accK._cstage2",
  "Rcic.F3.PSet.CandidateScopeAttack.acc_original_mem",
  "Rcic.F3.PSet.CandidateScopeAttack.AccWitness",
  "Rcic.F3.PSet.CandidateScopeAttack.bodyless._closed_2._cstage2",
  "Rcic.F3.PSet.CandidateScopeAttack.accρ._closed_2._cstage2",
  "Rcic.F3.PSet.CandidateScopeAttack.accρ._cstage2",
  "Rcic.F3.PSet.CandidateScopeAttack.nonfresh_rejected",
  "Rcic.F3.PSet.CandidateScopeAttack.accσ._cstage1",
  "Rcic.F3.PSet.CandidateScopeAttack.accK",
  "Rcic.F3.PSet.CandidateScopeAttack.reader_nonrefutable",
  "Rcic.F3.PSet.CandidateScopeAttack.accσ._closed_1._cstage2",
  "Rcic.F3.PSet.CandidateScopeAttack.acc_parameters_fit",
  "Rcic.F3.PSet.CandidateScopeAttack.bodies_equal",
  "Rcic.F3.PSet.CandidateScopeAttack.accK._cstage1",
  "Rcic.F3.PSet.CandidateScopeAttack.acc_normalized",
  "Rcic.F3.PSet.CandidateScopeAttack.bodyless._cstage1",
  "Rcic.F3.PSet.CandidateScopeAttack.reader_witness",
  "Rcic.F3.PSet.CandidateScopeAttack.accμ",
  "Rcic.F3.PSet.CandidateScopeAttack.accρ._cstage1",
  "Rcic.F3.PSet.CandidateScopeAttack.acc_normalized.match_1",
  "Rcic.F3.PSet.CandidateTupleAttack.instances",
  "Rcic.F3.PSet.CandidateTupleAttack.raw_admissible",
  "Rcic.F3.PSet.CandidateTupleAttack.certificates",
  "Rcic.F3.PSet.CandidateTupleAttack.proper_inclusion",
  "Rcic.F3.PSet.CandidateTupleAttack.component_nonrefutable",
  "Rcic.F3.PSet.CandidateTupleAttack.X._cstage1",
  "Rcic.F3.PSet.CandidateTupleAttack.raw_tuple.match_1",
  "Rcic.F3.PSet.CandidateTupleAttack.Witness",
  "Rcic.F3.PSet.CandidateTupleAttack.candidate_tuple",
  "Rcic.F3.PSet.CandidateTupleAttack.family_all",
  "Rcic.F3.PSet.CandidateTupleAttack.component_witness",
  "Rcic.F3.PSet.CandidateTupleAttack.X",
  "Rcic.F3.PSet.CandidateTupleAttack.X._cstage2",
  "Rcic.F3.PSet.CandidateTupleAttack.R",
  "Rcic.F3.PSet.CandidateTupleAttack.scan",
  "Rcic.F3.PSet.CandidateTupleAttack.raw_closed",
  "Rcic.F3.PSet.CandidateTupleAttack.raw_tuple",
  "Rcic.F3.PSet.CandidateTupleAttack.frame_sub",
  "Rcic.F3.PSet.PiCleanViews.Clean",
  "Rcic.F3.PSet.PiCleanViews.liftFields_free",
  "Rcic.F3.PSet.PiCleanViews.Clean.recursive_frees",
  "Rcic.F3.PSet.PiCleanViews.Clean.match_1._cstage1",
  "Rcic.F3.PSet.PiCleanViews.of_admitted",
  "Rcic.F3.PSet.PiCleanViews.Clean.match_1",
  "Rcic.F3.PSet.PiCleanViews.Clean.lift",
  "Rcic.F3.PSet.PropEval.inputs_of_admitted",
  "Rcic.F3.PSet.PropEval.Context.rootCtx.eq_1",
  "Rcic.F3.PSet.PropEval.eval_of_candidate_fields",
  "Rcic.F3.PSet.PropEvalAdmittedInputsAttack.candidate_prefix.match_1",
  "Rcic.F3.PSet.PropEvalAdmittedInputsAttack.candidateTable",
  "Rcic.F3.PSet.PropEvalAdmittedInputsAttack.candidate_fields",
  "Rcic.F3.PSet.PropEvalAdmittedInputsAttack.component_witness",
  "Rcic.F3.PSet.PropEvalAdmittedInputsAttack.instances",
  "Rcic.F3.PSet.PropEvalAdmittedInputsAttack.bound._cstage1",
  "Rcic.F3.PSet.PropEvalAdmittedInputsAttack.component_nonrefutable",
  "Rcic.F3.PSet.PropEvalAdmittedInputsAttack.Witness",
  "Rcic.F3.PSet.PropEvalAdmittedInputsAttack.reader_closed",
  "Rcic.F3.PSet.PropEvalAdmittedInputsAttack.bound",
  "Rcic.F3.PSet.PropEvalAdmittedInputsAttack.prefix_bodies",
  "Rcic.F3.PSet.PropEvalAdmittedInputsAttack.bound._cstage2",
  "Rcic.F3.PSet.PropEvalAdmittedInputsAttack.candidate_prefix",
  "Rcic.F3.PSet.PiIndependent.telFits_free",
  "Rcic.F3.PSet.PropEvalCandidate.admissible",
  "Rcic.F3.PSet.PropEvalCandidate.EvalPredicate",
  "Rcic.F3.PSet.PropEvalCandidate.canonical_agreement",
  "Rcic.F3.PSet.PropEvalCandidate.leaf_eval",
  "Rcic.F3.PSet.PiIndependent.leafArgs.eq_1",
  "Rcic.F3.PSet.PropEvalCandidate.candidate",
  "Rcic.F3.PSet.PropEvalCandidate.exists_of_closed",
  "Rcic.F3.PSet.PropEvalCandidate.exists_of_mem",
  "Rcic.F3.PSet.PropEvalCandidateAttack.candidate_admissible",
  "Rcic.F3.PSet.PropEvalCandidateAttack.component_nonrefutable",
  "Rcic.F3.PSet.PropEvalCandidateAttack.X",
  "Rcic.F3.PSet.PropEvalCandidateAttack.Witness",
  "Rcic.F3.PSet.PropEvalCandidateAttack.candidate_closed",
  "Rcic.F3.PSet.PropEvalCandidateAttack.component_witness",
  "Rcic.F3.PSet.PropEval.inputs_of_clean_views",
  "Rcic.F3.PSet.PropEval.recursive_packet_of_clean_view",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.field._closed_3._cstage2",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.assignment._closed_1._cstage2",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.parameters_free",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.Witness",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.composed_nonrefutable",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.field._cstage1",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.inhabited_domain",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.domains._cstage2",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.arguments._cstage1",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.assignment",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.assignment._cstage2",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.arguments_free",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.field._closed_2._cstage2",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.fitted_leaf",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.domains._closed_1._cstage2",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.domains._closed_2._cstage2",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.model",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.field._closed_1._cstage2",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.arguments",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.arguments._closed_1._cstage2",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.children",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.reached_arguments",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.domains",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.assignment._cstage1",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.composed_witness",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.normalized_member",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.domains._closed_4._cstage2",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.field",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.field._cstage2",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.arguments._closed_2._cstage2",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.component_witness",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.domains._closed_3._cstage2",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.domains._cstage1",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.arguments._cstage2",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.domains_free",
  "Rcic.F3.PSet.PropEvalCandidateLeafAttack.component_nonrefutable",
  "Rcic.F3.PSet.PropEvalCandidate.ctorAt_parameters_at",
  "Rcic.F3.PSet.PropEvalCandidateLevelsAttack.Witness",
  "Rcic.F3.PSet.PropEvalCandidateLevelsAttack.component_nonrefutable",
  "Rcic.F3.PSet.PropEvalCandidateLevelsAttack.component_witness",
  "Rcic.F3.PSet.PropEvalCandidateLevelsAttack.family_bounded",
  "Rcic.F3.PSet.PropEvalCandidate.ctorAt_parameters",
  "Rcic.F3.PSet.PropEvalCandidateParamsAttack.component_nonrefutable",
  "Rcic.F3.PSet.PropEvalCandidateParamsAttack.suffix_rejected",
  "Rcic.F3.PSet.PropEvalCandidateParamsAttack.component_witness",
  "Rcic.F3.PSet.PropEvalCandidateParamsAttack.Witness",
  "Rcic.F3.PSet.PropEvalCandidateParamsAttack.constructor",
  "Rcic.F3.PSet.PropEvalCandidate.constructor_step_of_prefixes",
  "Rcic.F3.PSet.PropEvalCandidate.closed_of_constructor_step",
  "Rcic.F3.PSet.PropEvalCandidate.constructor_step",
  "Rcic.F3.PSet.PropEvalCandidateStepAttack.produced_closed",
  "Rcic.F3.PSet.PropEvalCandidateStepAttack.component_nonrefutable",
  "Rcic.F3.PSet.PropEvalCandidateStepAttack.produced_step.match_1",
  "Rcic.F3.PSet.PropEvalCandidateStepAttack.raw_major",
  "Rcic.F3.PSet.PropEvalCandidateStepAttack.Witness",
  "Rcic.F3.PSet.PropEvalCandidateStepAttack.produced_step",
  "Rcic.F3.PSet.PropEvalCandidateStepAttack.component_witness",
  "Rcic.F3.PSet.PropEvalCandidateStepAttack.produced",
  "Rcic.F3.PSet.PropEvalCandidateStepAttack.candidate_major",
  "Rcic.F3.PSet.PropEvalCandidateSuite.Witness",
  "Rcic.F3.PSet.PropEvalCandidateSuite.component_witness",
  "Rcic.F3.PSet.PropEvalCandidateSuite.component_nonrefutable",
  "Rcic.F3.PSet.PropEval.inputs_of_certified_views",
  "Rcic.F3.PSet.PropEval.FieldCertificates.match_1._cstage1",
  "Rcic.F3.PSet.PropEval.FieldCertificates.lift",
  "Rcic.F3.PSet.PropEval.FieldCertificates._sunfold",
  "Rcic.F3.PSet.PropEval.FieldCertificates._unsafe_rec",
  "Rcic.F3.PSet.PropEval.FieldCertificates",
  "Rcic.F3.PSet.PropEval.RecursivePacket",
  "Rcic.F3.PSet.PropEval.FieldCertificates.match_1",
  "Rcic.F3.PSet.PropEval.Eval.mem_guarded_of_typed_motive",
  "Rcic.F3.PSet.fits_of_typed_fapps_ne",
  "Rcic.F3.PSet.PropEvalMotiveGuardAttack.Witness",
  "Rcic.F3.PSet.PropEvalMotiveGuardAttack.family_proof",
  "Rcic.F3.PSet.PropEvalMotiveGuardAttack.ctx",
  "Rcic.F3.PSet.PropEvalMotiveGuardAttack.guarded",
  "Rcic.F3.PSet.PropEvalMotiveGuardAttack.component_witness",
  "Rcic.F3.PSet.PropEvalMotiveGuardAttack.component_nonrefutable",
  "Rcic.F3.PSet.PropEval.childCarrier",
  "Rcic.F3.PSet.PropEval.recursive_packet_of_candidate",
  "Rcic.F3.PSet.PropEval.recursive_packet_of_leaf_evaluations",
  "Rcic.F3.PSet.PropEvalCandidate.raw_family_inputs",
  "Rcic.F3.PSet.PropEvalRawFamilyAttack.installed_family_all",
  "Rcic.F3.PSet.PropEvalRawFamilyAttack.component_nonrefutable",
  "Rcic.F3.PSet.PropEvalRawFamilyAttack.component_witness",
  "Rcic.F3.PSet.PropEvalRawFamilyAttack.Witness"
]

def sealedTheorems : List Name :=
  (sealedTheoremsRaw.split (· == ' ') |>.map String.toName)

def allowedAxioms : List Name := [``propext, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let mut actual : Array Name := #[]
  for m in sealedModules do
    let some idx := env.getModuleIdx? m
      | throwError "[a_candidate_step_seal] module {m} is not imported"
    actual := actual ++ env.header.moduleData[idx.toNat]!.constNames
  unless actual.size == sealedTheorems.length do
    throwError "[a_candidate_step_seal] inventory size {sealedTheorems.length} differs from {actual.size}"
  for t in actual do
    unless sealedTheorems.contains t do
      throwError "[a_candidate_step_seal] uncovered declaration {t}"
  for t in sealedTheorems do
    unless actual.contains t && env.contains t do
      throwError "[a_candidate_step_seal] stale or foreign declaration {t}"
  let (_, s) := ((do
    for t in sealedTheorems do CollectAxioms.collect t).run env).run {}
  let bad := s.axioms.filter (fun ax => !allowedAxioms.contains ax)
  unless bad.isEmpty do
    for t in sealedTheorems do
      let (_, st) := ((CollectAxioms.collect t).run env).run {}
      for ax in st.axioms do
        unless allowedAxioms.contains ax do
          throwError "[a_candidate_step_seal] {t} depends on {ax}"
  logInfo m!"[a_candidate_step_seal] {sealedTheorems.length} declarations in {sealedModules.length} modules; exact coverage; axioms ⊆ {allowedAxioms}; closure_claim = 0"

end Rcic.F3.ACandidateStepSeal

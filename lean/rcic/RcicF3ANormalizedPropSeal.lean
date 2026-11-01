import Lean
import rcic.RcicF3AEvalEndpointSeal
import rcic.RcicF3DeltaNormalize
import rcic.RcicF3EvalRoleDelta
import rcic.RcicF3EvalRoleDeltaAttack
import rcic.RcicF3EvalPlanNormal
import rcic.RcicF3EvalPlanNormalMono
import rcic.RcicF3EvalPlanNormalProp
import rcic.RcicF3EvalPlanNormalLevels
import rcic.RcicF3EvalPlanNormalSlice
import rcic.RcicF3EvalPlanNormalTuple
import rcic.RcicF3EvalPlanNormalCompare
import rcic.RcicF3EvalPlanNormalAttack
import rcic.RcicF3EvalPlanNormalPropAttack
import rcic.RcicF3EvalPlanNormalCompareAttack
import rcic.RcicF3PropEvalFrame
import rcic.RcicF3PropEvalFramePacket
import rcic.RcicF3PropEvalFrameInputs
import rcic.RcicF3PropEvalFrameAdmitted
import rcic.RcicF3PropEvalNormalStep
import rcic.RcicF3PropEvalNormalTotal
import rcic.RcicF3PropEvalNormalValue
import rcic.RcicF3PropEvalNormalAttack
import rcic.RcicF3EvalPropRecMem
import rcic.RcicF3EvalPropRecMemAttack
import rcic.RcicF3EvalPropRecIota
import rcic.RcicF3EvalPropRecPkg
import rcic.RcicF3EvalPropRecPkgAttack
import rcic.RcicF3ANormalizedPropContract

/-!
# Exact axiom seal for the produced normalized Prop recursor package

All declarations, including private and generated declarations, in the
27 producer and witness modules are sealed. The inherited three exact
seals remain imported. Universal StepAG, the normalized-role migration,
small data frames and the checked apex remain unpaid. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.ANormalizedPropSeal
open Lean Elab Command

def sealedModules : List Name := [
  `rcic.RcicF3DeltaNormalize,
  `rcic.RcicF3EvalRoleDelta,
  `rcic.RcicF3EvalRoleDeltaAttack,
  `rcic.RcicF3EvalPlanNormal,
  `rcic.RcicF3EvalPlanNormalMono,
  `rcic.RcicF3EvalPlanNormalProp,
  `rcic.RcicF3EvalPlanNormalLevels,
  `rcic.RcicF3EvalPlanNormalSlice,
  `rcic.RcicF3EvalPlanNormalTuple,
  `rcic.RcicF3EvalPlanNormalCompare,
  `rcic.RcicF3EvalPlanNormalAttack,
  `rcic.RcicF3EvalPlanNormalPropAttack,
  `rcic.RcicF3EvalPlanNormalCompareAttack,
  `rcic.RcicF3PropEvalFrame,
  `rcic.RcicF3PropEvalFramePacket,
  `rcic.RcicF3PropEvalFrameInputs,
  `rcic.RcicF3PropEvalFrameAdmitted,
  `rcic.RcicF3PropEvalNormalStep,
  `rcic.RcicF3PropEvalNormalTotal,
  `rcic.RcicF3PropEvalNormalValue,
  `rcic.RcicF3PropEvalNormalAttack,
  `rcic.RcicF3EvalPropRecMem,
  `rcic.RcicF3EvalPropRecMemAttack,
  `rcic.RcicF3EvalPropRecIota,
  `rcic.RcicF3EvalPropRecPkg,
  `rcic.RcicF3EvalPropRecPkgAttack,
  `rcic.RcicF3ANormalizedPropContract
]

def sealedTheoremsRaw : String := " ".intercalate [
  "Rcic.F3.PSet.DeltaNormalize.whnf_of_ne",
  "Rcic.F3.PSet.DeltaNormalize.BodyEquations",
  "Rcic.F3.PSet.DeltaNormalize.telescope_of_mem.match_1",
  "Rcic.F3.PSet.DeltaNormalize.whnf_of_ne.match_1",
  "Rcic.F3.PSet.DeltaNormalize.telescope_of_mem",
  "Rcic.F3.PSet.EvalRoleDelta.transparent_body_data.match_1",
  "Rcic.F3.PSet.EvalRoleDelta.bodyEquations_at_node",
  "Rcic.F3.PSet.memberVal.eq_1",
  "Rcic.F3.PSet.EvalRoleDelta.transparent_body_data",
  "Rcic.F3.PSet.EvalRoleDelta.bodyEquations_extension",
  "Rcic.F3.PSet.EvalRoleDelta.bodyEquations_transfer",
  "Rcic.F3.PSet.EvalRoleDelta.bodyEquations_of_faithful",
  "Rcic.F3.PSet.EvalRoleDelta.bodyEquations_fresh_extension",
  "Rcic.F3.PSet.EvalRoleDelta.body_eq_of_faithful",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.high_levels",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.longInstance._cstage2",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.longInstance._closed_4._cstage2",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.longInstance._closed_3._cstage2",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.long_high_equation",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.longInstance._closed_2._cstage2",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.component_witness",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.every_instance",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.longInstance",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.longInstance._closed_5._cstage2",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.lookup",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.fresh_equations",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.component_nonrefutable",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.Witness",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.longInstance._cstage1",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.longInstance._closed_1._cstage2",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.malformed_arity",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.faithful",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.table",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.equations",
  "Rcic.F3.PSet.EvalRoleDeltaAttack.longInstance._closed_6._cstage2",
  "Rcic.F3.PSet.EvalPlanNormal.ctors_length",
  "Rcic.F3.PSet.EvalPlanNormal.fieldSpec.match_1",
  "Rcic.F3.PSet.EvalPlanNormal.fieldSpec",
  "Rcic.F3.PSet.EvalPlanNormal.ctorAt_of_bodyEquations",
  "Rcic.F3.PSet.EvalPlanNormal.ctorAt_of_group",
  "Rcic.F3.PSet.EvalPlanNormal.constructors.eq_1",
  "Rcic.F3.PSet.EvalPlanNormal.fields",
  "Rcic.F3.PSet.EvalPlanNormal.constructors",
  "Rcic.F3.PSet.EvalPlanNormal.constructors.proof_1",
  "Rcic.F3.PSet.EvalPlanNormal.fields.proof_1",
  "Rcic.F3.PSet.EvalPlanNormal.index.proof_1",
  "Rcic.F3.PSet.EvalPlanNormal.specs._sunfold",
  "Rcic.F3.PSet.EvalPlanNormal.specs_clean",
  "Rcic.F3.PSet.EvalPlanNormal.fd.eq_1",
  "Rcic.F3.PSet.EvalPlanNormal.fd",
  "Rcic.F3.PSet.EvalPlanNormal.index",
  "Rcic.F3.PSet.EvalPlanNormal.fieldSpec.match_1._cstage1",
  "Rcic.F3.PSet.EvalPlanNormal.specs.match_1",
  "Rcic.F3.PSet.EvalPlanNormal.specs",
  "Rcic.F3.PSet.EvalPlanNormal.fields_forward",
  "Rcic.F3.PSet.EvalPlanNormal.index.eq_1",
  "Rcic.F3.PSet.EvalPlanNormal.field_den_of_mem",
  "Rcic.F3.PSet.EvalPlanNormal.ctor_get",
  "Rcic.F3.PSet.EvalPlanNormal.table_eq",
  "Rcic.F3.PSet.EvalPlanNormal.specs.match_1._cstage1",
  "Rcic.F3.PSet.EvalPlanNormal.constructorMono_of_group",
  "Rcic.F3.PSet.EvalPlanNormalProp.normalized_closed",
  "Rcic.F3.PSet.EvalPlanNormalProp.raw_le_normalized",
  "Rcic.F3.PSet.EvalPlanNormal.bounded_of_group",
  "Rcic.F3.PSet.EvalPlanNormal.field_levels",
  "Rcic.F3.PSet.EvalPlanNormal.reader_bodies_levels",
  "Rcic.F3.PSet.EvalPlanNormal.fields_levels",
  "Rcic.F3.PSet.EvalPlanNormal.telescope_levels",
  "Rcic.F3.PSet.EvalPlanNormalSlice.application_sub_at",
  "Rcic.F3.PSet.EvalPlanNormalSlice.recursive_sub",
  "Rcic.F3.PSet.EvalPlanNormalSlice.Predicate",
  "Rcic.F3.PSet.EvalPlanNormalSlice.GuardedSub",
  "Rcic.F3.PSet.EvalPlanNormalSlice.parameter_key",
  "Rcic.F3.PSet.EvalPlanNormalSlice.recursive_sub_of_guarded",
  "_private.rcic.RcicF3EvalPlanNormalTuple.0.Rcic.F3.PSet.EvalPlanNormal.specs.match_1.splitter",
  "_private.rcic.RcicF3EvalPlanNormalTuple.0.Rcic.F3.PSet.EvalPlanNormal.specs.match_1.splitter._rarg._cstage2",
  "_private.rcic.RcicF3EvalPlanNormalTuple.0.Rcic.F3.PSet.EvalPlanNormal.specs.match_1.splitter._cstage1",
  "Rcic.F3.PSet.EvalPlanNormal.specs.eq_2",
  "_private.rcic.RcicF3EvalPlanNormalTuple.0.Rcic.F3.PSet.EvalPlanNormal.specs.match_1.eq_2",
  "Rcic.F3.PSet.EvalPlanNormal.specs_length",
  "Rcic.F3.PSet.EvalPlanNormal.fields_to_raw_of_guarded",
  "Rcic.F3.PSet.EvalPlanNormal.specs.eq_1",
  "_private.rcic.RcicF3EvalPlanNormalTuple.0.Rcic.F3.PSet.EvalPlanNormal.specs.match_1.splitter._cstage2",
  "_private.rcic.RcicF3EvalPlanNormalTuple.0.Rcic.F3.PSet.EvalPlanNormal.specs.match_1.eq_1",
  "Rcic.F3.PSet.EvalPlanNormal.field_at",
  "Rcic.F3.PSet.EvalPlanNormal.fields_to_raw",
  "Rcic.F3.PSet.EvalPlanNormal.tuple_transport",
  "Rcic.F3.PSet.EvalPlanNormalCompare.target_facts",
  "Rcic.F3.PSet.EvalPlanNormalCompare.constructor_to_raw",
  "Rcic.F3.PSet.EvalPlanNormalCompare.normalized_le_raw",
  "Rcic.F3.PSet.EvalPlanNormalAttack.ctor.proof_1",
  "Rcic.F3.PSet.EvalPlanNormalAttack.Witness",
  "Rcic.F3.PSet.EvalPlanNormalAttack.plan",
  "Rcic.F3.PSet.EvalPlanNormalAttack.parameter._closed_1._cstage2",
  "Rcic.F3.PSet.EvalPlanNormalAttack.μ",
  "Rcic.F3.PSet.EvalPlanNormalAttack.hidden_normal",
  "Rcic.F3.PSet.EvalPlanNormalAttack.ctor",
  "Rcic.F3.PSet.EvalPlanNormalAttack.parameter._cstage1",
  "Rcic.F3.PSet.EvalPlanNormalAttack.carrier",
  "Rcic.F3.PSet.EvalPlanNormalAttack.Witness.proof_1",
  "Rcic.F3.PSet.EvalPlanNormalAttack.parameter",
  "Rcic.F3.PSet.EvalPlanNormalAttack.Witness.proof_2",
  "Rcic.F3.PSet.EvalPlanNormalAttack.parameter._cstage2",
  "Rcic.F3.PSet.EvalPlanNormalAttack.component_witness",
  "Rcic.F3.PSet.EvalPlanNormalAttack.component_nonrefutable",
  "Rcic.F3.PSet.EvalPlanNormalPropAttack.Witness",
  "Rcic.F3.PSet.EvalPlanNormalPropAttack.component_witness",
  "Rcic.F3.PSet.EvalPlanNormalPropAttack.component_nonrefutable",
  "Rcic.F3.PSet.EvalPlanNormalCompareAttack.component_witness",
  "Rcic.F3.PSet.EvalPlanNormalCompareAttack.component_witness.match_1",
  "Rcic.F3.PSet.EvalPlanNormalCompareAttack.component_nonrefutable",
  "Rcic.F3.PSet.EvalPlanNormalCompareAttack.Witness",
  "Rcic.F3.PSet.PropEvalFrame.admissible",
  "Rcic.F3.PSet.PropEvalFrame.candidate",
  "Rcic.F3.PSet.PropEvalFrame.leaf_eval",
  "Rcic.F3.PSet.PropEvalFrame.exists_of_mem",
  "Rcic.F3.PSet.PropEval.recursive_packet_on_frame",
  "Rcic.F3.PSet.PropEval.inputs_of_clean_views_on_frame",
  "Rcic.F3.PSet.PropEval.recursive_packet_of_clean_view_on_frame",
  "Rcic.F3.PSet.PropEval.eval_of_frame_fields",
  "Rcic.F3.PSet.PropEval.inputs_of_admitted_on_frame",
  "Rcic.F3.PSet.PropEval.Context.rootCtx.eq_1",
  "Rcic.F3.PSet.PropEvalNormalized.candidate",
  "Rcic.F3.PSet.PropEvalNormalized.base",
  "Rcic.F3.PSet.PropEvalNormalized.constructor_step",
  "Rcic.F3.PSet.PropEvalNormalized.raw_evaluates",
  "Rcic.F3.PSet.PropEvalNormalized.normalized_evaluates",
  "Rcic.F3.PSet.PropEvalNormalized.candidate_closed",
  "Rcic.F3.PSet.PropEvalNormalized.major_at_frame",
  "Rcic.F3.PSet.PropEvalNormalized.result_spec",
  "Rcic.F3.PSet.PropEvalNormalAttack.Witness",
  "Rcic.F3.PSet.PropEvalNormalAttack.component_witness.match_1",
  "Rcic.F3.PSet.PropEvalNormalAttack.component_nonrefutable",
  "Rcic.F3.PSet.PropEvalNormalAttack.C",
  "Rcic.F3.PSet.PropEvalNormalAttack.component_witness",
  "Rcic.F3.PSet.PropEvalNormalAttack.X",
  "Rcic.F3.PSet.PropEvalNormalAttack.result",
  "Rcic.F3.PSet.PropEvalNormalAttack.μ",
  "_private.rcic.RcicF3PropEvalNormalAttack.0.Rcic.F3.PSet.PropEvalNormalAttack.ed_table",
  "Rcic.F3.PSet.EvalPropRecMem.memberValue_mem.match_1",
  "Rcic.F3.PSet.EvalPropRecMem.family_equation_of_group",
  "Rcic.F3.PSet.EvalPropRecMem.memberValue_mem",
  "Rcic.F3.PSet.EvalPropRecMem.member_sound",
  "Rcic.F3.PSet.EvalPropRecMemAttack.component_nonrefutable",
  "Rcic.F3.PSet.EvalPropRecMemAttack.component_witness.match_1",
  "Rcic.F3.PSet.EvalPropRecMemAttack.Witness",
  "Rcic.F3.PSet.EvalPropRecMemAttack.component_witness",
  "Rcic.F3.PSet.EvalPropRecIota.witness_kinds",
  "Rcic.F3.PSet.EvalPropRecIota.witness_row",
  "Rcic.F3.PSet.EvalPropRecIota.iota_prop",
  "Rcic.F3.PSet.EvalPropRecIota.no_witness",
  "Rcic.F3.PSet.EvalPropRecIota.iota_at",
  "Rcic.F3.PSet.EvalPropRecPkg.rec_pkg",
  "Rcic.F3.PSet.EvalPropRecPkgAttack.component_witness.match_1",
  "Rcic.F3.PSet.EvalPropRecPkgAttack.component_witness",
  "Rcic.F3.PSet.EvalPropRecPkgAttack.Witness",
  "Rcic.F3.PSet.EvalPropRecPkgAttack.component_nonrefutable",
  "Rcic.F3.PSet.ANormalizedPropContract.components",
  "Rcic.F3.PSet.ANormalizedPropContract.Target",
  "Rcic.F3.PSet.ANormalizedPropContract.target_iff_stepAG",
  "Rcic.F3.PSet.ANormalizedPropContract.components_nonrefutable",
  "Rcic.F3.PSet.ANormalizedPropContract.target_of_stepAG",
  "Rcic.F3.PSet.ANormalizedPropContract.Components"
]

def sealedTheorems : List Name :=
  (sealedTheoremsRaw.split (· == ' ') |>.map String.toName)

def allowedAxioms : List Name := [``propext, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let mut actual : Array Name := #[]
  for m in sealedModules do
    let some idx := env.getModuleIdx? m
      | throwError "[a_normalized_prop_seal] module {m} is not imported"
    actual := actual ++ env.header.moduleData[idx.toNat]!.constNames
  unless actual.size == sealedTheorems.length do
    throwError "[a_normalized_prop_seal] inventory size {sealedTheorems.length} differs from {actual.size}"
  for t in actual do
    unless sealedTheorems.contains t do
      throwError "[a_normalized_prop_seal] uncovered declaration {t}"
  for t in sealedTheorems do
    unless actual.contains t && env.contains t do
      throwError "[a_normalized_prop_seal] stale or foreign declaration {t}"
  let (_, s) := ((do
    for t in sealedTheorems do CollectAxioms.collect t).run env).run {}
  let bad := s.axioms.filter (fun ax => !allowedAxioms.contains ax)
  unless bad.isEmpty do
    for t in sealedTheorems do
      let (_, st) := ((CollectAxioms.collect t).run env).run {}
      for ax in st.axioms do
        unless allowedAxioms.contains ax do
          throwError "[a_normalized_prop_seal] {t} depends on {ax}"
  logInfo m!"[a_normalized_prop_seal] {sealedTheorems.length} declarations in {sealedModules.length} modules; exact coverage; axioms ⊆ {allowedAxioms}; closure_claim = 0"


end Rcic.F3.ANormalizedPropSeal

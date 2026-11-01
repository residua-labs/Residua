import Lean
import rcic.RcicF3ADataKeySeal
import rcic.RcicF3NormPendAWRecPkg
import rcic.RcicF3NormPendAWGroup
import rcic.RcicF3RawNatFrame
import rcic.RcicF3NormNatPlan
import rcic.RcicF3NormNatInvariant
import rcic.RcicF3NormPendAWInvariant
import rcic.RcicF3NormPendAWChecked
import rcic.RcicF3NormPendAWSameTable
import rcic.RcicF3AWFixtureContract

/-!
# Exact declaration seal for the produced normalized Nat/W fixture

Every private and generated declaration in these nine modules is sealed.
The previous exact seals remain imported. Full new Nat and W invariants,
the actual W recursor package, same-environment checked conditions and
same-table nontrivial values are produced. Universal StepAG and migration
into the checked W/D apex remain unpaid. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.AWFixtureSeal
open Lean Elab Command

def sealedModules : List Name := [
  `rcic.RcicF3NormPendAWRecPkg,
  `rcic.RcicF3NormPendAWGroup,
  `rcic.RcicF3RawNatFrame,
  `rcic.RcicF3NormNatPlan,
  `rcic.RcicF3NormNatInvariant,
  `rcic.RcicF3NormPendAWInvariant,
  `rcic.RcicF3NormPendAWChecked,
  `rcic.RcicF3NormPendAWSameTable,
  `rcic.RcicF3AWFixtureContract
]

def sealedTheoremsRaw : String := " ".intercalate [
  "Rcic.F3.PSet.NormPendAWRecPkg.component_witness",
  "Rcic.F3.PSet.NormPendAWRecPkg.values",
  "Rcic.F3.PSet.NormPendAWRecPkg.Witness",
  "Rcic.F3.PSet.NormPendAWRecPkg.actual_rec_pkg",
  "Rcic.F3.PSet.NormPendAWRecPkg.component_nonrefutable",
  "Rcic.F3.PSet.NormPendAWRecPkg.rec_pkg_of_values",
  "Rcic.F3.PSet.NormPendAWRecPkg.actual_values",
  "Rcic.F3.PSet.NormPendAWGroup.at_table",
  "Rcic.F3.PSet.NormPendAWGroup.Witness.proof_1",
  "Rcic.F3.PSet.NormPendAWGroup.component_nonrefutable",
  "rcic.RcicF3NormPendAWGroup._auxLemma.2",
  "rcic.RcicF3NormPendAWGroup._auxLemma.3",
  "Rcic.F3.PSet.NormPendAWGroup.Witness",
  "Rcic.F3.PSet.NormPendAWGroup.group_step",
  "rcic.RcicF3NormPendAWGroup._auxLemma.1",
  "Rcic.F3.PSet.NormPendAWGroup.Witness.proof_2",
  "Rcic.F3.PSet.NormPendAWGroup.component_witness",
  "Rcic.F3.PSet.RawNatFrame.role_value",
  "Rcic.F3.PSet.RawNatFrame.numeral._sunfold",
  "Rcic.F3.PSet.RawNatFrame.data._closed_5._cstage2",
  "Rcic.F3.PSet.RawNatFrame.type_read",
  "Rcic.F3.PSet.RawNatFrame.numeral._unsafe_rec",
  "Rcic.F3.PSet.RawNatFrame.fibre_full",
  "Rcic.F3.PSet.RawNatFrame.data._closed_1._cstage2",
  "Rcic.F3.PSet.RawNatFrame.Witness",
  "Rcic.F3.PSet.RawNatFrame.admissible_at_node",
  "Rcic.F3.PSet.RawNatFrame.numeral",
  "Rcic.F3.PSet.RawNatFrame.numeral._closed_1._cstage2",
  "Rcic.F3.PSet.RawNatFrame.of_candidate",
  "Rcic.F3.PSet.RawNatFrame.data._closed_2._cstage2",
  "Rcic.F3.PSet.RawNatFrame.numeral.match_1._cstage1",
  "Rcic.F3.PSet.RawNatFrame.descriptor",
  "Rcic.F3.PSet.RawNatFrame.raw_closed",
  "Rcic.F3.PSet.RawNatFrame.numeral._cstage2",
  "Rcic.F3.PSet.RawNatFrame.nonIR",
  "Rcic.F3.PSet.RawNatFrame.numeral.match_1",
  "Rcic.F3.PSet.RawNatFrame.field_read",
  "Rcic.F3.PSet.RawNatFrame.candidate",
  "Rcic.F3.PSet.RawNatFrame.raw_admissible",
  "Rcic.F3.PSet.RawNatFrame.data._closed_7._cstage2",
  "Rcic.F3.PSet.RawNatFrame.zero_ne_one",
  "Rcic.F3.PSet.RawNatFrame.data._cstage1",
  "Rcic.F3.PSet.RawNatFrame.data._closed_4._cstage2",
  "Rcic.F3.PSet.RawNatFrame.ctor_cases",
  "Rcic.F3.PSet.RawNatFrame.data._closed_3._cstage2",
  "Rcic.F3.PSet.RawNatFrame.data",
  "Rcic.F3.PSet.RawNatFrame.closed_cross",
  "Rcic.F3.PSet.RawNatFrame.successor_mem",
  "Rcic.F3.PSet.RawNatFrame.numeral._cstage1",
  "Rcic.F3.PSet.RawNatFrame.zero_mem",
  "Rcic.F3.PSet.RawNatFrame.role_value_at_node",
  "Rcic.F3.PSet.RawNatFrame.bounded",
  "Rcic.F3.PSet.RawNatFrame.raw_fibre",
  "Rcic.F3.PSet.RawNatFrame.closed_at_node",
  "Rcic.F3.PSet.RawNatFrame.component_witness",
  "Rcic.F3.PSet.RawNatFrame.result_tuple",
  "Rcic.F3.PSet.RawNatFrame.numeral_mem",
  "Rcic.F3.PSet.RawNatFrame.data._closed_6._cstage2",
  "Rcic.F3.PSet.RawNatFrame.candidate_admissible",
  "Rcic.F3.PSet.RawNatFrame.component_nonrefutable",
  "Rcic.F3.PSet.RawNatFrame.data._cstage2",
  "Rcic.F3.PSet.RawNatFrame.candidate_closed",
  "Rcic.F3.PSet.NormNatPlan.raw_plan",
  "Rcic.F3.PSet.NormNatPlan.component_witness",
  "Rcic.F3.PSet.NormNatPlan.member_value_eq",
  "Rcic.F3.PSet.NormNatPlan.fields_eq",
  "Rcic.F3.PSet.NormNatPlan.endpoint_eq",
  "Rcic.F3.PSet.NormNatPlan.actual_field_inhabited",
  "Rcic.F3.PSet.NormNatPlan.normalized_context",
  "Rcic.F3.PSet.NormNatPlan.successorSlot.proof_1",
  "Rcic.F3.PSet.NormNatPlan.arity",
  "Rcic.F3.PSet.NormNatPlan.fields_identity",
  "Rcic.F3.PSet.NormNatPlan.field_reader",
  "Rcic.F3.PSet.NormNatPlan.constructors_exact",
  "Rcic.F3.PSet.NormNatPlan.installed_recursor",
  "Rcic.F3.PSet.NormNatPlan.actual_fields_inhabited",
  "Rcic.F3.PSet.NormNatPlan.bounded",
  "Rcic.F3.PSet.NormNatPlan.recursor_role",
  "Rcic.F3.PSet.NormNatPlan.ctorClasses",
  "Rcic.F3.PSet.NormNatPlan.Witness",
  "rcic.RcicF3NormNatPlan._auxLemma.3",
  "Rcic.F3.PSet.NormNatPlan.scan",
  "Rcic.F3.PSet.NormNatPlan.canonical_plan",
  "Rcic.F3.PSet.NormNatPlan.node_plan",
  "Rcic.F3.PSet.NormNatPlan.context_eq",
  "Rcic.F3.PSet.NormNatPlan.field_shape",
  "Rcic.F3.PSet.NormNatPlan.field_identity",
  "Rcic.F3.PSet.NormNatPlan.node_shapes",
  "Rcic.F3.PSet.NormNatPlan.faithful",
  "rcic.RcicF3NormNatPlan._auxLemma.1",
  "Rcic.F3.PSet.NormNatPlan.fd",
  "Rcic.F3.PSet.NormNatPlan.plan",
  "Rcic.F3.PSet.NormNatPlan.plan.proof_2",
  "Rcic.F3.PSet.NormNatPlan.family_role",
  "Rcic.F3.PSet.NormNatPlan.plan.proof_1",
  "Rcic.F3.PSet.NormNatPlan.constructors_eq",
  "Rcic.F3.PSet.NormNatPlan.descriptor",
  "Rcic.F3.PSet.NormNatPlan.singleton_shapes",
  "Rcic.F3.PSet.NormNatPlan.family_value",
  "Rcic.F3.PSet.NormNatPlan.component_nonrefutable",
  "Rcic.F3.PSet.NormNatPlan.original_context",
  "Rcic.F3.PSet.NormNatPlan.successorSlot",
  "Rcic.F3.PSet.NormNatPlan.table",
  "Rcic.F3.PSet.NormNatPlan.family_body",
  "Rcic.F3.PSet.NormNatPlan.normalized_descriptor",
  "rcic.RcicF3NormNatPlan._auxLemma.2",
  "Rcic.F3.PSet.NormNatInvariant.actual_invariant",
  "Rcic.F3.PSet.NormNatInvariant.Witness",
  "Rcic.F3.PSet.NormNatInvariant.gInv",
  "Rcic.F3.PSet.NormNatInvariant.component_nonrefutable",
  "Rcic.F3.PSet.NormNatInvariant.component_witness",
  "Rcic.F3.PSet.NormNatInvariant.installed_numeral",
  "Rcic.F3.PSet.NormNatInvariant.faithful_to_least",
  "Rcic.F3.PSet.NormPendAWInvariant.invariant_nonrefutable",
  "Rcic.F3.PSet.NormPendAWInvariant.component_witness",
  "Rcic.F3.PSet.NormPendAWInvariant.actual_invariant",
  "Rcic.F3.PSet.NormPendAWInvariant.gInv",
  "Rcic.F3.PSet.NormPendAWInvariant.component_nonrefutable",
  "Rcic.F3.PSet.NormPendAWInvariant.Witness",
  "Rcic.F3.PSet.NormPendAWChecked.Witness",
  "Rcic.F3.PSet.NormPendAWChecked.refusedBound._cstage1",
  "Rcic.F3.PSet.NormPendAWChecked.w_d_side_iff",
  "Rcic.F3.PSet.NormPendAWChecked.d_check_iff",
  "rcic.RcicF3NormPendAWChecked._auxLemma.1",
  "Rcic.F3.PSet.NormPendAWChecked.w_check",
  "Rcic.F3.PSet.NormPendAWChecked.env_sound",
  "Rcic.F3.PSet.NormPendAWChecked.component_witness",
  "Rcic.F3.PSet.NormPendAWChecked.w_checked",
  "Rcic.F3.PSet.NormPendAWChecked.refusedBound",
  "Rcic.F3.PSet.NormPendAWChecked.nat_w_checked",
  "rcic.RcicF3NormPendAWChecked._auxLemma.2",
  "Rcic.F3.PSet.NormPendAWChecked.component_nonrefutable",
  "Rcic.F3.PSet.NormPendAWChecked.nat_d_side_iff",
  "Rcic.F3.PSet.NormPendAWChecked.refusedBound._cstage2",
  "Rcic.F3.PSet.NormPendAWChecked.d_check",
  "Rcic.F3.PSet.NormPendAWChecked.d_check_refuses",
  "Rcic.F3.PSet.NormPendAWChecked.axiom_free",
  "rcic.RcicF3NormPendAWChecked._auxLemma.3",
  "Rcic.F3.PSet.NormPendAWSameTable.component_nonrefutable",
  "Rcic.F3.PSet.NormPendAWSameTable.Witness",
  "Rcic.F3.PSet.NormPendAWSameTable.zero_one",
  "Rcic.F3.PSet.NormPendAWSameTable.installed_numeral",
  "Rcic.F3.PSet.NormPendAWSameTable.component_witness",
  "Rcic.F3.PSet.NormPendAWSameTable.nat_family_role",
  "Rcic.F3.PSet.NormPendAWSameTable.nat_family_value",
  "Rcic.F3.PSet.AWFixtureContract.Components",
  "Rcic.F3.PSet.AWFixtureContract.components",
  "Rcic.F3.PSet.AWFixtureContract.Target",
  "Rcic.F3.PSet.AWFixtureContract.target_iff_stepAG",
  "Rcic.F3.PSet.AWFixtureContract.target_of_stepAG",
  "Rcic.F3.PSet.AWFixtureContract.components_nonrefutable"
]

def sealedTheorems : List Name :=
  (sealedTheoremsRaw.split (· == ' ') |>.map String.toName)

def allowedAxioms : List Name := [``propext, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let mut actual : Array Name := #[]
  for m in sealedModules do
    let some idx := env.getModuleIdx? m
      | throwError "[a_w_fixture_seal] module {m} is not imported"
    actual := actual ++ env.header.moduleData[idx.toNat]!.constNames
  unless actual.size == sealedTheorems.length do
    throwError "[a_w_fixture_seal] inventory size {sealedTheorems.length} differs from {actual.size}"
  for t in actual do
    unless sealedTheorems.contains t do
      throwError "[a_w_fixture_seal] uncovered declaration {t}"
  for t in sealedTheorems do
    unless actual.contains t && env.contains t do
      throwError "[a_w_fixture_seal] stale or foreign declaration {t}"
  let (_, s) := ((do
    for t in sealedTheorems do CollectAxioms.collect t).run env).run {}
  let bad := s.axioms.filter (fun ax => !allowedAxioms.contains ax)
  unless bad.isEmpty do
    for t in sealedTheorems do
      let (_, st) := ((CollectAxioms.collect t).run env).run {}
      for ax in st.axioms do
        unless allowedAxioms.contains ax do
          throwError "[a_w_fixture_seal] {t} depends on {ax}"
  logInfo m!"[a_w_fixture_seal] {sealedTheorems.length} declarations in {sealedModules.length} modules; exact coverage; axioms ⊆ {allowedAxioms}; closure_claim = 0"


end Rcic.F3.AWFixtureSeal

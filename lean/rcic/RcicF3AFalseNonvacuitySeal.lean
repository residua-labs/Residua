import Lean
import rcic.RcicF3ACheckedMigrationSeal
import rcic.RcicF3NormFalseNonvacuity
import rcic.RcicF3AFalseNonvacuityContract

/-!
Exact declarations for the actual distinguished-False-prefix nontrivial model.
All prior component seals are retained. This environment certificate supplies
both checks and every original environment antecedent at arbitrary K; it
leaves the universal normalized A producer explicit. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.AFalseNonvacuitySeal
open Lean Elab Command

def sealedModules : List Name := [
  `rcic.RcicF3NormFalseNonvacuity,
  `rcic.RcicF3AFalseNonvacuityContract
]

def sealedTheoremsRaw : String := " ".intercalate [
  "Rcic.F3.PSet.NormFalseNonvacuity.propMember._closed_1._cstage2",
  "Rcic.F3.PSet.NormFalseNonvacuity.axiom_free",
  "Rcic.F3.PSet.NormFalseNonvacuity.invariant",
  "Rcic.F3.PSet.NormFalseNonvacuity.true_inhabited",
  "Rcic.F3.PSet.NormFalseNonvacuity.boundDG",
  "Rcic.F3.PSet.NormFalseNonvacuity.distinct",
  "Rcic.F3.PSet.NormFalseNonvacuity.base_invariant",
  "Rcic.F3.PSet.NormFalseNonvacuity.plan.proof_2",
  "Rcic.F3.PSet.NormFalseNonvacuity.prop_present",
  "Rcic.F3.PSet.NormFalseNonvacuity.propTyped._cstage1",
  "Rcic.F3.PSet.NormFalseNonvacuity.d_check",
  "Rcic.F3.PSet.NormFalseNonvacuity.count",
  "Rcic.F3.PSet.NormFalseNonvacuity.plan.proof_1",
  "Rcic.F3.PSet.NormFalseNonvacuity.propTyped",
  "Rcic.F3.PSet.NormFalseNonvacuity.noFun",
  "Rcic.F3.PSet.NormFalseNonvacuity.true_mem",
  "Rcic.F3.PSet.NormFalseNonvacuity.trueValue._closed_2._cstage2",
  "Rcic.F3.PSet.NormFalseNonvacuity.prop_value",
  "Rcic.F3.PSet.NormFalseNonvacuity.propMember._closed_5._cstage2",
  "Rcic.F3.PSet.NormFalseNonvacuity.boundG",
  "Rcic.F3.PSet.NormFalseNonvacuity.wf",
  "Rcic.F3.PSet.NormFalseNonvacuity.prop_role",
  "Rcic.F3.PSet.NormFalseNonvacuity.ctorClasses",
  "Rcic.F3.PSet.NormFalseNonvacuity.wf.proof_1",
  "Rcic.F3.PSet.NormFalseNonvacuity.trueValue",
  "Rcic.F3.PSet.NormFalseNonvacuity.trueValue._closed_1._cstage2",
  "Rcic.F3.PSet.NormFalseNonvacuity.family",
  "Rcic.F3.PSet.NormFalseNonvacuity.component_nonrefutable",
  "Rcic.F3.PSet.NormFalseNonvacuity.environment_antecedents",
  "Rcic.F3.PSet.NormFalseNonvacuity.wf.proof_3",
  "Rcic.F3.PSet.NormFalseNonvacuity.d_checked",
  "Rcic.F3.PSet.NormFalseNonvacuity.family_member",
  "Rcic.F3.PSet.NormFalseNonvacuity.falseValue._closed_1._cstage2",
  "Rcic.F3.PSet.NormFalseNonvacuity.trueValue._cstage2",
  "Rcic.F3.PSet.NormFalseNonvacuity.propTyped._closed_1._cstage2",
  "Rcic.F3.PSet.NormFalseNonvacuity.wf.proof_4",
  "Rcic.F3.PSet.NormFalseNonvacuity.d_side",
  "Rcic.F3.PSet.NormFalseNonvacuity.consistent",
  "Rcic.F3.PSet.NormFalseNonvacuity.w_checked",
  "Rcic.F3.PSet.NormFalseNonvacuity.env",
  "Rcic.F3.PSet.NormFalseNonvacuity.propTyped._cstage2",
  "Rcic.F3.PSet.NormFalseNonvacuity.no_constructor",
  "Rcic.F3.PSet.NormFalseNonvacuity.EnvironmentAntecedents",
  "Rcic.F3.PSet.NormFalseNonvacuity.component_witness",
  "Rcic.F3.PSet.NormFalseNonvacuity.propMember._cstage2",
  "Rcic.F3.PSet.NormFalseNonvacuity.false_present",
  "Rcic.F3.PSet.NormFalseNonvacuity.falseValue._cstage1",
  "Rcic.F3.PSet.NormFalseNonvacuity.fields_free",
  "Rcic.F3.PSet.NormFalseNonvacuity.propMember._closed_3._cstage2",
  "Rcic.F3.PSet.NormFalseNonvacuity.faithful",
  "Rcic.F3.PSet.NormFalseNonvacuity.table",
  "Rcic.F3.PSet.NormFalseNonvacuity.propMember._closed_4._cstage2",
  "Rcic.F3.PSet.NormFalseNonvacuity.prop_bound",
  "Rcic.F3.PSet.NormFalseNonvacuity.env_sound",
  "Rcic.F3.PSet.NormFalseNonvacuity.w_check",
  "Rcic.F3.PSet.NormFalseNonvacuity.wf.proof_5",
  "Rcic.F3.PSet.NormFalseNonvacuity.false_mem",
  "Rcic.F3.PSet.NormFalseNonvacuity.propMember",
  "Rcic.F3.PSet.NormFalseNonvacuity.trueValue._cstage1",
  "Rcic.F3.PSet.NormFalseNonvacuity.Node",
  "Rcic.F3.PSet.NormFalseNonvacuity.Witness",
  "Rcic.F3.PSet.NormFalseNonvacuity.plan",
  "Rcic.F3.PSet.NormFalseNonvacuity.falseValue",
  "Rcic.F3.PSet.NormFalseNonvacuity.propMember._cstage1",
  "Rcic.F3.PSet.NormFalseNonvacuity.falseValue._cstage2",
  "Rcic.F3.PSet.NormFalseNonvacuity.false_empty",
  "Rcic.F3.PSet.NormFalseNonvacuity.policy",
  "Rcic.F3.PSet.NormFalseNonvacuity.base_step",
  "Rcic.F3.PSet.NormFalseNonvacuity.propMember._closed_2._cstage2",
  "Rcic.F3.PSet.NormFalseNonvacuity.wf.proof_2",
  "Rcic.F3.PSet.NormFalseNonvacuity.falseRec_present",
  "Rcic.F3.PSet.AFalseNonvacuityContract.Target",
  "Rcic.F3.PSet.AFalseNonvacuityContract.target_iff_stepAG",
  "Rcic.F3.PSet.AFalseNonvacuityContract.components_nonrefutable",
  "Rcic.F3.PSet.AFalseNonvacuityContract.components",
  "Rcic.F3.PSet.AFalseNonvacuityContract.target_nonrefutable_iff",
  "Rcic.F3.PSet.AFalseNonvacuityContract.Components",
  "Rcic.F3.PSet.AFalseNonvacuityContract.target_of_stepAG"
]

def sealedTheorems : List Name :=
  (sealedTheoremsRaw.split (· == ' ') |>.map String.toName)

def allowedAxioms : List Name := [``propext, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let mut actual : Array Name := #[]
  for m in sealedModules do
    let some idx := env.getModuleIdx? m
      | throwError "[a_false_nonvacuity_seal] module {m} is not imported"
    actual := actual ++ env.header.moduleData[idx.toNat]!.constNames
  unless actual.size == sealedTheorems.length do
    throwError "[a_false_nonvacuity_seal] inventory size {sealedTheorems.length} differs from {actual.size}"
  for t in actual do
    unless sealedTheorems.contains t do
      throwError "[a_false_nonvacuity_seal] uncovered declaration {t}"
  for t in sealedTheorems do
    unless actual.contains t && env.contains t do
      throwError "[a_false_nonvacuity_seal] stale or foreign declaration {t}"
  let (_, s) := ((do
    for t in sealedTheorems do CollectAxioms.collect t).run env).run {}
  let bad := s.axioms.filter (fun ax => !allowedAxioms.contains ax)
  unless bad.isEmpty do
    for t in sealedTheorems do
      let (_, st) := ((CollectAxioms.collect t).run env).run {}
      for ax in st.axioms do
        unless allowedAxioms.contains ax do
          throwError "[a_false_nonvacuity_seal] {t} depends on {ax}"
  logInfo m!"[a_false_nonvacuity_seal] {sealedTheorems.length} declarations in {sealedModules.length} modules; exact coverage; axioms ⊆ {allowedAxioms}; closure_claim = 0"


end Rcic.F3.AFalseNonvacuitySeal

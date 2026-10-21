import Lean
import rcic.RcicSynBelowPortsTableObstruction
import rcic.RcicSynCensusCorePortRefutations
import rcic.RcicSynStepSkeleton

/-!
# A demanded delta query whose frame and local environments differ

The flat delta adapter's `E₀ = E` input is not a uniform consequence of
`Demand`.  An original `ewk_es` edge retains its outer scope while returning
to the prefix environment of its conversion child.  This module exhibits
that situation in an actual admitted environment.  It does not refute the
delta `CaseStep` conclusion.
-/

namespace Rcic.Syn.ESPortsFrameControl

open Rcic.Declarative Q269DeltaObservationIndependent

def added : CheckedMember := ⟨.axiomM, 0, .sort u0, none⟩

def E2 : ResolvedEnv := extendEnv E 1 added

def hW2 : EnvWfT E2 :=
  .axiom E 1 (.sort u0) u1 ewf rfl (HasTyT.sort [] u0) (fun _ => rfl) rfl

def extension : EnvExt E E2 := envExt_extendEnv (r := 1) added rfl

def scope2 : ScopedCtx E2 E2 0 [] := ⟨hW2, envExt_refl _, .nil⟩

def outer : CvP E2 0 [] (.const 0 []) (.sort u0) (.sort u1) :=
  .ewk E E2 0 [] (.const 0 []) (.sort u0) (.sort u1) extension conversion

theorem outer_demand_closed : Demand (.es outer scope2 id []) :=
  .rootEs outer conversion_ap scope2 id levelHom_id

/-- The retained scope still refers to E2; the original delta child refers
    to its strict environment prefix E. -/
theorem inner_delta_demand_closed : Demand (.es conversion scope2 id []) :=
  .issued (.es outer scope2 id []) (.es conversion scope2 id [])
    outer_demand_closed Issues.ewk_es

/-- Member 1 is present only in the larger, actually admitted environment. -/
theorem frame_env_ne_local_env_closed : E2 ≠ E := by
  intro heq
  have hm : (some added : Option CheckedMember) = none :=
    congrArg (fun X : ResolvedEnv => X.members 1) heq
  exact Option.noConfusion hm

/-- The flat adapter's environment-equality port is false on this active
    demanded delta input.  The conjunction records the exact domain and
    the failed input without asserting a negative `CaseStep`. -/
theorem delta_frame_env_control_closed :
    Demand (.es conversion scope2 id []) ∧ E2 ≠ E :=
  ⟨inner_delta_demand_closed, frame_env_ne_local_env_closed⟩

/-- The arbitrary-weight agreement port also fails in this admitted
environment: member 1 is an actual resolved member, while zero weights
cannot carry its canonical admission. -/
theorem zero_agreement_admitted_control_closed :
    ¬ AgreeOn E2 (fun _ => 0) (enrichEnvWfT hW2).admW :=
  CensusCorePortRefutations.agreeOn_zero_admW_refuted hW2
    (r := 1) (m := added) rfl

end Rcic.Syn.ESPortsFrameControl

#print axioms Rcic.Syn.ESPortsFrameControl.outer_demand_closed
#print axioms Rcic.Syn.ESPortsFrameControl.inner_delta_demand_closed
#print axioms Rcic.Syn.ESPortsFrameControl.frame_env_ne_local_env_closed
#print axioms Rcic.Syn.ESPortsFrameControl.delta_frame_env_control_closed
#print axioms Rcic.Syn.ESPortsFrameControl.zero_agreement_admitted_control_closed

/- The report-only round keeps only false-port counterexamples.
This command checks their public proof/definition dependency closures without
adding a declaration or importing either foundation umbrella. -/
open Lean Elab Command in
run_cmd do
  let names : List Name :=
    [``Rcic.Syn.not_convMod_distinct_const_heads_closed,
     ``Rcic.Syn.natSucc_rhs_beta_closed,
     ``Rcic.Syn.natSucc_not_es_tableOf_closed,
     ``Rcic.Syn.natSucc_simulation_tableOf_refuted,
     ``Rcic.Syn.natSucc_iota_positive_control,
     ``Rcic.Syn.natSucc_assumpPref_closed,
     ``Rcic.Syn.natSucc_belowScope,
     ``Rcic.Syn.natSucc_demand_closed,
     ``Rcic.Syn.natSucc_not_allBelowScoped_closed,
     ``Rcic.Syn.natSucc_not_stepSuppliers_closed,
     ``Rcic.Syn.envWfT_allBelowScoped_tableOf_producer_refuted,
     ``Rcic.Syn.ESPortsFrameControl.added,
     ``Rcic.Syn.ESPortsFrameControl.E2,
     ``Rcic.Syn.ESPortsFrameControl.hW2,
     ``Rcic.Syn.ESPortsFrameControl.extension,
     ``Rcic.Syn.ESPortsFrameControl.scope2,
     ``Rcic.Syn.ESPortsFrameControl.outer,
     ``Rcic.Syn.ESPortsFrameControl.outer_demand_closed,
     ``Rcic.Syn.ESPortsFrameControl.inner_delta_demand_closed,
     ``Rcic.Syn.ESPortsFrameControl.frame_env_ne_local_env_closed,
     ``Rcic.Syn.ESPortsFrameControl.delta_frame_env_control_closed,
     ``Rcic.Syn.ESPortsFrameControl.zero_agreement_admitted_control_closed,
     ``Rcic.Syn.CensusCorePortRefutations.typeAdm_zero_empty,
     ``Rcic.Syn.CensusCorePortRefutations.eutConstPorts_zero_empty,
     ``Rcic.Syn.CensusCorePortRefutations.agreeOn_zero_admW_refuted,
     ``Rcic.Syn.CensusCorePortRefutations.eutLamPorts_sort_zero_one_refuted,
     ``Rcic.Syn.CensusCorePortRefutations.eutLamPorts_tableOf_empty_refuted]
  let env ← getEnv
  for name in names do
    let some info := env.find? name
      | throwError "[below_census] missing counterexample declaration {name}"
    if info.isUnsafe || info.isPartial then
      throwError "[below_census] unsafe or partial declaration {name}"
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Quot.sound].contains axiomName do
        throwError "[below_census] forbidden axiom {axiomName} in {name}"
    logInfo m!"BELOW_CENSUS_PUBLIC {name} AXIOMS {axioms}"
  logInfo m!"BELOW_CENSUS_AXIOMS_PASS {names.length} declarations"

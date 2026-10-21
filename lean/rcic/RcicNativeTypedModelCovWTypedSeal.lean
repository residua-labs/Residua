import Lean
import rcic.RcicNativeTypedModelCovWSeal
import rcic.RcicNativeTypedModelCovWTypedActions
import rcic.RcicNativeTypedModelCovWTypedAntiReduction
import rcic.RcicNativeTypedModelCovWTypedBetaBoundary
import rcic.RcicNativeTypedModelCovWTypedRawAdequacy

/-!
# Bounded seal: typed actions and inhabited observation-transport boundaries

Literal beta and let fail observation anti-reduction at a typed Nat demand,
already in a closed, recursor-free instance with an actual realizer and a
matching normal constructor reduct. The independent eta-index and raw True
controls separately delimit native K transport. Typed action introductions
and bounded raw supply retain their explicitly documented scope; no general
exact typed-action, guarded adequacy, or interpretation supplier is claimed.

All authored public roots are checked below. The old bounded seals and the
exact external #7776 replay are checked separately. Neither full Foundation
root is imported. closure_claim = 0.
-/

private def covWTypedRoots : Array Lean.Name := #[
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_actionCore,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.CovWTypedAction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_action_typing,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_action_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_action_app,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_action_core_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_action_head,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_rawCore,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_rawAction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_core_of_value,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_action_of_value,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_action_app,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_antiReductionAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_failureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_failureAt.refutes,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_guarded_bot_valuation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_bot_valuation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_prop_demand,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_eta_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_eta_failure,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_eta_same_stage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_no_guarded_step_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_no_guarded_red_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_prop_const_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_app_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_foldApps_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_prop_spine_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_true_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_true_failure,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_true_guarded_control,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_no_raw_step_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_no_raw_red_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatArrow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatBody,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatSource,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatLet,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatTarget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatCpt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatArrow_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatBody_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatLetBody_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatSource_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatLet_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatTarget_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_source_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_target_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_type_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_compact_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_source_not_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_not_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_type_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_normal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_readback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_readback,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_matching_constructor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_kFree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_rec_occurrence,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_nat_not_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_nonbottom,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_target_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_type_raw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_source_raw_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_raw_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_source_guarded_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_guarded_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.CovWTypedNatFailureAt,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.CovWTypedNatFailureAt.refutes,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_raw_failure,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_guarded_failure,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_raw_failure,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_guarded_failure,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.CovWTypedBetaHead,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.CovWTypedLetHead,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_raw_beta_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_guarded_beta_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_raw_let_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_guarded_let_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_raw_step_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_guarded_step_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_raw_conversion_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_guarded_conversion_antiReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_same_stage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_closed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_instantiated,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_subst,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_closed_row,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_exact_raw_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_exact_raw_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_exact_raw_sort,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_exact_raw_pi
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Quot.sound]
  for root in covWTypedRoots do
    if !env.contains root then
      throwError "CovWTyped seal: missing declaration {root}"
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "CovWTyped seal: {root} has forbidden axioms {forbidden}"
  logInfo m!"CovWTyped seal: {covWTypedRoots.size} public roots checked; allowed axioms = {allowed}"

#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_actionCore
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.CovWTypedAction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_action_typing
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_action_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_action_app
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_action_core_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_action_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_rawCore
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_rawAction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_core_of_value
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_action_of_value
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_action_app
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_antiReductionAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_failureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_failureAt.refutes
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_guarded_bot_valuation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_bot_valuation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_prop_demand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_eta_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_eta_failure
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_eta_same_stage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_no_guarded_step_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_no_guarded_red_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_prop_const_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_app_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_foldApps_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_prop_spine_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_true_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_true_failure
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_true_guarded_control
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_no_raw_step_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_no_raw_red_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatArrow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatBody
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatSource
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatLet
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatTarget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatCpt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatArrow_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatBody_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatLetBody_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatSource_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatLet_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNatTarget_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_source_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_target_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_type_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_compact_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_source_not_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_not_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_type_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_normal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_readback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_readback
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_matching_constructor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_kFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_rec_occurrence
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_nat_not_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_nonbottom
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_target_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_type_raw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_source_raw_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_raw_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_source_guarded_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_guarded_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.CovWTypedNatFailureAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.CovWTypedNatFailureAt.refutes
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_raw_failure
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_guarded_failure
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_raw_failure
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_let_guarded_failure
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.CovWTypedBetaHead
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.CovWTypedLetHead
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_raw_beta_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_guarded_beta_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_raw_let_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_guarded_let_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_raw_step_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_guarded_step_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_raw_conversion_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_no_guarded_conversion_antiReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTypedBetaNat_same_stage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_closed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_instantiated
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_subst
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_raw_closed_row
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_exact_raw_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_exact_raw_prop
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_exact_raw_sort
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit.covWTyped_exact_raw_pi

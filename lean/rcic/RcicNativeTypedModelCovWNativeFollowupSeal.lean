import Lean
import rcic.RcicNativeTypedModelCovWNativeSeal
import rcic.RcicNativeTypedModelCovWNativeExpansionBoundary
import rcic.RcicNativeTypedModelCovWNativeEtaFunctionBoundary

/-!
# Bounded seal: positive-observation expansion and function-context boundaries

The new declarations compose the native-aligned constructor observation with
the existing Ho invariant. Native beta/zeta and eta/application conversions,
both typings, actual occurrence evidence, observed types, strict nonbottom
demands and closed realization are supplied by the checked fixtures.
Every prior statement is unchanged. No full Foundation import.
closure_claim = 0.
-/

private def covWNativeFollowupRoots : Array Lean.Name := #[
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_nonconstant_major_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_prefix_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoBetaBody,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoBetaFn,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoBetaSource,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoLetSource,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_substitution,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_body_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_fn_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_source_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_source_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_observation_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_observation_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_pair,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_pair,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_prop_absent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_prop_absent,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_not_typed_equal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_not_typed_equal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.CovWNativeClosedSubjectExpansion,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNative_subject_expansion_false,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_failure_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_failure_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_expansion_binder_test,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_fn_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoArrow,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_prefix_arrow_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_eta_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_eta_context_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_functions_all_tagged,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_functions_all_public,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_functions_typed_equal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoFunctionContext,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_function_context_not_equal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_arrow_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_arrow_demand,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_eta_function_failure_inhabited
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  for root in covWNativeFollowupRoots do
    if !env.contains root then
      throwError "CovWNative followup seal: missing declaration {root}"
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "CovWNative followup seal: {root} has forbidden axioms {forbidden}"
  logInfo m!"CovWNative followup seal: {covWNativeFollowupRoots.size} public roots checked; allowed axioms = {allowed}"

#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_nonconstant_major_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_prefix_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoBetaBody
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoBetaFn
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoBetaSource
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoLetSource
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_substitution
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_body_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_fn_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_source_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_source_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_observation_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_observation_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_pair
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_pair
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_prop_absent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_prop_absent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_not_typed_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_not_typed_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.CovWNativeClosedSubjectExpansion
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNative_subject_expansion_false
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_failure_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_failure_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_expansion_binder_test
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_fn_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoArrow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_prefix_arrow_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_eta_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_eta_context_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_functions_all_tagged
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_functions_all_public
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_functions_typed_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoFunctionContext
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_function_context_not_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_arrow_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_arrow_demand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_eta_function_failure_inhabited

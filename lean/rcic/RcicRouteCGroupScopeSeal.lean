import Lean
import rcic.RcicRouteCGroupScope

/-! Bounded route-C C2 seal: the admission-driven group-scope assembly.
Syntactic factorization, family/constructor/recursor views and
`groupInScopeT_of`. No checker-elimination or global row-supply claim.
closure_claim = 0. -/

#print axioms Rcic.Declarative.unplainIdx
#print axioms Rcic.Declarative.plainVar_unplainIdx
#print axioms Rcic.Declarative.unshiftSubst
#print axioms Rcic.Declarative.lift_zero_one_bvar
#print axioms Rcic.Declarative.unshiftSubst_apply_lt
#print axioms Rcic.Declarative.unshiftSubst_apply_ge
#print axioms Rcic.Declarative.unshiftSubst_up
#print axioms Rcic.Declarative.substT_unshift
#print axioms Rcic.Declarative.maskSubst
#print axioms Rcic.Declarative.unshiftSubst_zero
#print axioms Rcic.Declarative.maskSubst_cons_false
#print axioms Rcic.Declarative.maskSubst_cons_true
#print axioms Rcic.Declarative.substT_mask_unshift
#print axioms Rcic.Declarative.maskSubst_nil
#print axioms Rcic.Declarative.ctorEndSubstT_maskSubst
#print axioms Rcic.Declarative.ctorEndSubstT_id
#print axioms Rcic.Declarative.mapM_unshift_substT
#print axioms Rcic.Declarative.policyParameterLocals_lift_succ
#print axioms Rcic.Declarative.policyLocals_eq
#print axioms Rcic.Declarative.recIdx?_spec
#print axioms Rcic.Declarative.drec_head_of_recIdx
#print axioms Rcic.Declarative.fieldsOfA
#print axioms Rcic.Declarative.fieldsOfA_doms
#print axioms Rcic.Declarative.fieldsOfA_labels
#print axioms Rcic.Declarative.ctorFieldLv
#print axioms Rcic.Declarative.ctorFieldLv_eq_fieldLevel
#print axioms Rcic.Declarative.ctorPlainFactorT_of
#print axioms Rcic.Declarative.ctorPlainLabelsRemaining_of
#print axioms Rcic.Declarative.fieldsOfA_noDrecD
#print axioms Rcic.Declarative.familyParamLevels
#print axioms Rcic.Declarative.familyIndexLevels
#print axioms Rcic.Declarative.famViewT_of
#print axioms Rcic.Declarative.famViewT_levelBounded
#print axioms Rcic.Declarative.CtorScopeInputT
#print axioms Rcic.Declarative.ctorViewT_of
#print axioms Rcic.Declarative.groupCtorT_of
#print axioms Rcic.Declarative.RecScopeInputT
#print axioms Rcic.Declarative.groupRecT_of
#print axioms Rcic.Declarative.ctorList_of
#print axioms Rcic.Declarative.ctorList_of_entries
#print axioms Rcic.Declarative.ctorList_of_refs
#print axioms Rcic.Declarative.ctorList_of_noDrecD
#print axioms Rcic.Declarative.groupInScopeT_of

private def routeCGroupScopePublicRoots : Array Lean.Name := #[
  ``Rcic.Declarative.unplainIdx,
  ``Rcic.Declarative.plainVar_unplainIdx,
  ``Rcic.Declarative.unshiftSubst,
  ``Rcic.Declarative.lift_zero_one_bvar,
  ``Rcic.Declarative.unshiftSubst_apply_lt,
  ``Rcic.Declarative.unshiftSubst_apply_ge,
  ``Rcic.Declarative.unshiftSubst_up,
  ``Rcic.Declarative.substT_unshift,
  ``Rcic.Declarative.maskSubst,
  ``Rcic.Declarative.unshiftSubst_zero,
  ``Rcic.Declarative.maskSubst_cons_false,
  ``Rcic.Declarative.maskSubst_cons_true,
  ``Rcic.Declarative.substT_mask_unshift,
  ``Rcic.Declarative.maskSubst_nil,
  ``Rcic.Declarative.ctorEndSubstT_maskSubst,
  ``Rcic.Declarative.ctorEndSubstT_id,
  ``Rcic.Declarative.mapM_unshift_substT,
  ``Rcic.Declarative.policyParameterLocals_lift_succ,
  ``Rcic.Declarative.policyLocals_eq,
  ``Rcic.Declarative.recIdx?_spec,
  ``Rcic.Declarative.drec_head_of_recIdx,
  ``Rcic.Declarative.fieldsOfA,
  ``Rcic.Declarative.fieldsOfA_doms,
  ``Rcic.Declarative.fieldsOfA_labels,
  ``Rcic.Declarative.ctorFieldLv,
  ``Rcic.Declarative.ctorFieldLv_eq_fieldLevel,
  ``Rcic.Declarative.ctorPlainFactorT_of,
  ``Rcic.Declarative.ctorPlainLabelsRemaining_of,
  ``Rcic.Declarative.fieldsOfA_noDrecD,
  ``Rcic.Declarative.familyParamLevels,
  ``Rcic.Declarative.familyIndexLevels,
  ``Rcic.Declarative.famViewT_of,
  ``Rcic.Declarative.famViewT_levelBounded,
  ``Rcic.Declarative.CtorScopeInputT,
  ``Rcic.Declarative.ctorViewT_of,
  ``Rcic.Declarative.groupCtorT_of,
  ``Rcic.Declarative.RecScopeInputT,
  ``Rcic.Declarative.groupRecT_of,
  ``Rcic.Declarative.ctorList_of,
  ``Rcic.Declarative.ctorList_of_entries,
  ``Rcic.Declarative.ctorList_of_refs,
  ``Rcic.Declarative.ctorList_of_noDrecD,
  ``Rcic.Declarative.groupInScopeT_of
]

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Quot.sound]
  for root in routeCGroupScopePublicRoots do
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "RouteCGroupScope: {root} has forbidden axioms {forbidden}"
  logInfo m!"RouteCGroupScope: {routeCGroupScopePublicRoots.size} public roots checked"

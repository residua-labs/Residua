import Lean
import rcic.RcicTypedScopeResidue
import rcic.RcicTypedScopeAdmission

/-! Bounded route-C scope audit. C1 operational residue; C2 measured admission evidence.
No checker-elimination or global row-supply claim. closure_claim = 0. -/

#print axioms Rcic.Declarative.ScopeGroupT
#print axioms Rcic.Declarative.EnvWfT.GroupAt
#print axioms Rcic.Declarative.ScopeGroupT.parameterSplits
#print axioms Rcic.Declarative.ScopeFieldsFunRecAt
#print axioms Rcic.Declarative.IndGroupAdmitted.ScopeFunRecField
#print axioms Rcic.Declarative.GroupMembersT.ScopeFunRecField
#print axioms Rcic.Declarative.ScopeCheckClause
#print axioms Rcic.Declarative.ScopeCheckClause.test
#print axioms Rcic.Declarative.scopeProfileShapeB
#print axioms Rcic.Declarative.ScopeCheckerNoAnswerAt
#print axioms Rcic.Declarative.ScopeDrecDAt
#print axioms Rcic.Declarative.ScopeProfileOutsideAt
#print axioms Rcic.Declarative.ScopeDrecDAt.not_noDrecD
#print axioms Rcic.Declarative.ScopeProfileOutsideAt.profileCheck_eq_false
#print axioms Rcic.Declarative.ScopeCandidatePassT
#print axioms Rcic.Declarative.ScopeAttemptFailure
#print axioms Rcic.Declarative.scopeCandidatePass_or_failure
#print axioms Rcic.Declarative.ScopeSearchFailure
#print axioms Rcic.Declarative.OutsideScope
#print axioms Rcic.Declarative.ScopeGroupT.outside_of_searchFailure
#print axioms Rcic.Declarative.ScopeGroupT.scopeCheck_or_outside
#print axioms Rcic.Declarative.ScopeAuditConfig
#print axioms Rcic.Declarative.ScopeGroupT.auditFuel
#print axioms Rcic.Declarative.ScopeGroupT.defaultAudit
#print axioms Rcic.Declarative.EnvWfT.scopeCheck_or_outsideWith
#print axioms Rcic.Declarative.EnvWfT.inScope_or_outside
#print axioms Rcic.Declarative.ScopeMemberAdmissionT
#print axioms Rcic.Declarative.groupMembersT_headAdmission
#print axioms Rcic.Declarative.groupMembersT_admission_at
#print axioms Rcic.Declarative.groupMembersT_constructor_scope_typing
#print axioms Rcic.Declarative.groupMembersT_constructor_constsIn
#print axioms Rcic.Declarative.envWfT_group_constructor_scope_typing
#print axioms Rcic.Declarative.familyTypedT_recorded_domain
#print axioms Rcic.Declarative.ctorTypedT_recorded_field
#print axioms Rcic.Declarative.constsIn_drop_extension
#print axioms Rcic.Declarative.constsIn_policyPi_domain
#print axioms Rcic.Declarative.constructor_scope_raw_field_constsIn
#print axioms Rcic.Declarative.constructor_scope_family_free_field_constsIn
#print axioms Rcic.Declarative.constsIn_does_not_supply_plain_factorization
#print axioms Rcic.Declarative.FamilyHeaderRetypingRemaining
#print axioms Rcic.Declarative.ConstructorRecordedRetypingRemaining
#print axioms Rcic.Declarative.CtorPlainFactorT
#print axioms Rcic.Declarative.CtorPlainFactorT.storedType
#print axioms Rcic.Declarative.ConstructorMirrorRetypingRemaining
#print axioms Rcic.Declarative.ConstructorPlainRetypingRemaining
#print axioms Rcic.Declarative.ConstructorPlainLabelsRemaining

private def scopeResiduePublicRoots : Array Lean.Name := #[
  ``Rcic.Declarative.ScopeGroupT,
  ``Rcic.Declarative.EnvWfT.GroupAt,
  ``Rcic.Declarative.ScopeGroupT.parameterSplits,
  ``Rcic.Declarative.ScopeFieldsFunRecAt,
  ``Rcic.Declarative.IndGroupAdmitted.ScopeFunRecField,
  ``Rcic.Declarative.GroupMembersT.ScopeFunRecField,
  ``Rcic.Declarative.ScopeCheckClause,
  ``Rcic.Declarative.ScopeCheckClause.test,
  ``Rcic.Declarative.scopeProfileShapeB,
  ``Rcic.Declarative.ScopeCheckerNoAnswerAt,
  ``Rcic.Declarative.ScopeDrecDAt,
  ``Rcic.Declarative.ScopeProfileOutsideAt,
  ``Rcic.Declarative.ScopeDrecDAt.not_noDrecD,
  ``Rcic.Declarative.ScopeProfileOutsideAt.profileCheck_eq_false,
  ``Rcic.Declarative.ScopeCandidatePassT,
  ``Rcic.Declarative.ScopeAttemptFailure,
  ``Rcic.Declarative.scopeCandidatePass_or_failure,
  ``Rcic.Declarative.ScopeSearchFailure,
  ``Rcic.Declarative.OutsideScope,
  ``Rcic.Declarative.ScopeGroupT.outside_of_searchFailure,
  ``Rcic.Declarative.ScopeGroupT.scopeCheck_or_outside,
  ``Rcic.Declarative.ScopeAuditConfig,
  ``Rcic.Declarative.ScopeGroupT.auditFuel,
  ``Rcic.Declarative.ScopeGroupT.defaultAudit,
  ``Rcic.Declarative.EnvWfT.scopeCheck_or_outsideWith,
  ``Rcic.Declarative.EnvWfT.inScope_or_outside,
  ``Rcic.Declarative.ScopeMemberAdmissionT,
  ``Rcic.Declarative.groupMembersT_headAdmission,
  ``Rcic.Declarative.groupMembersT_admission_at,
  ``Rcic.Declarative.groupMembersT_constructor_scope_typing,
  ``Rcic.Declarative.groupMembersT_constructor_constsIn,
  ``Rcic.Declarative.envWfT_group_constructor_scope_typing,
  ``Rcic.Declarative.familyTypedT_recorded_domain,
  ``Rcic.Declarative.ctorTypedT_recorded_field,
  ``Rcic.Declarative.constsIn_drop_extension,
  ``Rcic.Declarative.constsIn_policyPi_domain,
  ``Rcic.Declarative.constructor_scope_raw_field_constsIn,
  ``Rcic.Declarative.constructor_scope_family_free_field_constsIn,
  ``Rcic.Declarative.constsIn_does_not_supply_plain_factorization,
  ``Rcic.Declarative.FamilyHeaderRetypingRemaining,
  ``Rcic.Declarative.ConstructorRecordedRetypingRemaining,
  ``Rcic.Declarative.CtorPlainFactorT,
  ``Rcic.Declarative.CtorPlainFactorT.storedType,
  ``Rcic.Declarative.ConstructorMirrorRetypingRemaining,
  ``Rcic.Declarative.ConstructorPlainRetypingRemaining,
  ``Rcic.Declarative.ConstructorPlainLabelsRemaining
]

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Quot.sound]
  for root in scopeResiduePublicRoots do
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "ScopeResidue: {root} has forbidden axioms {forbidden}"
  logInfo m!"ScopeResidue: {scopeResiduePublicRoots.size} public roots checked"

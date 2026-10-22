import Lean
import rcic.RcicRouteCGroupWalk

/-! Bounded route-C C2 seal: the `GroupMembersT` walk extraction —
member receipts, admission-case dispatch, ctor/recursor bundles, and
`groupInScopeT_of_envWfT_group` / `envWfT_inScope_of_groups` under the
named remaining obligations. No checker-elimination claim.
closure_claim = 0. -/

#print axioms Rcic.Declarative.groupMembersT_memberAt
#print axioms Rcic.Declarative.isArity_policyPi
#print axioms Rcic.Declarative.isArity_foldApps_cons
#print axioms Rcic.Declarative.isArity_foldApps_snoc
#print axioms Rcic.Declarative.isArity_policyRecursorType
#print axioms Rcic.Declarative.familyNotRecursorCase
#print axioms Rcic.Declarative.familyAdmittedView
#print axioms Rcic.Declarative.recursorAdmittedView
#print axioms Rcic.Declarative.RecursorAdmissionClass
#print axioms Rcic.Declarative.ctorAdmittedView
#print axioms Rcic.Declarative.CtorAdmissionBundle
#print axioms Rcic.Declarative.envWfT_group_ctorBundle
#print axioms Rcic.Declarative.envWfT_group_familyView
#print axioms Rcic.Declarative.RecAdmissionBundle
#print axioms Rcic.Declarative.head_getElem
#print axioms Rcic.Declarative.tailLast_getElem
#print axioms Rcic.Declarative.lastEntry_getElem
#print axioms Rcic.Declarative.envWfT_group_recBundle
#print axioms Rcic.Declarative.recStored_of_bundle
#print axioms Rcic.Declarative.CtorScopeTransports
#print axioms Rcic.Declarative.ctorScopeInput_of_transports
#print axioms Rcic.Declarative.ctorEntry_getElem_of
#print axioms Rcic.Declarative.RecScopeTransports
#print axioms Rcic.Declarative.recScopeInput_of_bundle
#print axioms Rcic.Declarative.envWfT_group_ctorScopeInput
#print axioms Rcic.Declarative.envWfT_group_recScopeInput
#print axioms Rcic.Declarative.ctorScopeInput_of_bundle
#print axioms Rcic.Declarative.GroupScopeEvidence
#print axioms Rcic.Declarative.groupInScopeT_of_envWfT_group
#print axioms Rcic.Declarative.envWfT_inScope_of_groups

private def routeCGroupWalkPublicRoots : Array Lean.Name := #[
  ``Rcic.Declarative.groupMembersT_memberAt,
  ``Rcic.Declarative.isArity_policyPi,
  ``Rcic.Declarative.isArity_foldApps_cons,
  ``Rcic.Declarative.isArity_foldApps_snoc,
  ``Rcic.Declarative.isArity_policyRecursorType,
  ``Rcic.Declarative.familyNotRecursorCase,
  ``Rcic.Declarative.familyAdmittedView,
  ``Rcic.Declarative.recursorAdmittedView,
  ``Rcic.Declarative.RecursorAdmissionClass,
  ``Rcic.Declarative.ctorAdmittedView,
  ``Rcic.Declarative.CtorAdmissionBundle,
  ``Rcic.Declarative.envWfT_group_ctorBundle,
  ``Rcic.Declarative.envWfT_group_familyView,
  ``Rcic.Declarative.RecAdmissionBundle,
  ``Rcic.Declarative.head_getElem,
  ``Rcic.Declarative.tailLast_getElem,
  ``Rcic.Declarative.lastEntry_getElem,
  ``Rcic.Declarative.envWfT_group_recBundle,
  ``Rcic.Declarative.recStored_of_bundle,
  ``Rcic.Declarative.CtorScopeTransports,
  ``Rcic.Declarative.ctorScopeInput_of_transports,
  ``Rcic.Declarative.ctorEntry_getElem_of,
  ``Rcic.Declarative.RecScopeTransports,
  ``Rcic.Declarative.recScopeInput_of_bundle,
  ``Rcic.Declarative.envWfT_group_ctorScopeInput,
  ``Rcic.Declarative.envWfT_group_recScopeInput,
  ``Rcic.Declarative.ctorScopeInput_of_bundle,
  ``Rcic.Declarative.GroupScopeEvidence,
  ``Rcic.Declarative.groupInScopeT_of_envWfT_group,
  ``Rcic.Declarative.envWfT_inScope_of_groups
]

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Quot.sound]
  for root in routeCGroupWalkPublicRoots do
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "RouteCGroupWalk: {root} has forbidden axioms {forbidden}"
  logInfo m!"RouteCGroupWalk: {routeCGroupWalkPublicRoots.size} public roots checked"

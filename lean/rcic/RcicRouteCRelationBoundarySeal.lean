import Lean
import rcic.RcicRouteCEqGuard
import rcic.RcicAnnEqLargeFixture
import rcic.RcicRouteCGuardedCycle
import rcic.RcicRouteCLargeIndexBoundary

/-! Bounded route-C R1/R2 audit. Inhabited Eq and large-index boundaries.
No replacement logical relation or new global row-supply claim. closure_claim = 0. -/

#print axioms Rcic.Declarative.RouteCEqGuard.envWf
#print axioms Rcic.Declarative.RouteCEqGuard.binder_context_wf
#print axioms Rcic.Declarative.RouteCEqGuard.eta_context_wf
#print axioms Rcic.Declarative.RouteCEqGuard.binder_witness
#print axioms Rcic.Declarative.RouteCEqGuard.eta_witness
#print axioms Rcic.Declarative.RouteCEqGuard.binder_families
#print axioms Rcic.Declarative.RouteCEqGuard.eta_families
#print axioms Rcic.Declarative.RouteCEqGuard.binder_major_typed
#print axioms Rcic.Declarative.RouteCEqGuard.eta_major_typed
#print axioms Rcic.Declarative.RouteCEqGuard.binder_native_typed
#print axioms Rcic.Declarative.RouteCEqGuard.eta_native_typed
#print axioms Rcic.Declarative.RouteCEqGuard.binder_native_conversion
#print axioms Rcic.Declarative.RouteCEqGuard.eta_native_conversion
#print axioms Rcic.Declarative.RouteCEqGuard.binder_guards
#print axioms Rcic.Declarative.RouteCEqGuard.eta_guards
#print axioms Rcic.Declarative.RouteCEqGuard.binder_canonical_typed
#print axioms Rcic.Declarative.RouteCEqGuard.eta_canonical_typed
#print axioms Rcic.Declarative.RouteCEqGuard.binder_canonical_irrelevance
#print axioms Rcic.Declarative.RouteCEqGuard.eta_canonical_irrelevance
#print axioms Rcic.Declarative.RouteCEqGuard.binder_syntactic_guard_fails
#print axioms Rcic.Declarative.RouteCEqGuard.eta_syntactic_guard_fails
#print axioms Rcic.Declarative.RouteCEqGuard.binder_inhabited
#print axioms Rcic.Declarative.RouteCEqGuard.eta_inhabited
#print axioms Rcic.Declarative.Ann.EqLargeFixture.one
#print axioms Rcic.Declarative.Ann.EqLargeFixture.two
#print axioms Rcic.Declarative.Ann.EqLargeFixture.params
#print axioms Rcic.Declarative.Ann.EqLargeFixture.indices
#print axioms Rcic.Declarative.Ann.EqLargeFixture.famTy
#print axioms Rcic.Declarative.Ann.EqLargeFixture.famSort
#print axioms Rcic.Declarative.Ann.EqLargeFixture.reflTy
#print axioms Rcic.Declarative.Ann.EqLargeFixture.reflSort
#print axioms Rcic.Declarative.Ann.EqLargeFixture.recTy
#print axioms Rcic.Declarative.Ann.EqLargeFixture.fam
#print axioms Rcic.Declarative.Ann.EqLargeFixture.reflMember
#print axioms Rcic.Declarative.Ann.EqLargeFixture.recMember
#print axioms Rcic.Declarative.Ann.EqLargeFixture.famEnv
#print axioms Rcic.Declarative.Ann.EqLargeFixture.prefixEnv
#print axioms Rcic.Declarative.Ann.EqLargeFixture.env
#print axioms Rcic.Declarative.Ann.EqLargeFixture.erase_env
#print axioms Rcic.Declarative.Ann.EqLargeFixture.famTyTyped
#print axioms Rcic.Declarative.Ann.EqLargeFixture.famView
#print axioms Rcic.Declarative.Ann.EqLargeFixture.famWf
#print axioms Rcic.Declarative.Ann.EqLargeFixture.famConstTyped
#print axioms Rcic.Declarative.Ann.EqLargeFixture.reflTyTyped
#print axioms Rcic.Declarative.Ann.EqLargeFixture.reflView
#print axioms Rcic.Declarative.Ann.EqLargeFixture.reflGroup
#print axioms Rcic.Declarative.Ann.EqLargeFixture.prefixWf
#print axioms Rcic.Declarative.Ann.EqLargeFixture.recTyTypedNoIota
#print axioms Rcic.Declarative.Ann.EqLargeFixture.prefix_noRec
#print axioms Rcic.Declarative.Ann.EqLargeFixture.prefix_in_env
#print axioms Rcic.Declarative.Ann.EqLargeFixture.fam_in_prefix
#print axioms Rcic.Declarative.Ann.EqLargeFixture.prefix_iface
#print axioms Rcic.Declarative.Ann.EqLargeFixture.reflTyTypedConcrete
#print axioms Rcic.Declarative.Ann.EqLargeFixture.wf
#print axioms Rcic.Declarative.Ann.EqLargeFixture.closed
#print axioms Rcic.Declarative.Ann.EqLargeFixture.normClosed
#print axioms Rcic.Declarative.Ann.EqLargeFixture.normCtorType
#print axioms Rcic.Declarative.Ann.EqLargeFixture.liftIface
#print axioms Rcic.Declarative.Ann.EqLargeFixture.substIface
#print axioms Rcic.Declarative.Ann.EqLargeFixture.parameter
#print axioms Rcic.Declarative.Ann.EqLargeFixture.result
#print axioms Rcic.Declarative.Ann.EqLargeFixture.eqAt
#print axioms Rcic.Declarative.Ann.EqLargeFixture.reflAt
#print axioms Rcic.Declarative.Ann.EqLargeFixture.domain
#print axioms Rcic.Declarative.Ann.EqLargeFixture.context
#print axioms Rcic.Declarative.Ann.EqLargeFixture.parameterTyped
#print axioms Rcic.Declarative.Ann.EqLargeFixture.resultTyped
#print axioms Rcic.Declarative.Ann.EqLargeFixture.eqTyped
#print axioms Rcic.Declarative.Ann.EqLargeFixture.contextWf
#print axioms Rcic.Declarative.Ann.EqLargeFixture.majorTyped
#print axioms Rcic.Declarative.Ann.EqLargeFixture.reflConstTyped
#print axioms Rcic.Declarative.Ann.EqLargeFixture.reflTyped
#print axioms Rcic.Declarative.Ann.EqLargeFixture.motiveTail
#print axioms Rcic.Declarative.Ann.EqLargeFixture.motiveBody
#print axioms Rcic.Declarative.Ann.EqLargeFixture.motive
#print axioms Rcic.Declarative.Ann.EqLargeFixture.motiveTy
#print axioms Rcic.Declarative.Ann.EqLargeFixture.motiveAt
#print axioms Rcic.Declarative.Ann.EqLargeFixture.motiveTyped
#print axioms Rcic.Declarative.Ann.EqLargeFixture.motiveAtTyped
#print axioms Rcic.Declarative.Ann.EqLargeFixture.motiveBeta
#print axioms Rcic.Declarative.Ann.EqLargeFixture.motiveTypeConv
#print axioms Rcic.Declarative.Ann.EqLargeFixture.recConstTyped
#print axioms Rcic.Declarative.Ann.EqLargeFixture.pre
#print axioms Rcic.Declarative.Ann.EqLargeFixture.recPrefix
#print axioms Rcic.Declarative.Ann.EqLargeFixture.call
#print axioms Rcic.Declarative.Ann.EqLargeFixture.prefixTyped
#print axioms Rcic.Declarative.Ann.EqLargeFixture.conversion
#print axioms Rcic.Declarative.Ann.EqLargeFixture.callStuck
#print axioms Rcic.Declarative.Ann.EqLargeFixture.envSem_false
#print axioms Rcic.Declarative.Ann.EqLargeFixture.inhabited_boundary
#print axioms Rcic.Syn.RouteCGuardedCycle.UnilateralF
#print axioms Rcic.Syn.RouteCGuardedCycle.Unilateral
#print axioms Rcic.Syn.RouteCGuardedCycle.unilateral_unfold
#print axioms Rcic.Syn.RouteCGuardedCycle.unilateral_of_positive_cycle
#print axioms Rcic.Syn.RouteCGuardedCycle.unilateral_symm
#print axioms Rcic.Syn.RouteCGuardedCycle.unilateral_normal_iff
#print axioms Rcic.Syn.RouteCGuardedCycle.loopIdentity
#print axioms Rcic.Syn.RouteCGuardedCycle.loopInput
#print axioms Rcic.Syn.RouteCGuardedCycle.loop_identity_cycle
#print axioms Rcic.Syn.RouteCGuardedCycle.loop_positive_cycle
#print axioms Rcic.Syn.RouteCGuardedCycle.loop_table_and_cycle
#print axioms Rcic.Syn.RouteCGuardedCycle.loop_relates_every
#print axioms Rcic.Syn.RouteCGuardedCycle.loop_sorts_not_related
#print axioms Rcic.Syn.RouteCGuardedCycle.loop_unilateral_not_transitive
#print axioms Rcic.Syn.RouteCGuardedCycle.loop_unilateral_not_finite_conversion_sound
#print axioms Rcic.Declarative.Ann.RouteCLargeIndex.envWf
#print axioms Rcic.Declarative.Ann.RouteCLargeIndex.noRec
#print axioms Rcic.Declarative.Ann.RouteCLargeIndex.recSem
#print axioms Rcic.Declarative.Ann.RouteCLargeIndex.remaining_premises
#print axioms Rcic.Declarative.Ann.RouteCLargeIndex.closed_application
#print axioms Rcic.Declarative.Ann.RouteCLargeIndex.closed_application_unrelated
#print axioms Rcic.Declarative.Ann.RouteCLargeIndex.inhabited_boundary
#print axioms Rcic.Declarative.Ann.RouteCLargeIndex.GroupsWithoutSmallIndex
#print axioms Rcic.Declarative.Ann.RouteCLargeIndex.not_groupsWithoutSmallIndex

private def routeCRelationPublicRoots : Array Lean.Name := #[
  ``Rcic.Declarative.RouteCEqGuard.envWf,
  ``Rcic.Declarative.RouteCEqGuard.binder_context_wf,
  ``Rcic.Declarative.RouteCEqGuard.eta_context_wf,
  ``Rcic.Declarative.RouteCEqGuard.binder_witness,
  ``Rcic.Declarative.RouteCEqGuard.eta_witness,
  ``Rcic.Declarative.RouteCEqGuard.binder_families,
  ``Rcic.Declarative.RouteCEqGuard.eta_families,
  ``Rcic.Declarative.RouteCEqGuard.binder_major_typed,
  ``Rcic.Declarative.RouteCEqGuard.eta_major_typed,
  ``Rcic.Declarative.RouteCEqGuard.binder_native_typed,
  ``Rcic.Declarative.RouteCEqGuard.eta_native_typed,
  ``Rcic.Declarative.RouteCEqGuard.binder_native_conversion,
  ``Rcic.Declarative.RouteCEqGuard.eta_native_conversion,
  ``Rcic.Declarative.RouteCEqGuard.binder_guards,
  ``Rcic.Declarative.RouteCEqGuard.eta_guards,
  ``Rcic.Declarative.RouteCEqGuard.binder_canonical_typed,
  ``Rcic.Declarative.RouteCEqGuard.eta_canonical_typed,
  ``Rcic.Declarative.RouteCEqGuard.binder_canonical_irrelevance,
  ``Rcic.Declarative.RouteCEqGuard.eta_canonical_irrelevance,
  ``Rcic.Declarative.RouteCEqGuard.binder_syntactic_guard_fails,
  ``Rcic.Declarative.RouteCEqGuard.eta_syntactic_guard_fails,
  ``Rcic.Declarative.RouteCEqGuard.binder_inhabited,
  ``Rcic.Declarative.RouteCEqGuard.eta_inhabited,
  ``Rcic.Declarative.Ann.EqLargeFixture.one,
  ``Rcic.Declarative.Ann.EqLargeFixture.two,
  ``Rcic.Declarative.Ann.EqLargeFixture.params,
  ``Rcic.Declarative.Ann.EqLargeFixture.indices,
  ``Rcic.Declarative.Ann.EqLargeFixture.famTy,
  ``Rcic.Declarative.Ann.EqLargeFixture.famSort,
  ``Rcic.Declarative.Ann.EqLargeFixture.reflTy,
  ``Rcic.Declarative.Ann.EqLargeFixture.reflSort,
  ``Rcic.Declarative.Ann.EqLargeFixture.recTy,
  ``Rcic.Declarative.Ann.EqLargeFixture.fam,
  ``Rcic.Declarative.Ann.EqLargeFixture.reflMember,
  ``Rcic.Declarative.Ann.EqLargeFixture.recMember,
  ``Rcic.Declarative.Ann.EqLargeFixture.famEnv,
  ``Rcic.Declarative.Ann.EqLargeFixture.prefixEnv,
  ``Rcic.Declarative.Ann.EqLargeFixture.env,
  ``Rcic.Declarative.Ann.EqLargeFixture.erase_env,
  ``Rcic.Declarative.Ann.EqLargeFixture.famTyTyped,
  ``Rcic.Declarative.Ann.EqLargeFixture.famView,
  ``Rcic.Declarative.Ann.EqLargeFixture.famWf,
  ``Rcic.Declarative.Ann.EqLargeFixture.famConstTyped,
  ``Rcic.Declarative.Ann.EqLargeFixture.reflTyTyped,
  ``Rcic.Declarative.Ann.EqLargeFixture.reflView,
  ``Rcic.Declarative.Ann.EqLargeFixture.reflGroup,
  ``Rcic.Declarative.Ann.EqLargeFixture.prefixWf,
  ``Rcic.Declarative.Ann.EqLargeFixture.recTyTypedNoIota,
  ``Rcic.Declarative.Ann.EqLargeFixture.prefix_noRec,
  ``Rcic.Declarative.Ann.EqLargeFixture.prefix_in_env,
  ``Rcic.Declarative.Ann.EqLargeFixture.fam_in_prefix,
  ``Rcic.Declarative.Ann.EqLargeFixture.prefix_iface,
  ``Rcic.Declarative.Ann.EqLargeFixture.reflTyTypedConcrete,
  ``Rcic.Declarative.Ann.EqLargeFixture.wf,
  ``Rcic.Declarative.Ann.EqLargeFixture.closed,
  ``Rcic.Declarative.Ann.EqLargeFixture.normClosed,
  ``Rcic.Declarative.Ann.EqLargeFixture.normCtorType,
  ``Rcic.Declarative.Ann.EqLargeFixture.liftIface,
  ``Rcic.Declarative.Ann.EqLargeFixture.substIface,
  ``Rcic.Declarative.Ann.EqLargeFixture.parameter,
  ``Rcic.Declarative.Ann.EqLargeFixture.result,
  ``Rcic.Declarative.Ann.EqLargeFixture.eqAt,
  ``Rcic.Declarative.Ann.EqLargeFixture.reflAt,
  ``Rcic.Declarative.Ann.EqLargeFixture.domain,
  ``Rcic.Declarative.Ann.EqLargeFixture.context,
  ``Rcic.Declarative.Ann.EqLargeFixture.parameterTyped,
  ``Rcic.Declarative.Ann.EqLargeFixture.resultTyped,
  ``Rcic.Declarative.Ann.EqLargeFixture.eqTyped,
  ``Rcic.Declarative.Ann.EqLargeFixture.contextWf,
  ``Rcic.Declarative.Ann.EqLargeFixture.majorTyped,
  ``Rcic.Declarative.Ann.EqLargeFixture.reflConstTyped,
  ``Rcic.Declarative.Ann.EqLargeFixture.reflTyped,
  ``Rcic.Declarative.Ann.EqLargeFixture.motiveTail,
  ``Rcic.Declarative.Ann.EqLargeFixture.motiveBody,
  ``Rcic.Declarative.Ann.EqLargeFixture.motive,
  ``Rcic.Declarative.Ann.EqLargeFixture.motiveTy,
  ``Rcic.Declarative.Ann.EqLargeFixture.motiveAt,
  ``Rcic.Declarative.Ann.EqLargeFixture.motiveTyped,
  ``Rcic.Declarative.Ann.EqLargeFixture.motiveAtTyped,
  ``Rcic.Declarative.Ann.EqLargeFixture.motiveBeta,
  ``Rcic.Declarative.Ann.EqLargeFixture.motiveTypeConv,
  ``Rcic.Declarative.Ann.EqLargeFixture.recConstTyped,
  ``Rcic.Declarative.Ann.EqLargeFixture.pre,
  ``Rcic.Declarative.Ann.EqLargeFixture.recPrefix,
  ``Rcic.Declarative.Ann.EqLargeFixture.call,
  ``Rcic.Declarative.Ann.EqLargeFixture.prefixTyped,
  ``Rcic.Declarative.Ann.EqLargeFixture.conversion,
  ``Rcic.Declarative.Ann.EqLargeFixture.callStuck,
  ``Rcic.Declarative.Ann.EqLargeFixture.envSem_false,
  ``Rcic.Declarative.Ann.EqLargeFixture.inhabited_boundary,
  ``Rcic.Syn.RouteCGuardedCycle.UnilateralF,
  ``Rcic.Syn.RouteCGuardedCycle.Unilateral,
  ``Rcic.Syn.RouteCGuardedCycle.unilateral_unfold,
  ``Rcic.Syn.RouteCGuardedCycle.unilateral_of_positive_cycle,
  ``Rcic.Syn.RouteCGuardedCycle.unilateral_symm,
  ``Rcic.Syn.RouteCGuardedCycle.unilateral_normal_iff,
  ``Rcic.Syn.RouteCGuardedCycle.loopIdentity,
  ``Rcic.Syn.RouteCGuardedCycle.loopInput,
  ``Rcic.Syn.RouteCGuardedCycle.loop_identity_cycle,
  ``Rcic.Syn.RouteCGuardedCycle.loop_positive_cycle,
  ``Rcic.Syn.RouteCGuardedCycle.loop_table_and_cycle,
  ``Rcic.Syn.RouteCGuardedCycle.loop_relates_every,
  ``Rcic.Syn.RouteCGuardedCycle.loop_sorts_not_related,
  ``Rcic.Syn.RouteCGuardedCycle.loop_unilateral_not_transitive,
  ``Rcic.Syn.RouteCGuardedCycle.loop_unilateral_not_finite_conversion_sound,
  ``Rcic.Declarative.Ann.RouteCLargeIndex.envWf,
  ``Rcic.Declarative.Ann.RouteCLargeIndex.noRec,
  ``Rcic.Declarative.Ann.RouteCLargeIndex.recSem,
  ``Rcic.Declarative.Ann.RouteCLargeIndex.remaining_premises,
  ``Rcic.Declarative.Ann.RouteCLargeIndex.closed_application,
  ``Rcic.Declarative.Ann.RouteCLargeIndex.closed_application_unrelated,
  ``Rcic.Declarative.Ann.RouteCLargeIndex.inhabited_boundary,
  ``Rcic.Declarative.Ann.RouteCLargeIndex.GroupsWithoutSmallIndex,
  ``Rcic.Declarative.Ann.RouteCLargeIndex.not_groupsWithoutSmallIndex
]

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Quot.sound]
  for root in routeCRelationPublicRoots do
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "RouteCRelation: {root} has forbidden axioms {forbidden}"
  logInfo m!"RouteCRelation: {routeCRelationPublicRoots.size} public roots checked"

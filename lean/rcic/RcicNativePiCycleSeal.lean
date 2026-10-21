import rcic.RcicNativePiCycleInputs
import rcic.RcicNativePiCycleDerivation
import rcic.RcicNativePiCycleRestatement
import rcic.RcicNativePiCycleProbe
import rcic.RcicNativePiCycleKOrder
import rcic.RcicNativePiCycleMeasure

/-!
# Independent segment-8 Pi-cycle audit seal

`closure_claim = 0`.

This bounded seal imports only the six new composition leaves.  Its roots
include the raw backward-transport obstruction, the actual regularity-size
counterexamples, the declared-telescope congruence construction, and the
explicitly conditional supporting controls.  It does not import the pending
segment-8 implementation or build either foundation aggregate.

The public-root axiom audit below permits only `propext` and `Quot.sound`.
-/

-- BEGIN RCIC_PI_CYCLE_AUDIT_ROOTS
#print axioms Rcic.Declarative.NativeValleys.PiCycleInputAudit.approxT_bvar_lamDomain_bot
#print axioms Rcic.Declarative.NativeValleys.PiCycleInputAudit.approxT_app_identity_lamDomain_bot
#print axioms Rcic.Declarative.NativeValleys.PiCycleInputAudit.no_pi_probe_lamDomain_factorization
#print axioms Rcic.Declarative.NativeValleys.PiCycleInputAudit.pi_probe_backward_obstruction
#print axioms Rcic.Declarative.NativeValleys.PiCycleInputAudit.not_raw_pi_probe_back
#print axioms Rcic.Declarative.NativeValleys.PiCycleInputAudit.not_raw_approxT_back
#print axioms Rcic.Declarative.NativeValleys.PiCycleInputAudit.no_readback_with_raw_approxT_back
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.regularityPad
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.regularityCtx
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.regularityCtxWf
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.regularityVar
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.regularityRefl
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.regularitySymm
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.regularityTrans
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.regularityPad_size
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.regularityPad_weaken
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.tySort_regularityCtxWf
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.convEnds_regularityCtxWf
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.tySort_regularity_unbounded
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.convEnds_index_unbounded
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.not_tySort_below_input
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.not_convEnds_index_below_symm
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.not_convEnds_index_below_trans
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.convArgsT_of_allSlots
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.declaredSlotConv
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.declaredSlotAlign
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.convArgsSymmT_of_envWfT
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.convArgsTransT_of_envWfT
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.typedPER_of_envWfT
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.distinctGuardValue
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.distinctGuardType
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.collapsedGuardValue
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.collapsedGuardType
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.distinctGuard_typed
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.collapsedGuard_not_typed
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.not_ctyS_preserved_of_guard_collapse
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.piProbe_typed_iff
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.piProbe_symmT
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.piProbe_transT
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.piProbe_right_diagonalT
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.PiProbeLinkT
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.piProbe_chainT
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.piProbe_diagT_of_typing
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.piRowField_of_piProbeLinkT
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.approxT_app_piProbe_inv
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.piProbeLinkT_requires_pi_readback
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.piProbeLinkT_requires_mixAnd_readback
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.not_piProbe_whStepCtx_mixAnd
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.not_piProbeLinkT_whStepCtx_andEnvU
#print axioms Rcic.Declarative.NativeValleys.PiCycleAudit.piProbe_whStepK_mixAnd
#print axioms Rcic.Declarative.NativePiCycleMeasure.ctx
#print axioms Rcic.Declarative.NativePiCycleMeasure.ctxWf
#print axioms Rcic.Declarative.NativePiCycleMeasure.propVarTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.familyApp
#print axioms Rcic.Declarative.NativePiCycleMeasure.familyAppTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.seedDomain
#print axioms Rcic.Declarative.NativePiCycleMeasure.seedDomainTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.seedDomainConv
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodeDomain
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodeDomainTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodeDomainConv
#print axioms Rcic.Declarative.NativePiCycleMeasure.tailType
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodePi
#print axioms Rcic.Declarative.NativePiCycleMeasure.declaredToNode
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodeToDeclared
#print axioms Rcic.Declarative.NativePiCycleMeasure.familyHeadNodeTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.argumentNodeTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.firstAppTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.firstApp_inv_domain
#print axioms Rcic.Declarative.NativePiCycleMeasure.familyAppNodeTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.familyAppNodeConv
#print axioms Rcic.Declarative.NativePiCycleMeasure.outerPi
#print axioms Rcic.Declarative.NativePiCycleMeasure.outerPiTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.outerPiConv
#print axioms Rcic.Declarative.NativePiCycleMeasure.reentryDomainConv
#print axioms Rcic.Declarative.NativePiCycleMeasure.reentryPiConv
#print axioms Rcic.Declarative.NativePiCycleMeasure.reentryRequest
#print axioms Rcic.Declarative.NativePiCycleMeasure.reentryRequest_eq
#print axioms Rcic.Declarative.NativePiCycleMeasure.reentry_no_strict_endpoint_rank
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodeDomain_size
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodePi_size
#print axioms Rcic.Declarative.NativePiCycleMeasure.outerPi_size
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodePi_not_smaller
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodePi_unbounded
#print axioms Rcic.Declarative.NativePiCycleMeasure.declared_closed
#print axioms Rcic.Declarative.NativePiCycleMeasure.declared_no_constants
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodeDomain_mentions_current_family
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodePi_mentions_current_family
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodePi_not_strictly_earlier
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodeToDeclared_not_clean
#print axioms Rcic.Declarative.NativePiCycleMeasure.no_alignment_in_earlier_environment
#print axioms Rcic.Declarative.NativePiCycleMeasure.admitted_measure_obstruction
-- END RCIC_PI_CYCLE_AUDIT_ROOTS

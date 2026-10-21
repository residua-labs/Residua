import Lean
import rcic.RcicNativeTypedModelKG
import rcic.RcicNativeTypedModelKGControls
import rcic.RcicNativeTypedModelKGInterface

/-!
# Bounded typed-model-K seal

The public declarations of the three new leaves are queried below.  Every leaf
is compiled from its current source; dependency sources are the #7749 chain
imported, never redefined.  Neither aggregate Foundation target is built.

Summary of what is sealed:

* `ApproxTK` and its gate `KGateAt`/`KIdxAgree`, with the transport into the
  landed `ApproxT` and the K-free reverse transport.
* Acceptance 1: the apart fixture reads only bottom
  (`approxTK_apartRec_bot`), so the premise of #7749's global refutation is
  gone (`not_apartRec_model_approxTK`).
* Acceptance 2: `.prop` is still observed at the β gap, the η control, the
  under-binder β control, and δ at the index head.
* Acceptance 3: the consumer status list (`approxTK_interface_status`) with
  non-degenerate inhabitants on `eqEnvT` and `natEnvUWfT`'s environment.
* Acceptance 4: the new interface obstruction is kernel-checked
  (`not_ctxModelTLaws_approxTK` — the old three-case `app_inv` fails at the
  guarded prefix), and the residual completeness divergence at δ under a
  binder is kernel-checked (`modelK_deltaBinder_divergence`).

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelKAudit.KG

/-- The exact project registration list, checked in this bounded module. -/
private def modelKSealedRoots : List Lean.Name := [
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.KIdxAgree,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.KIdxAgree.red,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.KIdxAgree.deltaL,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.KIdxAgree.deltaR,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.KIdxAgree.etaL,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.KIdxAgree.etaR,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.kIdxAgree_refl,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.lift01_ne_bvar0,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.KIdxJoinListAt,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.KGateAt,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.ApproxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.ApproxTK.recursorPropK,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.ApproxTK.recursorPropIdxFree,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_cases,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_app_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.foldAppCptT_curryStepT_app,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_to_approxT,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.PropRecAppFree,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.propRecAppFree_natExpand,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_of_approxT,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.ctxModelTApproxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.kIdxAgree_cases,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.apartPre,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.eqRecConst,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.apartRight_eq,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.eqS65_data,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.eqW65_indices,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.kIdxAgree_eqGap,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.not_kIdxAgree_apart,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.not_kGateAt_apart,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.kIdxAgree_etaIndex,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.kIdxAgree_deltaHead,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.kIdxAgree_binder,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.not_kIdxAgree_deltaBinder,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.eqW65_delta_indices,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.eqS65_data_delta,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.append_single_inj,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.eqIndexWS_exists,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_eqRec_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_eqRecConst65_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_eqSpine65_short_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_eqSpine65_apart_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_apartRec_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.not_apartRec_model_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_eqGapRedex_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_etaIndexRedex_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_deltaRedex_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_binderIndexRedex_prop,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.not_kGateAt_deltaBinder,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_deltaSpine5_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.modelK_deltaBinder_divergence,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_app_inv_four,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_app_inv_transport,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_interface_status,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_eqGapPrefix_lam,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.not_ctxModelTLaws_approxTK,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_eqEnvT_nonvacuity,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_natEnvU_nonvacuity,
  -- #7756 audit fix: auxiliary public theorems of the model leaf join the
  -- seal enumeration (they were leaf-local #print'ed only).
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.iotaWitnessS_preMajor_ne_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.foldApps_preMajor_is_app,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.recursorPropK_source_ne_bvar,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_bvar_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_sort_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_pi_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_lam_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_letE_inv,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_sort_code,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG.approxTK_bot
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Quot.sound]
  for root in modelKSealedRoots do
    let (_, state) := ((CollectAxioms.collect root).run env).run {}
    for ax in state.axioms do
      unless allowed.contains ax do
        throwError "[rcic_modelk_seal] {root} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_modelk_seal] {modelKSealedRoots.length} public roots sealed; axioms ⊆ {allowed}"

end Rcic.Declarative.NativeValleys.TypedModelKAudit.KG

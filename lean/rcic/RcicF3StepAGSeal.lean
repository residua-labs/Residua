import rcic.RcicF3StepAG
import rcic.RcicF3StepAGProp
import rcic.RcicF3FamKTFnObstr
import rcic.RcicF3FamKTFnReal
import rcic.RcicF3FamKTPropTwin

/-!
# Seal for `RcicF3StepAG`

Every sealed declaration's axiom set is audited at compile time: allowed
axioms are exactly `propext` and `Quot.sound` (`P`-elimination is only via
`Premises4.dec`, never `Classical.choice`). The list includes the public
`def`/`structure` declarations (`FamKTBridgeA`, `IotaAtCell`, `KTTypePrem`,
`AGPropAny`, `AGMixedAD`) matching `RcicF3StepAObstrSeal.lean`, plus the
bridge wiring (§4b: `fieldsClass_of_classA_noFn`, `hcls_of_groupA_noFn`,
`ktTypePrem_of_famKT`, `stepAG_of_famKT_type`) and the hN discharge
(§4c: `hN_of_nonIR`, `hN_of_envScoped`, the two strengthened apices) and the
hLimTab producer (§4d: `hLimTab_of_faithfulR`). The famKT follow-up
modules are sealed here for bounded reachability (audit fix, agy REFUSE
2026-10-27): `RcicF3FamKTFnObstr` (38), `RcicF3FamKTFnReal` (71),
`RcicF3FamKTPropTwin` (23) — every public declaration of each — plus the
Prop-uniform StepAG wiring (§4e, `RcicF3StepAGProp`, 9 declarations).

`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.F3.StepAGSeal

open Lean Elab Command

/-- Declarations sealed by this module. -/
def sealedTheorems : List Name := [
  ``Rcic.F3.StepAG.FamKTBridgeA,
  ``Rcic.F3.StepAG.tabKT_equiv,
  ``Rcic.F3.StepAG.agfix_of_famKTBridgeA,
  ``Rcic.F3.StepAG.agfixA_of_famKTBridgeA,
  ``Rcic.F3.StepAG.IotaAtCell,
  ``Rcic.F3.StepAG.memberSoundA_type_of_kt,
  ``Rcic.F3.StepAG.recPkgA_of_ms_iota,
  ``Rcic.F3.StepAG.KTTypePrem,
  ``Rcic.F3.StepAG.hpkgA_type_of_kt,
  ``Rcic.F3.StepAG.stepAG_of_ktType,
  ``Rcic.F3.StepAG.fieldsClass_of_classA_noFn,
  ``Rcic.F3.StepAG.hcls_of_groupA_noFn,
  ``Rcic.F3.StepAG.recApp_of_directRec,
  ``Rcic.F3.StepAG.hclsRec_of_classA_noFn,
  ``Rcic.F3.StepAG.hfix_of_lim_classA_noFn,
  ``Rcic.F3.StepAG.ktTypePrem_of_famKT,
  ``Rcic.F3.StepAG.stepAG_of_famKT_type,
  ``Rcic.F3.StepAG.stepAG_of_famKT_type_lim,
  ``Rcic.F3.StepAG.hN_of_nonIR,
  ``Rcic.F3.StepAG.hN_of_envScoped,
  ``Rcic.F3.StepAG.stepAG_of_famKT_type_nonIR,
  ``Rcic.F3.StepAG.iotaAtCell_of_witDirect,
  ``Rcic.F3.StepAG.stepAG_of_famKT_type_lim_nonIR,
  ``Rcic.F3.StepAG.hLimTab_of_faithfulR,
  ``Rcic.F3.StepAG.AGPropAny,
  ``Rcic.F3.StepAG.AGMixedAD,
  ``Rcic.F3.StepAG.fieldsClassA_get,
  ``Rcic.F3.StepAG.fieldShapesFuel_get,
  ``Rcic.F3.StepAG.pendA_deltaExposed_of_groupA_noFn,
  -- Rcic.F3.PSet.FnObstr (38)
  ``Rcic.F3.PSet.fnDom,
  ``Rcic.F3.PSet.fnDom_func,
  ``Rcic.F3.PSet.Fn2br,
  ``Rcic.F3.PSet.Fn2code,
  ``Rcic.F3.PSet.Fn2GSig,
  ``Rcic.F3.PSet.fnLeafT,
  ``Rcic.F3.PSet.fnSuccT,
  ``Rcic.F3.PSet.fnT,
  ``Rcic.F3.PSet.fnDepth,
  ``Rcic.F3.PSet.fnW,
  ``Rcic.F3.PSet.decG_leaf,
  ``Rcic.F3.PSet.decG_succ,
  ``Rcic.F3.PSet.decG_fnT_succ,
  ``Rcic.F3.PSet.decG_W,
  ``Rcic.F3.PSet.fnDepth_mk,
  ``Rcic.F3.PSet.fnCls,
  ``Rcic.F3.PSet.fnDepth_cls,
  ``Rcic.F3.PSet.graphOf_inj,
  ``Rcic.F3.PSet.gIterOf,
  ``Rcic.F3.PSet.gIter2,
  ``Rcic.F3.PSet.fnIdx,
  ``Rcic.F3.PSet.fnIdx_func_node,
  ``Rcic.F3.PSet.fnIdx_func,
  ``Rcic.F3.PSet.fnT_mem,
  ``Rcic.F3.PSet.leafNode_absurd,
  ``Rcic.F3.PSet.fnT_not_mem,
  ``Rcic.F3.PSet.gUnion,
  ``Rcic.F3.PSet.fnW_not_mem_union,
  ``Rcic.F3.PSet.fnW_valid,
  ``Rcic.F3.PSet.fnW_diverges,
  ``Rcic.F3.PSet.fnUIdx,
  ``Rcic.F3.PSet.fnUIdx_func,
  ``Rcic.F3.PSet.gphi_func_node,
  ``Rcic.F3.PSet.fnW_mem_gphi_union,
  ``Rcic.F3.PSet.FnContGSig,
  ``Rcic.F3.PSet.fnContGSig_false,
  ``Rcic.F3.PSet.gt_empty,
  ``Rcic.F3.PSet.gSet_empty_of_all_branching,
  -- Rcic.F3.PSet.FnReal (71)
  ``Rcic.F3.PSet.lift_ord,
  ``Rcic.F3.PSet.fxF,
  ``Rcic.F3.PSet.fxC,
  ``Rcic.F3.PSet.fxDom0,
  ``Rcic.F3.PSet.fxS,
  ``Rcic.F3.PSet.fxμ,
  ``Rcic.F3.PSet.fxσ,
  ``Rcic.F3.PSet.fxρp,
  ``Rcic.F3.PSet.fxA,
  ``Rcic.F3.PSet.fxLeaf,
  ``Rcic.F3.PSet.fxNode,
  ``Rcic.F3.PSet.fxFd,
  ``Rcic.F3.PSet.fxFd_ctors_len,
  ``Rcic.F3.PSet.fxFd_leaf,
  ``Rcic.F3.PSet.fxFd_node,
  ``Rcic.F3.PSet.fx_kind,
  ``Rcic.F3.PSet.fx_kinds,
  ``Rcic.F3.PSet.fx_level,
  ``Rcic.F3.PSet.fx_bound,
  ``Rcic.F3.PSet.fx_den_dom,
  ``Rcic.F3.PSet.ord_succ_not_pempty,
  ``Rcic.F3.PSet.fx_dich,
  ``Rcic.F3.PSet.fx_Ed_eq,
  ``Rcic.F3.PSet.fxDomEF,
  ``Rcic.F3.PSet.fx_domEF_eq,
  ``Rcic.F3.PSet.fx_domEF_mem,
  ``Rcic.F3.PSet.fxDomBig,
  ``Rcic.F3.PSet.fx_domBig_eq,
  ``Rcic.F3.PSet.fx_domBig_mem,
  ``Rcic.F3.PSet.fx_domBig_nonempty,
  ``Rcic.F3.PSet.fxT,
  ``Rcic.F3.PSet.fx_graph_const,
  ``Rcic.F3.PSet.fx_S,
  ``Rcic.F3.PSet.fx_fxS_mem,
  ``Rcic.F3.PSet.fx_domBig_mem_W4,
  ``Rcic.F3.PSet.fx_graph_const_mem,
  ``Rcic.F3.PSet.fxT_mem_W4,
  ``Rcic.F3.PSet.fx_resTup,
  ``Rcic.F3.PSet.fx_recTup,
  ``Rcic.F3.PSet.fapp_graph_const,
  ``Rcic.F3.PSet.childAtV_graph_const,
  ``Rcic.F3.PSet.fxT_fib_mem,
  ``Rcic.F3.PSet.fx_graph_mem_pi,
  ``Rcic.F3.PSet.fx_mem_PsiF_iff,
  ``Rcic.F3.PSet.fxT_mem_iter,
  ``Rcic.F3.PSet.childAtV_congr_left,
  ``Rcic.F3.PSet.fxT_not_mem_iter,
  ``Rcic.F3.PSet.fx_domBig_num,
  ``Rcic.F3.PSet.fxNumOf,
  ``Rcic.F3.PSet.fxNumOf_prop,
  ``Rcic.F3.PSet.fx_numOf_pinned,
  ``Rcic.F3.PSet.fx_numOf_congr,
  ``Rcic.F3.PSet.fxNumOfTPred,
  ``Rcic.F3.PSet.fxNumOfT_ex,
  ``Rcic.F3.PSet.fxNumOfT,
  ``Rcic.F3.PSet.fxNumOfT_prop,
  ``Rcic.F3.PSet.fx_numOfT_pinned,
  ``Rcic.F3.PSet.fx_numOfT_congr,
  ``Rcic.F3.PSet.fxhW,
  ``Rcic.F3.PSet.fx_hW_beta,
  ``Rcic.F3.PSet.fxSec,
  ``Rcic.F3.PSet.fx_xW_eq_sImage,
  ``Rcic.F3.PSet.fx_xW_mem,
  ``Rcic.F3.PSet.fapp_graphOf,
  ``Rcic.F3.PSet.childAtV_graphOf,
  ``Rcic.F3.PSet.fxZW,
  ``Rcic.F3.PSet.fxT_mem_iUnionN,
  ``Rcic.F3.PSet.fx_xW_mem_pi,
  ``Rcic.F3.PSet.fx_zW_mem_PsiF,
  ``Rcic.F3.PSet.fx_zW_not_mem,
  ``Rcic.F3.PSet.fnContUnion_false,
  -- Rcic.F3.PSet.PropTwin (23)
  ``Rcic.F3.PSet.iUnionN_tv,
  ``Rcic.F3.PSet.hclsRec_of_classA,
  ``Rcic.F3.PSet.ctorFitsStage,
  ``Rcic.F3.PSet.famEnd_propStage,
  ``Rcic.F3.PSet.limEnd_propStage,
  ``Rcic.F3.PSet.hnoFn_of_mem,
  ``Rcic.F3.PSet.ed_iter_lift,
  ``Rcic.F3.PSet.telFits_iter_lift,
  ``Rcic.F3.PSet.ctorFitsStage_succ,
  ``Rcic.F3.PSet.telFitsP_of_telFits_zero,
  ``Rcic.F3.PSet.telFitsP_of_telFits_succ,
  ``Rcic.F3.PSet.dstarP_of_fits,
  ``Rcic.F3.PSet.dstarP_of_ctorFitsStage,
  ``Rcic.F3.PSet.stageQ,
  ``Rcic.F3.PSet.ctorFitsStage_le,
  ``Rcic.F3.PSet.ctorFitsStage_leq,
  ``Rcic.F3.PSet.okP_plain_inv,
  ``Rcic.F3.PSet.okP_direct_inv,
  ``Rcic.F3.PSet.telFits_iterSucc_of_telFitsP,
  ``Rcic.F3.PSet.ctorFitsStage_of_dstarP,
  ``Rcic.F3.PSet.limEnd_famEndP,
  ``Rcic.F3.PSet.famLim_famLfpP,
  ``Rcic.F3.PSet.famLim_famKT_prop,
  -- Rcic.F3.StepAGProp (6)
  ``Rcic.F3.StepAG.memberSoundA_prop_of_kt,
  ``Rcic.F3.StepAG.KTPropPrem,
  ``Rcic.F3.StepAG.hpkgA_prop_of_kt,
  ``Rcic.F3.StepAG.stepAG_of_ktProp,
  ``Rcic.F3.StepAG.ktPropPrem_of_famKT,
  ``Rcic.F3.StepAG.stepAG_of_famKT_prop,
  ``Rcic.F3.StepAG.stepAG_of_famKT_prop_lim,
  ``Rcic.F3.StepAG.stepAG_of_famKT_prop_nonIR,
  ``Rcic.F3.StepAG.stepAG_of_famKT_prop_lim_nonIR
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_stepag_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_stepag_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_stepag_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.StepAGSeal

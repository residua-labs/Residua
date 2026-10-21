import rcic.RcicDT008Equiv
import rcic.RcicIARecTyped
import rcic.RcicPEqLeafTProp
import rcic.RcicStepsSREnvWf
import rcic.RcicUntypedConvCollapse

/-!
# RcicCoreMetatheory — core layer 4: weakening, substitution, inversion, parallel reduction, subject reduction

Mathematical-map entry module (swe-mathmap, 2026-10-21): imports this layer's
maximal elements and adds no declarations. Part of the `rcic` core map; the
core is exactly the import closure of `rcic.RcicCore`.

Key definitions and theorems of the layer:

* `Rcic.Declarative.hasTyWeaken` / `Rcic.Declarative.convWeaken` / `Rcic.Declarative.stepWeaken` — weakening on the raw judgment
* `Rcic.Declarative.hasTyTWeaken` / `Rcic.Declarative.convTWeaken` — weakening on the typed judgment
* `Rcic.Declarative.hasTyT_subst` / `Rcic.Declarative.convT_subst` / `Rcic.Declarative.hasTyT_substS` — typed substitution
* `Rcic.Declarative.hasTyTInv_lam` / `Rcic.Declarative.hasTyTInv_app` / `Rcic.Declarative.hasTyTInv_pi` — typed inversion
* `Rcic.Declarative.ParRed` / `Rcic.Declarative.ParRedCtx` — parallel reduction (raw)
* `Rcic.Declarative.ParRedT` / `Rcic.Declarative.ParRedArgsT` / `Rcic.Declarative.ParRedCtxT` / `Rcic.Declarative.ParRedTStar` — typed parallel reduction
* `Rcic.Declarative.parRedT_sr` — subject reduction of `ParRedT`
* `Rcic.Declarative.PEqT` / `Rcic.Declarative.CtxConvT` — comparison modulo proof positions and context conversion
* `Rcic.Declarative.regularT` / `Rcic.Declarative.regularT_of_envWfT` — validity (regularity) of the typed judgment
* `Rcic.Declarative.DT007T_typing_regularity_of_envWfT` / `Rcic.Declarative.DT009T_endpoints_envWfT` / `Rcic.Declarative.DT008T_tyConvT_equivalence` — the discharged DT-007/008/009 debts
* `Rcic.Declarative.step_srT` / `Rcic.Declarative.steps_srT` — one-step and star subject reduction at `EnvWfT`
* `Rcic.Declarative.DT010T_one_step_subject_reduction` / `Rcic.Declarative.DT011T_multi_step_subject_reduction` — subject reduction (in `RcicDTMetaTypedSR`)

Layer members: the raw metatheory (`RcicCtxMorph`, `RcicDerivationRec`,
`RcicWeaken`, `RcicSubst`, `RcicSubstLet`, `RcicInvert`, `RcicInvertFamily`,
`RcicRefutations`, `RcicUntypedConvCollapse`, `RcicConvChar`), the parallel
reduction development (`RcicParRedCore`, `RcicParRedIota`, `RcicParRedWeight`,
`RcicParRedSortWall`, `RcicParRedSubst`, `RcicParRedDevel`, `RcicParRedDiamond`,
`RcicParRed`), the typed parallel reduction (`RcicParRedT`, `RcicParRedTSR`,
`RcicParRedSRTyped`, `RcicPEqT`, `RcicPEqTCtx`, `RcicPEqLeafTProp`), the typed
metatheory (`RcicTypedWeaken`, `RcicTypedSubst`, `RcicTypedSubstLet`,
`RcicTypedInvert`, `RcicTypedValidity`, `RcicTypedLevels`,
`RcicTypedLevelsCongr`, `RcicTypedInst0Congr`, `RcicCtxConvT`), the
inductive-admission recursor packages (`RcicIARecMotive`, `RcicIARecTel`,
`RcicIARecTyped`, `RcicIATypedMinor`), and the DT carriers (`RcicDTMeta`,
`RcicDTMetaTyped`, `RcicDTMetaTypedSR`, `RcicDT008Equiv`, `RcicDT0709EnvWf`,
`RcicStepArmsEnvWf`, `RcicStepsSREnvWf`).
-/

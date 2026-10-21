import rcic.RcicTypedEnvEntry
import rcic.RcicTypedGroup
import rcic.RcicTypedIdxAdmittedPins
import rcic.RcicTypedRef

/-!
# RcicCoreJudgments — core layer 3: the typed judgments

Mathematical-map entry module (swe-mathmap, 2026-10-21): imports this layer's
maximal elements and adds no declarations. Part of the `rcic` core map; the
core is exactly the import closure of `rcic.RcicCore`.

The judgment family `HasTyT` / `ConvT` / `TyConvT` / `CtxWfT` / `ConvArgsT`
itself is defined in `rcic.RcicDeclarative` (syntax layer); this layer holds
the typed judgment's environment form, its certified checkers and its group
views.

Key definitions and theorems of the layer:

* `Rcic.Declarative.EnvWfT` — the typed environment judgment
* `Rcic.Declarative.IndGroupTypedT` / `Rcic.Declarative.FamilyTypedT` / `Rcic.Declarative.CtorTypedT` / `Rcic.Declarative.IotaEquationTypedT` / `Rcic.Declarative.TelTypedT` — group members typed at `EnvWfT`
* `Rcic.Declarative.checkT` / `Rcic.Declarative.inferT` / `Rcic.Declarative.synCheck` / `Rcic.Declarative.hasTyT_of_inferT` — the certified syntactic checker
* `Rcic.Declarative.headStep?` / `Rcic.Declarative.whnfTy` / `Rcic.Declarative.toSort?` / `Rcic.Declarative.toPi?` — the conversion checker
* `Rcic.Declarative.SubstT` / `Rcic.Declarative.substT` / `Rcic.Declarative.FieldT` — substitutions and fields on the typed root
* `Rcic.Declarative.iotaSchemaAtIn` — the ι schema's index admission
* `Rcic.TypedRef.TRVal` / `Rcic.TypedRef.adjudicate` — the typed-ref adjudication guard

Layer members: `RcicTypedEnv`, `RcicTypedEnvEntry`, `RcicTypedRef`,
`RcicTypedJ`, `RcicTypedCheck`, `RcicTypedConv`, `RcicTypedConvPins`,
`RcicTypedGroup`, `RcicTypedGroupPins`, `RcicTypedGroupPinsList`,
`RcicTypedGroupPinsVec`, `RcicTypedIdxAdmitted`, `RcicTypedIdxAdmittedPins`,
`RcicTypedDeltaRecPins`.
-/

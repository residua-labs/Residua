import rcic.RcicDerivedIotaU
import rcic.RcicEtaKPeakPins
import rcic.RcicIndGroupExclusions
import rcic.RcicIotaShapeAdapter

/-!
# RcicCoreEnv — core layer 2: environments, inductive groups and admission, ι, source environments

Mathematical-map entry module (swe-mathmap, 2026-10-21): imports this layer's
maximal elements and adds no declarations. Part of the `rcic` core map; the
core is exactly the import closure of `rcic.RcicCore`.

Key definitions and theorems of the layer:

* `Rcic.Declarative.ResolvedEnv` / `Rcic.Declarative.CheckedMember` / `Rcic.Declarative.MemberClass` — resolved environments (defined in `RcicDeclarative`, syntax layer)
* `Rcic.Declarative.IndGroupAdmitted` — the inductive-group admission judgment
* `Rcic.Declarative.PolicyFamilyView` / `Rcic.Declarative.PolicyTelescopeTyping` — the inductive policy's family views
* `Rcic.Declarative.recursorGroupAdmitted` — recursor admission at a declared group
* `Rcic.Declarative.iotaSchemaAt` / `Rcic.Declarative.equationDoms` / `Rcic.Declarative.iotaLhsType` — the ι-rule schema
* `Rcic.Declarative.DerivedIota` / `Rcic.Declarative.DerivedIotaU` / `Rcic.Declarative.IotaWitnessS` — derived ι reduction and its witnesses
* `Rcic.Declarative.IotaWitnessS.recData_admitted` — recursor data admitted through the index path
* `Rcic.Scm.SrcG.srcMembersG` / `Rcic.Scm.SrcG.envPre` — the source-environment fixtures and their prefixes

Layer members: `RcicEnv`, `RcicFamRef`, `RcicAdmit`, `RcicFixtures`,
`RcicIndGroupAdmitted`, `RcicIndGroupExclusions`, `RcicIndGroupFixtureWf`,
`RcicIndGroupJudgment`, `RcicInductivePolicy`, `RcicIota`, `RcicIotaShape`,
`RcicIotaShapeAdapter`, `RcicIotaShapeStable`, `RcicDerivedIotaU`,
`RcicSrcEnvV1`, `RcicEGTypedGroup`, `RcicPinEqEraseWf`, `RcicPinEqIotaStarK`,
`RcicKGateNoGo`, `RcicEtaKPeakPins`, and the `ScmSrcGroups*` source
environment modules.
-/

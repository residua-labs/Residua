import rcic.RcicAnnIotaCorr
import rcic.RcicDerivedIotaU

/-!
# R-NoFunRec S6 (R-A): the ι-correspondence past `EnvNoFunA`, at the union face

The three theorems that carry the `EnvNoFunA` premise (`derivedIota_of_iotaFnA`,
`iotaErasesTA_of_envWfA`, `iotaCorrTA_of_envWfA` — `RcicAnnIotaCorr.lean:695/:1747/:1958`)
refuse function-recursive Ann environments because the LEGACY `IotaWitness` cannot express a
`.frec` field (`FieldShape.kind?` is `none` at inner > 0). The union relation `DerivedIotaU`
(S2, option (b)) has the `.ofUS` arm for exactly that case.

This file restates the correspondence over the union face (`IotaCorrTUA`), additive — the
sealed statements stay untouched. Segment 1 (this file's first section) lifts the NOFUN
fragment: on a NoFun environment the union correspondence is the legacy one relabeled
(`derivedIotaU_elim` recovers both faces at the same endpoints), and the annotation direction
needs NO `EnvNoFunA` at all — it passes the premise unconditionally at the union. The FREC
fragment (a firing `.recursive (n+1)` field landing `.ofUS` under a rigidity certificate)
is segment 3 (`derivedIusiOfIotaFnA_frec` below); its per-field theory is segment 2
(`RcicIotaFunRecFrag.lean`).

Plan: `research/rcic/nofunrec/S6_PLAN.md`. `closure_claim` stays 0.
-/

namespace Rcic.Declarative.Ann

/-! ## the union faces

`IotaErasesTo D EA` (`RcicAnnIotaCorr.lean:979`) is parameterized over the landing relation;
the three below mirror `IotaErasesA`/`IotaErasesTA`/`IotaAnnotatesA`/`IotaCorrTA` at
`D = DerivedIotaU`. -/

/-- R-A: the erasure direction at the UNION evidence — a step of the copy's ι is a
    `DerivedIotaU` step of the erased environment, on the erased terms. -/
def IotaErasesTUA (EA : ResolvedEnvA) : Prop := IotaErasesTo DerivedIotaU EA

/-- R-A: the annotation direction at the UNION evidence — a `DerivedIotaU` step of the
    erased environment on an erased left-hand side fires the copy's ι, with a reduct
    erasing to the step's right-hand side. -/
def IotaAnnotatesUA (EA : ResolvedEnvA) : Prop :=
  ∀ e rhs, DerivedIotaU (eraseEnv EA) (erase e) rhs →
    ∃ e', iotaFnA EA e = some e' ∧ erase e' = rhs

/-- R-A: the two per-witness directions bundled — `IotaCorrTA`'s union sibling. -/
structure IotaCorrTUA (EA : ResolvedEnvA) : Prop where
  /-- annotation at the union face. -/
  ann : IotaAnnotatesUA EA
  /-- erasure at the union face. -/
  eraseT : IotaErasesTUA EA

/-! ## segment 1: the NoFun fragment — the three theorems' union counterparts

On a NoFun environment the union erase direction IS the legacy one (`derivedIotaU_ofDerivedIota`
lands `.ofU`, no certificate needed — the legacy route's honest strength); the annotation
direction upgrades the `.ofU` arm to the typed root through the erase certificate
(`derivedIotaT_of_derivedIota`, `RcicAnnIotaCorr.lean:1981`) and takes the `.ofUS` arm
directly. Nothing here re-proves what `RcicAnnIotaCorr` already carries. -/

/-- `derivedIota_of_iotaFnA` at the union face: on a NoFun environment a step of the copy's
    ι is a union derived-ι step of the erased environment, landing the LEGACY arm `.ofU`. -/
theorem derivedIotaU_of_iotaFnA {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (hnf : EnvNoFunA EA) (hn : EnvNormEraseA EA) {e e' : ExprA}
    (h : iotaFnA EA e = some e') :
    Nonempty (DerivedIotaU (eraseEnv EA) (erase e) (erase e')) :=
  have ⟨d⟩ := derivedIota_of_iotaFnA hW hnf hn h
  ⟨derivedIotaU_ofDerivedIota d⟩

/-- `iotaErasesTA_of_envWfA` at the union face (the `hnf` premise KEPT — the frec fragment
    is segment 3). No certificate: the legacy landing is the debt-free one. -/
theorem iotaErasesTUA_of_envWfA {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (hnf : EnvNoFunA EA) (hn : EnvNormEraseA EA) : IotaErasesTUA EA :=
  fun _ _ h => derivedIotaU_of_iotaFnA hW hnf hn h

/-- the annotation direction at the union face — `EnvNoFunA` does NOT appear: `ann` never
    needed it at the typed root, and the `.ofU` arm upgrades through the erase certificate. -/
theorem iotaAnnotatesUA_of_envWfA {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (hn : EnvNormEraseA EA) (hCe : EnvCorrEraseCert (eraseEnv EA))
    (hCa : EnvCorrAnnCert (eraseEnv EA)) : IotaAnnotatesUA EA := by
  intro e rhs hu
  obtain u | t := derivedIotaU_elim hu
  · obtain ⟨t⟩ := derivedIotaT_of_derivedIota hCe u
    exact iotaAnnotatesA_of_envWfA hW hn hCa e rhs t
  · exact iotaAnnotatesA_of_envWfA hW hn hCa e rhs t

/-- `iotaCorrTA_of_envWfA` at the union face: the two-direction correspondence restated
    over `DerivedIotaU`, on the same premises the typed-root version carries. -/
theorem iotaCorrTUA_of_envWfA {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (hnf : EnvNoFunA EA) (hn : EnvNormEraseA EA)
    (hCe : EnvCorrEraseCert (eraseEnv EA)) (hCa : EnvCorrAnnCert (eraseEnv EA)) :
    IotaCorrTUA EA where
  ann := iotaAnnotatesUA_of_envWfA hW hn hCe hCa
  eraseT := iotaErasesTUA_of_envWfA hW hnf hn

#print axioms Rcic.Declarative.Ann.iotaCorrTUA_of_envWfA

end Rcic.Declarative.Ann

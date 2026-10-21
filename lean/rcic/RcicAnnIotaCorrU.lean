import rcic.RcicDTMetaTypedSR
import rcic.RcicDerivedIotaU
import rcic.RcicTypedDeltaRecPins
import rcic.RcicIotaShapeStable

/-!
# R4 — `CorrCertsBelowU`: the union counterpart (cc ruling on #6592)

cc's ruling on `research/rcic/corr/S0_VEC.md` (S0): **R4** — a union counterpart
carrying **R1**'s per-env `.ann` certificate, with NO sealed edits.  This module
is that landing: `CorrCertsBelow` stays sealed exactly as it is; the sibling
`CorrCertsBelowU E` is `CorrCertsBelow E ∨ EnvCorrAnnCert E`, and the typed-root
ι subject-reduction consumers are restated against it.

## The open sub-measurements (ruling's first clause)

- **Junk witnesses at the env itself.**  `wVconsBadIdx` — a legal `IotaWitness`
  of `vecEnv` whose `preMajor` index slot is off — ADAPTS:
  `iotaWitnessSB wVconsBadIdx 64 = true` (the recognizer demands schema/RHS
  agreement on the witness's OWN declared endpoints, which hold).  The canonical
  shape witness `wVconsS` passes the annotation recognizer
  (`iotaWitnessSAnnB vecEnv wVconsS = true`).  The at-env `.ann` certificate is
  not refuted by Vec's junk witnesses.
- **The universal discharge is REFUTED.**  `∀ E, EnvWfT E → EnvCorrAnnCert E`
  fails at `drEnv` (`drEnvWfT`, R-NoDeltaRec's `Id F` group): the mk field is
  `Id F` — recursive only THROUGH the transparent `Id` — so `fieldShapesFuel`
  reads `.recursive 0` (the typed analysis reaches through δ), the `IotaWitnessS`
  `wDrMkS` exists, and `iotaWitnessSAnnB drEnv wDrMkS = false` because
  `DirectFieldFrag`'s `noTransparentB` conjunct refuses the non-rigid head.
  This is a THIRD failure mode, distinct from `vecOnlyEnvU`'s member-closure
  gap: here the env itself is well-formed and the witness is well-formed; the
  annotation recognizer's DIRECT fragment is stricter than admission's
  δ-permissive field analysis.  So the `.ann` arm is a genuine per-env premise,
  not a theorem — IA-024/DT-019 keep a real certificate obligation, now
  per-environment and annotation-side only.

## Contents

- `wDrMkS` — the canonical `IotaWitnessS` at `F.rec`/`mk` (same construction
  pattern as `wIotaWitnessS`, stability by
  `iotaWitnessS_hstable_of_constsMemberFuel`).
- `pin_iotaWitnessSAnnB_wDrMkS`, `not_envCorrAnnCert_drEnv`,
  `not_envCorrAnnCert_of_envWfT` — the refutation chain.
- `CorrCertsBelowU` + `corrCertsBelowU_annCert` — the union and its eliminator.
- `hasTyT_iota_srTU`, `iotaPreserveTTU`, `iotaPreserveTU` — the consumers:
  `hasTyT_iota_srT`'s proof shape with `iotaCorrTA_of_envWfA` replaced by
  `iotaAnnotatesA_of_envWfA` (the `.ann` half is ALL the SR proof consumes —
  `EnvNoFunA` and the erasure cert were only needed for the unused `.eraseT`
  half), and the `DerivedIotaU` cover that takes the legacy arm premise-free.

`closure_claim` stays 0; `InScope` is the separate #6217 lane.
-/

namespace Rcic.Declarative

/-! ## (1) the canonical `IotaWitnessS` at `F.rec`/`mk` (drEnv) -/

/-- the shape-based ι witness at the δ-recursive group: recursor `F.rec` at `3`,
    constructor `mk` at `2`, family `F` at `1`, no params or indices, one minor,
    fields `[x]` with shapes `[.recursive 0]` — the shape the typed analyzer
    reaches THROUGH `Id`'s transparent body — schema `drSchema`. -/
def wDrMkS : IotaWitnessS drEnv where
  recRef := 3
  ctorRef := 2
  ls := [.param 0]
  lsC := []
  recMember := drRecMember
  ctorMember := drMkMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := preMajorBvars 0 1 0 1
  fields := fieldBvars 1
  ctorParams := []
  familyRef := 1
  famMember := drFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  ctorDoms := [drField]
  ctorResult := .const 1 []
  hpeel := rfl
  hfamApp := rfl
  recDoms := [drMotiveTy, drMinorTy, .const 1 []]
  recBody := .app (.bvar 2) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  fuel := 8
  shapes := [.recursive 0]
  hshapes := rfl
  schema := drSchema
  hschema := rfl
  hstable := iotaWitnessS_hstable_of_constsMemberFuel rfl rfl (by
    have hmem0 : drEnv.members 0 = some drIdMember := rfl
    have hmem1 : drEnv.members 1 = some drFamMember := rfl
    show iotaWitnessStableB drEnv 8 [drField] (fieldBvars 1)
      (lift 0 2 (ctorFieldTelRaw 0 [drField] (.const 1 []))) = true
    simp [iotaWitnessStableB, drField, fieldBvars, ctorFieldTelRaw, lift,
      constsMemberFuel, hmem0, hmem1, drIdMember, drFamMember, transparent,
      instantiateLevels])
  hschemaScope := rfl

/-! ## (2) the refutation: the universal `.ann` discharge fails at `drEnv` -/

/-- THE REFUTATION WITNESS: `wDrMkS` is a legal `IotaWitnessS` of the well-formed
    `drEnv`, but the annotation recognizer refuses it — `directFragCheck`'s
    `noTransparentB` conjunct rejects the `Id F` field whose head is the
    transparent `Id`.  The divergence `fieldAnalyze` (δ-permissive) vs
    `DirectFieldFrag` (rigid heads only) is exactly R-NoDeltaRec-4d-iii's
    `drecD`-freeness, surfacing here as an `.ann`-cert failure. -/
theorem pin_iotaWitnessSAnnB_wDrMkS :
    Ann.iotaWitnessSAnnB drEnv wDrMkS = false := rfl

/-- `EnvCorrAnnCert` is refuted at `drEnv` itself — no sub-environment needed.
    This is the at-env analogue of `not_corrCertsBelow_vecEnvUT`, with a
    different cause: not member closure (Vec) and not the frec gate (S6), but
    the δ-reached non-rigid field (R-NoDeltaRec). -/
theorem not_envCorrAnnCert_drEnv : ¬ Ann.EnvCorrAnnCert drEnv := by
  intro h
  have h' := h wDrMkS
  rw [pin_iotaWitnessSAnnB_wDrMkS] at h'
  exact Bool.noConfusion h'

/-- THE UNIVERSAL DISCHARGE IS FALSE (the ruling's "if it holds" branch settles
    to NOT): `EnvWfT` does not imply the annotation certificate.  `drEnv` is
    well-formed (`drEnvWfT`) yet refuses `wDrMkS` — well-formedness admits
    δ-recursive fields that the DIRECT fragment does not.  IA-024/DT-019
    therefore keep `CorrCertsBelowU`'s `.ann` arm as a real per-env premise. -/
theorem not_envCorrAnnCert_of_envWfT :
    ¬ (∀ E : ResolvedEnv, EnvWfT E → Ann.EnvCorrAnnCert E) := by
  intro h
  exact not_envCorrAnnCert_drEnv (h drEnv drEnvWfT)

/-! ## (3) `CorrCertsBelowU` — the union counterpart, no sealed edits -/

/-- R4's union: EITHER the sealed hereditary certificates (`CorrCertsBelow E`,
    the `.drecD` bridge consumer's full strength) OR R1's per-env annotation
    certificate at `E` itself (`EnvCorrAnnCert E`, all `hasTyT_iota_srT`'s proof
    actually consumes).  `CorrCertsBelow` is untouched. -/
def CorrCertsBelowU (E : ResolvedEnv) : Prop :=
  Ann.CorrCertsBelow E ∨ Ann.EnvCorrAnnCert E

/-- the `.below` arm: the hereditary certificates imply the union. -/
theorem corrCertsBelowU_of_below {E : ResolvedEnv} (h : Ann.CorrCertsBelow E) :
    CorrCertsBelowU E := Or.inl h

/-- the `.ann` arm: R1's per-env annotation certificate implies the union. -/
theorem corrCertsBelowU_of_ann {E : ResolvedEnv} (h : Ann.EnvCorrAnnCert E) :
    CorrCertsBelowU E := Or.inr h

/-- the union's common payoff: both arms yield the at-env `.ann` certificate —
    `.below` at `envSub_refl`, `.ann` directly.  This is the only conjunct the
    typed-root ι SR route consumes. -/
theorem corrCertsBelowU_annCert {E : ResolvedEnv} (h : CorrCertsBelowU E) :
    Ann.EnvCorrAnnCert E :=
  h.elim (fun hC => (hC _ (Ann.envSub_refl _)).2) id

/-! ## (4) the consumers — `iotaPreserveT`'s union sibling -/

/-- ι SUBJECT REDUCTION AT THE SHAPE-BASED EVIDENCE, union form:
    `hasTyT_iota_srT`'s proof shape with the annotation direction discharged by
    `iotaAnnotatesA_of_envWfA` off `CorrCertsBelowU`'s common payoff — the
    `.ann` half is all the SR proof consumes (`EnvNoFunA` and the erasure cert
    fed only the unused `.eraseT` half of `IotaCorrTA`). -/
theorem hasTyT_iota_srTU (C : Ann.AnnEnvA E) (hn : Ann.EnvNormEraseA E)
    (hC : CorrCertsBelowU (Ann.eraseEnv E))
    {Γ : LCtx} (hΓ : CtxWfT (Ann.eraseEnv E) n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT (Ann.eraseEnv E) lhs rhs)
    (hlhs : HasTyT (Ann.eraseEnv E) n Γ lhs T) :
    Nonempty (HasTyT (Ann.eraseEnv E) n Γ rhs T) := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := Ann.annCtxWfT' C hn hΓ
  obtain ⟨eA, TA, he, hT, ⟨tA⟩⟩ := Ann.annHasTyT' C hn hlhs hΓA hctx
  subst he
  obtain ⟨hW⟩ := C.wf
  obtain ⟨e', hfn, he'⟩ := Ann.iotaAnnotatesA_of_envWfA hW hn
    (corrCertsBelowU_annCert hC) _ _ hd
  obtain ⟨t'⟩ := Ann.iotaSRA_ty C hΓA hfn tA
  obtain ⟨hT'⟩ := Ann.hasTyT_of_hasTyA hW (C.hNS hn) t'
  rw [he', hT, hctx] at hT'
  exact ⟨hT'⟩

/-- TYPED-ROUTE UNION SIBLING (R4): `iotaPreserveTT` against `CorrCertsBelowU` —
    the premise an environment pays is now EITHER the hereditary certificates
    (every admitted env of the S0 fixtures, still useful where they hold) OR
    `EnvCorrAnnCert` at `E` itself.  Per-env, decided by `iotaWitnessSAnnB`,
    never universal — `drEnv` is the standing countermodel. -/
theorem iotaPreserveTTU {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) (hC : CorrCertsBelowU E)
    {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) := by
  obtain ⟨EA, rfl, C, hn⟩ := Ann.annEnvA_of_envWfT_semPrefix hW hP
  exact hasTyT_iota_srTU C hn hC hΓ hd hlhs

/-- THE UNION-EVIDENCE CONSUMER: ι subject reduction over `DerivedIotaU` — the
    legacy `.ofU` arm rides premise-free `hasTyT_iota_sr` (S6's route); the
    `.ofUS` arm rides `hasTyT_iota_srTU` on `CorrCertsBelowU`. -/
theorem iotaPreserveTU {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) (hC : CorrCertsBelowU E)
    {lhs rhs T : Expr Nat}
    (hd : DerivedIotaU E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) := by
  obtain ⟨EA, rfl, C, hn⟩ := Ann.annEnvA_of_envWfT_semPrefix hW hP
  match hd with
  | .ofU w => exact Ann.hasTyT_iota_sr C hn hΓ (.of w) hlhs
  | .ofUS w => exact hasTyT_iota_srTU C hn hC hΓ (.of w) hlhs

end Rcic.Declarative

#print axioms Rcic.Declarative.wDrMkS
#print axioms Rcic.Declarative.pin_iotaWitnessSAnnB_wDrMkS
#print axioms Rcic.Declarative.not_envCorrAnnCert_drEnv
#print axioms Rcic.Declarative.not_envCorrAnnCert_of_envWfT
#print axioms Rcic.Declarative.CorrCertsBelowU
#print axioms Rcic.Declarative.corrCertsBelowU_of_below
#print axioms Rcic.Declarative.corrCertsBelowU_of_ann
#print axioms Rcic.Declarative.corrCertsBelowU_annCert
#print axioms Rcic.Declarative.hasTyT_iota_srTU
#print axioms Rcic.Declarative.iotaPreserveTTU
#print axioms Rcic.Declarative.iotaPreserveTU

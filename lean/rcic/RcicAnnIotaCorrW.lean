import rcic.RcicAnnIotaCorrD
import rcic.RcicWitnessFuelStable

/-!
# S4 — the witness-fuel arm (`W`-arm): the universal `.ann` discharge, retried

cc LAND #6624, ruling **R5a**: *run the D-arm's normalization at the witness's
own `w.fuel`, the budget under which admission's analyses succeeded;
DT-024T-witness's monotonicity and uniqueness (#6570) make verdicts stable
above it.  R5b only if the universal proof needs a witness-independent bound.*

The S3 counterexample (`fgEnv`, `RcicFuelGapPins` — batch 17) showed the only
remaining hole in the δ-arm was its BUDGET: `domsFuelBound` bounds whnf by the
stored domains' own size, while the witness's semantic analysis
(`IotaWitnessS.hshapes`/`hschema`) already succeeded at `w.fuel`.  Running
`telWhnfDom`/`drecFragCheck` at `w.fuel` makes the recognizer's normalization
budget the same quantity the analyses were pinned at — `whnfFuel_mono` then
lifts every verdict `fieldAnalyze` produced into the recognizer's walk, and
`IotaWitnessS.analysis_agree` pins uniqueness.

## Contents

- `iotaWitnessSAnnDArmW` — the D-arm with `w.fuel` as the normalization budget.
- `iotaWitnessSAnnDW` — `iotaWitnessSAnnB || iotaWitnessSAnnDArmW` (a strict
  superset of `iotaWitnessSAnnDB`: the W-arm subsumes the `domsFuelBound` arm
  whenever `domsFuelBound ≤ w.fuel`, and in any case the union is `||`).
- `EnvCorrAnnDW` / `CorrCertsBelowDW` — the per-env certificate and the union.
- `NormCorrDW` — the `NormCorrD` analogue at `w.fuel`-normalized telescopes.
- Consumers: `iotaFnA_of_witnessS_drecW`, `iotaAnnotatesADW_of_envWfA`,
  `hasTyT_iota_srTDW`, `iotaPreserveTTDW`, `iotaPreserveTDW`.
- Pins: `wDrMkD` passes the W-arm at `drEnv`; the S6 frec witness still fails
  the W-union (the `.recursive (_+1)` shape still demands the direct fragment,
  fuel-independent).

`closure_claim` stays 0.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the witness-fuel δ-arm -/

/-- THE W-ARM of the annotation recognizer: `iotaWitnessSAnnDArm` with the
    witness's own `fuel` as the normalization budget — the same bound under
    which `w.hshapes`/`w.hschema` pinned the semantic analysis. -/
def iotaWitnessSAnnDArmW (E : ResolvedEnv) (w : IotaWitnessS E) : Bool :=
  drecFragCheck E w.fuel
      w.familyRef w.famMember.arity w.nparams w.nindices w.nparams
      (w.ctorDoms.drop w.nparams) w.shapes &&
  match applyTel (w.preMajor.take w.nparams)
      (instantiateLevels (w.ls.take w.ctorMember.arity) w.ctorMember.mtype) with
  | some ctorAfter =>
      fieldsTelS w.fields w.shapes (telWhnfDom E w.fuel ctorAfter) &&
      match w.preMajor[w.nparams + 1 + w.ctorIdx]? with
      | some minor =>
          decide (iotaRhsOfS w =
            foldApps minor (rhsArgsS (.const w.recRef w.ls) w.preMajor
              w.nparams w.nMinors w.fields w.shapes
              (telWhnfDom E w.fuel ctorAfter)))
      | none => false
  | none => false

/-- THE W-UNION recognizer: direct fragment OR the witness-fuel δ-arm. -/
def iotaWitnessSAnnDW (E : ResolvedEnv) (w : IotaWitnessS E) : Bool :=
  iotaWitnessSAnnB E w || iotaWitnessSAnnDArmW E w

/-- the per-env W certificate: every shape-based witness passes the W-union. -/
def EnvCorrAnnDW (E : ResolvedEnv) : Prop :=
  ∀ w : IotaWitnessS E, iotaWitnessSAnnDW E w = true

/-- the union counterpart at the W-mode: the sealed hereditary certificates OR
    the W-arm per-env certificate. -/
def CorrCertsBelowDW (E : ResolvedEnv) : Prop :=
  CorrCertsBelow E ∨ EnvCorrAnnDW E

/-- the extended recognizer implies the W-union (the `domsFuelBound` arm feeds
    it whenever `domsFuelBound ≤ w.fuel`; `directFragCheck_mono` lifts the
    fragment part, and the normalized-telescope conjuncts are monotone in the
    whnf budget — but the cheap route is simply: `annB` already implies `annDW`). -/
theorem iotaWitnessSAnnB_imp_annDW {E : ResolvedEnv} {w : IotaWitnessS E}
    (h : iotaWitnessSAnnB E w = true) : iotaWitnessSAnnDW E w = true := by
  unfold iotaWitnessSAnnDW
  rw [h]
  rfl

theorem envCorrAnnDW_of_annCert {E : ResolvedEnv} (h : EnvCorrAnnCert E) :
    EnvCorrAnnDW E :=
  fun w => iotaWitnessSAnnB_imp_annDW (h w)

/-- the union's common payoff. -/
theorem corrCertsBelowDW_annDW {E : ResolvedEnv} (h : CorrCertsBelowDW E) :
    EnvCorrAnnDW E :=
  h.elim (fun hC => envCorrAnnDW_of_annCert (hC _ (envSub_refl _)).2) id

/-- `iotaWitnessSAnnDArmW` decomposed, mirroring `iotaWitnessSAnnDArm_parts`. -/
theorem iotaWitnessSAnnDArmW_parts {E : ResolvedEnv} {w : IotaWitnessS E}
    (h : iotaWitnessSAnnDArmW E w = true) :
    drecFragCheck E w.fuel
        w.familyRef w.famMember.arity w.nparams w.nindices w.nparams
        (w.ctorDoms.drop w.nparams) w.shapes = true ∧
    ∃ (ctorAfter minor : Expr Nat),
      applyTel (w.preMajor.take w.nparams)
        (instantiateLevels (w.ls.take w.ctorMember.arity) w.ctorMember.mtype) =
          some ctorAfter ∧
      fieldsTelS w.fields w.shapes
        (telWhnfDom E w.fuel ctorAfter) = true ∧
      w.preMajor[w.nparams + 1 + w.ctorIdx]? = some minor ∧
      iotaRhsOfS w = foldApps minor
        (rhsArgsS (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
          w.fields w.shapes (telWhnfDom E w.fuel ctorAfter)) := by
  unfold iotaWitnessSAnnDArmW at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hfrag, hrest⟩ := h
  refine ⟨hfrag, ?_⟩
  cases ha : applyTel (w.preMajor.take w.nparams)
      (instantiateLevels (w.ls.take w.ctorMember.arity) w.ctorMember.mtype) with
  | none => rw [ha] at hrest; exact Bool.noConfusion hrest
  | some ctorAfter =>
      rw [ha] at hrest
      simp only at hrest
      rw [Bool.and_eq_true] at hrest
      obtain ⟨hwalk, hrest⟩ := hrest
      cases hm : w.preMajor[w.nparams + 1 + w.ctorIdx]? with
      | none => rw [hm] at hrest; exact Bool.noConfusion hrest
      | some minor =>
          rw [hm] at hrest
          simp only at hrest
          exact ⟨ctorAfter, minor, rfl, hwalk, rfl, of_decide_eq_true hrest⟩

/-! ## (2) the `.drecD` premise at witness fuel and the ann-side consumer -/

/-- `NormCorrD` at `w.fuel`: the normed member's parameter-application erases
    to the `w.fuel`-normalized stored telescope. -/
def NormCorrDW (EA : ResolvedEnvA) {E : ResolvedEnv} (w : IotaWitnessS E) :
    Prop :=
  ∀ cm : CheckedMemberA, EA.members w.ctorRef = some cm →
    cm.mclass = .constructorM →
    piCountA (cm.normA.getD cm.mtypeA) = w.nparams + w.fields.length ∧
    ctorShapesA w.familyRef w.nparams (cm.normA.getD cm.mtypeA) =
      some w.shapes ∧
    ∀ args : List ExprA, args.map erase = w.preMajor.take w.nparams →
      ∃ ctorAfterA,
        applyTelA args
          (instantiateLevelsA (w.ls.take w.ctorMember.arity)
            (cm.normA.getD cm.mtypeA)) = some ctorAfterA ∧
        ∀ ctorAfterE,
          applyTel (w.preMajor.take w.nparams)
            (instantiateLevels (w.ls.take w.ctorMember.arity)
              w.ctorMember.mtype) = some ctorAfterE →
          erase ctorAfterA = telWhnfDom E w.fuel ctorAfterE

/-- the W-arm ann-side reduct: `iotaFnA_of_witnessS_drec` with the
    `w.fuel`-normalized telescope. -/
theorem iotaFnA_of_witnessS_drecW {EA : ResolvedEnvA}
    (w : IotaWitnessS (eraseEnv EA)) (hB : iotaWitnessSAnnDArmW (eraseEnv EA) w = true)
    (hL : ∀ cm, EA.members w.ctorRef = some cm → cm.arity ≤ w.ls.length)
    (hND : NormCorrDW EA w)
    {e : ExprA} (he : erase e = iotaLhsOfS w) :
    ∃ e', iotaFnA EA e = some e' ∧ erase e' = iotaRhsOfS w := by
  obtain ⟨hfragD, ctorAfterE, minorE, happE, hwalkE, hminE', hrhsE⟩ :=
    iotaWitnessSAnnDArmW_parts hB
  obtain ⟨recA, hrA, hrE⟩ := members_of_eraseEnv w.hrec
  obtain ⟨ctorA, hcA, hcE⟩ := members_of_eraseEnv w.hctor
  obtain ⟨famA, hfA, hfE⟩ := members_of_eraseEnv w.hfam
  have hg := iotaGroupA_of_witnessS w hrA hrE hcA hcE hfA hfE
  have hsp : appsSpine (erase e) = (.const w.recRef w.ls,
      w.preMajor ++ [foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)]) := by
    rw [he]
    unfold iotaLhsOfS recCall
    rw [appsSpine_foldApps]
    rfl
  obtain ⟨argsA, hargsA, hmap⟩ := appsSpineA_of_erase_const hsp
  obtain ⟨preA, majL, rfl, hpre, hmaj⟩ := map_erase_eq_append hmap
  obtain ⟨majA, rfl, hmajE⟩ := map_erase_eq_singleton hmaj
  have hs := recSpineA_of_spine hargsA
  have hmsp : appsSpine (erase majA) =
      (.const w.ctorRef w.lsC, w.ctorParams ++ w.fields) := by
    rw [hmajE, appsSpine_foldApps]
    rfl
  obtain ⟨margsA, hmargsA, hmmap⟩ := appsSpineA_of_erase_const hmsp
  have hc : spineHeadRefA majA = some w.ctorRef := spineHeadRefA_of_const (by rw [hmargsA])
  rw [iotaFnA_of_layers hs hc hg]
  have hcT : erase ctorA.mtypeA = w.ctorMember.mtype := by rw [← hcE]; rfl
  have hrT : erase recA.mtypeA = w.recMember.mtype := by rw [← hrE]; rfl
  have hcar : ctorA.arity ≤ w.ls.length := hL ctorA hcA
  have hcar' : ctorA.arity = w.ctorMember.arity := by rw [← hcE]; rfl
  have hrar : recA.arity = w.recMember.arity := by rw [← hrE]; rfl
  have hprelen : preA.length = w.preMajor.length := by rw [← hpre, List.length_map]
  have hmlen : margsA.length = w.ctorParams.length + w.fields.length := by
    rw [← List.length_append, ← hmmap, List.length_map]
  have hcnt : piCountA ctorA.mtypeA = w.nparams + w.fields.length := by
    rw [← piCountA_erase, hcT, ← w.hnpar]
  have hrcnt : piCountA recA.mtypeA = w.nparams + 1 + w.nMinors + w.nindices + 1 := by
    rw [← piCountA_erase, hrT, w.hnmin]
  obtain ⟨hcntN, hshapesN, happD⟩ := hND ctorA hcA (by rw [← w.hctorK, ← hcE]; rfl)
  obtain ⟨minorA, hminA, hminEA⟩ := getElem?_map_erase hpre hminE'
  have hpreT : (preA.take w.nparams).map erase = w.preMajor.take w.nparams := by
    rw [List.map_take, hpre]
  obtain ⟨ctorAfterA, hcaA0, hcaED⟩ := happD (preA.take w.nparams) hpreT
  rw [← hcar'] at hcaA0
  have hcaA : applyTelA (preA.take w.nparams)
      (instantiateLevelsA (w.ls.take ctorA.arity)
        (ctorA.normA.getD ctorA.mtypeA)) = some ctorAfterA :=
    hcaA0
  have hcaE : erase ctorAfterA =
      telWhnfDom (eraseEnv EA) w.fuel ctorAfterE :=
    hcaED ctorAfterE happE
  have hfieldsA : (margsA.drop w.nparams).map erase = w.fields := by
    rw [List.map_drop, hmmap, ← w.hctorParams, List.drop_left]
  have hwalk : fieldsTelA (margsA.drop w.nparams) w.shapes ctorAfterA = true := by
    rw [fieldsTelA_erase, hfieldsA, hcaE]
    exact hwalkE
  have hcond : w.ctorRef = w.ctorRef ∧ preA.length + 1 = piCountA recA.mtypeA ∧
      w.ls.length = recA.arity ∧
      (appsSpineA majA).2.length = piCountA (ctorA.normA.getD ctorA.mtypeA) ∧
      ctorA.arity ≤ w.ls.length := by
    refine ⟨rfl, ?_, ?_, ?_, hcar⟩
    · rw [hprelen, w.hpre, hrcnt]
    · rw [hrar, w.hlsLen]
    · rw [hmargsA]
      show margsA.length = _
      rw [hmlen, w.hctorParams, hcntN]
  refine ⟨foldAppsA minorA (rhsArgsA (.const w.recRef w.ls) preA w.nparams w.nMinors
    (margsA.drop w.nparams) w.shapes ctorAfterA), ?_, ?_⟩
  · unfold iotaReductA
    simp only [hc, Option.some_bind]
    rw [if_pos ⟨trivial, hcond.2⟩]
    simp only [hshapesN, Option.some_bind, hminA, hcaA, hmargsA, hwalk, if_true]
  · rw [foldAppsA_erase, rhsArgsA_eraseS, hminEA, hpre, hfieldsA, hcaE]
    exact hrhsE.symm

/-- ANNOTATION AT ι, W-mode. -/
theorem iotaAnnotatesADW_of_envWfA {I : IotaIfaceA} {EA : ResolvedEnvA}
    (hW : EnvWfA I EA)
    (hsel : ∀ w : IotaWitnessS (eraseEnv EA),
      (iotaWitnessSAnnB (eraseEnv EA) w = true →
        ∀ cm, EA.members w.ctorRef = some cm → cm.mclass = .constructorM →
          ∀ T, cm.normA = some T → erase T = erase cm.mtypeA) ∧
      (iotaWitnessSAnnDArmW (eraseEnv EA) w = true → NormCorrDW EA w))
    (hC : EnvCorrAnnDW (eraseEnv EA)) : IotaAnnotatesA EA :=
  fun e rhs hd => by
    obtain ⟨w, hl, hr⟩ := derivedIotaT_unpack hd
    subst hr
    have hB := hC w
    unfold iotaWitnessSAnnDW at hB
    rw [Bool.or_eq_true] at hB
    obtain ⟨hselB, hselD⟩ := hsel w
    cases hB with
    | inl hAnn =>
        exact iotaFnA_of_witnessS w hAnn
          (fun cm h => witness_ctor_arityS hW w h)
          (fun cm hcm => hselB hAnn cm hcm) hl
    | inr hD =>
        exact iotaFnA_of_witnessS_drecW w hD
          (fun cm h => witness_ctor_arityS hW w h) (hselD hD) hl

/-- ι SUBJECT REDUCTION, W-union form. -/
theorem hasTyT_iota_srTDW (C : AnnEnvA E) (hn : EnvNormEraseA E)
    (hselD : ∀ w : IotaWitnessS (eraseEnv E),
      iotaWitnessSAnnDArmW (eraseEnv E) w = true → NormCorrDW E w)
    (hC : CorrCertsBelowDW (eraseEnv E))
    {Γ : LCtx} (hΓ : CtxWfT (eraseEnv E) n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT (eraseEnv E) lhs rhs)
    (hlhs : HasTyT (eraseEnv E) n Γ lhs T) :
    Nonempty (HasTyT (eraseEnv E) n Γ rhs T) := by
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfT' C hn hΓ
  obtain ⟨eA, TA, he, hT, ⟨tA⟩⟩ := annHasTyT' C hn hlhs hΓA hctx
  subst he
  obtain ⟨hW⟩ := C.wf
  have hsel : ∀ w : IotaWitnessS (eraseEnv E),
      (iotaWitnessSAnnB (eraseEnv E) w = true →
        ∀ cm, E.members w.ctorRef = some cm → cm.mclass = .constructorM →
          ∀ T, cm.normA = some T → erase T = erase cm.mtypeA) ∧
      (iotaWitnessSAnnDArmW (eraseEnv E) w = true → NormCorrDW E w) :=
    fun w => ⟨fun _ cm hcm hcl T hT => hn _ _ hcm hcl _ hT, hselD w⟩
  obtain ⟨e', hfn, he'⟩ := iotaAnnotatesADW_of_envWfA hW hsel
    (corrCertsBelowDW_annDW hC) _ _ hd
  obtain ⟨t'⟩ := iotaSRA_ty C hΓA hfn tA
  obtain ⟨hT'⟩ := hasTyT_of_hasTyA hW (C.hNS hn) t'
  rw [he', hT, hctx] at hT'
  exact ⟨hT'⟩

/-- TYPED-ROUTE UNION SIBLING (S4): `iotaPreserveTT` against
    `CorrCertsBelowDW` + the W-arm selector premise. -/
theorem iotaPreserveTTDW {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (hselD : ∀ EA : ResolvedEnvA, ∀ _C : AnnEnvA EA, eraseEnv EA = E →
      ∀ w : IotaWitnessS E, iotaWitnessSAnnDArmW E w = true → NormCorrDW EA w)
    (hC : CorrCertsBelowDW E)
    {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_semPrefix hW hP
  exact hasTyT_iota_srTDW C hn (fun w hD => hselD EA C rfl w hD) hC hΓ hd hlhs

/-- the `DerivedIotaU` cover, W-mode. -/
theorem iotaPreserveTDW {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (hselD : ∀ EA : ResolvedEnvA, ∀ _C : AnnEnvA EA, eraseEnv EA = E →
      ∀ w : IotaWitnessS E, iotaWitnessSAnnDArmW E w = true → NormCorrDW EA w)
    (hC : CorrCertsBelowDW E)
    {lhs rhs T : Expr Nat}
    (hd : DerivedIotaU E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_semPrefix hW hP
  match hd with
  | .ofU w => exact hasTyT_iota_sr C hn hΓ (.of w) hlhs
  | .ofUS w =>
      exact hasTyT_iota_srTDW C hn (fun w hD => hselD EA C rfl w hD) hC hΓ
        (.of w) hlhs

/-! ## (3) pins -/

/-- `wDrMkD` passes the W-arm at `drEnv` (fuel 8 ≥ the `Id` chain's δ-depth). -/
theorem pin_iotaWitnessSAnnDW_wDrMkD :
    iotaWitnessSAnnDW drEnv wDrMkD = true := by
  decide

/-- the S6 gate is fuel-independent: the function-recursive witness at `wEnv`
    still fails the W-union — `.recursive (_+1)` demands the direct fragment
    at EVERY fuel. -/
theorem pin_iotaWitnessSAnnDW_wIotaWitnessS_frec :
    iotaWitnessSAnnDW wEnv wIotaWitnessS = false := by
  decide

end Rcic.Declarative.Ann

import rcic.RcicAnnIotaCorr
import rcic.RcicAnnIotaSR
import rcic.RcicDTMetaTypedSR
import rcic.RcicDerivedIotaU
import rcic.RcicTypedDeltaRecPins
import rcic.RcicTypedFunRecIotaPins
import rcic.RcicIotaShapeStable
import rcic.RcicAnnDeltaPin

/-!
# S2 — `CorrCertsBelowDU`: the δ-transparent recursive-field mode (cc LAND #6598)

S1 (`RcicAnnIotaCorrU`) refuted the universal `.ann` discharge at `drEnv`:
`iotaWitnessSAnnB drEnv wDrMkS = false`.  S2 measures the failure precisely and
closes the mode.

## The measurement (ι-SR at `drEnv` holds — the certificate was the gap)

`pin_iotaSR_drEnv_lhs`/`pin_iotaSR_drEnv_rhs`: at the canonical equation
context `drIotaCtx` and the equation type `drEqTy`, BOTH the redex
`F.rec P m (mk x)` (`iotaLhsOfS wDrMkD`) and the reduct `drSchema`
(`minor x (rec P m x)`) type in `HasTyT` — the conversion checker `tyAtC`
produces the judgments directly.  ι subject reduction is TRUE at `drEnv`.

`iotaWitnessSAnnB` fails on TWO conjuncts, not one:

1. `directFragCheck`'s `noTransparentB` rejects `Id F`'s transparent head —
   measured in S1.
2. **The decided schema/RHS agreement also fails.**  `rhsArgsS` walks the
   STORED constructor telescope `Π (x : Id F), F`; `recCallField` extracts
   `familyIdx 0 (Id F) = [F]` — the stored spine's argument `F` — and emits
   `rec P m F x` (four arguments — the pre-step-0 reading).  `iotaOpenRhs`'s
   semantic analysis reaches `F` THROUGH `Id`'s transparent body and emits
   `rec P m x` — the equation the conversion checker actually types
   (`drIota_needs_conversion`).  The erased-side syntactic walk cannot see
   through δ; the normed ann-side type `Π (x : F), F` (the member's `normA`,
   `drCtorMemberA_normA`) is what `iotaReductA` actually reads, and on it
   `familyIdx 0 F = []` — the schema agrees.

So the `.ann` recognizer must run its telescope walk on the **δ-normalized**
domains — the erased counterpart of `FieldA.drecD`'s `.norm` (`.drecD` fields
record the surface domain; their `.norm` is the family application that
`ctorTypeA` rebuilds, `drFieldA_norm`).  `telWhnfDom` is that erased-side
normalizer: `whnfFuel` on each Π-domain — `whnfFuel drEnv 5 (Id F) = some F`.

## Contents

- `telWhnfDom`, `drecFieldCheck`/`drecFragCheck` — the erased-side pieces.
- `iotaWitnessSAnnDArm` — the δ-arm: per-field, the direct fragment OR a
  non-function-recursive semantic shape (`.recursive (_+1)` still requires the
  direct fragment, which frec fields cannot satisfy — the S6 gate is kept),
  plus the applyTel/`fieldsTelS`/schema-RHS checks on the NORMALIZED telescope.
- `iotaWitnessSAnnDB := iotaWitnessSAnnB || iotaWitnessSAnnDArm` — the extended
  recognizer, a strict super-set (`envCorrAnnDU_of_annCert`).
- `EnvCorrAnnDU`, `CorrCertsBelowDU` — the arm and the union.
- `NormCorrD` — the per-witness `.drecD` evidence the ann-side consumer needs
  where the D-arm carried the check: the member's `normA`-residing type has
  the same Π-count and `ctorShapesA` reading as the witness's semantic shapes,
  and its erased parameter-application equals the whnf-normalized stored
  telescope (R-NoDeltaRec-4d-iii's `ctorMemberA` invariant).
- `iotaFnA_of_witnessS_drec`, `iotaAnnotatesADU_of_envWfA`,
  `hasTyT_iota_srTDU`, `iotaPreserveTTDU`, `iotaPreserveTDU` — the consumers.
- `wDrMkD`, `pin_iotaWitnessSAnnDB_wDrMkD`, `pin_iotaWitnessSAnnDB_wIotaWitnessS`
  (the frec gate preserved), `envCorrAnnDU_drEnv`, `pin_iotaSR_drEnv`.

`closure_claim` stays 0.  The D-arm's ann-side payoff is conditional on
`NormCorrD` — at a `.drecD` member the erased environment cannot see `normA`,
so the agreement is carried as an explicit premise, discharged by the
group-admission evidence where it holds.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the erased-side telescope normalizer -/

/-- Whnf-normalize every Π-domain of a telescope — the erased-side shadow of
    the `.drecD` norm (`FieldA.norm`): a field whose domain is a
    δ-transparent application (`Id F`) reads, through the copy's `normA`, as
    its whnf (`F`).  Domains that do not whnf are kept — the walk degrades to
    the stored reading, matching `normA = none` members. -/
def telWhnfDom (E : ResolvedEnv) (fuel : Nat) : Expr Nat → Expr Nat
  | .pi A B => .pi ((whnfFuel E fuel A).getD A) (telWhnfDom E fuel B)
  | T => T

/-- `telWhnfDom` at the normalized dr telescope: `Π (x : Id F), F` normalizes
    to `Π (x : F), F` — the erased counterpart of `drFieldA.norm = .drec []`. -/
theorem telWhnfDom_drMk :
    telWhnfDom drEnv (domsFuelBound [drField]) drMkMember.mtype =
      .pi (.const 1 []) (.const 1 []) := by
  decide

/-! ## (2) the δ-permissive per-field check -/

/-- Per-field fragment check, δ-permissive: the DIRECT fragment
    (`directFragOne` — rigid head, whnf-stable tail, canonical family shape)
    OR a semantic shape that is not function-recursive.  A `.recursive 0`
    field reached only through δ (a `.drecD` field — the typed analyzer's
    verdict, carried by `w.hshapes`) is admitted; a `.recursive (_+1)` field
    still demands the direct fragment, which no frec field satisfies — the S6
    gate is preserved structurally. -/
def drecFieldCheck (E : ResolvedEnv)
    (fuel fam nuniv nparams nindices depth : Nat) (T : Expr Nat) :
    FieldShape → Bool
  | .recursive (_ + 1) => directFragOne E fuel fam nuniv nparams nindices depth T
  | _ => directFragOne E fuel fam nuniv nparams nindices depth T || true

/-- The paired check over the post-parameter domains and the witness's
    certified semantic shapes (`w.hshapes` pairs them pointwise). -/
def drecFragCheck (E : ResolvedEnv)
    (fuel fam nuniv nparams nindices depth : Nat) :
    List (Expr Nat) → List FieldShape → Bool
  | [], _ => true
  | T :: Ts, s :: ss =>
      drecFieldCheck E fuel fam nuniv nparams nindices depth T s &&
      drecFragCheck E fuel fam nuniv nparams nindices (depth + 1) Ts ss
  | _, _ => false

/-! ## (3) the extended recognizer -/

/-- THE δ-ARM of the annotation recognizer: the per-field δ-permissive
    fragment check, then the parameter application, field-telescope guard and
    decided schema/RHS agreement on the **whnf-normalized** telescope — the
    erased-side shadow of the copy's `normA.getD` reading
    (R-NoDeltaRec-4d-iii). -/
def iotaWitnessSAnnDArm (E : ResolvedEnv) (w : IotaWitnessS E) : Bool :=
  drecFragCheck E (domsFuelBound (w.ctorDoms.drop w.nparams))
      w.familyRef w.famMember.arity w.nparams w.nindices w.nparams
      (w.ctorDoms.drop w.nparams) w.shapes &&
  match applyTel (w.preMajor.take w.nparams)
      (instantiateLevels (w.ls.take w.ctorMember.arity) w.ctorMember.mtype) with
  | some ctorAfter =>
      fieldsTelS w.fields w.shapes
        (telWhnfDom E (domsFuelBound (w.ctorDoms.drop w.nparams)) ctorAfter) &&
      match w.preMajor[w.nparams + 1 + w.ctorIdx]? with
      | some minor =>
          decide (iotaRhsOfS w =
            foldApps minor (rhsArgsS (.const w.recRef w.ls) w.preMajor
              w.nparams w.nMinors w.fields w.shapes
              (telWhnfDom E (domsFuelBound (w.ctorDoms.drop w.nparams)) ctorAfter)))
      | none => false
  | none => false

/-- THE EXTENDED `.ann` RECOGNIZER: `iotaWitnessSAnnB` (the direct fragment on
    the stored telescope) OR the δ-arm (the δ-permissive fragment on the
    normalized telescope). -/
def iotaWitnessSAnnDB (E : ResolvedEnv) (w : IotaWitnessS E) : Bool :=
  iotaWitnessSAnnB E w || iotaWitnessSAnnDArm E w

/-- the union's ANNOTATION certificate: every shape-based witness passes the
    extended recognizer. -/
def EnvCorrAnnDU (E : ResolvedEnv) : Prop :=
  ∀ w : IotaWitnessS E, iotaWitnessSAnnDB E w = true

/-- the union counterpart at the δ-mode: the sealed hereditary certificates OR
    the extended per-env annotation certificate. -/
def CorrCertsBelowDU (E : ResolvedEnv) : Prop :=
  CorrCertsBelow E ∨ EnvCorrAnnDU E

/-- the extended recognizer strictly extends the direct one. -/
theorem iotaWitnessSAnnB_imp_annDB {E : ResolvedEnv} {w : IotaWitnessS E}
    (h : iotaWitnessSAnnB E w = true) : iotaWitnessSAnnDB E w = true := by
  unfold iotaWitnessSAnnDB
  rw [h]
  rfl

/-- the sealed `.ann` certificate implies the extended one. -/
theorem envCorrAnnDU_of_annCert {E : ResolvedEnv} (h : EnvCorrAnnCert E) :
    EnvCorrAnnDU E :=
  fun w => iotaWitnessSAnnB_imp_annDB (h w)

/-- the union's common payoff: both arms yield the extended `.ann`
    certificate — `.below` at `envSub_refl` + `envCorrAnnDU_of_annCert`,
    `.annDU` directly. -/
theorem corrCertsBelowDU_annDU {E : ResolvedEnv} (h : CorrCertsBelowDU E) :
    EnvCorrAnnDU E :=
  h.elim (fun hC => envCorrAnnDU_of_annCert (hC _ (envSub_refl _)).2) id

/-- `iotaWitnessSAnnDArm` decomposed: the pointwise δ-permissive fragment, the
    parameter application, the normalized field-telescope guard, the minor,
    and the decided schema/`rhsArgsS` agreement at the NORMALIZED telescope. -/
theorem iotaWitnessSAnnDArm_parts {E : ResolvedEnv} {w : IotaWitnessS E}
    (h : iotaWitnessSAnnDArm E w = true) :
    drecFragCheck E (domsFuelBound (w.ctorDoms.drop w.nparams))
        w.familyRef w.famMember.arity w.nparams w.nindices w.nparams
        (w.ctorDoms.drop w.nparams) w.shapes = true ∧
    ∃ (ctorAfter minor : Expr Nat),
      applyTel (w.preMajor.take w.nparams)
        (instantiateLevels (w.ls.take w.ctorMember.arity) w.ctorMember.mtype) =
          some ctorAfter ∧
      fieldsTelS w.fields w.shapes
        (telWhnfDom E (domsFuelBound (w.ctorDoms.drop w.nparams)) ctorAfter) =
          true ∧
      w.preMajor[w.nparams + 1 + w.ctorIdx]? = some minor ∧
      iotaRhsOfS w = foldApps minor
        (rhsArgsS (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
          w.fields w.shapes
          (telWhnfDom E (domsFuelBound (w.ctorDoms.drop w.nparams)) ctorAfter)) := by
  unfold iotaWitnessSAnnDArm at h
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

/-! ## (4) the `.drecD` evidence premise and the ann-side consumer -/

/-- THE `.drecD` EVIDENCE a witness's constructor member must carry where the
    δ-arm (not the direct fragment) justified the field: the member's
    `normA`-residing type has the same Π-spine length as the stored type's
    field count says, reads the witness's semantic shapes through
    `ctorShapesA` (the `.drecD → .recursive 0` reading), and its erased
    parameter-application is exactly the whnf-normalized stored telescope the
    recognizer walked (the `ctorMemberA`/`FieldA.norm` invariant, erased).
    `EnvNormEraseA` implies the first conjunct vacuously fails for genuine
    `.drecD` members; this premise is what remains provable there — and it is
    discharged by the group-admission's `GroupCtorA` view evidence where the
    member is `ctorMemberA`-built. -/
def NormCorrD (EA : ResolvedEnvA) {E : ResolvedEnv} (w : IotaWitnessS E) :
    Prop :=
  ∀ cm : CheckedMemberA, EA.members w.ctorRef = some cm →
    cm.mclass = .constructorM →
    piCountA (cm.normA.getD cm.mtypeA) = w.nparams + w.fields.length ∧
    ctorShapesA w.familyRef w.nparams (cm.normA.getD cm.mtypeA) =
      some w.shapes ∧
    ∀ args : List ExprA, args.map erase = w.preMajor.take w.nparams →
      ∃ T', applyTelA args
          (instantiateLevelsA (w.ls.take w.ctorMember.arity)
            (cm.normA.getD cm.mtypeA)) = some T' ∧
        ∀ T₀, applyTel (w.preMajor.take w.nparams)
            (instantiateLevels (w.ls.take w.ctorMember.arity)
              w.ctorMember.mtype) = some T₀ →
          erase T' = telWhnfDom E
            (domsFuelBound (w.ctorDoms.drop w.nparams)) T₀

/-- ANNOTATION AT ι, the δ-recursive route: `iotaFnA_of_witnessS` with the
    `EnvNormEraseA` premise replaced by the per-member `.drecD` evidence.  At
    a `.drecD` member the stored and normed types genuinely diverge
    (`drCtorMemberA_diverge`), so the erased-side checks are run on the
    normalized telescope (`telWhnfDom`) and the member's `normA` supplies the
    ann-side reading — exactly what `iotaReductA`'s `ctorShapesA`/
    `applyTelA`/`fieldsTelA`/`rhsArgsA` consume. -/
theorem iotaFnA_of_witnessS_drec {EA : ResolvedEnvA}
    (w : IotaWitnessS (eraseEnv EA)) (hB : iotaWitnessSAnnDArm (eraseEnv EA) w = true)
    (hL : ∀ cm, EA.members w.ctorRef = some cm → cm.arity ≤ w.ls.length)
    (hND : NormCorrD EA w)
    {e : ExprA} (he : erase e = iotaLhsOfS w) :
    ∃ e', iotaFnA EA e = some e' ∧ erase e' = iotaRhsOfS w := by
  obtain ⟨hfragD, ctorAfterE, minorE, happE, hwalkE, hminE', hrhsE⟩ :=
    iotaWitnessSAnnDArm_parts hB
  obtain ⟨recA, hrA, hrE⟩ := members_of_eraseEnv w.hrec
  obtain ⟨ctorA, hcA, hcE⟩ := members_of_eraseEnv w.hctor
  obtain ⟨famA, hfA, hfE⟩ := members_of_eraseEnv w.hfam
  have hg := iotaGroupA_of_witnessS w hrA hrE hcA hcE hfA hfE
  -- the spine
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
  -- the major
  have hmsp : appsSpine (erase majA) =
      (.const w.ctorRef w.lsC, w.ctorParams ++ w.fields) := by
    rw [hmajE, appsSpine_foldApps]
    rfl
  obtain ⟨margsA, hmargsA, hmmap⟩ := appsSpineA_of_erase_const hmsp
  have hc : spineHeadRefA majA = some w.ctorRef := spineHeadRefA_of_const (by rw [hmargsA])
  rw [iotaFnA_of_layers hs hc hg]
  -- the reduct's checks
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
  -- the `.drecD` evidence: the normed type's Π-count and shape read
  obtain ⟨hcntN, hshapesN, happD⟩ := hND ctorA hcA (by rw [← w.hctorK, ← hcE]; rfl)
  -- the minor
  obtain ⟨minorA, hminA, hminEA⟩ := getElem?_map_erase hpre hminE'
  -- the normed parameter application, whose erasure is the whnf-normalized
  -- stored telescope `ctorAfterD`
  have hpreT : (preA.take w.nparams).map erase = w.preMajor.take w.nparams := by
    rw [List.map_take, hpre]
  obtain ⟨ctorAfterA, hcaA0, hcaED⟩ := happD (preA.take w.nparams) hpreT
  rw [← hcar'] at hcaA0
  have hcaA : applyTelA (preA.take w.nparams)
      (instantiateLevelsA (w.ls.take ctorA.arity)
        (ctorA.normA.getD ctorA.mtypeA)) = some ctorAfterA :=
    hcaA0
  have hcaE : erase ctorAfterA =
      telWhnfDom (eraseEnv EA) (domsFuelBound (w.ctorDoms.drop w.nparams))
        ctorAfterE :=
    hcaED ctorAfterE happE
  -- the fields
  have hfieldsA : (margsA.drop w.nparams).map erase = w.fields := by
    rw [List.map_drop, hmmap, ← w.hctorParams, List.drop_left]
  have hwalk : fieldsTelA (margsA.drop w.nparams) w.shapes ctorAfterA = true := by
    rw [fieldsTelA_erase, hfieldsA, hcaE]
    exact hwalkE
  -- assemble
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

/-- ANNOTATION AT ι, the typed landing, δ-mode: under the copy's admission,
    the per-witness selector (`annB`-witnesses keep the `EnvNormEraseA`
    member agreement; δ-arm-witnesses carry `NormCorrD`), and the extended
    certificate. -/
theorem iotaAnnotatesADU_of_envWfA {I : IotaIfaceA} {EA : ResolvedEnvA}
    (hW : EnvWfA I EA)
    (hsel : ∀ w : IotaWitnessS (eraseEnv EA),
      (iotaWitnessSAnnB (eraseEnv EA) w = true →
        ∀ cm, EA.members w.ctorRef = some cm → cm.mclass = .constructorM →
          ∀ T, cm.normA = some T → erase T = erase cm.mtypeA) ∧
      (iotaWitnessSAnnDArm (eraseEnv EA) w = true → NormCorrD EA w))
    (hC : EnvCorrAnnDU (eraseEnv EA)) : IotaAnnotatesA EA :=
  fun e rhs hd => by
    obtain ⟨w, hl, hr⟩ := derivedIotaT_unpack hd
    subst hr
    have hB := hC w
    unfold iotaWitnessSAnnDB at hB
    rw [Bool.or_eq_true] at hB
    obtain ⟨hselB, hselD⟩ := hsel w
    cases hB with
    | inl hAnn =>
        exact iotaFnA_of_witnessS w hAnn
          (fun cm h => witness_ctor_arityS hW w h)
          (fun cm hcm => hselB hAnn cm hcm) hl
    | inr hD =>
        exact iotaFnA_of_witnessS_drec w hD
          (fun cm h => witness_ctor_arityS hW w h) (hselD hD) hl

/-! ## (5) the consumers -/

/-- ι SUBJECT REDUCTION AT THE SHAPE-BASED EVIDENCE, δ-union form:
    `hasTyT_iota_srT`'s proof shape with `CorrCertsBelowDU` and the per-witness
    `.drecD` selector.  `hn : EnvNormEraseA` still pays the annotation
    apparatus (`annCtxWfT'`, `annHasTyT'`, `C.hNS`) and every `annB`-routed
    witness; `hselD` pays only the δ-arm witnesses. -/
theorem hasTyT_iota_srTDU (C : AnnEnvA E) (hn : EnvNormEraseA E)
    (hselD : ∀ w : IotaWitnessS (eraseEnv E),
      iotaWitnessSAnnDArm (eraseEnv E) w = true → NormCorrD E w)
    (hC : CorrCertsBelowDU (eraseEnv E))
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
      (iotaWitnessSAnnDArm (eraseEnv E) w = true → NormCorrD E w) :=
    fun w => ⟨fun _ cm hcm hcl T hT => hn _ _ hcm hcl _ hT, hselD w⟩
  obtain ⟨e', hfn, he'⟩ := iotaAnnotatesADU_of_envWfA hW hsel
    (corrCertsBelowDU_annDU hC) _ _ hd
  obtain ⟨t'⟩ := iotaSRA_ty C hΓA hfn tA
  obtain ⟨hT'⟩ := hasTyT_of_hasTyA hW (C.hNS hn) t'
  rw [he', hT, hctx] at hT'
  exact ⟨hT'⟩

/-- TYPED-ROUTE UNION SIBLING (S2): `iotaPreserveTT` against
    `CorrCertsBelowDU` + the δ-arm selector premise. -/
theorem iotaPreserveTTDU {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (hselD : ∀ EA : ResolvedEnvA, ∀ _C : AnnEnvA EA, eraseEnv EA = E →
      ∀ w : IotaWitnessS E, iotaWitnessSAnnDArm E w = true → NormCorrD EA w)
    (hC : CorrCertsBelowDU E)
    {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_semPrefix hW hP
  exact hasTyT_iota_srTDU C hn (fun w hD => hselD EA C rfl w hD) hC hΓ hd hlhs

/-- THE UNION-EVIDENCE CONSUMER, δ-mode: ι subject reduction over
    `DerivedIotaU` — the legacy `.ofU` arm rides premise-free
    `hasTyT_iota_sr`; the `.ofUS` arm rides `hasTyT_iota_srTDU`. -/
theorem iotaPreserveTDU {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (hselD : ∀ EA : ResolvedEnvA, ∀ _C : AnnEnvA EA, eraseEnv EA = E →
      ∀ w : IotaWitnessS E, iotaWitnessSAnnDArm E w = true → NormCorrD EA w)
    (hC : CorrCertsBelowDU E)
    {lhs rhs T : Expr Nat}
    (hd : DerivedIotaU E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_semPrefix hW hP
  match hd with
  | .ofU w => exact hasTyT_iota_sr C hn hΓ (.of w) hlhs
  | .ofUS w =>
      exact hasTyT_iota_srTDU C hn (fun w hD => hselD EA C rfl w hD) hC hΓ
        (.of w) hlhs

/-! ## (6) the drEnv measurements -/

/-- the canonical `IotaWitnessS` at `F.rec`/`mk` over `drEnv` — S1's `wDrMkS`
    construction, re-pinned on this branch's namespace (the S1 module lands in
    the same batch; this copy keeps S2 self-contained). -/
def wDrMkD : IotaWitnessS drEnv where
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

/-- ι SUBJECT REDUCTION HOLDS AT `drEnv`: the redex `F.rec P m (mk x)` and the
    reduct `minor x (rec P m x)` are both typed at the equation's type
    `drEqTy` in `HasTyT` — `tyAtC` produces both judgments by the conversion
    checker.  The `.ann` certificate was the only failure; the step itself is
    sound. -/
theorem drIotaSR_lhs :
    Nonempty (HasTyT drEnv 1 drIotaCtx (iotaLhsOfS wDrMkD) drEqTy) :=
  ⟨tyAtC drEnv 1 8 drIotaCtx (iotaLhsOfS wDrMkD) drEqTy |>.get (by rfl)⟩

theorem drIotaSR_rhs :
    Nonempty (HasTyT drEnv 1 drIotaCtx drSchema drEqTy) :=
  ⟨tyAtC drEnv 1 8 drIotaCtx drSchema drEqTy |>.get (by rfl)⟩

/-- the extended recognizer accepts the drEnv witness: the `.drecD` field's
    non-frec semantic shape passes `drecFragCheck`, and the normalized
    telescope `Π (x : F), F` walks to the semantic schema — BOTH of
    `iotaWitnessSAnnB`'s drEnv failures close. -/
theorem pin_iotaWitnessSAnnDB_wDrMkD :
    iotaWitnessSAnnDB drEnv wDrMkD = true := by decide

/-- the frec gate is preserved: the S6 witness's `.recursive 1` field still
    fails the δ-arm — the extension only admits non-frec semantic shapes. -/
theorem pin_iotaWitnessSAnnDB_wIotaWitnessS_frec :
    iotaWitnessSAnnDB wEnv wIotaWitnessS = false := by decide

/-- `List.length = 2` unpacks to a pair (matched on a variable — the
    constructive `List.rec`; `obtain`-`match` on a projection goes through
    classical generalization). `List.length_eq_one` covers the singleton case
    in core. -/
theorem list_pair_of_length_two {α : Type} {xs : List α}
    (h : xs.length = 2) : ∃ a b, xs = [a, b] := by
  match xs with
  | [] => simp at h
  | [a] => simp at h
  | [a, b] => exact ⟨a, b, rfl⟩
  | a :: b :: c :: _ => simp at h

/-- `drEnv`'s member table: membership pins ref AND member. -/
theorem drEnv_members {r : Nat} {m : CheckedMember}
    (h : drEnv.members r = some m) :
    (r = 0 ∧ m = drIdMember) ∨ (r = 1 ∧ m = drFamMember) ∨
      (r = 2 ∧ m = drMkMember) ∨ (r = 3 ∧ m = drRecMember) := by
  match r with
  | 0 =>
      left
      rw [show drEnv.members 0 = some drIdMember from rfl] at h
      exact ⟨rfl, (Option.some.inj h).symm⟩
  | 1 =>
      right; left
      rw [show drEnv.members 1 = some drFamMember from rfl] at h
      exact ⟨rfl, (Option.some.inj h).symm⟩
  | 2 =>
      right; right; left
      rw [show drEnv.members 2 = some drMkMember from rfl] at h
      exact ⟨rfl, (Option.some.inj h).symm⟩
  | 3 =>
      right; right; right
      rw [show drEnv.members 3 = some drRecMember from rfl] at h
      exact ⟨rfl, (Option.some.inj h).symm⟩
  | r + 4 =>
      rw [show drEnv.members (r + 4) = none from rfl] at h
      exact Option.noConfusion h

/-- `EnvCorrAnnDU drEnv`: every shape witness of `drEnv` passes the extended
    recognizer — the union's right arm now holds at the env that refuted
    `EnvCorrAnnCert`.  The refs pin every witness to the `F`/`mk`/`F.rec`
    triple; `hshapes`/`hschema` then force the same `.recursive 0` reading and
    `drSchema` as `wDrMkD`, and the δ-arm's normalized-telescope walk
    reproduces it for arbitrary `preMajor`/`fields`/`ls`. -/
theorem envCorrAnnDU_drEnv : EnvCorrAnnDU drEnv := by
  intro w
  have hfam : w.familyRef = 1 ∧ w.famMember = drFamMember := by
    obtain (⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩) :=
      drEnv_members w.hfam
    · exact absurd (hm ▸ w.hfamK) (by decide)
    · exact ⟨hr, hm⟩
    · exact absurd (hm ▸ w.hfamK) (by decide)
    · exact absurd (hm ▸ w.hfamK) (by decide)
  have hctor : w.ctorRef = 2 ∧ w.ctorMember = drMkMember := by
    obtain (⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩) :=
      drEnv_members w.hctor
    · exact absurd (hm ▸ w.hctorK) (by decide)
    · exact absurd (hm ▸ w.hctorK) (by decide)
    · exact ⟨hr, hm⟩
    · exact absurd (hm ▸ w.hctorK) (by decide)
  have hrec : w.recRef = 3 ∧ w.recMember = drRecMember := by
    obtain (⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩) :=
      drEnv_members w.hrec
    · exact absurd (hm ▸ w.hrecK) (by decide)
    · exact absurd (hm ▸ w.hrecK) (by decide)
    · exact absurd (hm ▸ w.hrecK) (by decide)
    · exact ⟨hr, hm⟩
  obtain ⟨hfR, hfM⟩ := hfam
  obtain ⟨hcR, hcM⟩ := hctor
  obtain ⟨hrR, hrM⟩ := hrec
  have hnp : w.nparams = 0 := by
    have h := w.hnidx
    rw [hfM] at h
    have hp : piCount drFamMember.mtype = 0 := rfl
    rw [hp] at h
    omega
  have hni : w.nindices = 0 := by
    have h := w.hnidx
    rw [hfM] at h
    have hp : piCount drFamMember.mtype = 0 := rfl
    rw [hp] at h
    omega
  have hnM : w.nMinors = 1 := by
    have h := w.hrecIdx
    rw [hrR, hfR] at h
    omega
  have hci : w.ctorIdx = 0 := by
    have h := w.hctorIdx
    rw [hcR, hfR] at h
    omega
  have hfl : w.fields.length = 1 := by
    have h := w.hnpar
    rw [hcM] at h
    have hp : piCount drMkMember.mtype = 1 := rfl
    rw [hp] at h
    omega
  have hcd : w.ctorDoms = [drField] ∧ w.ctorResult = .const 1 [] := by
    have h := w.hpeel
    rw [hcM, hnp, hfl] at h
    have hp : peelPis (0 + 1) drMkMember.mtype = some ([drField], .const 1 []) := rfl
    rw [hp] at h
    exact ⟨(congrArg Prod.fst (Option.some.inj h)).symm,
      (congrArg Prod.snd (Option.some.inj h)).symm⟩
  obtain ⟨pa, pb, hpm'⟩ := list_pair_of_length_two (by
    have h := w.hpre
    rw [hnp, hnM, hni] at h
    exact h)
  have hcp : w.ctorParams = [] := by
    have h := w.hctorParams
    rw [hnp] at h
    exact List.length_eq_zero.mp h
  obtain ⟨f, hfl'⟩ := List.length_eq_one.mp hfl
  obtain ⟨l, hls'⟩ := List.length_eq_one.mp (by
    have h := w.hlsLen
    rw [hrM] at h
    have ha : drRecMember.arity = 1 := rfl
    rw [ha] at h
    exact h)
  have hsh : w.shapes = [.recursive 0] := by
    have h := w.hshapes
    rw [hfR, hfM, hnp, hni, hcd.1, List.drop_zero] at h
    have hconc : fieldShapesFuel drEnv 8 1 drFamMember.arity 0 0 0 [drField] =
        some [.recursive 0] := wDrMkD.hshapes
    exact fieldShapesFuel_agree drEnv h hconc
  have hsc : w.schema = drSchema := by
    have h := w.hschema
    rw [hrR, hrM, hnp, hnM, hni, hci, hfl, hcd.1, hcd.2, hsh] at h
    have hconc : iotaOpenRhs drEnv 8 (.const 3 (canonRecLevels drRecMember.arity))
        (.bvar (1 + 0 + (1 - 1 - 0))) (preMajorBvars 0 1 0 1) 0 1
        [.recursive 0] (fieldBvars 1)
        (lift 0 (1 + 1 + 1 + 0) (ctorFieldTelRaw 0 [drField] (.const 1 []))) =
          some drSchema := wDrMkD.hschema
    exact iotaOpenRhs_agree drEnv h hconc
  -- the recognizer: the δ-arm computes for arbitrary pa/pb/f/l
  show iotaWitnessSAnnDB drEnv w = true
  unfold iotaWitnessSAnnDB
  rw [Bool.or_eq_true]
  right
  unfold iotaWitnessSAnnDArm
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- drecFragCheck on [drField] × [.recursive 0]: non-frec → true
    rw [hfM, hnp, hni, hcd.1, List.drop_zero, hsh]
    rfl
  · -- the tail: applyTel on stored, then the normalized walk
    have happ : applyTel (w.preMajor.take w.nparams)
        (instantiateLevels (w.ls.take drMkMember.arity) drMkMember.mtype) =
        some drMkMember.mtype := by
      rw [hnp, hpm']
      show applyTel ([pa, pb].take 0)
          (instantiateLevels (w.ls.take drMkMember.arity) drMkMember.mtype) =
            some drMkMember.mtype
      rw [List.take_zero]
      have har0 : drMkMember.arity = 0 := rfl
      rw [har0, List.take_zero]
      rfl
    rw [hcM]
    rw [happ]
    simp only
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · -- fieldsTelS [f] [.recursive 0] (Π (x : F), F)
      rw [hfl', hsh, hnp, hcd.1, List.drop_zero, telWhnfDom_drMk]
      rfl
    · -- the minor is preMajor[1] = pb
      have hmin' : w.preMajor[w.nparams + 1 + w.ctorIdx]? = some pb := by
        rw [hnp, hci, hpm']; rfl
      rw [hmin']
      simp only
      rw [decide_eq_true_eq]
      rw [hrR, hpm', hnp, hnM, hfl', hsh, hcd.1, List.drop_zero, telWhnfDom_drMk]
      -- the normalized walk's rhsArgsS is `[f, rec pa pb f]`
      have hrhs : rhsArgsS (.const 3 [l]) [pa, pb] 0 1 [f] [.recursive 0]
          (.pi (.const 1 []) (.const 1 [])) =
          [f, foldApps (.const 3 [l]) [pa, pb, f]] := by
        simp only [rhsArgsS, recCallsS, recCallField, recPrefix, familyIdx,
          List.take, List.drop, List.append_nil, List.cons_append,
          List.nil_append]
        rfl
      rw [hls', hrhs]
      -- iotaRhsOfS: instPrefix over [pa,pb,f] of the [l]-instantiated schema
      unfold iotaRhsOfS
      rw [hpm', hfl', hsc, hls']
      have hIL : instantiateLevels [l] drSchema =
          .app (.app (.bvar 1) (.bvar 0))
            (foldApps (.const 3 [l]) [.bvar 2, .bvar 1, .bvar 0]) := rfl
      rw [hIL]
      show instPrefix [pa, pb, f] (foldApps (.bvar 1)
          [.bvar 0, foldApps (.const 3 [l]) [.bvar 2, .bvar 1, .bvar 0]]) =
        foldApps pb [f, foldApps (.const 3 [l]) [pa, pb, f]]
      rw [instPrefix_foldApps]
      simp only [List.map_cons, List.map_nil]
      rw [instPrefix_bvar_lt (j := 1) (a := pb) (by simp) rfl]
      rw [instPrefix_foldApps]
      simp only [List.map_cons, List.map_nil]
      rw [instPrefix_bvar_lt (j := 0) (a := f) (by simp) rfl,
        instPrefix_const [pa, pb, f] 3 [l],
        instPrefix_bvar_lt (j := 2) (a := pa) (by simp) rfl,
        instPrefix_bvar_lt (j := 1) (a := pb) (by simp) rfl]

end Rcic.Declarative.Ann

import rcic.RcicAnnIotaCorrUA
import rcic.RcicIotaFunRecCorrR

/-!
# R-NoFunRec S6-5 — the frec-aware annotation certificate

`EnvCorrAnnCert`'s recognizer `iotaWitnessSAnnB` carries `directFragCheck` as
conjunct (i): the DIRECT fragment (`DirectFieldFrag`) on the constructor's
post-parameter field domains.  That fragment is a SUFFICIENT CONDITION for
what the annotation direction actually owes — the `fieldShapesE`/
`fieldShapesFuel` agreement `ctorShapesA_of_witnessS` consumes — and its
`noInner` clause (`piCount T = 0 ∨ the Π-tail is not a proper family
application`) refuses exactly the `.recursive (k+1)` domains: every
function-recursive field.  On a frec environment `EnvCorrAnnCert` is therefore
uninhabited even though the erased-side shape analysis already agrees.

This module adds the frec-aware path under new names (nothing landed is
touched): `iotaWitnessSAnnBF` replaces conjunct (i) by a DECIDED check of the
obligation itself — `fieldShapesE w.familyRef (w.ctorDoms.drop w.nparams) =
some w.shapes` — the same discipline conjunct (iii) already applies to the
schema/RHS agreement (checked by `decide`, never assumed).  The fragment is a
strict extension: `envCorrAnnCertF_of_envCorrAnnCert` composes the landed
certificate into the new one, so every environment the old recognizer
certified stays certified.

## Contents

- `iotaWitnessSAnnBF`, `iotaWitnessSAnnBF_parts` — the recognizer and its
  decomposition.
- `EnvCorrAnnCertF` — the frec-aware annotation certificate.
- `envCorrAnnCertF_of_envCorrAnnCert` — the strict-extension composition.
- `ctorShapesA_of_witnessSF` — `ctorShapesA` agreement directly from the
  decided `fieldShapesE` read (the `DirectFieldFrag` detour was only ever a
  means to this).
- `iotaFnA_of_witnessSF` — `iotaFnA_of_witnessS` at the frec-aware
  recognizer.
- `iotaAnnotatesA_of_envWfAF`, `iotaAnnotatesUA_of_envWfAF` — the annotation
  payoffs at the typed root and the union face.
- `iotaCorrTUA_frecRA` — the full union correspondence on a frec-gated
  environment: `ann` through `EnvCorrAnnCertF`, `eraseT` through
  `iotaErasesTUA_frecR`.

`closure_claim` stays 0.
-/

namespace Rcic.Declarative.Ann

/-- THE FREC-AWARE ANNOTATION RECOGNIZER — `iotaWitnessSAnnB` with the DIRECT
    fragment replaced by a decided check of the obligation itself: the
    erased-side syntactic field analysis `fieldShapesE` returns the witness's
    stored shapes.  On the DIRECT fragment this conjunct is implied by
    `directFragCheck` (through `fieldShapesE_of_fieldShapesFuel_directFrag`),
    so the recognizer accepts every witness the landed one does — while also
    accepting `.recursive (k+1)` domains where the two analyses genuinely
    agree.  Conjuncts (ii) (parameter application + field-telescope guard)
    and (iii) (decided schema/`rhsArgsS` agreement) are unchanged. -/
def iotaWitnessSAnnBF (E : ResolvedEnv) (w : IotaWitnessS E) : Bool :=
  decide (fieldShapesE w.familyRef (w.ctorDoms.drop w.nparams) = some w.shapes) &&
  match applyTel (w.preMajor.take w.nparams)
      (instantiateLevels (w.ls.take w.ctorMember.arity) w.ctorMember.mtype) with
  | some ctorAfter =>
      fieldsTelS w.fields w.shapes ctorAfter &&
      match w.preMajor[w.nparams + 1 + w.ctorIdx]? with
      | some minor =>
          decide (iotaRhsOfS w =
            foldApps minor (rhsArgsS (.const w.recRef w.ls) w.preMajor
              w.nparams w.nMinors w.fields w.shapes ctorAfter))
      | none => false
  | none => false

/-- `iotaWitnessSAnnBF` decomposed: the decided `fieldShapesE` agreement, the
    parameter application, the field-telescope guard, the minor, and the
    decided schema/`rhsArgsS` agreement. -/
theorem iotaWitnessSAnnBF_parts {E : ResolvedEnv} {w : IotaWitnessS E}
    (h : iotaWitnessSAnnBF E w = true) :
    (fieldShapesE w.familyRef (w.ctorDoms.drop w.nparams) = some w.shapes) ∧
    ∃ (ctorAfter minor : Expr Nat),
      applyTel (w.preMajor.take w.nparams)
        (instantiateLevels (w.ls.take w.ctorMember.arity) w.ctorMember.mtype) =
          some ctorAfter ∧
      fieldsTelS w.fields w.shapes ctorAfter = true ∧
      w.preMajor[w.nparams + 1 + w.ctorIdx]? = some minor ∧
      iotaRhsOfS w = foldApps minor
        (rhsArgsS (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
          w.fields w.shapes ctorAfter) := by
  unfold iotaWitnessSAnnBF at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hfrag, hrest⟩ := h
  refine ⟨of_decide_eq_true hfrag, ?_⟩
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

/-- FREC-AWARE ANNOTATION certificate: every shape-based witness of the erased
    environment passes `iotaWitnessSAnnBF` — the decided `fieldShapesE`
    agreement on its constructor's field domains, the parameter application
    and field guard, and the decided schema/RHS agreement.  Strictly weaker
    than `EnvCorrAnnCert`: everything the DIRECT fragment certified is still
    certified (`envCorrAnnCertF_of_envCorrAnnCert`), and function-recursive
    domains — where `fieldShapesE` still agrees — are newly covered. -/
def EnvCorrAnnCertF (E : ResolvedEnv) : Prop :=
  ∀ w : IotaWitnessS E, iotaWitnessSAnnBF E w = true

/-- The strict extension: the landed DIRECT-fragment certificate composes into
    the frec-aware one — `fieldShapesE_of_witnessS` is exactly the decided
    conjunct. -/
theorem envCorrAnnCertF_of_envCorrAnnCert {E : ResolvedEnv}
    (hC : EnvCorrAnnCert E) : EnvCorrAnnCertF E := by
  intro w
  unfold iotaWitnessSAnnBF
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [decide_eq_true_eq]
    exact fieldShapesE_of_witnessS hC w
  · have hB := (iotaWitnessSAnnB_parts (hC w)).2
    obtain ⟨ctorAfter, minor, happE, hwalkE, hminE, hrhsE⟩ := hB
    rw [happE]
    simp only
    rw [Bool.and_eq_true]
    refine ⟨hwalkE, ?_⟩
    rw [hminE]
    simp only
    rw [decide_eq_true_eq]
    exact hrhsE

/-- `ctorShapesA` at the copy's read, from the decided `fieldShapesE`
    agreement directly — `ctorShapesA_of_witnessS` minus the `DirectFieldFrag`
    detour. -/
theorem ctorShapesA_of_witnessSF {EA : ResolvedEnvA}
    (w : IotaWitnessS (eraseEnv EA))
    (hfe : fieldShapesE w.familyRef (w.ctorDoms.drop w.nparams) = some w.shapes)
    {ctorA : CheckedMemberA} (hcE : eraseMember ctorA = w.ctorMember) :
    ctorShapesA w.familyRef w.nparams ctorA.mtypeA = some w.shapes := by
  have hcmT : erase ctorA.mtypeA = w.ctorMember.mtype := congrArg CheckedMember.mtype hcE
  have hcnt : piCountA ctorA.mtypeA = w.nparams + w.fields.length := by
    rw [← piCountA_erase, hcmT, ← w.hnpar]
  have hpeel := piDomsA_erase_peelPis ctorA.mtypeA
  rw [hcnt, hcmT, w.hpeel] at hpeel
  have hdoms : (piDomsA ctorA.mtypeA).map erase = w.ctorDoms :=
    (Prod.ext_iff.mp (Option.some.inj hpeel).symm).1
  unfold ctorShapesA
  rw [List.map_drop, hdoms]
  exact hfe

/-- ANNOTATION AT ι, the typed witness, at the frec-aware recognizer: a
    shape-based `IotaWitnessS` of the erased environment certified by
    `iotaWitnessSAnnBF` makes the copy's ι fire on every annotation of its
    left-hand side.  Same premises as `iotaFnA_of_witnessS`; the only
    difference is where the `ctorShapesA` agreement comes from — the decided
    `fieldShapesE` read instead of the DIRECT fragment. -/
theorem iotaFnA_of_witnessSF {EA : ResolvedEnvA}
    (w : IotaWitnessS (eraseEnv EA)) (hB : iotaWitnessSAnnBF (eraseEnv EA) w = true)
    (hL : ∀ cm, EA.members w.ctorRef = some cm → cm.arity ≤ w.ls.length)
    (hN : ∀ cm, EA.members w.ctorRef = some cm → cm.mclass = .constructorM →
      ∀ T, cm.normA = some T → erase T = erase cm.mtypeA)
    {e : ExprA} (he : erase e = iotaLhsOfS w) :
    ∃ e', iotaFnA EA e = some e' ∧ erase e' = iotaRhsOfS w := by
  obtain ⟨hfe, ctorAfterE, minorE, happE, hwalkE, hminE', hrhsE⟩ :=
    iotaWitnessSAnnBF_parts hB
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
  -- the shapes, through erasure and the decided agreement
  have hshapes : ctorShapesA w.familyRef w.nparams ctorA.mtypeA = some w.shapes :=
    ctorShapesA_of_witnessSF w hfe hcE
  -- the minor
  obtain ⟨minorA, hminA, hminEA⟩ := getElem?_map_erase hpre hminE'
  -- the constructor member's `normA`, when it carries one, erases to the stored type
  -- (`EnvNormEraseA` at the constructor — R-NoDeltaRec-4d-iii); the ι reads go through
  -- erasure, so they agree with the witness's tree-side counts
  have hNE : erase (ctorA.normA.getD ctorA.mtypeA) = erase ctorA.mtypeA := by
    cases hNm : ctorA.normA with
    | none => rfl
    | some T => exact hN ctorA hcA (by rw [← w.hctorK, ← hcE]; rfl) T hNm
  have hcntN : piCountA (ctorA.normA.getD ctorA.mtypeA) = w.nparams + w.fields.length := by
    rw [← piCountA_erase, hNE, piCountA_erase, hcnt]
  have hshapesN : ctorShapesA w.familyRef w.nparams (ctorA.normA.getD ctorA.mtypeA) =
      some w.shapes := (ctorShapesA_of_erase hNE).trans hshapes
  -- the constructor telescope after the parameters, at the constructor-side levels
  have happ := applyTelA_erase (preA.take w.nparams)
    (instantiateLevelsA (w.ls.take ctorA.arity) (ctorA.normA.getD ctorA.mtypeA))
  rw [List.map_take, hpre, erase_instantiateLevelsA, hNE, hcT] at happ
  rw [← hcar'] at happE
  rw [happE] at happ
  obtain ⟨ctorAfterA, hcaA, hcaE⟩ : ∃ T, applyTelA (preA.take w.nparams)
      (instantiateLevelsA (w.ls.take ctorA.arity) (ctorA.normA.getD ctorA.mtypeA)) = some T ∧
      erase T = ctorAfterE := by
    cases h : applyTelA (preA.take w.nparams)
        (instantiateLevelsA (w.ls.take ctorA.arity) (ctorA.normA.getD ctorA.mtypeA)) with
    | none => rw [h] at happ; exact Option.noConfusion happ
    | some T =>
        rw [h] at happ
        exact ⟨T, rfl, Option.some.inj happ⟩
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

/-- ANNOTATION AT ι, the typed landing, at the frec-aware certificate: under
    the copy's admission and `EnvCorrAnnCertF`, a shape-based derived ι step
    of the erased environment on an erased left-hand side fires the copy's ι
    with the reduct erasing to the witness's right-hand side. -/
theorem iotaAnnotatesA_of_envWfAF {I : IotaIfaceA} {EA : ResolvedEnvA}
    (hW : EnvWfA I EA) (hn : EnvNormEraseA EA) (hC : EnvCorrAnnCertF (eraseEnv EA)) :
    IotaAnnotatesA EA :=
  fun e rhs hd => by
    obtain ⟨w, hl, hr⟩ := derivedIotaT_unpack hd
    subst hr
    exact iotaFnA_of_witnessSF w (hC w) (fun cm h => witness_ctor_arityS hW w h)
      (fun cm hcm => hn _ _ hcm) hl

/-- The annotation direction at the union face, frec-aware: `EnvNoFunA` does
    not appear — `ann` never needed it — and the `.ofU` arm still upgrades
    through the erasure certificate (`EnvCorrEraseCert`, unchanged). -/
theorem iotaAnnotatesUA_of_envWfAF {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (hn : EnvNormEraseA EA) (hCe : EnvCorrEraseCert (eraseEnv EA))
    (hCa : EnvCorrAnnCertF (eraseEnv EA)) : IotaAnnotatesUA EA := by
  intro e rhs hu
  obtain u | t := derivedIotaU_elim hu
  · obtain ⟨t⟩ := derivedIotaT_of_derivedIota hCe u
    exact iotaAnnotatesA_of_envWfAF hW hn hCa e rhs t
  · exact iotaAnnotatesA_of_envWfAF hW hn hCa e rhs t

/-- THE FULL UNION ι-CORRESPONDENCE on a frec-gated environment, with the
    annotation certificate frec-aware: `ann` composes `EnvCorrAnnCertF`, and
    `eraseT` is the reduct-gated `.ofUS` arm.  This is `iotaCorrTUA_frecR`
    with the honest `.ann` gate — on a frec environment `EnvCorrAnnCert` is
    refuted (the DIRECT fragment's no-inner-escape clause), while
    `EnvCorrAnnCertF` is inhabited wherever the erased-side shape analysis
    genuinely agrees. -/
theorem iotaCorrTUA_frecRA {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (hn : EnvNormEraseA EA) (hT : EnvWfT (eraseEnv EA)) (fuel : Nat)
    (hCe : EnvCorrEraseCert (eraseEnv EA)) (hCa : EnvCorrAnnCertF (eraseEnv EA))
    (hgate : ∀ (e e' : ExprA) (s : RecSpineA) (c : Nat) (g : IotaGroupA),
      recSpineA e = some s → spineHeadRefA s.major = some c →
      iotaGroupA EA s.recRef c = some g → iotaReductA s g = some e' →
      FrecFiringGates EA fuel s g) :
    IotaCorrTUA EA where
  ann := iotaAnnotatesUA_of_envWfAF hW hn hCe hCa
  eraseT := iotaErasesTUA_frecR hW hn hT fuel hgate

#print axioms iotaWitnessSAnnBF_parts
#print axioms envCorrAnnCertF_of_envCorrAnnCert
#print axioms iotaFnA_of_witnessSF
#print axioms iotaAnnotatesUA_of_envWfAF
#print axioms iotaCorrTUA_frecRA

end Rcic.Declarative.Ann

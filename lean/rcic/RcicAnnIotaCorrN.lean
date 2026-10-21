import rcic.RcicAnnIotaCorr

/-!
# R-NoDeltaRec class (b) — the ι correspondence at the NORMED constructor type

`RcicAnnIotaCorr` proves the copy↔tree ι correspondence under `EnvNormEraseA` — every
constructor member's `normA`, when it carries one, erases to its stored type. At a genuine
`.drecD` member that premise is FALSE (`drCtorMemberA_diverge`, `RcicAnnDeltaPin`): the
normed type reads the δ-reached domain as the family application while the stored type keeps
its surface form, so `erase (normA.getD mtypeA) ≠ erase mtypeA`. The wall is not in the copy —
`iotaReductA` already reads `normA.getD` — but in the WITNESS: `IotaWitness` peels and counts
the STORED type. This module restates the witness on the normalized type and re-proves both
directions of the correspondence WITHOUT `EnvNormEraseA` (route-C rule: a false statement is
restated under a new name, never assumed).

`memberNormTy`/`memberNormTyA` are the re-keyed erased reads the package asks for:
`erase (m.normA.getD m.mtypeA)`. `IotaWitnessN` is `IotaWitness` with the constructor-side
counts, peel, closedness and `applyTel` keyed on `memberNormTy`; the recursor and family stay
erased members of `eraseEnv`. Both directions then go through with no norm-erasure premise:

* `iotaFnA_of_derivedIotaN` (annotation): the `.drecD` wall's direction — the copy's ι reads
  the normed type already, so a witness keyed on it makes `iotaFnA` fire with no hypothesis.
* `derivedIotaN_of_iotaFnA` (erasure): `iotaReductA_inv` hands back the normed reads, which
  are exactly what the witness wants — `hNE` is never needed.

`IotaCorrN` bundles the two as an environment property, derived from `EnvWfA` + `EnvNoFunA`
alone (`iotaCorrN_of_envWfA`). This is the load-bearing premise of the D-keyed typed
judgment (`RcicTypedJD`) and of `annConvTD` (`RcicAnnAnnotateD`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- the member's NORMALIZED type: `normA.getD mtypeA`, the read the copy's ι machinery takes
    (`iotaReductA`'s `ctorShapesA`/`applyTelA`, `iotaReductA_inv`). At a `.drecD`-free member
    this is the stored type; at a `.drecD` member it is the view-built constructor type
    (`GroupCtorA.normA_getD`). `@[reducible]` so the re-keyed witness fields `rw`-match the
    literal `normA.getD` forms the readers produce. -/
@[reducible] def memberNormTyA (m : CheckedMemberA) : ExprA := m.normA.getD m.mtypeA

/-- the re-keyed erased read: the member's normalized type, erased (R-NoDeltaRec class (b)).
    `analyzeFields`, `peelPis`, `piCount`, `applyTel` and `lift`-closedness all consume this
    instead of `erase m.mtypeA`. -/
@[reducible] def memberNormTy (m : CheckedMemberA) : Expr Nat := erase (memberNormTyA m)

/-! ## (1) the witness at the normalized constructor type -/

/-- the ι witness, constructor side re-keyed on the normalized type (`memberNormTy ctorMember`)
    and membership read on the ANNOTATED environment. Recursor and family stay `CheckedMember`
    of the erased environment: the group-layer reads (`iotaGroupA`, `groupCountsA`) take the
    recursor's and the family's stored type, which are what the copy's `piDomsA`/`piBodyA`
    calls see — the `.drecD` divergence lives in the constructor only. -/
structure IotaWitnessN (EA : ResolvedEnvA) : Type where
  recRef : Nat
  ctorRef : Nat
  ls : List Level
  lsC : List Level
  recMember : CheckedMember
  ctorMember : CheckedMemberA
  hrec : (eraseEnv EA).members recRef = some recMember
  hctor : EA.members ctorRef = some ctorMember
  hrecK : recMember.mclass = MemberClass.recursorM
  hctorK : ctorMember.mclass = MemberClass.constructorM
  preMajor : List (Expr Nat)
  fields : List (Expr Nat)
  ctorParams : List (Expr Nat)
  kinds : List RecKind
  minor : Expr Nat
  hlen : kinds.length = fields.length
  familyRef : Nat
  famMember : CheckedMember
  hfam : (eraseEnv EA).members familyRef = some famMember
  hfamK : famMember.mclass = MemberClass.inductiveM
  nparams : Nat
  nindices : Nat
  nMinors : Nat
  ctorIdx : Nat
  hctorParams : ctorParams.length = nparams
  /-- RE-KEYED: the constructor's Π-count is read on the normalized type. -/
  hnpar : nparams + fields.length = piCount (memberNormTy ctorMember)
  hnidx : nparams + nindices = piCount famMember.mtype
  hnmin : nparams + 1 + nMinors + nindices + 1 = piCount recMember.mtype
  hidx : ctorIdx < nMinors
  hctorIdx : ctorRef = familyRef + 1 + ctorIdx
  hrecIdx : recRef = familyRef + 1 + nMinors
  hpre : preMajor.length = nparams + 1 + nMinors + nindices
  hminor : preMajor[nparams + 1 + ctorIdx]? = some minor
  ctorDoms : List (Expr Nat)
  ctorResult : Expr Nat
  /-- RE-KEYED: the peel is off the normalized type (at `.drecD` the stored peel does not even
      see the family's recursive domain — `drCtorShapesA_none`). -/
  hpeel : peelPis (nparams + fields.length) (memberNormTy ctorMember) =
      some (ctorDoms, ctorResult)
  hfamApp : isFamilyApp familyRef ctorResult = true
  hkinds : analyzeFields familyRef (ctorDoms.drop nparams) = some kinds
  recDoms : List (Expr Nat)
  recBody : Expr Nat
  hpeelRec : peelPis (nparams + 1 + nMinors + nindices + 1) recMember.mtype =
      some (recDoms, recBody)
  hrecBody : recBody =
      foldApps (.bvar (nMinors + nindices + 1))
        ((List.range nindices).reverse.map (fun i => Expr.bvar (i + 1)) ++
          [Expr.bvar 0])
  hmajorTy : recDoms[nparams + 1 + nMinors + nindices]? = some
      (foldApps (.const familyRef ((List.range famMember.arity).map Level.param))
        ((List.range nparams).reverse.map
          (fun i => Expr.bvar (i + nindices + nMinors + 1)) ++
          (List.range nindices).reverse.map (fun i => Expr.bvar i)))
  hrecClosed : lift 0 1 recMember.mtype = recMember.mtype
  /-- RE-KEYED: the closedness the witness transports is the normalized type's
      (`GroupCtorA.normA_getD_closed` supplies it). -/
  hctorClosed : lift 0 1 (memberNormTy ctorMember) = memberNormTy ctorMember
  hlsLen : ls.length = recMember.arity
  ctorAfterParams : Expr Nat
  /-- RE-KEYED: the stored-type view is of the normalized type (`instantiateLevelsA` agrees
      with it on the annotated side, so `applyTelA_erase` transports directly). -/
  hctorAfter : applyTel (preMajor.take nparams)
      (instantiateLevels ls (memberNormTy ctorMember)) = some ctorAfterParams
  hctorTel : isPiTel kinds.length ctorAfterParams = true
  hfamTel : directRecConstHead kinds ctorAfterParams = true
  hresTel : resultConstHead kinds ctorAfterParams = true

/-- 05 §14 major: `ctor_j params fields` — spine form as `IotaWitness`'s. -/
def ctorSpineN {EA : ResolvedEnvA} (w : IotaWitnessN EA) : List (Expr Nat) :=
  w.ctorParams ++ w.fields

def ctorMajorN {EA : ResolvedEnvA} (w : IotaWitnessN EA) : Expr Nat :=
  foldApps (.const w.ctorRef w.lsC) (ctorSpineN w)

def iotaLhsOfN {EA : ResolvedEnvA} (w : IotaWitnessN EA) : Expr Nat :=
  recCall (.const w.recRef w.ls) w.preMajor (ctorMajorN w)

def iotaRhsOfN {EA : ResolvedEnvA} (w : IotaWitnessN EA) : Expr Nat :=
  foldApps w.minor
    (rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
      w.fields w.kinds w.ctorAfterParams)

/-- 05 §11–12 / 02 §9 ι at the normalized constructor type: lhs a derived recursor applied to
    a constructor-headed major; rhs the §12-selected minor application. At a `.drecD`-free
    member this is `DerivedIota` (`memberNormTy` is the stored type there); at a `.drecD`
    member it is inhabited where `DerivedIota` is not (`drCtorMemberA_diverge`). -/
inductive DerivedIotaN (EA : ResolvedEnvA) : Expr Nat → Expr Nat → Type
  | of (w : IotaWitnessN EA) : DerivedIotaN EA (iotaLhsOfN w) (iotaRhsOfN w)

/-- the witness unpacked, `derivedIota_unpack` at `DerivedIotaN`. -/
def derivedIotaN_unpack {EA : ResolvedEnvA} {lhs rhs : Expr Nat} :
    DerivedIotaN EA lhs rhs →
    Σ' (w : IotaWitnessN EA), (lhs = iotaLhsOfN w) ×' (rhs = iotaRhsOfN w)
  | .of w => ⟨w, rfl, rfl⟩

/-! ## (2) the group read off a normalized witness -/

/-- the group the copy's ι reads, from a normalized witness: the constructor the witness
    carries IS the member (`EA.members ctorRef`), the recursor and family are the annotated
    members above their erased images. -/
theorem iotaGroupA_of_witnessN {EA : ResolvedEnvA} (w : IotaWitnessN EA)
    {recA famA : CheckedMemberA}
    (hrA : EA.members w.recRef = some recA) (hrE : eraseMember recA = w.recMember)
    (hfA : EA.members w.familyRef = some famA) (hfE : eraseMember famA = w.famMember) :
    iotaGroupA EA w.recRef w.ctorRef =
      some ⟨recA, w.ctorMember, famA, w.ctorRef, w.familyRef, w.nparams, w.nindices, w.nMinors,
        w.ctorIdx⟩ := by
  have hrK : recA.mclass = .recursorM := by rw [← w.hrecK, ← hrE]; rfl
  have hcK : w.ctorMember.mclass = .constructorM := w.hctorK
  have hfK : famA.mclass = .inductiveM := by rw [← w.hfamK, ← hfE]; rfl
  have hrT : erase recA.mtypeA = w.recMember.mtype := by rw [← hrE]; rfl
  have hfT : erase famA.mtypeA = w.famMember.mtype := by rw [← hfE]; rfl
  have hcnt : piCountA recA.mtypeA = w.nparams + 1 + w.nMinors + w.nindices + 1 := by
    rw [← piCountA_erase, hrT, w.hnmin]
  have hpeel := piDomsA_erase_peelPis recA.mtypeA
  rw [hcnt, hrT, w.hpeelRec] at hpeel
  injection hpeel with hpeel
  injection hpeel with hdoms hbody
  have hlenD : (piDomsA recA.mtypeA).length = w.nparams + 1 + w.nMinors + w.nindices + 1 := by
    have := congrArg List.length hdoms
    rw [List.length_map, peelPis_length _ _ w.hpeelRec] at this
    exact this.symm
  obtain ⟨D, hD, hDe⟩ := getElem?_map_erase hdoms.symm w.hmajorTy
  have hlast : (piDomsA recA.mtypeA).getLast? = some D := by
    rw [List.getLast?_eq_getElem?, hlenD]
    exact hD
  have hDsp : appsSpine (erase D) = (.const w.familyRef
      ((List.range w.famMember.arity).map Level.param),
      (List.range w.nparams).reverse.map (fun i => Expr.bvar (i + w.nindices + w.nMinors + 1)) ++
        (List.range w.nindices).reverse.map (fun i => Expr.bvar i)) := by
    rw [hDe, appsSpine_foldApps]
    rfl
  obtain ⟨_, hDA, _⟩ := appsSpineA_of_erase_const hDsp
  have hBsp : appsSpine (erase (piBodyA recA.mtypeA)) = (.bvar (w.nMinors + w.nindices + 1),
      (List.range w.nindices).reverse.map (fun i => Expr.bvar (i + 1)) ++ [Expr.bvar 0]) := by
    rw [← hbody, w.hrecBody, appsSpine_foldApps]
    rfl
  obtain ⟨bargs, hBA, hbargs⟩ := appsSpineA_of_erase_bvar hBsp
  have hblen : (appsSpineA (piBodyA recA.mtypeA)).2.length = w.nindices + 1 := by
    rw [hBA]
    have := congrArg List.length hbargs
    simp only [List.length_map, List.length_append, List.length_reverse, List.length_range,
      List.length_singleton] at this
    exact this
  have hfcnt : piCountA famA.mtypeA = w.nparams + w.nindices := by
    rw [← piCountA_erase, hfT, w.hnidx]
  have hcounts : groupCountsA recA famA (w.recRef - w.familyRef - 1) = some (w.nparams, w.nindices) := by
    unfold groupCountsA
    rw [hblen]
    have hrec := w.hrecIdx
    simp only
    rw [if_pos ⟨by omega, by rw [hcnt, hfcnt]; omega⟩]
    congr 2
    omega
  have hlay : famA.mclass = .inductiveM ∧ w.familyRef < w.ctorRef ∧ w.ctorRef < w.recRef := by
    have h1 := w.hctorIdx
    have h2 := w.hrecIdx
    have h3 := w.hidx
    exact ⟨hfK, by omega, by omega⟩
  have hmin : w.recRef - w.familyRef - 1 = w.nMinors := by have := w.hrecIdx; omega
  have hcidx : w.ctorRef - w.familyRef - 1 = w.ctorIdx := by have := w.hctorIdx; omega
  unfold iotaGroupA
  rw [hrA, w.hctor]
  simp only
  rw [if_pos ⟨hrK, hcK⟩, hlast]
  simp only
  rw [hDA]
  simp only
  rw [hfA]
  simp only
  rw [if_pos hlay, hcounts]
  simp only [hmin, hcidx]

/-- ANNOTATION AT ι (normed): a witness of the annotated environment makes the copy's ι fire
    on every annotation of its left-hand side, and the reduct erases to the witness's
    right-hand side. The witness's reads are the normed ones the reduct itself performs, so
    no `EnvNormEraseA` premise stands: at a `.drecD` member the stored peel that
    `EnvNormEraseA` used to transport is exactly what the witness no longer needs. -/
theorem iotaFnA_of_witnessN {EA : ResolvedEnvA} (w : IotaWitnessN EA) {e : ExprA}
    (he : erase e = iotaLhsOfN w)
    (hL1 : ∀ cm, EA.members w.ctorRef = some cm → cm.arity ≤ w.ls.length)
    (hL2 : ∀ cm, EA.members w.ctorRef = some cm →
      exprLevelsBoundedA cm.arity (memberNormTyA cm) = true) :
    ∃ e', iotaFnA EA e = some e' ∧ erase e' = iotaRhsOfN w := by
  obtain ⟨recA, hrA, hrE⟩ := members_of_eraseEnv w.hrec
  obtain ⟨famA, hfA, hfE⟩ := members_of_eraseEnv w.hfam
  have hg := iotaGroupA_of_witnessN w hrA hrE hfA hfE
  -- the spine
  have hsp : appsSpine (erase e) = (.const w.recRef w.ls, w.preMajor ++ [ctorMajorN w]) := by
    rw [he]
    unfold iotaLhsOfN recCall
    rw [appsSpine_foldApps]
    rfl
  obtain ⟨argsA, hargsA, hmap⟩ := appsSpineA_of_erase_const hsp
  obtain ⟨preA, majL, rfl, hpre, hmaj⟩ := map_erase_eq_append hmap
  obtain ⟨majA, rfl, hmajE⟩ := map_erase_eq_singleton hmaj
  have hs := recSpineA_of_spine hargsA
  -- the major
  have hmsp : appsSpine (erase majA) = (.const w.ctorRef w.lsC, w.ctorParams ++ w.fields) := by
    rw [hmajE]
    unfold ctorMajorN ctorSpineN
    rw [appsSpine_foldApps]
    rfl
  obtain ⟨margsA, hmargsA, hmmap⟩ := appsSpineA_of_erase_const hmsp
  have hc : spineHeadRefA majA = some w.ctorRef := spineHeadRefA_of_const (by rw [hmargsA])
  rw [iotaFnA_of_layers hs hc hg]
  -- the reduct's checks, on the normalized type directly
  have hrT : erase recA.mtypeA = w.recMember.mtype := by rw [← hrE]; rfl
  have hcar : w.ctorMember.arity ≤ w.ls.length := hL1 w.ctorMember w.hctor
  have hrar : recA.arity = w.recMember.arity := by rw [← hrE]; rfl
  have hprelen : preA.length = w.preMajor.length := by rw [← hpre, List.length_map]
  have hmlen : margsA.length = w.ctorParams.length + w.fields.length := by
    rw [← List.length_append, ← hmmap, List.length_map]
  have hcnt : piCountA (w.ctorMember.normA.getD w.ctorMember.mtypeA) =
      w.nparams + w.fields.length := by
    rw [← piCountA_erase]
    exact w.hnpar.symm
  have hrcnt : piCountA recA.mtypeA = w.nparams + 1 + w.nMinors + w.nindices + 1 := by
    rw [← piCountA_erase, hrT, w.hnmin]
  -- the kinds, off the normalized peel
  have hkinds : ctorKindsA w.familyRef w.nparams
      (w.ctorMember.normA.getD w.ctorMember.mtypeA) = some w.kinds := by
    rw [ctorKindsA_eq]
    have hpeel := piDomsA_erase_peelPis (w.ctorMember.normA.getD w.ctorMember.mtypeA)
    rw [hcnt] at hpeel
    have hpeelN : peelPis (w.nparams + w.fields.length) (memberNormTy w.ctorMember) =
        some ((piDomsA (w.ctorMember.normA.getD w.ctorMember.mtypeA)).map erase,
          erase (piBodyA (w.ctorMember.normA.getD w.ctorMember.mtypeA))) := hpeel
    rw [w.hpeel] at hpeelN
    injection hpeelN with hpeelN
    injection hpeelN with hdoms _
    rw [← hdoms]
    exact w.hkinds
  -- the minor
  obtain ⟨minorA, hminA, hminE⟩ := getElem?_map_erase hpre w.hminor
  -- the constructor telescope after the parameters, at the constructor-side levels
  have hbound : exprLevelsBoundedA w.ctorMember.arity
      (w.ctorMember.normA.getD w.ctorMember.mtypeA) = true := hL2 w.ctorMember w.hctor
  have hlvl : instantiateLevelsA (w.ls.take w.ctorMember.arity)
      (w.ctorMember.normA.getD w.ctorMember.mtypeA) =
      instantiateLevelsA w.ls (w.ctorMember.normA.getD w.ctorMember.mtypeA) :=
    (instantiateLevelsA_take w.ctorMember.arity w.ls _ hbound).symm
  have happ := applyTelA_erase (preA.take w.nparams)
    (instantiateLevelsA (w.ls.take w.ctorMember.arity)
      (w.ctorMember.normA.getD w.ctorMember.mtypeA))
  rw [erase_instantiateLevelsA, ← erase_instantiateLevelsA, hlvl, erase_instantiateLevelsA,
    List.map_take, hpre, w.hctorAfter] at happ
  rw [← hlvl] at happ
  obtain ⟨ctorAfterA, hcaA, hcaE⟩ : ∃ T, applyTelA (preA.take w.nparams)
      (instantiateLevelsA (w.ls.take w.ctorMember.arity)
        (w.ctorMember.normA.getD w.ctorMember.mtypeA)) =
      some T ∧ erase T = w.ctorAfterParams := by
    cases h : applyTelA (preA.take w.nparams)
        (instantiateLevelsA (w.ls.take w.ctorMember.arity)
          (w.ctorMember.normA.getD w.ctorMember.mtypeA)) with
    | none => rw [h] at happ; exact Option.noConfusion happ
    | some T =>
        rw [h] at happ
        exact ⟨T, rfl, Option.some.inj happ⟩
  -- the fields
  have hfieldsA : (margsA.drop w.nparams).map erase = w.fields := by
    rw [List.map_drop, hmmap, ← w.hctorParams, List.drop_left]
  have hflen : (margsA.drop w.nparams).length = w.kinds.length := by
    rw [← List.length_map (f := erase), hfieldsA, w.hlen]
  have hshapes : ctorShapesA w.familyRef w.nparams
      (w.ctorMember.normA.getD w.ctorMember.mtypeA) = some (w.kinds.map RecKind.shape) :=
    ctorShapesA_of_kinds hkinds
  have hwalk : fieldsTelA (margsA.drop w.nparams) (w.kinds.map RecKind.shape) ctorAfterA = true :=
    fieldsTelA_of_open _ _ _ hflen (by rw [hcaE]; exact w.hctorTel) (by rw [hcaE]; exact w.hfamTel)
  -- assemble
  have hcond : w.ctorRef = w.ctorRef ∧ preA.length + 1 = piCountA recA.mtypeA ∧
      w.ls.length = recA.arity ∧
      (appsSpineA majA).2.length =
        piCountA (w.ctorMember.normA.getD w.ctorMember.mtypeA) ∧
      w.ctorMember.arity ≤ w.ls.length := by
    refine ⟨rfl, ?_, ?_, ?_, hcar⟩
    · rw [hprelen, w.hpre, hrcnt]
    · rw [hrar, w.hlsLen]
    · rw [hmargsA]
      show margsA.length = _
      rw [hcnt, hmlen, w.hctorParams]
  refine ⟨foldAppsA minorA (rhsArgsA (.const w.recRef w.ls) preA w.nparams w.nMinors
    (margsA.drop w.nparams) (w.kinds.map RecKind.shape) ctorAfterA), ?_, ?_⟩
  · unfold iotaReductA
    simp only [hc, Option.some_bind]
    rw [if_pos ⟨trivial, hcond.2⟩]
    simp only [hshapes, Option.some_bind, hminA, hcaA, hmargsA, hwalk, if_true]
  · rw [foldAppsA_erase, rhsArgsA_erase _ _ _ _ _ _ _ hwalk, hminE, hpre, hfieldsA, hcaE]
    rfl

/-! ## (3) annotation at ι, under the copy's admission -/

/-- the constructor a normalized witness reads is one of its recursor's group, so its universe
    arity is at most the redex's list. -/
theorem witness_ctor_arityN {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (w : IotaWitnessN EA) {cm : CheckedMemberA} (hcm : EA.members w.ctorRef = some cm) :
    cm.arity ≤ w.ls.length := by
  obtain ⟨recA, hrA, hrE⟩ := members_of_eraseEnv w.hrec
  obtain ⟨famA, hfA, hfE⟩ := members_of_eraseEnv w.hfam
  have hrK : recA.mclass = .recursorM := by rw [← w.hrecK, ← hrE]; rfl
  obtain ⟨E₀, f, fm, fv, cs, rec, hrr, hrec, hcls, hfresh, hlay, hpre, _⟩ :=
    envWfA_recGroup hW _ _ hrA hrK
  have hst : rec.member.mtypeA = recTypeA f (canonLevelsA fm.arity) fv.params fv.indices fv.sort
      (rec.elim.motiveLevel fm.arity) (cs.reverse.map GroupCtorA.minorData) := rec.stored
  have hfamf : w.familyRef = f := by
    obtain ⟨D, ls', hD, hhead⟩ :=
      iotaGroupA_lastDom (iotaGroupA_of_witnessN w hrA hrE hfA hfE)
    simp only at hD hhead
    rw [← hrec, hst, piDomsA_recTypeA_getLast] at hD
    injection hD with hD
    rw [← hD, appsSpineA_majorDom] at hhead
    injection hhead with h1 _
    exact h1.symm
  have hk : w.nMinors = cs.length := by have := w.hrecIdx; omega
  have hj : w.ctorIdx < cs.length := by have := w.hidx; omega
  obtain ⟨gc, hgcj⟩ : ∃ gc, cs.reverse[w.ctorIdx]? = some gc :=
    ⟨cs.reverse[w.ctorIdx]'(by rw [List.length_reverse]; exact hj), List.getElem?_eq_getElem _⟩
  obtain ⟨href, _⟩ := ref_of_layoutA hlay hgcj
  obtain ⟨_, _, hmc⟩ := members_groupRecA hfresh hlay hpre
  have hctor : w.ctorRef = gc.ref := by have := w.hctorIdx; omega
  rw [hctor, hmc hgcj] at hcm
  injection hcm with hcm
  subst hcm
  have hls : w.ls.length = rec.member.arity := by
    rw [w.hlsLen, ← hrE, hrec]; rfl
  rw [hls, gc.harity, rec.harity]
  exact Nat.le_add_right _ _

/-- the normalized type of a constructor member is level-bounded at the member's arity —
    `normA.getD` is the stored type when `normA` is none and the normed bound
    (`envWfA_normLevels`) otherwise. No norm-erasure premise. -/
theorem envWfA_normTy_levels {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    {r : Nat} {cm : CheckedMemberA} (hcm : EA.members r = some cm)
    (hmc : cm.mclass = .constructorM) :
    exprLevelsBoundedA cm.arity (memberNormTyA cm) = true := by
  show exprLevelsBoundedA cm.arity (cm.normA.getD cm.mtypeA) = true
  cases hnm : cm.normA with
  | none => exact (envWfA_levels hW _ _ hcm).1
  | some T => exact envWfA_normLevels hW _ _ hcm hmc T hnm

/-- ANNOTATION AT ι (normed), under the copy's admission: a derived normalized ι step of the
    annotated environment on an erased left-hand side is a step of the copy's ι, with a reduct
    that erases to its right-hand side. No `EnvNormEraseA`: the arity bound comes from the
    group (`witness_ctor_arityN`), the level bound from the normed bound
    (`envWfA_normTy_levels`). -/
theorem iotaFnA_of_derivedIotaN {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    {e : ExprA} {rhs : Expr Nat} (hd : DerivedIotaN EA (erase e) rhs) :
    ∃ e', iotaFnA EA e = some e' ∧ erase e' = rhs := by
  obtain ⟨w, hl, hr⟩ := derivedIotaN_unpack hd
  rw [hr]
  exact iotaFnA_of_witnessN w hl (fun cm hcm => witness_ctor_arityN hW w hcm)
    (fun cm hcm => envWfA_normTy_levels hW hcm
      (by rw [w.hctor] at hcm; injection hcm with h; exact h ▸ w.hctorK))

/-! ## (4) erasure: a step of the copy's ι is a normalized derived ι step -/

/-- ERASURE AT ι (normed): under the copy's admission, a step of the copy's ι is a derived
    normalized ι step of the annotated environment, on the erased terms. `iotaReductA_inv`
    hands back the normed reads — `ctorShapesA`/`applyTelA`/`piCountA` of `normA.getD` —
    which are exactly what `IotaWitnessN` wants; `EnvNormEraseA` is never invoked. The
    group-identification argument (`envWfA_recGroup`, `iotaGroupA_groupRecA`) is unchanged. -/
theorem derivedIotaN_of_iotaFnA {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (hnf : EnvNoFunA EA) {e e' : ExprA} (h : iotaFnA EA e = some e') :
    Nonempty (DerivedIotaN EA (erase e) (erase e')) := by
  obtain ⟨⟨recRef, ls, pre, major⟩, c, g, hs, hc, hg, hr⟩ := iotaFnA_some h
  have hsp := recSpineA_some hs
  simp only at hsp hc hg
  obtain ⟨hrm, hrk, _, _, _, _, _, hlt1, hlt2, _, _, _, _⟩ := iotaGroupA_some hg
  obtain ⟨E₀, f, fm, fv, cs, rec, hrr, hrec, hcls, hfresh, hlay, hpre, _⟩ :=
    envWfA_recGroup hW _ _ hrm hrk
  subst hrr
  have hst : rec.member.mtypeA = recTypeA f (canonLevelsA fm.arity) fv.params fv.indices fv.sort
      (rec.elim.motiveLevel fm.arity) (cs.reverse.map GroupCtorA.minorData) := rec.stored
  -- the family is the group's: the recursor type's last domain is headed by `f`
  have hfamf : g.familyRef = f := by
    obtain ⟨D, ls', hD, hhead⟩ := iotaGroupA_lastDom hg
    rw [← hrec, hst, piDomsA_recTypeA_getLast] at hD
    injection hD with hD
    rw [← hD, appsSpineA_majorDom] at hhead
    injection hhead with h1 _
    exact h1.symm
  -- the constructor is the group's `j`-th
  rw [hfamf] at hlt1
  have hj : c - f - 1 < cs.length := by omega
  obtain ⟨gc, hgcj⟩ : ∃ gc, cs.reverse[c - f - 1]? = some gc :=
    ⟨cs.reverse[c - f - 1]'(by rw [List.length_reverse]; exact hj), List.getElem?_eq_getElem _⟩
  obtain ⟨href, _⟩ := ref_of_layoutA hlay hgcj
  have hcref : c = gc.ref := by omega
  subst hcref
  have hg' := iotaGroupA_groupRecA hfresh hlay hcls hpre hgcj
  rw [hg'] at hg
  injection hg with hg
  subst hg
  -- the members
  obtain ⟨hmr, hmf, hmc⟩ := members_groupRecA hfresh hlay hpre
  have hmg := hmc hgcj
  have hNF : ∀ x ∈ gc.view.fields, x.NoFun := fun x hx =>
    viewNoFun_of_envNoFunA hnf gc hmg hmf hfresh.base x hx
  -- the reduct's data and the arities — normed reads, no erase-transport
  obtain ⟨shapes, minor, ctorAfter, hshapes, hmin, happ, hwalk, he'⟩ := iotaReductA_inv hr
  obtain ⟨_, _, _, hplen, hlslen, hmlen, har⟩ := iotaReductA_some hr
  simp only at hshapes hmin happ hwalk he' hplen hlslen hmlen har
  rw [gc.normA_getD] at hshapes hmlen
  have hnpF : fv.params.length = fm.nparamsA := fv.nparams
  have hgar : gc.member.arity = fm.arity := gc.harity
  have hrar : rec.member.arity = fm.arity + rec.elim.extra := rec.harity
  have hcpN : piCountA (ctorTypeA f (canonLevelsA fm.arity) fv.sort gc.view.mirrors
      (gc.view.fields.map FieldA.norm) gc.view.res) =
      fv.params.length + gc.view.fields.length := by
    rw [piCountA_ctorTypeA, gc.view.mirrors_length, List.length_map, hnpF]
  have hrp : piCountA rec.member.mtypeA =
      fv.params.length + 1 + cs.length + fv.indices.length + 1 := by
    rw [hst, piCountA_recTypeA, List.length_map, List.length_reverse]
  -- the shapes are the view's, the kinds' too (no field is function-recursive)
  have hshv : shapes = gc.view.fields.map FieldA.shape := by
    have := gc.view.shapes hfresh.base
    rw [← hnpF, hshapes] at this
    exact Option.some.inj this
  have hkinds : ctorKindsA f fv.params.length (gc.member.normA.getD gc.member.mtypeA) =
      some (gc.view.fields.map FieldA.kind) := by
    rw [hnpF, gc.normA_getD]; exact gc.view.kinds hfresh.base hNF
  have hshk : shapes = (gc.view.fields.map FieldA.kind).map RecKind.shape := by
    rw [hshv, FieldA.map_kind_shape hNF]
  subst hshk
  -- the constructor telescope after the parameters is the built one
  have htakeL : (ls.take fm.arity).length = fm.arity := by
    rw [List.length_take]; rw [hgar] at har; omega
  have htakeP : (pre.take fv.params.length).length = fm.nparamsA := by
    rw [List.length_take, ← hnpF]; rw [hrp] at hplen; omega
  have happV := gc.applyTel_params (ls.take fm.arity) htakeL (pre.take fv.params.length) htakeP
  rw [hgar, happV] at happ
  injection happ with hca
  -- the major
  obtain ⟨lsC, hmh⟩ := spineHeadRefA_some hc
  have hmaj : major = foldAppsA (.const gc.ref lsC) (appsSpineA major).2 := by
    conv => lhs; rw [← foldAppsA_appsSpineA major]
    rw [hmh]
  have he : e = foldAppsA (.const (f + 1 + cs.length) ls) (pre ++ [major]) := by
    conv => lhs; rw [← foldAppsA_appsSpineA e]
    rw [hsp]
  have hmlen' : (appsSpineA major).2.length = fv.params.length + gc.view.fields.length := by
    rw [hmlen, hcpN]
  have hfslen : ((appsSpineA major).2.drop fv.params.length).length = gc.view.fields.length := by
    rw [List.length_drop, hmlen']; omega
  have hklen : (gc.view.fields.map FieldA.kind).length = gc.view.fields.length := by rw [List.length_map]
  -- the witness, constructor side on `memberNormTy`
  let w : IotaWitnessN EA :=
    { recRef := f + 1 + cs.length
      ctorRef := gc.ref
      ls := ls
      lsC := lsC
      recMember := eraseMember rec.member
      ctorMember := gc.member
      hrec := by rw [members_eraseEnv, hmr]; rfl
      hctor := hmg
      hrecK := rec.hcls
      hctorK := gc.hcls
      preMajor := pre.map erase
      fields := ((appsSpineA major).2.drop fv.params.length).map erase
      ctorParams := ((appsSpineA major).2.take fv.params.length).map erase
      kinds := gc.view.fields.map FieldA.kind
      minor := erase minor
      hlen := by simp only [List.length_map, hfslen]
      familyRef := f
      famMember := eraseMember fm
      hfam := by rw [members_eraseEnv, hmf]; rfl
      hfamK := hcls
      nparams := fv.params.length
      nindices := fv.indices.length
      nMinors := cs.length
      ctorIdx := gc.ref - f - 1
      hctorParams := by rw [List.length_map, List.length_take, hmlen']; omega
      hnpar := by
        show fv.params.length + _ = piCount (erase (gc.member.normA.getD gc.member.mtypeA))
        rw [List.length_map, hfslen, piCountA_erase, gc.normA_getD, hcpN]
      hnidx := by
        show _ = piCount (erase fm.mtypeA)
        rw [piCountA_erase, piCountA_famView fv]
      hnmin := by
        show _ = piCount (erase rec.member.mtypeA)
        rw [piCountA_erase, hrp]
      hidx := hj
      hctorIdx := href
      hrecIdx := rfl
      hpre := by rw [List.length_map]; rw [hrp] at hplen; omega
      hminor := by rw [List.getElem?_map, hmin]; rfl
      ctorDoms := (piDomsA (memberNormTyA gc.member)).map erase
      ctorResult := erase (piBodyA (memberNormTyA gc.member))
      hpeel := by
        show peelPis (fv.params.length + _) (erase (gc.member.normA.getD gc.member.mtypeA)) = _
        rw [List.length_map, hfslen]
        unfold memberNormTyA
        rw [gc.normA_getD]
        have hp := piDomsA_erase_peelPis (ctorTypeA f (canonLevelsA fm.arity) fv.sort
          gc.view.mirrors (gc.view.fields.map FieldA.norm) gc.view.res)
        rw [hcpN] at hp
        exact hp
      hfamApp := by
        show isFamilyApp f (erase (piBodyA (gc.member.normA.getD gc.member.mtypeA))) = true
        rw [gc.normA_getD]
        exact isFamilyApp_erase_piBodyA_ctorTypeA _ _ _ _ _ _ (gc.view.freeOf hfresh.base).2
      hkinds := by
        show analyzeFields f (((piDomsA (gc.member.normA.getD gc.member.mtypeA)).map erase).drop
          fv.params.length) = some (gc.view.fields.map FieldA.kind)
        rw [← List.map_drop, ← ctorKindsA]
        exact hkinds
      recDoms := (piDomsA rec.member.mtypeA).map erase
      recBody := erase (piBodyA rec.member.mtypeA)
      hpeelRec := by
        show peelPis _ (erase rec.member.mtypeA) = _
        rw [← hrp]
        exact piDomsA_erase_peelPis _
      hrecBody := by
        rw [hst, piBodyA_recTypeA, List.length_map, List.length_reverse, erase_recBodyA]
      hmajorTy := by
        have hl := piDomsA_recTypeA_getLast f (canonLevelsA fm.arity) fv.params fv.indices fv.sort
          (rec.elim.motiveLevel fm.arity) (cs.reverse.map GroupCtorA.minorData)
        rw [← hst, List.getLast?_eq_getElem?, length_piDomsA, hrp] at hl
        rw [List.getElem?_map]
        have hidx : fv.params.length + 1 + cs.length + fv.indices.length + 1 - 1 =
            fv.params.length + 1 + cs.length + fv.indices.length := by omega
        rw [hidx] at hl
        rw [hl]
        simp only [List.length_map, List.length_reverse, Option.map_some']
        rw [erase_majorDomA]
        rfl
      hrecClosed := by
        show lift 0 1 (erase rec.member.mtypeA) = erase rec.member.mtypeA
        rw [← erase_liftA, rec.hclT 0]
      hctorClosed := by
        show lift 0 1 (erase (gc.member.normA.getD gc.member.mtypeA)) =
          erase (gc.member.normA.getD gc.member.mtypeA)
        rw [← erase_liftA, gc.normA_getD_closed 0]
      hlsLen := hlslen
      ctorAfterParams := erase ctorAfter
      hctorAfter := by
        show applyTel ((pre.map erase).take fv.params.length)
          (instantiateLevels ls (erase (gc.member.normA.getD gc.member.mtypeA))) =
          some (erase ctorAfter)
        have := applyTelA_erase (pre.take fv.params.length)
          (instantiateLevelsA ls (gc.member.normA.getD gc.member.mtypeA))
        rw [erase_instantiateLevelsA, List.map_take,
          instantiateLevelsA_take gc.member.arity ls _ gc.normA_getD_levels, hgar, happV] at this
        rw [← this, ← hca]
        rfl
      hctorTel := by
        rw [← hca, hklen]
        have := isPiTel_erase_ctorFieldsA f (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort)
          (gc.view.res.map (instantiateLevelsA (ls.take fm.arity)))
          ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels (ls.take fm.arity)))
          (pre.take fv.params.length) (consListA (pre.take fv.params.length) SubstA.id)
        rw [List.length_map, List.length_map] at this
        exact this
      hfamTel := by
        rw [← hca, ← map_kind_norm gc.view.fields,
          ← map_kind_instLevels (ls.take fm.arity) (gc.view.fields.map FieldA.norm)]
        exact directRecConstHead_erase_ctorFieldsA _ _ _ _ _ (fun y hy => by
          obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hy
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hx'
          exact FieldA.treeField_instLevels _ (FieldA.norm_treeField (hNF x hx))) _ _
      hresTel := by
        rw [← hca, ← map_kind_norm gc.view.fields,
          ← map_kind_instLevels (ls.take fm.arity) (gc.view.fields.map FieldA.norm)]
        exact resultConstHead_erase_ctorFieldsA _ _ _ _ _ _ _ }
  have hmajE : erase major = foldApps (.const gc.ref lsC)
      (((appsSpineA major).2.take fv.params.length).map erase ++
        ((appsSpineA major).2.drop fv.params.length).map erase) := by
    rw [← List.map_append, List.take_append_drop]
    conv => lhs; rw [hmaj]
    rw [foldAppsA_erase]
    rfl
  have hL : iotaLhsOfN w = erase e := by
    rw [he, foldAppsA_erase, List.map_append, List.map_cons, List.map_nil, hmajE]
    rfl
  have hR : iotaRhsOfN w = erase e' := by
    rw [he', foldAppsA_erase, rhsArgsA_erase _ _ _ _ _ _ _ hwalk]
    rfl
  exact ⟨hL ▸ hR ▸ DerivedIotaN.of w⟩

/-! ## (5) both directions under the copy's admission -/

/-- the copy's ι steps erase to normalized derived ι steps of the annotated environment, at
    an evidence family `D` keyed on `EA` (`IotaErasesTo`'s twin at the normalized witness). -/
def IotaErasesToN (D : ResolvedEnvA → Expr Nat → Expr Nat → Type) (EA : ResolvedEnvA) : Prop :=
  ∀ e e', iotaFnA EA e = some e' → Nonempty (D EA (erase e) (erase e'))

/-- `IotaErasesToN` at `DerivedIotaN`. -/
def IotaErasesAN (EA : ResolvedEnvA) : Prop := IotaErasesToN DerivedIotaN EA

/-- a normalized derived ι step of the annotated environment on an erased left-hand side fires
    the copy's ι, with a reduct that erases to the right-hand side (`IotaAnnotatesA`'s twin). -/
def IotaAnnotatesAN (EA : ResolvedEnvA) : Prop :=
  ∀ e rhs, DerivedIotaN EA (erase e) rhs →
    ∃ e', iotaFnA EA e = some e' ∧ erase e' = rhs

/-- the copy↔tree ι correspondence at the normalized witness, both directions bundled —
    `IotaCorrTA`'s analogue that `EnvWfA` + `EnvNoFunA` PROVE, unconditionally (no
    `EnvNormEraseA`, no analysis-agreement debt): the witness reads the same normalized type
    the copy's ι does. -/
structure IotaCorrN (EA : ResolvedEnvA) : Prop where
  ann : IotaAnnotatesAN EA
  eraseN : IotaErasesAN EA

/-- every admitted environment has the normalized ι correspondence: erasure under
    `EnvNoFunA` (the `.frec` boundary, class (c) — untouched here), annotation with no
    further premise. -/
theorem iotaCorrN_of_envWfA {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (hnf : EnvNoFunA EA) : IotaCorrN EA where
  ann := fun _ _ hd => iotaFnA_of_derivedIotaN hW hd
  eraseN := fun _ _ h => derivedIotaN_of_iotaFnA hW hnf h

/-- the annotation direction standalone (the premise `annConvTD` reads). -/
theorem iotaAnnotatesAN_of_envWfA {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA) :
    IotaAnnotatesAN EA := fun _ _ hd => iotaFnA_of_derivedIotaN hW hd

/-- the erasure direction standalone (the premise `erase_convAD` reads). -/
theorem iotaErasesAN_of_envWfA {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (hnf : EnvNoFunA EA) : IotaErasesAN EA := fun _ _ h => derivedIotaN_of_iotaFnA hW hnf h

end Rcic.Declarative.Ann

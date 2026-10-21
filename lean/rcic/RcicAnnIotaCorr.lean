import rcic.RcicAnnCoh
import rcic.RcicIota
import rcic.RcicIotaShapeAdapter

/-!
# M3-b-1 — the ι correspondence: the copy's `iotaFnA` and main's `DerivedIota`

The landing (M3) moves derivations between the copy and the tree in both directions, and each
direction meets ι once. Main's ι step is `DerivedIota E lhs rhs`, an inductive over `IotaWitness`.
On the copy ι is a function, `iotaFnA EA`. Both directions are proved here under the copy's
admission (`EnvWfA`), for the erased environment `eraseEnv EA`:

* ANNOTATION (tree → copy), `iotaFnA_of_derivedIota`: a derived ι step on an erased left-hand side
  is a step of the copy's ι, with a reduct that erases to the right-hand side. The core is
  `iotaFnA_of_witness` (section 3), which needs only two facts about the constructor member: its
  universe arity is at most the redex's universe list, and its stored type is level-bounded at that
  arity. Section 7 discharges both from `EnvWfA` (`witness_ctor_arity`, `envWfA_levels`).
* ERASURE (copy → tree), `derivedIota_of_iotaFnA` (section 6): a step of the copy's ι is a derived
  ι step on the erased terms. Every recursor of an admitted environment entered with its group
  (`envWfA_recGroup`, section 4). So the witness's counts and layout come from the layers. The
  shapes the witness pins come from the builders (section 5): the recursor's body and major domain,
  the constructor's result as a family application, and the guards on the open telescope. The
  conclusion is `Nonempty`, the form the landing states the erasure direction in (M3-b-0 O5: the
  copy's rows are existence results).

The two ι presentations do not agree off admitted groups, and the gap is in the field walk. Main's
witness checks the constructor telescope OPEN (`isPiTel`, `directRecConstHead` on the telescope
after the parameters, the fields' binders left as variables). The copy's `fieldsTelA` walks it
with each field SUBSTITUTED. Substitution preserves a Π and a constant head (`isPiTel_instantiate`,
`directRecConstHead_instantiate`, main's `RcicIota`), so the open check gives the substituted one
(`fieldsTelA_of_open`). The converse fails at a recursive domain headed by an earlier field's
variable, which only substitution turns constant-headed. The builder never makes such a domain
(`directRecConstHead_erase_ctorFieldsA`), which is why the erasure direction reads the admission.

W-1 (e): the copy's ι contracts to the minor applied to the fields at every group, struct groups
included, as main's does (at a struct group's recursor spine the head step is the struct arm's,
`structPosA`, and ι's rule there is `ConvA.structIota`). So both directions hold at every step, and the
erasure direction, as a property of an environment (`IotaErasesA`, section 7), is what the bridge reads.

`IotaWitness` and `IotaTyping` are byte-identical on `main` and on the typed face
(`wip/rcic-face`, measured 2026-10-05), so the correspondence does not depend on which typed root
lands. Section 8 pins the annotation direction at the copy's Nat group.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) erasure inversions at a constant-headed spine -/

/-- an erased spine headed by a constant is the erasure of an annotated spine with the same
    head. -/
theorem appsSpineA_of_erase_const {e : ExprA} {r : Nat} {ls : List Level} {args : List (Expr Nat)}
    (h : appsSpine (erase e) = (.const r ls, args)) :
    ∃ argsA, appsSpineA e = (.const r ls, argsA) ∧ argsA.map erase = args := by
  rw [appsSpineA_erase] at h
  injection h with h1 h2
  exact ⟨(appsSpineA e).2, Prod.ext (erase_eq_const h1) rfl, h2⟩

/-- an erased spine headed by a variable is the erasure of an annotated spine with the same
    head. -/
theorem appsSpineA_of_erase_bvar {e : ExprA} {i : Nat} {args : List (Expr Nat)}
    (h : appsSpine (erase e) = (.bvar i, args)) :
    ∃ argsA, appsSpineA e = (.bvar i, argsA) ∧ argsA.map erase = args := by
  rw [appsSpineA_erase] at h
  injection h with h1 h2
  exact ⟨(appsSpineA e).2, Prod.ext (erase_eq_bvar h1) rfl, h2⟩

/-- a list whose erasure splits splits the same way. -/
theorem map_erase_eq_append {xs : List ExprA} {ys zs : List (Expr Nat)}
    (h : xs.map erase = ys ++ zs) :
    ∃ ysA zsA, xs = ysA ++ zsA ∧ ysA.map erase = ys ∧ zsA.map erase = zs := by
  refine ⟨xs.take ys.length, xs.drop ys.length, (List.take_append_drop _ _).symm, ?_, ?_⟩
  · rw [List.map_take, h, List.take_left]
  · rw [List.map_drop, h, List.drop_left]

theorem map_erase_eq_singleton {xs : List ExprA} {y : Expr Nat} (h : xs.map erase = [y]) :
    ∃ x, xs = [x] ∧ erase x = y := by
  match xs, h with
  | [x], h => exact ⟨x, rfl, by injection h⟩

theorem getElem?_map_erase {xs : List ExprA} {ys : List (Expr Nat)} (h : xs.map erase = ys) {i : Nat}
    {y : Expr Nat} (hy : ys[i]? = some y) : ∃ x, xs[i]? = some x ∧ erase x = y := by
  subst h
  rw [List.getElem?_map] at hy
  cases hx : xs[i]? with
  | none => rw [hx] at hy; exact Option.noConfusion hy
  | some x =>
      rw [hx] at hy
      exact ⟨x, rfl, Option.some.inj hy⟩

/-- a member of the erased environment is the erasure of a member of the copy's. -/
theorem members_of_eraseEnv {EA : ResolvedEnvA} {r : Nat} {m : CheckedMember}
    (h : (eraseEnv EA).members r = some m) : ∃ mA, EA.members r = some mA ∧ eraseMember mA = m := by
  rw [members_eraseEnv] at h
  cases hm : EA.members r with
  | none => rw [hm] at h; exact Option.noConfusion h
  | some mA =>
      rw [hm] at h
      exact ⟨mA, rfl, Option.some.inj h⟩

/-! ## (2) the field walk: main's open check gives the copy's substituted one -/

theorem spineHeadConstA_of_erase {A : ExprA} (h : spineHeadConst (erase A) = true) :
    spineHeadConstA A = true := by
  unfold spineHeadConst at h
  rw [appsSpineA_erase] at h
  simp only at h
  unfold spineHeadConstA
  cases hA : (appsSpineA A).1 with
  | const _ _ => rfl
  | bvar _ => rw [hA] at h; exact Bool.noConfusion h
  | sort _ => rw [hA] at h; exact Bool.noConfusion h
  | app _ _ => rw [hA] at h; exact Bool.noConfusion h
  | lam _ _ _ => rw [hA] at h; exact Bool.noConfusion h
  | pi _ _ _ _ => rw [hA] at h; exact Bool.noConfusion h
  | letE _ _ _ => rw [hA] at h; exact Bool.noConfusion h
  | lit _ => rw [hA] at h; exact Bool.noConfusion h

/-- main's open walk (a Π at every field, a constant head at every recursive domain) gives the
    copy's walk with the fields substituted. -/
theorem fieldsTelA_of_open : (fs : List ExprA) → (ks : List RecKind) → (T : ExprA) →
    fs.length = ks.length → isPiTel ks.length (erase T) = true →
    directRecConstHead ks (erase T) = true → fieldsTelA fs (ks.map RecKind.shape) T = true
  | [], [], _, _, _, _ => rfl
  | f :: fs, k :: ks, T, hlen, htel, hdr => by
      have htel' : isPiTel (ks.length + 1) (erase T) = true := htel
      cases hT : erase T with
      | pi A B =>
          obtain ⟨A', u, B', v, rfl, hA, hB⟩ := erase_eq_pi hT
          rw [hT] at htel' hdr
          simp only [isPiTel] at htel'
          have hB'tel : isPiTel ks.length (erase (instantiate0A f B')) = true := by
            rw [erase_instantiate0A, hB]
            exact isPiTel_instantiate 0 (erase f) ks.length B htel'
          cases k with
          | plain =>
              simp only [directRecConstHead] at hdr
              have hB'dr : directRecConstHead ks (erase (instantiate0A f B')) = true := by
                rw [erase_instantiate0A, hB]
                exact directRecConstHead_instantiate 0 (erase f) ks B htel' hdr
              show (shapeGuardA A' .nonrecursive && fieldsTelA fs (ks.map RecKind.shape) (instantiate0A f B')) = true
              rw [fieldsTelA_of_open fs ks _ (Nat.succ.inj hlen) hB'tel hB'dr]
              rfl
          | directRec =>
              simp only [directRecConstHead] at hdr
              have hA'c : spineHeadConstA A' = true :=
                spineHeadConstA_of_erase (by rw [hA]; exact boolAnd_left hdr)
              have hB'dr : directRecConstHead ks (erase (instantiate0A f B')) = true := by
                rw [erase_instantiate0A, hB]
                exact directRecConstHead_instantiate 0 (erase f) ks B htel' (boolAnd_right hdr)
              show (shapeGuardA A' (.recursive 0) && fieldsTelA fs (ks.map RecKind.shape) (instantiate0A f B')) = true
              rw [fieldsTelA_of_open fs ks _ (Nat.succ.inj hlen) hB'tel hB'dr]
              show (spineHeadConstA A' && true) = true
              rw [hA'c]
              rfl
      | bvar _ => rw [hT] at htel'; exact Bool.noConfusion htel'
      | sort _ => rw [hT] at htel'; exact Bool.noConfusion htel'
      | const _ _ => rw [hT] at htel'; exact Bool.noConfusion htel'
      | app _ _ => rw [hT] at htel'; exact Bool.noConfusion htel'
      | lam _ _ => rw [hT] at htel'; exact Bool.noConfusion htel'
      | letE _ _ _ => rw [hT] at htel'; exact Bool.noConfusion htel'
      | lit _ => rw [hT] at htel'; exact Bool.noConfusion htel'
  | [], _ :: _, _, h, _, _ => nomatch h
  | _ :: _, [], _, h, _, _ => nomatch h

/-! ## (3) annotation: a witness of the erased environment fires the copy's ι -/

/-- the group the copy's ι reads, from a witness of the erased environment. -/
theorem iotaGroupA_of_witness {EA : ResolvedEnvA} (w : IotaWitness (eraseEnv EA))
    {recA ctorA famA : CheckedMemberA}
    (hrA : EA.members w.recRef = some recA) (hrE : eraseMember recA = w.recMember)
    (hcA : EA.members w.ctorRef = some ctorA) (hcE : eraseMember ctorA = w.ctorMember)
    (hfA : EA.members w.familyRef = some famA) (hfE : eraseMember famA = w.famMember) :
    iotaGroupA EA w.recRef w.ctorRef =
      some ⟨recA, ctorA, famA, w.ctorRef, w.familyRef, w.nparams, w.nindices, w.nMinors,
        w.ctorIdx⟩ := by
  have hrK : recA.mclass = .recursorM := by rw [← w.hrecK, ← hrE]; rfl
  have hcK : ctorA.mclass = .constructorM := by rw [← w.hctorK, ← hcE]; rfl
  have hfK : famA.mclass = .inductiveM := by rw [← w.hfamK, ← hfE]; rfl
  have hrT : erase recA.mtypeA = w.recMember.mtype := by rw [← hrE]; rfl
  have hfT : erase famA.mtypeA = w.famMember.mtype := by rw [← hfE]; rfl
  -- the recursor's telescope, through erasure
  have hcnt : piCountA recA.mtypeA = w.nparams + 1 + w.nMinors + w.nindices + 1 := by
    rw [← piCountA_erase, hrT, w.hnmin]
  have hpeel := piDomsA_erase_peelPis recA.mtypeA
  rw [hcnt, hrT, w.hpeelRec] at hpeel
  injection hpeel with hpeel
  injection hpeel with hdoms hbody
  -- the major's domain is the last one; its head is the family
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
  -- the recursor's body is `motive indices major`: `nindices + 1` arguments
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
  rw [hrA, hcA]
  simp only
  rw [if_pos ⟨hrK, hcK⟩, hlast]
  simp only
  rw [hDA]
  simp only
  rw [hfA]
  simp only
  rw [if_pos hlay, hcounts]
  simp only [hmin, hcidx]

/-- ANNOTATION AT ι: a witness of the erased environment makes the copy's ι fire on every
    annotation of its left-hand side, and the reduct erases to the witness's right-hand side. The
    constructor's universe arity is at most the redex's list (the copy reads the constructor
    type at `ls.take arity`, main at `ls`), and its stored type is level-bounded at that arity
    (so the two readings agree). -/
theorem iotaFnA_of_witness {EA : ResolvedEnvA} (w : IotaWitness (eraseEnv EA)) {e : ExprA}
    (he : erase e = iotaLhsOf w)
    (hL1 : ∀ cm, EA.members w.ctorRef = some cm → cm.arity ≤ w.ls.length)
    (hL2 : ∀ cm, EA.members w.ctorRef = some cm → exprLevelsBoundedA cm.arity cm.mtypeA = true)
    (hN : ∀ cm, EA.members w.ctorRef = some cm → cm.mclass = .constructorM →
      ∀ T, cm.normA = some T → erase T = erase cm.mtypeA) :
    ∃ e', iotaFnA EA e = some e' ∧ erase e' = iotaRhsOf w := by
  obtain ⟨recA, hrA, hrE⟩ := members_of_eraseEnv w.hrec
  obtain ⟨ctorA, hcA, hcE⟩ := members_of_eraseEnv w.hctor
  obtain ⟨famA, hfA, hfE⟩ := members_of_eraseEnv w.hfam
  have hg := iotaGroupA_of_witness w hrA hrE hcA hcE hfA hfE
  -- the spine
  have hsp : appsSpine (erase e) = (.const w.recRef w.ls, w.preMajor ++ [ctorMajor w]) := by
    rw [he]
    unfold iotaLhsOf recCall
    rw [appsSpine_foldApps]
    rfl
  obtain ⟨argsA, hargsA, hmap⟩ := appsSpineA_of_erase_const hsp
  obtain ⟨preA, majL, rfl, hpre, hmaj⟩ := map_erase_eq_append hmap
  obtain ⟨majA, rfl, hmajE⟩ := map_erase_eq_singleton hmaj
  have hs := recSpineA_of_spine hargsA
  -- the major
  have hmsp : appsSpine (erase majA) = (.const w.ctorRef w.lsC, w.ctorParams ++ w.fields) := by
    rw [hmajE]
    unfold ctorMajor
    rw [appsSpine_foldApps]
    rfl
  obtain ⟨margsA, hmargsA, hmmap⟩ := appsSpineA_of_erase_const hmsp
  have hc : spineHeadRefA majA = some w.ctorRef := spineHeadRefA_of_const (by rw [hmargsA])
  rw [iotaFnA_of_layers hs hc hg]
  -- the reduct's checks
  have hcT : erase ctorA.mtypeA = w.ctorMember.mtype := by rw [← hcE]; rfl
  have hrT : erase recA.mtypeA = w.recMember.mtype := by rw [← hrE]; rfl
  have hcar : ctorA.arity ≤ w.ls.length := hL1 ctorA hcA
  have hrar : recA.arity = w.recMember.arity := by rw [← hrE]; rfl
  have hprelen : preA.length = w.preMajor.length := by rw [← hpre, List.length_map]
  have hmlen : margsA.length = w.ctorParams.length + w.fields.length := by
    rw [← List.length_append, ← hmmap, List.length_map]
  have hcnt : piCountA ctorA.mtypeA = w.nparams + w.fields.length := by
    rw [← piCountA_erase, hcT, ← w.hnpar]
  have hrcnt : piCountA recA.mtypeA = w.nparams + 1 + w.nMinors + w.nindices + 1 := by
    rw [← piCountA_erase, hrT, w.hnmin]
  -- the kinds, through erasure
  have hkinds : ctorKindsA w.familyRef w.nparams ctorA.mtypeA = some w.kinds := by
    rw [ctorKindsA_eq]
    have hpeel := piDomsA_erase_peelPis ctorA.mtypeA
    rw [hcnt, hcT, w.hpeel] at hpeel
    injection hpeel with hpeel
    injection hpeel with hdoms _
    rw [← hdoms]
    exact w.hkinds
  -- the minor
  obtain ⟨minorA, hminA, hminE⟩ := getElem?_map_erase hpre w.hminor
  -- the constructor member's `normA`, when it carries one, erases to the stored type
  -- (`EnvNormEraseA`; at a `drecD` member the erased types diverge and the ι-correspondence is
  -- out of scope — R-NoDeltaRec-4d-iii); the ι reads then agree with the witness's tree-side counts
  have hgetD : erase (ctorA.normA.getD ctorA.mtypeA) = erase ctorA.mtypeA := by
    cases hNm : ctorA.normA with
    | none => rfl
    | some T => exact hN ctorA hcA (by rw [← w.hctorK, ← hcE]; rfl) T hNm
  have hpc : piCountA (ctorA.normA.getD ctorA.mtypeA) = piCountA ctorA.mtypeA := by
    rw [← piCountA_erase (ctorA.normA.getD ctorA.mtypeA),
      ← piCountA_erase ctorA.mtypeA, hgetD]
  have hdoms : (piDomsA (ctorA.normA.getD ctorA.mtypeA)).map erase =
      (piDomsA ctorA.mtypeA).map erase := by
    have h1 := piDomsA_erase_peelPis (ctorA.normA.getD ctorA.mtypeA)
    have h2 := piDomsA_erase_peelPis ctorA.mtypeA
    rw [hpc, hgetD] at h1
    exact (Prod.mk.inj (Option.some.inj (h1.symm.trans h2))).1
  -- the constructor telescope after the parameters, at the constructor-side levels
  have hbound := hL2 ctorA hcA
  have hlvl : instantiateLevelsA (w.ls.take ctorA.arity) ctorA.mtypeA =
      instantiateLevelsA w.ls ctorA.mtypeA :=
    (instantiateLevelsA_take ctorA.arity w.ls ctorA.mtypeA hbound).symm
  have happ := applyTelA_erase (preA.take w.nparams)
    (instantiateLevelsA (w.ls.take ctorA.arity) (ctorA.normA.getD ctorA.mtypeA))
  rw [erase_instantiateLevelsA, hgetD, ← erase_instantiateLevelsA, hlvl,
    erase_instantiateLevelsA, hcT, List.map_take, hpre, w.hctorAfter] at happ
  obtain ⟨ctorAfterA, hcaA, hcaE⟩ : ∃ T, applyTelA (preA.take w.nparams)
      (instantiateLevelsA (w.ls.take ctorA.arity) (ctorA.normA.getD ctorA.mtypeA)) =
      some T ∧ erase T = w.ctorAfterParams := by
    cases h : applyTelA (preA.take w.nparams)
        (instantiateLevelsA (w.ls.take ctorA.arity) (ctorA.normA.getD ctorA.mtypeA)) with
    | none => rw [h] at happ; exact Option.noConfusion happ
    | some T =>
        rw [h] at happ
        exact ⟨T, rfl, Option.some.inj happ⟩
  -- the fields
  have hfieldsA : (margsA.drop w.nparams).map erase = w.fields := by
    rw [List.map_drop, hmmap, ← w.hctorParams, List.drop_left]
  have hflen : (margsA.drop w.nparams).length = w.kinds.length := by
    rw [← List.length_map (f := erase), hfieldsA, w.hlen]
  have hshapes : ctorShapesA w.familyRef w.nparams ctorA.mtypeA = some (w.kinds.map RecKind.shape) :=
    ctorShapesA_of_kinds hkinds
  have hshapesN : ctorShapesA w.familyRef w.nparams (ctorA.normA.getD ctorA.mtypeA) =
      some (w.kinds.map RecKind.shape) := by
    unfold ctorShapesA
    rw [List.map_drop, hdoms, ← List.map_drop]
    exact hshapes
  have hwalk : fieldsTelA (margsA.drop w.nparams) (w.kinds.map RecKind.shape) ctorAfterA = true :=
    fieldsTelA_of_open _ _ _ hflen (by rw [hcaE]; exact w.hctorTel) (by rw [hcaE]; exact w.hfamTel)
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
      rw [hpc, hmlen, w.hctorParams, hcnt]
  refine ⟨foldAppsA minorA (rhsArgsA (.const w.recRef w.ls) preA w.nparams w.nMinors
    (margsA.drop w.nparams) (w.kinds.map RecKind.shape) ctorAfterA), ?_, ?_⟩
  · unfold iotaReductA
    simp only [hc, Option.some_bind]
    rw [if_pos ⟨trivial, hcond.2⟩]
    simp only [hshapesN, Option.some_bind, hminA, hcaA, hmargsA, hwalk, if_true]
  · rw [foldAppsA_erase, rhsArgsA_erase _ _ _ _ _ _ _ hwalk, hminE, hpre, hfieldsA, hcaE]
    rfl

/-! ## (4) erasure: every recursor of an admitted environment entered with its group -/

/-- THE RECURSOR'S GROUP: in an admitted environment a recursor member entered at a `groupRec`
    step (the free-standing recursor step was withdrawn in M2-f (5a)), and that step's
    environment is a prefix, with the recursor's reference fresh in its group's environment
    (W-1 (e-2): ι subject reduction at a struct group reads the group's environment as a prefix). -/
theorem envWfA_recGroup {I : IotaIfaceA} : {E : ResolvedEnvA} → EnvWfA I E →
    (r : Nat) → (m : CheckedMemberA) → E.members r = some m → m.mclass = .recursorM →
    ∃ (E₀ : ResolvedEnvA) (f : Nat) (fm : CheckedMemberA) (fv : FamViewA fm)
      (cs : List (GroupCtorA I E₀ f fm fv)) (rec : GroupRecA I E₀ f fm fv cs),
      r = f + 1 + cs.length ∧ rec.member = m ∧ fm.mclass = .inductiveM ∧
      GroupFreshA E₀ f fm (cs.map GroupCtorA.entry) ∧
      cs.reverse.map GroupCtorA.ref = List.range' (f + 1) cs.length ∧
      PrefixA (groupRecEnvA cs rec) E ∧
      (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)).members (f + 1 + cs.length) = none
  | _, .empty, _, _, h, _ => Option.noConfusion h
  | _, .axiomM E r' _ _ hE hfresh _ _ _, r, m, hm, hk => by
      by_cases hr : r = r'
      · subst hr
        rw [members_extendEnvA_self] at hm
        cases hm
        cases hk
      · rw [members_extendEnvA_ne _ _ _ hr] at hm
        obtain ⟨E₀, f, fm, fv, cs, rec, h1, h2, h3, h4, h5, h6, h7⟩ := envWfA_recGroup hE _ _ hm hk
        exact ⟨E₀, f, fm, fv, cs, rec, h1, h2, h3, h4, h5,
          prefixA_trans h6 (prefixA_extend E r' _ hfresh), h7⟩
  | _, .definitionM E r' _ _ _ hE hfresh _ _ _ _ _ _, r, m, hm, hk => by
      by_cases hr : r = r'
      · subst hr
        rw [members_extendEnvA_self] at hm
        cases hm
        cases hk
      · rw [members_extendEnvA_ne _ _ _ hr] at hm
        obtain ⟨E₀, f, fm, fv, cs, rec, h1, h2, h3, h4, h5, h6, h7⟩ := envWfA_recGroup hE _ _ hm hk
        exact ⟨E₀, f, fm, fv, cs, rec, h1, h2, h3, h4, h5,
          prefixA_trans h6 (prefixA_extend E r' _ hfresh), h7⟩
  | _, .theoremM E r' _ _ hE hfresh _ _ _ _ _ _, r, m, hm, hk => by
      by_cases hr : r = r'
      · subst hr
        rw [members_extendEnvA_self] at hm
        cases hm
        cases hk
      · rw [members_extendEnvA_ne _ _ _ hr] at hm
        obtain ⟨E₀, f, fm, fv, cs, rec, h1, h2, h3, h4, h5, h6, h7⟩ := envWfA_recGroup hE _ _ hm hk
        exact ⟨E₀, f, fm, fv, cs, rec, h1, h2, h3, h4, h5,
          prefixA_trans h6 (prefixA_extend E r' _ hfresh), h7⟩
  | _, .opaqueM E r' _ _ _ hE hfresh _ _ _ _ _ _, r, m, hm, hk => by
      by_cases hr : r = r'
      · subst hr
        rw [members_extendEnvA_self] at hm
        cases hm
        cases hk
      · rw [members_extendEnvA_ne _ _ _ hr] at hm
        obtain ⟨E₀, f, fm, fv, cs, rec, h1, h2, h3, h4, h5, h6, h7⟩ := envWfA_recGroup hE _ _ hm hk
        exact ⟨E₀, f, fm, fv, cs, rec, h1, h2, h3, h4, h5,
          prefixA_trans h6 (prefixA_extend E r' _ hfresh), h7⟩
  | _, .group E f' fm' _ hE hcls' _ _ _ _ _ cs' hfresh', r, m, hm, hk => by
      rcases members_groupEnvA _ r m hm with ⟨_, rfl⟩ | hin | hb
      · rw [hcls'] at hk; cases hk
      · obtain ⟨gc, _, hge⟩ := List.mem_map.mp hin
        have hgm : gc.member = m := congrArg Prod.snd hge
        rw [← hgm, gc.hcls] at hk; cases hk
      · obtain ⟨E₀, f, fm, fv, cs, rec, h1, h2, h3, h4, h5, h6, h7⟩ := envWfA_recGroup hE _ _ hb hk
        exact ⟨E₀, f, fm, fv, cs, rec, h1, h2, h3, h4, h5,
          prefixA_trans h6 (prefixA_groupEnvA hfresh'), h7⟩
  | _, .groupRec E f' fm' _ hE hcls' _ _ _ _ fv' cs' hfresh' hlay' rec' hrfresh', r, m, hm, hk => by
      by_cases hr : r = f' + 1 + cs'.length
      · subst hr
        unfold groupRecEnvA at hm
        rw [members_extendEnvA_self] at hm
        cases hm
        exact ⟨E, f', fm', fv', cs', rec', rfl, rfl, hcls', hfresh', hlay', prefixA_refl _, hrfresh'⟩
      · unfold groupRecEnvA at hm
        rw [members_extendEnvA_ne _ _ _ hr] at hm
        rcases members_groupEnvA _ r m hm with ⟨_, rfl⟩ | hin | hb
        · rw [hcls'] at hk; cases hk
        · obtain ⟨gc, _, hge⟩ := List.mem_map.mp hin
          have hgm : gc.member = m := congrArg Prod.snd hge
          rw [← hgm, gc.hcls] at hk; cases hk
        · obtain ⟨E₀, f, fm, fv, cs, rec, h1, h2, h3, h4, h5, h6, h7⟩ := envWfA_recGroup hE _ _ hb hk
          exact ⟨E₀, f, fm, fv, cs, rec, h1, h2, h3, h4, h5,
            prefixA_trans h6 (prefixA_trans (prefixA_groupEnvA hfresh')
              (prefixA_extend _ _ _ hrfresh')), h7⟩

/-! ## (5) the builders' shapes on the erased side -/

theorem paramLocalsA_eq : (n : Nat) → paramLocalsA n = (List.range n).reverse.map ExprA.bvar
  | 0 => rfl
  | n + 1 => by
      rw [paramLocalsA, paramLocalsA_eq n, List.range_succ, List.reverse_append]
      rfl

/-- the recursor's body, erased: the motive past the minors and indices, applied to the index
    locals and the major (main's `hrecBody`). -/
theorem erase_recBodyA (ni k : Nat) :
    erase (recBodyA ni k) = foldApps (.bvar (k + ni + 1))
      ((List.range ni).reverse.map (fun i => Expr.bvar (i + 1)) ++ [Expr.bvar 0]) := by
  rw [recBodyA, foldAppsA_erase, paramLocalsA_eq, List.map_append, List.map_map, List.map_map]
  have hk : ni + k + 1 = k + ni + 1 := by omega
  rw [hk]
  congr 2
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, liftA, Nat.zero_le, if_true, erase]

/-- the major's domain, erased: the family at its levels over the parameter locals past the
    motive, the minors and the indices, then the index locals (main's `hmajorTy`). -/
theorem erase_majorDomA (f : Nat) (ls : List Level) (np ni k : Nat) :
    erase (liftA ni (k + 1) (famLocalsA f ls np ni)) = foldApps (.const f ls)
      ((List.range np).reverse.map (fun i => Expr.bvar (i + ni + k + 1)) ++
        (List.range ni).reverse.map (fun i => Expr.bvar i)) := by
  rw [famLocalsA, liftA_foldAppsA, foldAppsA_erase, paramLocalsA_eq, paramLocalsA_eq]
  simp only [List.map_append, List.map_map]
  congr 2
  · apply List.map_congr_left
    intro i _
    simp only [Function.comp, liftA, Nat.zero_le, if_true, erase]
    rw [if_pos (Nat.le_add_left ni i)]
    rfl
  · apply List.map_congr_left
    intro i hi
    have hi' : i < ni := by
      rw [List.mem_reverse, List.mem_range] at hi
      exact hi
    simp only [Function.comp, liftA, erase]
    rw [if_neg (by omega)]
    rfl

theorem spineHeadConst_erase_foldAppsA_const (f : Nat) (ls : List Level) (xs : List ExprA) :
    spineHeadConst (erase (foldAppsA (.const f ls) xs)) = true := by
  rw [foldAppsA_erase]
  unfold spineHeadConst
  rw [appsSpine_foldApps]
  rfl

/-- the field telescope's result is a family application with family-free arguments (05 §6),
    when the parameter locals, the plain context and the result indices are free of the family. -/
theorem isFamilyApp_erase_piBodyA_ctorFieldsA (f : Nat) (ls : List Level) (w : Level)
    (res : List ExprA) (hres : ∀ a ∈ res, FreeOfA f a) :
    (fs : List FieldA) → (pl : List ExprA) → (σ : SubstA) → (∀ p ∈ pl, FreeOfA f p) →
    (∀ i, FreeOfA f (σ i)) →
    isFamilyApp f (erase (piBodyA (ctorFieldsA f ls w pl σ fs res).1)) = true
  | [], pl, σ, hpl, hσ => by
      simp only [ctorFieldsA]
      rw [piBodyA_of_not_pi (foldAppsA_const_ne_pi f ls _)]
      apply isFamilyApp_erase_foldAppsA
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hpl x hx
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
        exact constsInA_substA a σ (hres a ha) hσ
  | .plain _ _ :: fs, pl, σ, hpl, hσ => by
      simp only [ctorFieldsA, piBodyA]
      exact isFamilyApp_erase_piBodyA_ctorFieldsA f ls w res hres fs (pl.map (liftA 0 1)) σ.up
        (fun p hp => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          exact constsInA_liftA 1 q 0 (hpl q hq))
        (constsInA_substA.up σ hσ)
  | .drec _ :: fs, pl, σ, hpl, hσ | .frec _ _ _ _ :: fs, pl, σ, hpl, hσ
  | .drecD _ _ :: fs, pl, σ, hpl, hσ => by
      simp only [ctorFieldsA, piBodyA]
      exact isFamilyApp_erase_piBodyA_ctorFieldsA f ls w res hres fs (pl.map (liftA 0 1)) σ.shift1
        (fun p hp => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          exact constsInA_liftA 1 q 0 (hpl q hq))
        (fun i => constsInA_liftA 1 (σ i) 0 (hσ i))

/-- the built constructor type's result is a family application (main's `hfamApp`). -/
theorem isFamilyApp_erase_piBodyA_ctorTypeA (f : Nat) (ls : List Level) (w : Level)
    (mirrors : List (ExprA × Level)) (fields : List FieldA) (res : List ExprA)
    (hres : ∀ a ∈ res, FreeOfA f a) :
    isFamilyApp f (erase (piBodyA (ctorTypeA f ls w mirrors fields res))) = true := by
  unfold ctorTypeA
  simp only
  rw [piBodyA_piTelA]
  exact isFamilyApp_erase_piBodyA_ctorFieldsA f ls w res hres fields _ _
    (paramLocalsA_freeOf f _) (fun _ => trivial)

/-- the built field telescope, erased, is a Π at every field (main's `hctorTel`). -/
theorem isPiTel_erase_ctorFieldsA (f : Nat) (ls : List Level) (w : Level) (res : List ExprA) :
    (fs : List FieldA) → (pl : List ExprA) → (σ : SubstA) →
    isPiTel fs.length (erase (ctorFieldsA f ls w pl σ fs res).1) = true
  | [], _, _ => rfl
  | .plain _ _ :: fs, pl, σ => by
      simp only [ctorFieldsA, erase, List.length_cons, isPiTel]
      exact isPiTel_erase_ctorFieldsA f ls w res fs _ _
  | .drec _ :: fs, pl, σ | .frec _ _ _ _ :: fs, pl, σ | .drecD _ _ :: fs, pl, σ => by
      simp only [ctorFieldsA, erase, List.length_cons, isPiTel]
      exact isPiTel_erase_ctorFieldsA f ls w res fs _ _

/-- every recursive domain of the built telescope is constant-headed, open (main's `hfamTel`), when no
    field is function-recursive. -/
theorem directRecConstHead_erase_ctorFieldsA (f : Nat) (ls : List Level) (w : Level)
    (res : List ExprA) :
    (fs : List FieldA) → (∀ x ∈ fs, x.TreeField) → (pl : List ExprA) → (σ : SubstA) →
    directRecConstHead (fs.map FieldA.kind) (erase (ctorFieldsA f ls w pl σ fs res).1) = true
  | [], _, _, _ => rfl
  | .frec _ _ _ _ :: _, hnf, _, _ => (hnf _ (List.mem_cons_self _ _)).elim
  | .drecD _ _ :: _, hnf, _, _ => (hnf _ (List.mem_cons_self _ _)).elim
  | .plain _ _ :: fs, hnf, pl, σ => by
      simp only [ctorFieldsA, erase, List.map, FieldA.kind, directRecConstHead]
      exact directRecConstHead_erase_ctorFieldsA f ls w res fs (fun y hy => hnf y (List.mem_cons_of_mem _ hy)) _ _
  | .drec _ :: fs, hnf, pl, σ => by
      simp only [ctorFieldsA, erase, List.map, FieldA.kind, directRecConstHead]
      rw [spineHeadConst_erase_foldAppsA_const,
        directRecConstHead_erase_ctorFieldsA f ls w res fs (fun y hy => hnf y (List.mem_cons_of_mem _ hy)) _ _]
      rfl

/-- the built telescope's result is constant-headed, open (main's `hresTel`). -/
theorem resultConstHead_erase_ctorFieldsA (f : Nat) (ls : List Level) (w : Level)
    (res : List ExprA) :
    (fs : List FieldA) → (pl : List ExprA) → (σ : SubstA) →
    resultConstHead (fs.map FieldA.kind) (erase (ctorFieldsA f ls w pl σ fs res).1) = true
  | [], pl, σ => by
      simp only [ctorFieldsA, List.map, resultConstHead]
      exact spineHeadConst_erase_foldAppsA_const _ _ _
  | .plain _ _ :: fs, pl, σ => by
      simp only [ctorFieldsA, erase, List.map, FieldA.kind, resultConstHead]
      exact resultConstHead_erase_ctorFieldsA f ls w res fs _ _
  | .drec _ :: fs, pl, σ | .frec _ _ _ _ :: fs, pl, σ | .drecD _ _ :: fs, pl, σ => by
      simp only [ctorFieldsA, erase, List.map, FieldA.kind, resultConstHead]
      exact resultConstHead_erase_ctorFieldsA f ls w res fs _ _

/-! ## (6) erasure: a step of the copy's ι is a derived ι step of the erased environment -/

/-- the argument-dependent layer, inverted in full: the kinds, the minor, the constructor
    telescope after the parameters, the field walk, and the reduct. -/
theorem iotaReductA_inv {s : RecSpineA} {g : IotaGroupA} {e' : ExprA} (h : iotaReductA s g = some e') :
    ∃ shapes minor ctorAfter,
      ctorShapesA g.familyRef g.nparams (g.ctorM.normA.getD g.ctorM.mtypeA) = some shapes ∧
      s.preMajor[g.nparams + 1 + g.ctorIdx]? = some minor ∧
      applyTelA (s.preMajor.take g.nparams)
        (instantiateLevelsA (s.ls.take g.ctorM.arity)
        (g.ctorM.normA.getD g.ctorM.mtypeA)) = some ctorAfter ∧
      fieldsTelA ((appsSpineA s.major).2.drop g.nparams) shapes ctorAfter = true ∧
      e' = foldAppsA minor (rhsArgsA (.const s.recRef s.ls) s.preMajor g.nparams g.nMinors
        ((appsSpineA s.major).2.drop g.nparams) shapes ctorAfter) := by
  unfold iotaReductA at h
  cases hc : spineHeadRefA s.major with
  | none => simp [hc] at h
  | some c =>
      simp only [hc, Option.some_bind] at h
      split at h
      · cases hk : ctorShapesA g.familyRef g.nparams (g.ctorM.normA.getD g.ctorM.mtypeA) with
        | none => simp [hk] at h
        | some shapes =>
            simp only [hk, Option.some_bind] at h
            cases hm : s.preMajor[g.nparams + 1 + g.ctorIdx]? with
            | none => simp [hm] at h
            | some minor =>
                simp only [hm, Option.some_bind] at h
                cases ha : applyTelA (s.preMajor.take g.nparams)
                    (instantiateLevelsA (s.ls.take g.ctorM.arity)
                      (g.ctorM.normA.getD g.ctorM.mtypeA)) with
                | none => simp [ha] at h
                | some ctorAfter =>
                    simp only [ha, Option.some_bind] at h
                    split at h
                    · rename_i hw
                      injection h with h
                      exact ⟨shapes, minor, ctorAfter, rfl, rfl, rfl, hw, h.symm⟩
                    · exact Option.noConfusion h
      · exact Option.noConfusion h

theorem length_piDomsA (T : ExprA) : (piDomsA T).length = piCountA T := by
  have h := piDomsA_erase_peelPis T
  have := peelPis_length _ _ h
  rw [List.length_map] at this
  exact this

/-- THE LEGACY TREE'S RESTRICTION (R-NoFunRec-1 step 1 (1c-ε3)): no constructor of the environment has a
    function-recursive field, read off its stored type (the shapes `ctorShapesA` reads). `main`'s ι and
    kinds are the tree's, which has no such field; the erasure and the bridge read this premise, which
    `AnnEnvA` carries. It is a property of the environment's members, whatever its admission. -/
def EnvNoFunA (E : ResolvedEnvA) : Prop :=
  ∀ (c : Nat) (cm : CheckedMemberA) (f : Nat) (fm : CheckedMemberA) (shapes : List FieldShape),
    E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
    E.members f = some fm → ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some shapes →
    ∀ s ∈ shapes, ∀ j, s ≠ .recursive (j + 1)

/-- THE ERASURE-INVARIANCE RESTRICTION (R-NoDeltaRec-4d-iii): no constructor's `normA` changes the
    Π-domains the erased reads see — `analyzeFields`, `fieldShapesE`, `peelPis`, `piCountA` and the
    open telescope all read `(piDomsA _).map erase`, and they agree on `normA.getD` and `mtypeA`
    exactly when this holds. At a `drecD`-free member `norm` is the identity and it is immediate;
    at a genuine `drecD` member the normed domain erases to the family application while the stored
    domain erases to its surface form — the two ι's genuinely diverge there, so the erasure
    correspondence is stated under this invariant, a hypothesis beside `AnnEnvA` (the bridge supplies
    it from `GroupInScopeT.hsnd`). It is the `.drecD` boundary of the correspondence, not a by-design
    exclusion: `00_MASTER_CLOSURE_SPEC.md` Erratum E-RowsInScope (5)(b) records R-NoDeltaRec as open. -/
def EnvNormEraseA (E : ResolvedEnvA) : Prop :=
  ∀ (r : Nat) (m : CheckedMemberA), E.members r = some m → m.mclass = .constructorM →
    ∀ T, m.normA = some T → erase T = erase m.mtypeA

/-- the invariant lifts through an extension by a non-constructor member (the family extension
    `extendEnvA E f fmA` adds no `.constructorM`; the group's own members live in `groupEnvA`). -/
theorem EnvNormEraseA.extend {E : ResolvedEnvA} (hn : EnvNormEraseA E) {r : Nat}
    {m : CheckedMemberA} (hm : m.mclass ≠ .constructorM) :
    EnvNormEraseA (extendEnvA E r m) := fun r' m' hm' hmc T hT => by
  by_cases hr : r' = r
  · subst hr; rw [members_extendEnvA_self] at hm'; cases hm'; exact absurd hmc hm
  · rw [members_extendEnvA_ne _ _ _ hr] at hm'; exact hn r' m' hm' hmc T hT

/-- a group constructor of an environment with the restriction has no function-recursive field. -/
theorem viewNoFun_of_envNoFunA {I : IotaIfaceA} {E₀ E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA}
    {fv : FamViewA fm} (hnf : EnvNoFunA E) (gc : GroupCtorA I E₀ f fm fv)
    (hgc : E.members gc.ref = some gc.member) (hf : E.members f = some fm) (hfresh : E₀.members f = none) :
    ∀ x ∈ gc.view.fields, x.NoFun := by
  intro x hx
  cases x with
  | plain _ _ => trivial
  | drec _ => trivial
  | drecD D₀ idx₀ => trivial
  | frec B uB Bs idx =>
      exact absurd rfl (hnf gc.ref gc.member f fm _ hgc gc.hcls gc.view.famRef hf
        (gc.normA_getD.symm ▸ gc.view.shapes hfresh) _
        (List.mem_map_of_mem FieldA.shape hx) Bs.length)

/-- ERASURE AT ι: under the copy's admission, a step of the copy's ι is a derived ι step of the
    erased environment, on the erased terms. The witness is read off the group the recursor
    entered with (`envWfA_recGroup`): its layout and counts from the layers, the shapes main's
    witness pins (the recursor's body and major domain, the constructor's result, the open
    telescope's guards) from the builders, closedness and level bounds from the group's checks. -/
theorem derivedIota_of_iotaFnA {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (hnf : EnvNoFunA EA) (hn : EnvNormEraseA EA) {e e' : ExprA} (h : iotaFnA EA e = some e') :
    Nonempty (DerivedIota (eraseEnv EA) (erase e) (erase e')) := by
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
  -- the normed constructor type erases to the stored one (`EnvNormEraseA`; out of scope at
  -- `drecD` members — R-NoDeltaRec-4d-iii)
  have hNE : erase (gc.member.normA.getD gc.member.mtypeA) = erase gc.member.mtypeA := by
    rw [gc.hnorm]
    exact hn _ _ hmg gc.hcls _ gc.hnorm
  have hdomsN : (piDomsA (gc.member.normA.getD gc.member.mtypeA)).map erase =
      (piDomsA gc.member.mtypeA).map erase := piDomsA_map_erase_of_erase hNE
  -- the reduct's data and the arities
  obtain ⟨shapes, minor, ctorAfter, hshapes, hmin, happ, hwalk, he'⟩ := iotaReductA_inv hr
  obtain ⟨_, _, _, hplen, hlslen, hmlen, har⟩ := iotaReductA_some hr
  simp only at hshapes hmin happ hwalk he' hplen hlslen hmlen har
  rw [gc.normA_getD] at hshapes hmlen
  have hnpF : fv.params.length = fm.nparamsA := fv.nparams
  have hgar : gc.member.arity = fm.arity := gc.harity
  have hrar : rec.member.arity = fm.arity + rec.elim.extra := rec.harity
  have hcp : piCountA gc.member.mtypeA = fv.params.length + gc.view.fields.length := by
    rw [gc.view.stored, piCountA_ctorTypeA, gc.view.mirrors_length, hnpF]
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
  have hkindsM : ctorKindsA f fv.params.length gc.member.mtypeA =
      some (gc.view.fields.map FieldA.kind) := by
    rw [ctorKindsA_eq, ← hdomsN, ← ctorKindsA_eq]
    exact hkinds
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
  -- the witness
  let w : IotaWitness (eraseEnv EA) :=
    { recRef := f + 1 + cs.length
      ctorRef := gc.ref
      ls := ls
      lsC := lsC
      recMember := eraseMember rec.member
      ctorMember := eraseMember gc.member
      hrec := by rw [members_eraseEnv, hmr]; rfl
      hctor := by rw [members_eraseEnv, hmg]; rfl
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
        show fv.params.length + _ = piCount (erase gc.member.mtypeA)
        rw [List.length_map, hfslen, piCountA_erase, hcp]
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
      ctorDoms := (piDomsA gc.member.mtypeA).map erase
      ctorResult := erase (piBodyA gc.member.mtypeA)
      hpeel := by
        show peelPis (fv.params.length + _) (erase gc.member.mtypeA) = _
        rw [List.length_map, hfslen, ← hcp]
        exact piDomsA_erase_peelPis _
      hfamApp := by
        rw [gc.view.stored]
        exact isFamilyApp_erase_piBodyA_ctorTypeA _ _ _ _ _ _ (gc.view.freeOf hfresh.base).2
      hkinds := by
        rw [← List.map_drop, ← ctorKindsA, hkindsM]
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
        show lift 0 1 (erase gc.member.mtypeA) = erase gc.member.mtypeA
        rw [← erase_liftA, gc.hclT 0]
      hlsLen := hlslen
      ctorAfterParams := erase ctorAfter
      hctorAfter := by
        show applyTel ((pre.map erase).take fv.params.length)
          (instantiateLevels ls (erase gc.member.mtypeA)) = some (erase ctorAfter)
        rw [← hNE]
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
  have hL : iotaLhsOf w = erase e := by
    rw [he, foldAppsA_erase, List.map_append, List.map_cons, List.map_nil, hmajE]
    rfl
  have hR : iotaRhsOf w = erase e' := by
    rw [he', foldAppsA_erase, rhsArgsA_erase _ _ _ _ _ _ _ hwalk]
    rfl
  exact ⟨hL ▸ hR ▸ DerivedIota.of w⟩

/-! ## (7) both directions under the copy's admission -/

/-- the constructor a witness of the erased environment reads is one of its recursor's group,
    so its universe arity is at most the redex's list. -/
theorem witness_ctor_arity {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (w : IotaWitness (eraseEnv EA)) {cm : CheckedMemberA} (hcm : EA.members w.ctorRef = some cm) :
    cm.arity ≤ w.ls.length := by
  obtain ⟨recA, hrA, hrE⟩ := members_of_eraseEnv w.hrec
  obtain ⟨ctorA, hcA, hcE⟩ := members_of_eraseEnv w.hctor
  obtain ⟨famA, hfA, hfE⟩ := members_of_eraseEnv w.hfam
  have hrK : recA.mclass = .recursorM := by rw [← w.hrecK, ← hrE]; rfl
  obtain ⟨E₀, f, fm, fv, cs, rec, hrr, hrec, hcls, hfresh, hlay, hpre, _⟩ :=
    envWfA_recGroup hW _ _ hrA hrK
  have hst : rec.member.mtypeA = recTypeA f (canonLevelsA fm.arity) fv.params fv.indices fv.sort
      (rec.elim.motiveLevel fm.arity) (cs.reverse.map GroupCtorA.minorData) := rec.stored
  -- the witness's family is the group's
  have hfamf : w.familyRef = f := by
    obtain ⟨D, ls', hD, hhead⟩ := iotaGroupA_lastDom (iotaGroupA_of_witness w hrA hrE hcA hcE hfA hfE)
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

/-- ANNOTATION AT ι, under the copy's admission: a derived ι step of the erased environment on
    an erased left-hand side is a step of the copy's ι, with a reduct that erases to its
    right-hand side. -/
theorem iotaFnA_of_derivedIota {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (hn : EnvNormEraseA EA)
    {e : ExprA} {rhs : Expr Nat} (hd : DerivedIota (eraseEnv EA) (erase e) rhs) :
    ∃ e', iotaFnA EA e = some e' ∧ erase e' = rhs := by
  obtain ⟨w, hl, hr⟩ := derivedIota_unpack hd
  rw [hr]
  exact iotaFnA_of_witness w hl (fun cm hcm => witness_ctor_arity hW w hcm)
    (fun cm hcm => ((envWfA_levels hW) _ _ hcm).1)
    (fun cm hcm hmc T hT => hn _ _ hcm hmc T hT)

/-! W-1 (e-2), WHAT THE BRIDGE READS OF ι: every step of the copy's ι is a derived ι step of the erased
    environment. Erasure reads exactly this (`RcicAnnErase`), and every admitted environment has it
    (`iotaErasesA_of_envWfA`). It replaces W-1 (b′)'s `NoStructIotaA` (ι at no struct group), which held
    under `PropElimOnlyA` only and is no longer needed: since W-1 (e) the copy's ι and `main`'s agree at
    every group, and annotation lifts `main`'s ι at a struct group to `ConvA.structIota`. -/
/-- the copy's ι steps erase to derived ι steps of the erased environment, at an evidence
    family `D`. The legacy landing's `D` is `DerivedIota`; the typed root's (R-NoFunRec-1 B2)
    is `DerivedIotaT`, the shape-based witness. -/
def IotaErasesTo (D : ResolvedEnv → Expr Nat → Expr Nat → Type) (EA : ResolvedEnvA) : Prop :=
  ∀ e e', iotaFnA EA e = some e' → Nonempty (D (eraseEnv EA) (erase e) (erase e'))

/-- `IotaErasesTo` at the legacy evidence: `main`'s `DerivedIota` (`RecKind` / `analyzeFields`
    reading — W-1 (e-2) above). -/
def IotaErasesA (EA : ResolvedEnvA) : Prop := IotaErasesTo DerivedIota EA

theorem iotaErasesA_of_envWfA {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (hnf : EnvNoFunA EA) (hn : EnvNormEraseA EA) :
    IotaErasesA EA :=
  fun _ _ h => derivedIota_of_iotaFnA hW hnf hn h

/-- R-NoFunRec-1 B2: a step of the copy's ι is a shape-based derived ι step of the erased
    environment. This is the erasure direction's correspondence at the typed root's witness;
    it asks the whnf/δ-aware `fieldShapesFuel` analysis — and `iotaOpenRhs`'s schema — to
    resolve on the erased stored types. -/
def IotaErasesTA (EA : ResolvedEnvA) : Prop := IotaErasesTo DerivedIotaT EA

/-- R-NoFunRec-1 B2: a shape-based derived ι step of the erased environment on an erased
    left-hand side fires the copy's ι, with a reduct that erases to the witness's right-hand
    side — the annotation direction at `DerivedIotaT`. -/
def IotaAnnotatesA (EA : ResolvedEnvA) : Prop :=
  ∀ e rhs, DerivedIotaT (eraseEnv EA) (erase e) rhs →
    ∃ e', iotaFnA EA e = some e' ∧ erase e' = rhs

/-- R-NoFunRec-1 B2: the copy↔typed-root ι correspondence at the shape-based witness, both
    directions bundled. `ann` is the annotation direction (`iotaFnA_of_derivedIotaT`, the
    load-bearing premise of `annConvT`'s ι case); `eraseT` is the erasure direction
    (`derivedIotaT_of_iotaFnA`, the premise of the typed landing's `IotaErasesTo`). Neither
    follows from `EnvWfA` yet — both need the analysis agreement between the copy's
    `ctorShapesA`/`fieldShapeE` readback and `main`'s fuel-bounded `fieldShapesFuel`, and
    `eraseT` needs a `IotaWitnessS` with its fuel adequacy besides — so the migrated
    consumers carry `IotaCorrTA` as a hypothesis (the B3 bridge's debt). -/
structure IotaCorrTA (E : ResolvedEnvA) : Prop where
  ann : IotaAnnotatesA E
  eraseT : IotaErasesTA E

/-- the shape-based witness unpacked, `derivedIota_unpack` at `DerivedIotaT` (the `Type`-valued
    inductive wants the `Σ'` transport, not `cases` at a fixed index). -/
def derivedIotaT_unpack {E : ResolvedEnv} {lhs rhs : Expr Nat} :
    DerivedIotaT E lhs rhs →
    Σ' (w : IotaWitnessS E), (lhs = iotaLhsOfS w) ×' (rhs = iotaRhsOfS w)
  | .of w => ⟨w, rfl, rfl⟩

/-! ## (6c′) the shape-based witness's group

`IotaWitnessS` carries the same member/redex bookkeeping as `IotaWitness` — the
recursor, constructor and family references, the telescope peels and the layout
counts — so the group-identification argument (`iotaGroupA_of_witness`,
`witness_ctor_arity`) lifts verbatim. What it does NOT carry is the direct
computation data (`kinds`/`minor`/`ctorAfterParams`/the telescope guards); those
must be DERIVED from `hshapes`/`hschema`/`CtorViewA` before `iotaReductA` can be
shown to fire (section (6e)). -/

/-- the shape-based witness's recursor, constructor and family identify the same
    `IotaGroupA` as a legacy witness's — the group-read depends only on the
    member references and the recursor/family telescopes, not on the field
    analysis. -/
theorem iotaGroupA_of_witnessS {EA : ResolvedEnvA} (w : IotaWitnessS (eraseEnv EA))
    {recA ctorA famA : CheckedMemberA}
    (hrA : EA.members w.recRef = some recA) (hrE : eraseMember recA = w.recMember)
    (hcA : EA.members w.ctorRef = some ctorA) (hcE : eraseMember ctorA = w.ctorMember)
    (hfA : EA.members w.familyRef = some famA) (hfE : eraseMember famA = w.famMember) :
    iotaGroupA EA w.recRef w.ctorRef =
      some ⟨recA, ctorA, famA, w.ctorRef, w.familyRef, w.nparams, w.nindices, w.nMinors,
        w.ctorIdx⟩ := by
  have hrK : recA.mclass = .recursorM := by rw [← w.hrecK, ← hrE]; rfl
  have hcK : ctorA.mclass = .constructorM := by rw [← w.hctorK, ← hcE]; rfl
  have hfK : famA.mclass = .inductiveM := by rw [← w.hfamK, ← hfE]; rfl
  have hrT : erase recA.mtypeA = w.recMember.mtype := by rw [← hrE]; rfl
  have hfT : erase famA.mtypeA = w.famMember.mtype := by rw [← hfE]; rfl
  -- the recursor's telescope, through erasure
  have hcnt : piCountA recA.mtypeA = w.nparams + 1 + w.nMinors + w.nindices + 1 := by
    rw [← piCountA_erase, hrT, w.hnmin]
  have hpeel := piDomsA_erase_peelPis recA.mtypeA
  rw [hcnt, hrT, w.hpeelRec] at hpeel
  injection hpeel with hpeel
  injection hpeel with hdoms hbody
  -- the major's domain is the last one; its head is the family
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
  -- the recursor's body is `motive indices major`: `nindices + 1` arguments
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
  rw [hrA, hcA]
  simp only
  rw [if_pos ⟨hrK, hcK⟩, hlast]
  simp only
  rw [hDA]
  simp only
  rw [hfA]
  simp only
  rw [if_pos hlay, hcounts]
  simp only [hmin, hcidx]

/-- the shape-based witness's constructor is one of its recursor's group, so its
    universe arity is at most the redex's list — `witness_ctor_arity` at
    `IotaWitnessS`. -/
theorem witness_ctor_arityS {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (w : IotaWitnessS (eraseEnv EA)) {cm : CheckedMemberA} (hcm : EA.members w.ctorRef = some cm) :
    cm.arity ≤ w.ls.length := by
  obtain ⟨recA, hrA, hrE⟩ := members_of_eraseEnv w.hrec
  obtain ⟨ctorA, hcA, hcE⟩ := members_of_eraseEnv w.hctor
  obtain ⟨famA, hfA, hfE⟩ := members_of_eraseEnv w.hfam
  have hrK : recA.mclass = .recursorM := by rw [← w.hrecK, ← hrE]; rfl
  obtain ⟨E₀, f, fm, fv, cs, rec, hrr, hrec, hcls, hfresh, hlay, hpre, _⟩ :=
    envWfA_recGroup hW _ _ hrA hrK
  have hst : rec.member.mtypeA = recTypeA f (canonLevelsA fm.arity) fv.params fv.indices fv.sort
      (rec.elim.motiveLevel fm.arity) (cs.reverse.map GroupCtorA.minorData) := rec.stored
  -- the witness's family is the group's
  have hfamf : w.familyRef = f := by
    obtain ⟨D, ls', hD, hhead⟩ :=
      iotaGroupA_lastDom (iotaGroupA_of_witnessS w hrA hrE hcA hcE hfA hfE)
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

/-! ## (6c½) forward shape agreement — the family-headed (`.drec`) field

`IotaAnnotatesA` at `IotaWitnessS` needs `ctorShapesA` (= `fieldShapesE`, the copy's syntactic
field analysis) to return `w.shapes` (= `fieldShapesFuel`, the admitted semantic analysis) on the
constructor domains `ctorDoms.drop nparams`. The verdicts agree on `CtorViewA.noFun` fields:
`.drec` is built by `ctorTypeA` as the canonical family application `f canon (paramLocals ++ idx)`,
which `whnfFuel` leaves alone (`inductiveM` is not transparent), so `fieldAnalyze`'s telescope is
empty and the only permitting branch is `properFamilyFuel` — the shape is `.recursive 0`. -/

/-- `containsFamilyFuel` under a head already known not to scan `false` stays non-`false` along
    the application spine: peeling an `app` either keeps the head's answer or runs out of fuel. -/
theorem containsFamilyFuel_foldApps_ne_false {E : ResolvedEnv} {fam : Nat} :
    ∀ (args : List (Expr Nat)) (h : Expr Nat),
      (∀ F, containsFamilyFuel E fam F h ≠ some false) →
      ∀ fuel, containsFamilyFuel E fam fuel (foldApps h args) ≠ some false := by
  intro args
  induction args with
  | nil => intro h hh fuel; exact hh fuel
  | cons x xs ih =>
      intro h hh fuel
      rw [foldApps_cons]
      apply ih
      intro F
      cases F with
      | zero => simp [containsFamilyFuel]
      | succ F' =>
          simp only [containsFamilyFuel]
          cases hc : containsFamilyFuel E fam F' h with
          | none => simp [hc]
          | some b =>
              cases b
              · exact absurd hc (hh F')
              · simp [hc]

/-- `containsFamilyFuel` under a family head is never a determined `false`. -/
theorem containsFamilyFuel_constFam_ne_false {E : ResolvedEnv} {fam : Nat}
    (ls : List Level) (args : List (Expr Nat)) (fuel : Nat) :
    containsFamilyFuel E fam fuel (foldApps (.const fam ls) args) ≠ some false :=
  containsFamilyFuel_foldApps_ne_false args (.const fam ls)
    (fun F => by cases F with
      | zero => simp [containsFamilyFuel]
      | succ F' => simp [containsFamilyFuel])
    fuel

/-- a rigid family application permitted by `fieldAnalyze` is `.recursive 0`: the telescope is
    empty (the family head is opaque to `whnfFuel`) and `.nonrecursive` is ruled out because the
    family head is present. -/
theorem fieldAnalyze_famApp_permitted {E : ResolvedEnv}
    {fam nuniv nparams nindices depth : Nat} {fuel : Nat}
    {ls : List Level} {args : List (Expr Nat)}
    (hrig : transparentBody E fam ls = none)
    {s : FieldShape} {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel fam nuniv nparams nindices depth
      (foldApps (.const fam ls) args) = .permitted s idx) :
    s = .recursive 0 := by
  cases fuel with
  | zero => exact FieldAnalyze.noConfusion h
  | succ F =>
      have hsp : appsSpine (foldApps (.const fam ls) args) =
          (.const fam ls, args) := appsSpine_foldApps_const _ _ _
      cases F with
      | zero =>
          simp only [fieldAnalyze, piTelescopeFuel] at h
          exact FieldAnalyze.noConfusion h
      | succ F' =>
          cases F' with
          | zero =>
              simp only [fieldAnalyze, piTelescopeFuel, whnfFuel] at h
              exact FieldAnalyze.noConfusion h
          | succ F'' =>
              have hpt : piTelescopeFuel E (F'' + 2)
                  (foldApps (.const fam ls) args) =
                  some ([], foldApps (.const fam ls) args) := by
                have hw' : whnfFuel E (F'' + 1) (foldApps (.const fam ls) args) =
                    some (foldApps (.const fam ls) args) := by
                  simp only [whnfFuel, hsp, hrig]
                simp only [piTelescopeFuel, hw']
                rcases List.eq_nil_or_concat args with rfl | ⟨xs, x, rfl⟩
                · rfl
                · rw [List.concat_eq_append, foldApps_snoc]
              simp only [fieldAnalyze, hpt, domainsContainFuel] at h
              cases hpf : properFamilyFuel E (F'' + 2) fam nuniv nparams nindices
                  (depth - 1) (foldApps (.const fam ls) args) with
              | none =>
                  simp [hpf] at h
              | some b =>
                  cases b with
                  | true =>
                      simp [hpf] at h
                      exact h.1.symm
                  | false =>
                      simp [hpf] at h
                      cases hcf : containsFamilyFuel E fam (F'' + 2)
                          (foldApps (.const fam ls) args) with
                      | none => simp [hcf] at h
                      | some b =>
                          cases b
                          · exact absurd hcf
                              (containsFamilyFuel_constFam_ne_false ls args _)
                          · rw [hcf, appsSpine_foldApps_const] at h
                            simp at h

/-- `shapeOfKind` is `main`'s `RecKind.shape` — pointwise, for the `.map` transport. -/
theorem shapeOfKind_eq_shape : ∀ k : RecKind, shapeOfKind k = RecKind.shape k := fun k => by
  cases k <;> rfl

/-- `DirectFieldFrag`'s `fuelBound` is a lower bound, so the fragment is fuel-monotone: the
    rigidity clauses are fuel-free, only `fuelBound` mentions `fuel`. -/
theorem DirectFieldFrag.weaken_fuel {E : ResolvedEnv} {T : Expr Nat}
    {fuel fuel' fam nuniv nparams nindices depth : Nat}
    (h : DirectFieldFrag E fuel fam nuniv nparams nindices depth T) (hle : fuel ≤ fuel') :
    DirectFieldFrag E fuel' fam nuniv nparams nindices depth T where
  rigid := h.rigid
  stableTail := h.stableTail
  fuelBound := Nat.le_trans h.fuelBound hle
  canon := h.canon
  noInner := h.noInner

/-- A fuel covering the whole domain list's `fuelBound`s: every member's bound is a summand. -/
def domsFuelBound : List (Expr Nat) → Nat
  | [] => 0
  | T :: Ts => esize T + piCount T + 2 + domsFuelBound Ts

theorem domsFuelBound_ge {Ts : List (Expr Nat)} : ∀ T ∈ Ts,
    esize T + piCount T + 2 ≤ domsFuelBound Ts := by
  induction Ts with
  | nil => intro T h; exact absurd h (List.not_mem_nil _)
  | cons T' Ts' ih =>
      intro T hT
      simp only [domsFuelBound]
      cases List.mem_cons.mp hT with
      | inl h => rw [h]; exact Nat.le_add_right _ _
      | inr h => exact Nat.le_trans (ih T h) (Nat.le_add_left _ _)

/-- THE FORWARD SHAPE AGREEMENT, on the DIRECT fragment. `fieldShapesFuel` is admission's
    semantic field analysis (`fieldAnalyze`, fuel-bounded, δ-aware); `fieldShapesE` is the
    relation's syntactic one (`occursConst`, terminating). On a `DirectFieldFrag` domain list
    — rigid (`noTransparentB`, so δ never fires inside a domain) with a whnf-stable Π-tail —
    the two coincide wherever the semantic read succeeds: `fieldShapesFuel` collapses to
    `analyzeFields` (`fieldShapesFuel_eq_analyzeFields_of_directFrag`), `analyzeFields` is
    `fieldShapesE` at the kinds (`analyzeFields_eq_shapes`), and `shapesKinds`/`shapeOfKind`
    invert on the no-function-recursive fragment. The certificate is what keeps δ from
    surfacing the family inside a `.plain` domain — `noTransparentB`, not the member layout.

    The hypothesis is the fuel-free fragment: each domain admits SOME fuel at which it is a
    `DirectFieldFrag` (the rigidity clauses do not depend on `fuel`, so this is just
    `noTransparentB ∧ headStableB (piTailOf) ∧ canon ∧ noInner`). The common fuel is the
    witness's plus the summed bounds, bridged by `fieldShapesFuel_mono`. -/
theorem fieldShapesE_of_fieldShapesFuel_directFrag {E : ResolvedEnv}
    {wF fam nuniv nparams nindices depth : Nat} {Ts : List (Expr Nat)} {ss : List FieldShape}
    (h : ∀ j (hj : j < Ts.length), ∃ F,
      DirectFieldFrag E F fam nuniv nparams nindices (depth + j) Ts[j])
    (hw : fieldShapesFuel E wF fam nuniv nparams nindices depth Ts = some ss) :
    fieldShapesE fam Ts = some ss := by
  -- a fuel covering every domain's bound and the witness's own fuel
  have hFge : ∀ j (hj : j < Ts.length),
      DirectFieldFrag E (wF + domsFuelBound Ts) fam nuniv nparams nindices
        (depth + j) Ts[j] := by
    intro j hj
    obtain ⟨F, hF⟩ := h j hj
    exact { rigid := hF.rigid, stableTail := hF.stableTail,
            fuelBound := Nat.le_trans
              (domsFuelBound_ge Ts[j] (List.getElem_mem _)) (Nat.le_add_left _ _),
            canon := hF.canon, noInner := hF.noInner }
  have hbig := fieldShapesFuel_eq_analyzeFields_of_directFrag Ts hFge
  have hmono : fieldShapesFuel E (wF + domsFuelBound Ts) fam nuniv nparams nindices
      depth Ts = some ss :=
    fieldShapesFuel_mono E (Nat.le_add_right _ _) hw
  rw [hbig] at hmono
  -- hmono : Option.map (·.map shapeOfKind) (analyzeFields fam Ts) = some ss
  rw [analyzeFields_eq_shapes] at hmono
  cases hfe : fieldShapesE fam Ts with
  | none =>
      simp [hfe] at hmono
  | some ss' =>
      cases hsk : shapesKinds ss' with
      | none => simp [hfe, hsk] at hmono
      | some ks' =>
          have hss' := shapesKinds_eq_map hsk
          simp [hfe, hsk] at hmono
          -- hmono : ks'.map shapeOfKind = ss ; hss' : ss' = ks'.map RecKind.shape
          have : ss' = ss := by
            rw [hss', ← hmono]
            exact List.map_congr_left (fun k _ => (shapeOfKind_eq_shape k).symm)
          rw [this]

/-! ## (6d) the erased weak-head bridge

`whnfFuel` on the erased environment is a β/ζ/δ SUBSTRATEGY of `hStepFnA` iterated by `whnfA`:
the three `whnfFuel` head cases — β at a λ-application spine, ζ at a `letE` spine, δ at a
transparent-constant spine — are `hStepFnA` arms, and `whnfFuel` reads no context (the `.bvar`
case, a local ζ on the copy, cannot fire; nor can ι, the struct or the major arm, or `lit`).
Consequences used by the shape analysis (`piTelescopeFuel`, `fieldShapesFuel`, `iotaOpenRhs`):

* TERMINATION: a `whnfA` witness for `X` bounds a `whnfFuel` witness for `erase X`
  (`whnfFuel_term_of_whnfA`) — every erased `whnfFuel` step is one of `hStepFnA`'s, so the
  erased trace is no longer than the typed one.
* SHAPE at a normal form: `hStepFnA X = none` forces `whnfFuel` to stop at `erase X`
  (`whnfFuel_normal_of_hStep_none`). -/

/-- the erased environment's transparent body is the erased annotated body's level instance. -/
theorem transparentBody_eraseEnv {EA : ResolvedEnvA} {r : Nat} {ls : List Level} :
    transparentBody (eraseEnv EA) r ls =
      match EA.members r with
      | some mA =>
          if transparent mA.mclass then
            match mA.bodyA with
            | some b => some (instantiateLevels ls (erase b))
            | none => none
          else none
      | none => none := by
  unfold transparentBody
  rw [members_eraseEnv]
  cases hm : EA.members r with
  | none => rfl
  | some mA =>
      simp only [Option.map_some', eraseMember]
      by_cases htr : transparent mA.mclass = true
      · rw [if_pos htr]
        cases hb : mA.bodyA <;> simp [hb, htr]
      · simp only [htr, Bool.false_eq_true, if_false]

/-- an `hStepFnA` step propagates along the spine: the head's reduct folds over the same
    arguments. -/
theorem hStepFnA_foldAppsA_some (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA)
    {f f' : ExprA} (hf : hStepFnA E iota Γ f = some f') :
    (args : List ExprA) →
      hStepFnA E iota Γ (foldAppsA f args) = some (foldAppsA f' args)
  | [] => hf
  | a :: as => hStepFnA_foldAppsA_some E iota Γ (hStepFnA_app_head E iota Γ a hf) as

/-- β: a λ-headed spine steps to the instantiated body refolded. -/
theorem hStepFnA_foldAppsA_lam (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA)
    (A : ExprA) (u : Level) (b a : ExprA) (rest : List ExprA) :
    hStepFnA E iota Γ (foldAppsA (.lam A u b) (a :: rest)) =
      some (foldAppsA (instantiate0A a b) rest) :=
  hStepFnA_foldAppsA_some E iota Γ (hStepFnA_app_lam E iota Γ A u b a) rest

/-- ζ: a `letE`-headed spine steps to the instantiated body refolded (at any argument list,
    empty included). -/
theorem hStepFnA_foldAppsA_letE (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA)
    (A v b : ExprA) (args : List ExprA) :
    hStepFnA E iota Γ (foldAppsA (.letE A v b) args) =
      some (foldAppsA (instantiate0A v b) args) :=
  hStepFnA_foldAppsA_some E iota Γ
    (rfl : hStepFnA E iota Γ (.letE A v b) = some _) args

/-- δ: a transparent-constant-headed spine steps to the instantiated body refolded. -/
theorem hStepFnA_foldAppsA_const (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA)
    {r : Nat} {ls : List Level} {mA : CheckedMemberA} {bA : ExprA}
    (hm : E.members r = some mA) (ht : transparent mA.mclass = true) (hb : mA.bodyA = some bA)
    (args : List ExprA) :
    hStepFnA E iota Γ (foldAppsA (.const r ls) args) =
      some (foldAppsA (instantiateLevelsA ls bA) args) := by
  have hc : hStepFnA E iota Γ (.const r ls) = some (instantiateLevelsA ls bA) := by
    show (match E.members r with
      | some m => if transparent m.mclass then m.bodyA.map (instantiateLevelsA ls) else none
      | none => none) = _
    rw [hm]
    show (if transparent mA.mclass then mA.bodyA.map (instantiateLevelsA ls) else none) = _
    rw [if_pos ht, hb, Option.map_some']
  exact hStepFnA_foldAppsA_some E iota Γ hc args

/-- the erased spine of an annotated spine whose head is not an application is the erased
    head and the erased arguments. -/
theorem appsSpine_erase_foldAppsA {h : ExprA} (hna : ∀ f x, h ≠ .app f x)
    (args : List ExprA) :
    appsSpine (erase (foldAppsA h args)) = (erase h, args.map erase) := by
  rw [foldAppsA_erase, appsSpine_foldApps]
  have h2 : appsSpine (erase h) = (erase h, []) := by
    cases h with
    | app f x => exact absurd rfl (hna f x)
    | _ => rfl
  rw [h2]
  rfl

/-- `whnfFuel` at `fuel + 1` on `erase X` either follows the `hStepFnA` step — the erased
    reduct is `erase X'`, so the computation continues at `fuel` — or stops at `erase X`,
    `some`-valued at once. The second disjunct covers exactly the steps `whnfFuel` does not
    know: local ζ (a `.bvar` head — `whnfFuel` has no context), ι, the struct and major arms,
    and `lit`-expansion. -/
theorem whnfFuel_step_or_normal {EA : ResolvedEnvA} {iota : IotaFnA} {Γ : LCtxA}
    {X X' : ExprA} (hs : hStepFnA EA iota Γ X = some X') (fuel : Nat) :
    whnfFuel (eraseEnv EA) (fuel + 1) (erase X) =
        whnfFuel (eraseEnv EA) fuel (erase X') ∨
      whnfFuel (eraseEnv EA) (fuel + 1) (erase X) = some (erase X) := by
  have hfold : X = foldAppsA (appsSpineA X).1 (appsSpineA X).2 := (foldAppsA_appsSpineA X).symm
  generalize hsp : appsSpineA X = S at hs hfold
  obtain ⟨h, args⟩ := S
  have hna : ∀ f x, h ≠ .app f x := fun f x e =>
    appsSpineA_fst_not_app X f x (by rw [hsp]; exact e)
  have hse : appsSpine (erase X) = (erase h, args.map erase) := by
    rw [hfold]; exact appsSpine_erase_foldAppsA hna args
  subst hfold
  rw [whnfFuel, hse]
  cases h with
  | lam A u b =>
      simp only [erase]
      cases args with
      | nil => exact Or.inr rfl
      | cons a rest =>
          simp only [List.map_cons, List.map_nil]
          left
          have hX' : X' = foldAppsA (instantiate0A a b) rest :=
            Option.some.inj (hs.symm.trans (hStepFnA_foldAppsA_lam EA iota Γ A u b a rest))
          subst hX'
          show whnfFuel (eraseEnv EA) fuel
              (foldApps (instantiate0 (erase a) (erase b)) (rest.map erase)) =
            whnfFuel (eraseEnv EA) fuel (erase (foldAppsA (instantiate0A a b) rest))
          rw [← erase_instantiate0A, ← foldAppsA_erase]
  | letE A v b =>
      simp only [erase]
      left
      have hX' : X' = foldAppsA (instantiate0A v b) args :=
        Option.some.inj (hs.symm.trans (hStepFnA_foldAppsA_letE EA iota Γ A v b args))
      subst hX'
      show whnfFuel (eraseEnv EA) fuel
          (foldApps (instantiate0 (erase v) (erase b)) (args.map erase)) =
        whnfFuel (eraseEnv EA) fuel (erase (foldAppsA (instantiate0A v b) args))
      rw [← erase_instantiate0A, ← foldAppsA_erase]
  | const r ls =>
      simp only [erase]
      cases hTB : transparentBody (eraseEnv EA) r ls with
      | none => exact Or.inr rfl
      | some body =>
          rw [transparentBody_eraseEnv] at hTB
          cases hm : EA.members r with
          | none => rw [hm] at hTB; exact Option.noConfusion hTB
          | some mA =>
              simp only [hm] at hTB
              cases htr : transparent mA.mclass with
              | false =>
                  simp only [htr, Bool.false_eq_true, if_false] at hTB
                  exact Option.noConfusion hTB
              | true =>
                  simp only [htr, if_true] at hTB
                  cases hbod : mA.bodyA with
                  | none =>
                      simp only [hbod] at hTB
                      exact Option.noConfusion hTB
                  | some bA =>
                      simp only [hbod] at hTB
                      injection hTB with hTB; subst hTB
                      left
                      have hX' : X' = foldAppsA (instantiateLevelsA ls bA) args :=
                        Option.some.inj (hs.symm.trans
                          (hStepFnA_foldAppsA_const EA iota Γ hm htr hbod args))
                      subst hX'
                      show whnfFuel (eraseEnv EA) fuel
                          (foldApps (instantiateLevels ls (erase bA)) (args.map erase)) =
                        whnfFuel (eraseEnv EA) fuel
                          (erase (foldAppsA (instantiateLevelsA ls bA) args))
                      rw [← erase_instantiateLevelsA, ← foldAppsA_erase]
  | _ => exact Or.inr rfl

/-- `hStepFnA`-normal erases to `whnfFuel`-normal: the erased spine has no λ-application, no
    `letE` head and no resolvable transparent head — those are the only `whnfFuel` cases, and
    each would force an `hStepFnA` step. -/
theorem whnfFuel_normal_of_hStep_none {EA : ResolvedEnvA} {iota : IotaFnA} {Γ : LCtxA}
    {X : ExprA} (hs : hStepFnA EA iota Γ X = none) (fuel : Nat) :
    whnfFuel (eraseEnv EA) (fuel + 1) (erase X) = some (erase X) := by
  have hfold : X = foldAppsA (appsSpineA X).1 (appsSpineA X).2 := (foldAppsA_appsSpineA X).symm
  generalize hsp : appsSpineA X = S at hs hfold
  obtain ⟨h, args⟩ := S
  have hna : ∀ f x, h ≠ .app f x := fun f x e =>
    appsSpineA_fst_not_app X f x (by rw [hsp]; exact e)
  have hse : appsSpine (erase X) = (erase h, args.map erase) := by
    rw [hfold]; exact appsSpine_erase_foldAppsA hna args
  subst hfold
  rw [whnfFuel, hse]
  cases h with
  | lam A u b =>
      simp only [erase]
      cases args with
      | nil => rfl
      | cons a rest =>
          simp only [List.map_cons, List.map_nil]
          exact Option.noConfusion (hs.symm.trans
            (hStepFnA_foldAppsA_lam EA iota Γ A u b a rest))
  | letE A v b =>
      simp only [erase]
      exact Option.noConfusion (hs.symm.trans
        (hStepFnA_foldAppsA_letE EA iota Γ A v b args))
  | const r ls =>
      simp only [erase]
      cases hTB : transparentBody (eraseEnv EA) r ls with
      | none => rfl
      | some body =>
          rw [transparentBody_eraseEnv] at hTB
          cases hm : EA.members r with
          | none => rw [hm] at hTB; exact Option.noConfusion hTB
          | some mA =>
              simp only [hm] at hTB
              cases htr : transparent mA.mclass with
              | false =>
                  simp only [htr, Bool.false_eq_true, if_false] at hTB
                  exact Option.noConfusion hTB
              | true =>
                  simp only [htr, if_true] at hTB
                  cases hbod : mA.bodyA with
                  | none =>
                      simp only [hbod] at hTB
                      exact Option.noConfusion hTB
                  | some bA =>
                      exact Option.noConfusion (hs.symm.trans
                        (hStepFnA_foldAppsA_const EA iota Γ hm htr hbod args))
  | _ => rfl

/-- TERMINATION TRANSFER: `whnfA` computes `X`'s head normal form in `fuel` steps; then
    `whnfFuel` terminates on `erase X` within `fuel + 1`. Every erased step is an `hStepFnA`
    step, so the erased trace cannot outlive the typed one — the fuel slack of `+1` pays for
    the terminal non-stepping check. -/
theorem whnfFuel_term_of_whnfA {EA : ResolvedEnvA} {iota : IotaFnA} {Γ : LCtxA} :
    ∀ {fuel : Nat} {X N : ExprA}, whnfA EA iota Γ fuel X = some N →
      ∃ w : Expr Nat, whnfFuel (eraseEnv EA) (fuel + 1) (erase X) = some w := by
  intro fuel
  induction fuel with
  | zero =>
      intro X N h
      cases hs : hStepFnA EA iota Γ X with
      | none =>
          rw [whnfA_of_normal EA iota Γ 0 X hs] at h
          injection h with hN; subst hN
          exact ⟨erase X, whnfFuel_normal_of_hStep_none hs 0⟩
      | some X' =>
          have hz : whnfA EA iota Γ 0 X = none := by simp only [whnfA, hs]
          rw [hz] at h; exact Option.noConfusion h
  | succ k ih =>
      intro X N h
      cases hs : hStepFnA EA iota Γ X with
      | none =>
          rw [whnfA_of_normal EA iota Γ (k + 1) X hs] at h
          injection h with hN; subst hN
          exact ⟨erase X, whnfFuel_normal_of_hStep_none hs (k + 1)⟩
      | some X' =>
          have step : whnfA EA iota Γ (k + 1) X = whnfA EA iota Γ k X' := by
            simp only [whnfA, hs]
          rw [step] at h
          obtain ⟨w, hw⟩ := ih h
          rcases whnfFuel_step_or_normal hs (k + 1) with e | e
          · rw [e]; exact ⟨w, hw⟩
          · exact ⟨erase X, e⟩

/-! ### The rigidity certificates (what gates `iotaCorrTA_of_envWfA`)

The unconditional `∀ EA, IotaCorrTA EA` is FALSE — on a non-rigid constructor field
(a transparent constant reaching the family through its δ-body, like `drFamEnv`'s
`Id F`) the semantic `fieldShapesFuel` and the syntactic `fieldShapesE` genuinely
diverge, so neither direction can be proved. The certificate is the DIRECT
fragment of `RcicIotaShapeAdapter`: each post-parameter constructor field domain
is `DirectFieldFrag` — `noTransparentB` (δ cannot surface the family), a
whnf-stable Π-tail, the canonical family-head shape where the head is the family,
and no inner-recursive escape — at SOME fuel.  Two statements, at the two witness
types:

* `EnvCorrEraseCert E`: every legacy `IotaWitness` over `E` adapts to a typed
  `IotaWitnessS` — `iotaWitnessSB` succeeds at some fuel.  This is the erasure
  direction's whole debt (fragment + closure + the decided schema/RHS equality).

* `EnvCorrAnnCert E`: every shape-based `IotaWitnessS`'s field domains are
  `DirectFieldFrag` — enough for the annotation direction's shape agreement
  (`fieldShapesE_of_fieldShapesFuel_directFrag`), since `ann` needs no fuel
  existence.

On the admitted fixtures the two coincide: every `CtorViewA`/`EnvWfA` field is
rigid and Π-normal (`#eval`: `noTransparentB`/`headStableB`/`directFragCheck`/
`iotaWitnessStableB`/`iotaWitnessSB` are `true` on `natEnv`, `natEnvU`,
`listEnv`, `vecEnv`, `vecEnvDecoy`), and the only non-rigid admitted field —
`drFamEnv`'s `Id F` — is where `fieldShapeE` already returns `none`, so `iotaFnA`
never fires there (`IotaErasesTA` is vacuous) while `fieldShapesFuel` does admit
it (`fieldAnalyze` reaches `F` through `Id`'s transparent body): `drFamEnv` fails
`EnvCorrAnnCert`, as it must. -/

/-- THE ANNOTATION-DIRECTION RECOGNIZER on a shape-based witness — the sibling of
    `iotaWitnessSB` for `IotaWitnessS` (which carries its schema, not the legacy
    kinds).  Three conjuncts:

    (i) `directFragCheck` on the post-parameter constructor field domains, at the
    domain list's own fuel bound (`domsFuelBound` — `fuelBound` is then free, so
    this checks exactly the meaningful clauses: `noTransparentB`, whnf-stable
    Π-tail, canonical family shape, no inner-recursive escape);
    (ii) the constructor's parameters apply (`applyTel` on the stored type at the
    constructor-side levels) and the erased fields walk the resulting telescope
    under the guard (`fieldsTelS`) — the copy's `iotaReductA` gates;
    (iii) the decided schema/RHS agreement: `iotaRhsOfS w` equals the minor applied
    to the copy's `rhsArgsS` walk — the equality `erase e' = iotaRhsOfS w` that the
    annotation direction owes is CHECKED, not assumed; a witness whose typed schema
    and the copy's walk disagree is refused and reported.

    Where any conjunct fails `IotaAnnotatesA`'s obligation for the witness is
    refused rather than asserted. -/
def iotaWitnessSAnnB (E : ResolvedEnv) (w : IotaWitnessS E) : Bool :=
  directFragCheck E (domsFuelBound (w.ctorDoms.drop w.nparams))
      w.familyRef w.famMember.arity w.nparams w.nindices w.nparams
      (w.ctorDoms.drop w.nparams) &&
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

/-- `iotaWitnessSAnnB` decomposed: the pointwise DIRECT fragment, the parameter
    application, the field-telescope guard, the minor, and the decided
    schema/`rhsArgsS` agreement. -/
theorem iotaWitnessSAnnB_parts {E : ResolvedEnv} {w : IotaWitnessS E}
    (h : iotaWitnessSAnnB E w = true) :
    (∀ j (hj : j < (w.ctorDoms.drop w.nparams).length),
        DirectFieldFrag E (domsFuelBound (w.ctorDoms.drop w.nparams))
          w.familyRef w.famMember.arity w.nparams w.nindices
          (w.nparams + j) ((w.ctorDoms.drop w.nparams)[j])) ∧
    ∃ (ctorAfter minor : Expr Nat),
      applyTel (w.preMajor.take w.nparams)
        (instantiateLevels (w.ls.take w.ctorMember.arity) w.ctorMember.mtype) =
          some ctorAfter ∧
      fieldsTelS w.fields w.shapes ctorAfter = true ∧
      w.preMajor[w.nparams + 1 + w.ctorIdx]? = some minor ∧
      iotaRhsOfS w = foldApps minor
        (rhsArgsS (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
          w.fields w.shapes ctorAfter) := by
  unfold iotaWitnessSAnnB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hfrag, hrest⟩ := h
  refine ⟨fun j hj => directFragCheck_getElem _ hj hfrag, ?_⟩
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

/-- ERASURE certificate: every legacy ι witness of the erased environment adapts
    to the typed shape-based witness at some fuel.  `iotaWitnessSB`'s three
    conjuncts — the DIRECT fragment (`directFragCheck`), the closure check
    (`iotaWitnessStableB`), and the decided schema/RHS equality — are all checked;
    where any of them fails the witness is refused and `IotaErasesTA`'s obligation
    for it is reported rather than asserted. -/
def EnvCorrEraseCert (E : ResolvedEnv) : Prop :=
  ∀ w : IotaWitness E, ∃ fuel, iotaWitnessSB w fuel = true

/-- ANNOTATION certificate: every shape-based witness of the erased environment
    passes the annotation recognizer `iotaWitnessSAnnB` — the DIRECT fragment on
    its constructor's field domains (which yields the `fieldShapesE`/`ctorShapesA`
    agreement through `fieldShapesE_of_fieldShapesFuel_directFrag`), the
    parameter-telescope application and field guard, and the decided schema/RHS
    agreement.  `DerivedIotaT` already carries the semantic `fieldShapesFuel`/
    `iotaOpenRhs` success, so `ann` needs no fuel existence — only this per-witness
    conditional agreement. -/
def EnvCorrAnnCert (E : ResolvedEnv) : Prop :=
  ∀ w : IotaWitnessS E, iotaWitnessSAnnB E w = true

/-- member inclusion on resolved environments: every member of `E₀` is a member of
    `E`, unchanged.  The environment bridge walks the prefixes of its target, so
    the correspondence premise is quantified over them (`CorrCertsBelow`). -/
def EnvSub (E₀ E : ResolvedEnv) : Prop :=
  ∀ r m, E₀.members r = some m → E.members r = some m

theorem envSub_refl (E : ResolvedEnv) : EnvSub E E := fun _ _ h => h

theorem envSub_trans {E₀ E₁ E₂ : ResolvedEnv} (h₁ : EnvSub E₀ E₁) (h₂ : EnvSub E₁ E₂) :
    EnvSub E₀ E₂ := fun r m h => h₂ r m (h₁ r m h)

/-- extending at a fresh reference keeps the base a prefix. -/
theorem envSub_extendEnv {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (h : E.members r = none) : EnvSub E (extendEnv E r m) := fun r' m' h' => by
  by_cases hr : r' = r
  · subst r'; rw [h] at h'; exact Option.noConfusion h'
  · show (if r' = r then some m else E.members r') = some m'
    rw [if_neg hr]; exact h'

/-- the correspondence certificates at EVERY sub-environment of `E`: the premise
    `envBridge`/`envBridgeSem` discharge `IotaCorrTA` from at each intermediate
    prefix they construct.  Per target environment, per witness, decided by
    `iotaWitnessSB`/`iotaWitnessSAnnB` — never the universal
    `∀ EA, IotaCorrTA EA`, which is false on divergent environments. -/
def CorrCertsBelow (E : ResolvedEnv) : Prop :=
  ∀ E₀ : ResolvedEnv, EnvSub E₀ E → EnvCorrEraseCert E₀ ∧ EnvCorrAnnCert E₀

/-- ERASURE AT ι, the typed landing: under the copy's admission, the tree
    restriction (`EnvNoFunA`, for `derivedIota_of_iotaFnA`'s legacy witness) AND
    the erasure certificate, a step of the copy's ι is a shape-based derived ι
    step of the erased environment.  The legacy witness comes from
    `derivedIota_of_iotaFnA`; the certificate adapts it (`iotaWitnessSOf`),
    preserving the two sides. -/
theorem iotaErasesTA_of_envWfA {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (hnf : EnvNoFunA EA) (hn : EnvNormEraseA EA) (hC : EnvCorrEraseCert (eraseEnv EA)) :
    IotaErasesTA EA :=
  fun e e' h => by
  obtain ⟨d⟩ := derivedIota_of_iotaFnA hW hnf hn h
  obtain ⟨w, hl, hr⟩ := derivedIota_unpack d
  obtain ⟨F, hB⟩ := hC w
  rw [hl, hr, ← iotaLhsOfS_iotaWitnessSOf w F hB, ← iotaRhsOfS_iotaWitnessSOf w F hB]
  exact ⟨.of (iotaWitnessSOf w F hB)⟩

/-- The ann-side shape agreement at a shape-based witness: under the certificate,
    `fieldShapesE` on the erased post-parameter domains returns the witness's shapes —
    `fieldShapesE_of_fieldShapesFuel_directFrag` instantiated at `w.hshapes`. -/
theorem fieldShapesE_of_witnessS {E : ResolvedEnv} (hC : EnvCorrAnnCert E)
    (w : IotaWitnessS E) :
    fieldShapesE w.familyRef (w.ctorDoms.drop w.nparams) = some w.shapes :=
  fieldShapesE_of_fieldShapesFuel_directFrag
    (fun j hj => ⟨_, (iotaWitnessSAnnB_parts (hC w)).1 j hj⟩) w.hshapes

/-- ... and at the copy's `ctorShapesA` read: the witness's constructor member's
    erased domains are `w.ctorDoms` (`hpeel` through `piDomsA_erase_peelPis`), so the
    syntactic field analysis the copy's ι gates on returns `w.shapes`. -/
theorem ctorShapesA_of_witnessS {EA : ResolvedEnvA}
    (w : IotaWitnessS (eraseEnv EA))
    (hF : ∀ j (hj : j < (w.ctorDoms.drop w.nparams).length), ∃ F,
      DirectFieldFrag (eraseEnv EA) F w.familyRef w.famMember.arity w.nparams
        w.nindices (w.nparams + j) ((w.ctorDoms.drop w.nparams)[j]))
    {ctorA : CheckedMemberA} (hcE : eraseMember ctorA = w.ctorMember) :
    ctorShapesA w.familyRef w.nparams ctorA.mtypeA = some w.shapes := by
  have hfe := fieldShapesE_of_fieldShapesFuel_directFrag hF w.hshapes
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

/-! ### Decomposition (what `iotaCorrTA_of_envWfA` reduces to)

`iotaFnA` (`iotaReductA`) classifies the constructor's fields through **erasure** by
`ctorShapesA`/`fieldShapesE` — `fieldShapeE` is the *syntactic* analysis (`occursConst`,
`piTelE`, `isFamilyApp`; terminating, fuel-free). `DerivedIotaT`/`IotaWitnessS` classifies the same
erased domains by `fieldShapesFuel` — `fieldAnalyze` is the *semantic* analysis
(`piTelescopeFuel`/`whnfFuel`/`containsFamilyFuel`/`properFamilyFuel`; fuel-bounded, δ-aware).
The correspondence is per-field `fieldShapeE` ↔ `fieldAnalyze` agreement plus
`iotaOpenRhs`/`rhsArgsA` schema agreement.

* VERDICTS coincide on the `CtorViewA.noFun` fragment: `.plain D u` (f-free) is `.nonrecursive`
  both ways (freshness — `CtorViewA.freeOf` and the `EnvWfA` prefix — means δ unfolding never
  reveals the fresh family `f`); `.drec idx` is `.recursive 0`/`directRec` both ways, and
  `ctorTypeA` builds it as the canonical `f canonLevels (paramLocalsA ++ idx)`, so
  `properFamilyFuel` recognizes it. So the *verdicts* agree — what remains is *termination*.

* `IotaAnnotatesA` (ann) needs **no** fuel existence: `DerivedIotaT` already carries a
  `fieldShapesFuel`-success at a stored `fuel`, so `fieldAnalyze = .permitted` is a witnessed
  fact. It reduces to the conditional per-field agreement `fieldAnalyze = .permitted s _ →
  fieldShapeE = some s` (`containsFamilyFuel = some false → occursConst = false` by a complete
  scan; `.recursive 0` by canonical recognition) plus the `iotaFnA_of_witness`-style spine
  decode at `IotaWitnessS`.

* `IotaErasesTA` (eraseT) needs fuel **existence** — `fieldShapeE`-success must yield
  `fieldShapesFuel`-success at some produced `fuel`. That terminates because (a)
  `containsFamilyFuel`-δ-closure is finite (member-rank / δ-DAG acyclicity, provable from
  `EnvWfA`), and (b) `piTelescopeFuel`'s iterated-whnf depth on a `.plain` domain `erase D`
  (`D : HasTyA E Γ (sort u)`) is the arity of `nf D` — this is the **typed-SN** gap: `EnvWfA`
  gives `HasTyA` but no `Acc`/normal-form bound, so `.plain` domains that are non-rigid
  (transparent consts, non-whnf-normal Π-tails) have no syntactic fuel bound. For `rigid`
  fields (`noTransparentB`+`headStableB`) `piTelescopeFuel`/`containsFamilyFuel` collapse to
  `esize`/`piCount`-bounded scans — the `DirectFieldFrag`/`iotaWitnessSB` certificate
  fragment — but `iotaFnA` does not gate on `directFragCheck`, so bare `EnvWfA` does not bound
  the non-rigid `.plain` tower. Sound resolutions: prove typed-SN, or restrict the
  correspondence/`iotaFnA`'s shape check to the certifiable fragment. -/

/-- ANNOTATION AT ι, the typed witness: a shape-based `IotaWitnessS` of the erased
    environment — certified by `iotaWitnessSAnnB` (the DIRECT fragment on the
    constructor's field domains, the parameter application and field-telescope
    guard, and the decided schema/`rhsArgsS` agreement) — makes the copy's ι fire
    on every annotation of its left-hand side, and the reduct erases to the
    witness's schema-instantiated right-hand side.  The constructor's universe
    arity bound is `hL` — `witness_ctor_arityS` discharges it under the admission,
    and a pin discharges it by computation; `hN` is the stored-type/`normA`
    agreement `iotaReductA` reads, through erasure (R-NoDeltaRec-4d-iii:
    `EnvNormEraseA` at the constructor — `envWfA_normEq`'s syntactic equality is
    false at a `.drecD` member, `drCtorMemberA_diverge`). -/
theorem iotaFnA_of_witnessS {EA : ResolvedEnvA}
    (w : IotaWitnessS (eraseEnv EA)) (hB : iotaWitnessSAnnB (eraseEnv EA) w = true)
    (hL : ∀ cm, EA.members w.ctorRef = some cm → cm.arity ≤ w.ls.length)
    (hN : ∀ cm, EA.members w.ctorRef = some cm → cm.mclass = .constructorM →
      ∀ T, cm.normA = some T → erase T = erase cm.mtypeA)
    {e : ExprA} (he : erase e = iotaLhsOfS w) :
    ∃ e', iotaFnA EA e = some e' ∧ erase e' = iotaRhsOfS w := by
  obtain ⟨hfrag, ctorAfterE, minorE, happE, hwalkE, hminE', hrhsE⟩ :=
    iotaWitnessSAnnB_parts hB
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
  -- the shapes, through erasure and the fragment
  have hshapes : ctorShapesA w.familyRef w.nparams ctorA.mtypeA = some w.shapes :=
    ctorShapesA_of_witnessS w (fun j hj => ⟨_, hfrag j hj⟩) hcE
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

/-- ANNOTATION AT ι, the typed landing: under the copy's admission AND the
    annotation certificate, a shape-based derived ι step of the erased
    environment on an erased left-hand side fires the copy's ι, with a reduct
    erasing to the witness's right-hand side. -/
theorem iotaAnnotatesA_of_envWfA {I : IotaIfaceA} {EA : ResolvedEnvA}
    (hW : EnvWfA I EA) (hn : EnvNormEraseA EA) (hC : EnvCorrAnnCert (eraseEnv EA)) :
    IotaAnnotatesA EA :=
  fun e rhs hd => by
    obtain ⟨w, hl, hr⟩ := derivedIotaT_unpack hd
    subst hr
    exact iotaFnA_of_witnessS w (hC w) (fun cm h => witness_ctor_arityS hW w h)
      (fun cm hcm => hn _ _ hcm) hl

/-- THE ι CORRESPONDENCE AT THE TYPED ROOT, conditionally: under the copy's
    admission, the tree restriction (`EnvNoFunA`, for the erasure direction's
    legacy witness), the erasure certificate and the annotation certificate —
    the two per-witness checks `iotaWitnessSB`/`iotaWitnessSAnnB` — both
    directions hold.  The unconditional `∀ EA, IotaCorrTA EA` is false
    (`drFamEnv`'s `Id F` field is where the analyses diverge); the certificates
    are the honest gate — each is discharged per witness by `decide` on the
    rigid fixtures and refuses the divergent ones. -/
theorem iotaCorrTA_of_envWfA {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (hnf : EnvNoFunA EA) (hn : EnvNormEraseA EA)
    (hCe : EnvCorrEraseCert (eraseEnv EA)) (hCa : EnvCorrAnnCert (eraseEnv EA)) :
    IotaCorrTA EA where
  ann := iotaAnnotatesA_of_envWfA hW hn hCa
  eraseT := iotaErasesTA_of_envWfA hW hnf hn hCe

/-- the legacy→typed evidence upgrade, discharged at a certified environment:
    every legacy ι witness adapts to a shape-based one at some fuel
    (`EnvCorrEraseCert` — `iotaWitnessSB`), so a `DerivedIota` step has a
    `DerivedIotaT` step at the same endpoints.  This is the `hιAdapt` residual's
    honest form — per-environment, per-witness, decided; the universal
    `∀ E, DerivedIota E lhs rhs → Nonempty (DerivedIotaT E lhs rhs)` is false
    where a witness fails the DIRECT fragment (`drFamEnv`'s transparent `Id F`
    field). -/
theorem derivedIotaT_of_derivedIota {E : ResolvedEnv} {lhs rhs : Expr Nat}
    (hC : EnvCorrEraseCert E) (d : DerivedIota E lhs rhs) :
    Nonempty (DerivedIotaT E lhs rhs) := by
  obtain ⟨w, hl, hr⟩ := derivedIota_unpack d
  obtain ⟨F, hB⟩ := hC w
  rw [hl, hr, ← iotaLhsOfS_iotaWitnessSOf w F hB, ← iotaRhsOfS_iotaWitnessSOf w F hB]
  exact ⟨.of (iotaWitnessSOf w F hB)⟩

/-! ## (8) pins: main's witness at the copy's Nat group

`pinNatEnvA` (`RcicAnnIota` §5) is not an admitted environment, but its recursor type has main's
canonical shapes: the body is `motive t` at `bvar (nMinors + nindices + 1) = bvar 3`, and the major's
domain is the family at its canonical levels. So main's witness exists on its erasure. The witness
below is `rec P mz ms zero`. `iotaFnA_of_witness` sends it to the copy's step `⇝ mz`, which `decide`
computes in `RcicAnnIota`. This is the annotation direction with every premise inhabited. The
erasure direction's premise, an admitted environment with a recursor, is inhabited by draft
minustwo/residua#6136 (`RcicAnnRecPins`, Nat with its AnySort recursor), which is not on main. -/

/-- main's ι witness for `rec P mz ms zero` in the erased Nat group. -/
def pinNatZeroWitness : IotaWitness (eraseEnv pinNatEnvA) where
  recRef := 13
  ctorRef := 11
  ls := []
  lsC := []
  recMember := eraseMember pinNatRecA
  ctorMember := eraseMember pinZeroA
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [.sort .zero, .sort (.succ .zero), erase pinMsA]
  fields := []
  ctorParams := []
  kinds := []
  minor := .sort (.succ .zero)
  hlen := rfl
  familyRef := 10
  famMember := eraseMember pinNatFamA
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 2
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := (piDomsA pinZeroA.mtypeA).map erase
  ctorResult := erase (piBodyA pinZeroA.mtypeA)
  hpeel := piDomsA_erase_peelPis pinZeroA.mtypeA
  hfamApp := by decide
  hkinds := rfl
  recDoms := (piDomsA pinNatRecA.mtypeA).map erase
  recBody := erase (piBodyA pinNatRecA.mtypeA)
  hpeelRec := piDomsA_erase_peelPis pinNatRecA.mtypeA
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := by decide
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := .const 10 []
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

example : iotaLhsOf pinNatZeroWitness =
    erase (pinNatRecSpineA (.sort .zero) (.sort (.succ .zero)) pinMsA (.const 11 [])) := rfl

example : iotaRhsOf pinNatZeroWitness = .sort (.succ .zero) := rfl

/-- the annotation direction at the pin: every premise discharged, and the copy's reduct is
    `mz`. -/
theorem pinNatZero_corr :
    ∃ e', iotaFnA pinNatEnvA (pinNatRecSpineA (.sort .zero) (.sort (.succ .zero)) pinMsA (.const 11 [])) =
      some e' ∧ erase e' = .sort (.succ .zero) :=
  iotaFnA_of_witness pinNatZeroWitness rfl
    (fun cm h => by cases h; exact Nat.le_refl 0)
    (fun cm h => by cases h; rfl)
    (fun cm h _ T hT => by cases h; cases hT; rfl)

/-- pin-env unfold set for the recognizers: `adapter_simp`'s unfold list plus the copy's
    pin Nat environment and its member access — `constsMemberFuel`'s compiled recursion is
    opaque at `decide`, so the recognizer is unfolded here. -/
macro "pinadapt_simp" : tactic =>
  `(tactic| simp [iotaWitnessSB, directFragCheck, directFragOne,
    iotaWitnessStableB,
    constsMemberFuel, iotaSchemaS, iotaOpenRhs, iotaArgs,
    pinNatEnvA, eraseEnv, eraseMember, extendEnvA, emptyEnvA, extendEnv,
    emptyEnv, pinNatFamA, pinZeroA, pinSuccA, pinNatRecA, pinNatZeroWitness,
    pinNatTyA, pinRecTyNatA, erase, piDomsA,
    transparent, instantiateLevels, fieldBvars, ctorFieldTelRaw, lift,
    piTelescopeFuel, whnfFuel, transparentBody, noTransparentB, headStableB,
    piTailOf, esize, piCount, properShapeB, isFamilyApp, instPrefix,
    exprClosedAt, iotaRhsOf, rhsArgs, ctorSpine, ctorMajor, recCall, foldApps,
    recCallField, recPrefix, familyIdx, exactParamLocals, appsSpine,
    occursConst, piDomsOf, instantiate, instantiate0, instLevel,
    canonRecLevels, preMajorBvars, minorTel])

/-- the pin witness in the DIRECT fragment — the erasure certificate's per-witness
    check, discharged by computation. -/
theorem pinNatZeroWitness_adapt : iotaWitnessSB pinNatZeroWitness 8 = true := by
  pinadapt_simp

/-- the pin witness adapted to a shape-based typed witness. -/
def pinNatZeroWitnessS : IotaWitnessS (eraseEnv pinNatEnvA) :=
  iotaWitnessSOf pinNatZeroWitness 8 pinNatZeroWitness_adapt

/-- the annotation certificate's per-witness check on the adapted pin witness. -/
theorem pinNatZeroWitnessS_ann :
    iotaWitnessSAnnB (eraseEnv pinNatEnvA) pinNatZeroWitnessS = true := by
  decide

/-- the annotation direction at the pin, CERTIFIED at the typed witness: the copy's
    reduct erases to the schema-instantiated right-hand side `iotaRhsOfS`. -/
theorem pinNatZero_corrS :
    ∃ e', iotaFnA pinNatEnvA (pinNatRecSpineA (.sort .zero) (.sort (.succ .zero)) pinMsA (.const 11 [])) =
      some e' ∧ erase e' = iotaRhsOfS pinNatZeroWitnessS :=
  iotaFnA_of_witnessS pinNatZeroWitnessS pinNatZeroWitnessS_ann
    (fun cm h => by cases h; exact Nat.le_refl 0)
    (fun cm h _ _ hT => by cases h; cases hT; rfl)
    rfl

#print axioms fieldsTelA_of_open
#print axioms iotaGroupA_of_witness
#print axioms iotaFnA_of_witness
#print axioms envWfA_recGroup
#print axioms erase_majorDomA
#print axioms isFamilyApp_erase_piBodyA_ctorTypeA
#print axioms directRecConstHead_erase_ctorFieldsA
#print axioms resultConstHead_erase_ctorFieldsA
#print axioms viewNoFun_of_envNoFunA
#print axioms derivedIota_of_iotaFnA
#print axioms witness_ctor_arity
#print axioms iotaFnA_of_derivedIota
#print axioms iotaErasesA_of_envWfA
#print axioms pinNatZero_corr
#print axioms iotaWitnessSAnnB_parts
#print axioms iotaFnA_of_witnessS
#print axioms iotaAnnotatesA_of_envWfA
#print axioms iotaCorrTA_of_envWfA
#print axioms pinNatZeroWitness_adapt
#print axioms pinNatZeroWitnessS_ann
#print axioms pinNatZero_corrS

end Rcic.Declarative.Ann

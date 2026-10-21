import rcic.RcicDeepNormalA
import rcic.RcicParRedIota
import rcic.RcicParRedDiamond
import rcic.RcicIota
import rcic.RcicLevelCalc
import rcic.RcicAnnIotaCorr
import rcic.RcicAnnLRConv
import rcic.RcicConvChar
import rcic.RcicAnnTel

/-!
# DT-025 M4 — the endpoint transfer: `DeepNormalA` ⇒ erased-`ParRed` inertness

For a deep-normal annotated term, every `ParRed` step on its erasure produces a
target the `eqExprN` relation tolerates:

    DeepNormalA E I Γ e →
      ParRed (eraseEnv E) n (eraseCtx Γ) (erase e) N' → eqExprN N' (erase e)

Per the M4 measurement (`issuecomment-6115889495`): `erase` drops only
binder-annotation levels; `eqExprN`'s `=ₙ` clauses live at `.sort`/`.const`
level positions — the two axes are disjoint. `ParRed.sortEq`/`.consts` level
drift is absorbed by `eqExprN.sort`/`.const`; every structural arm is excluded
by `hStepFnA`-inertia at the corresponding position:

- `beta`/`zeta`/`lit` — `hStepFnA` fires unconditionally at the redex shape;
  erasure is shape-faithful, so the clause's `= none` is contradicted.
- `bvarZeta` — a `.letBinding` cell at `i` is exactly `lookupValueA`'s firing
  condition (`get?_eraseCtx`).
- `delta` — `(eraseEnv E).members r = some m` with `m.body`/`transparent` is
  erasure-exact (`members_of_eraseEnv`), so `hStepFnA`'s const arm fires.
- congruences (`app`/`lam`/`pi`/`letE`) — deep recursion; `lam`/`pi` step in
  the `assumption`-extended context, which `DeepNormalA` tracks.
- `iotaSpine` — the subtle arm. `hStepFnA`'s ι call site fires only off the
  struct position, so the bridge quantifies over `NoUnitStructA` environments
  (the same K-rule gap class as M3's `kunit`/`kstruct` port). The step's
  witness `w2` sits at the REDUCED spine (`iotaSpine.hlhs`); the source-side
  witness at the unreduced spine and drifted levels is rebuilt by
  `iotaWitness_of_spine` (the `parRedWitness` recipe, backwards). The coverage
  premise `hι` — satisfiable by `iotaIfaceA` via `iotaFnA_of_derivedIota`
  under `EnvWfA`/`EnvNormEraseA` — turns the source-side `DerivedIota` into an
  `I.fn` fire, and `IotaIfaceA.rel_of_pos` into an `hStepFnA` fire.

Premises of the theorem: `NoUnitStructA` (struct-position death) and the
ι-coverage premise `hι`. `DeepNormalA` itself is premise-free.
-/

namespace Rcic.Declarative.Ann

/-- No unit or struct K-groups in the environment (port of the M3 premise):
    under it `hStepFnA`'s struct arm and `unitMinorA` K-rule are vacuous, so
    an `hStepFnA = none` head genuinely excludes every erased `ParRed` arm. -/
def NoUnitStructA (E : ResolvedEnvA) : Prop :=
  ∀ r m, E.members r = some m → unitGroupA r m = false ∧ structGroupA r m = false

/-- `structHeadA` reads a member's `structGroupA`: dead under `NoUnitStructA`. -/
theorem structHeadA_false_of_noUnitStruct {E : ResolvedEnvA}
    (hN : NoUnitStructA E) (f : ExprA) : structHeadA E f = false := by
  simp only [structHeadA]
  cases hh : (appsSpineA f).1 with
  | const r _ =>
      cases hm : E.members r with
      | none => simp only [hm]
      | some m =>
          simp only [hm]
          exact (hN r m hm).2
  | bvar _ => rfl
  | sort _ => rfl
  | app _ _ => rfl
  | lam _ _ _ => rfl
  | pi _ _ _ _ => rfl
  | letE _ _ _ => rfl
  | lit _ => rfl

/-- the struct position is dead under `NoUnitStructA`: `hStepFnA` always
    reaches the `iota` consultation at a non-λ application. -/
theorem structPosA_false_of_noUnitStruct {E : ResolvedEnvA}
    (hN : NoUnitStructA E) (f : ExprA) : structPosA E f = false := by
  simp only [structPosA, structHeadA_false_of_noUnitStruct hN f, Bool.and_false]

/-- the head step is dead at a deep-normal node: every constructor case's
    clause is either the equation itself or `hStepFnA`'s definitional `none`. -/
theorem deepNormalA_head {E : ResolvedEnvA} {I : IotaIfaceA} {Γ : LCtxA}
    {e : ExprA} (h : DeepNormalA E I Γ e) : hStepFnA E I.fn Γ e = none := by
  cases e with
  | sort _ => rfl
  | lam _ _ _ => rfl
  | pi _ _ _ _ => rfl
  | bvar _ => exact h
  | const _ _ => exact h
  | app _ _ => exact h.1
  | letE _ _ _ => exact h
  | lit _ => exact h

/-- a const-headed spine head is never a λ (the `rel_of_pos` non-λ premise). -/
theorem nonlam_of_spineHead_const {f : ExprA} {r : Nat} {ls : List Level}
    (h : (appsSpineA f).1 = .const r ls) : ∀ A u b, f ≠ .lam A u b := by
  intro A u b he
  subst he
  simp only [appsSpineA] at h
  exact ExprA.noConfusion h

/-- an erased `lam` can only come from a `lam` (erasure is shape-faithful). -/
theorem lam_of_erase_lam {f : ExprA} {A' b' : Expr Nat}
    (h : erase f = .lam A' b') : ∃ A u b, f = .lam A u b := by
  cases f with
  | lam A u b => exact ⟨A, u, b, rfl⟩
  | bvar _ => exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | pi _ _ _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

/-- an atomic term (nil spine tail) is never an `iotaSpine` source: `recCall`
    has the nonempty tail `pre ++ [major]`. Closes the `iotaSpine` case at
    non-application nodes. -/
theorem recCall_ne_of_spineNil {e : Expr Nat} {r : Nat} {ls : List Level}
    {pre : List (Expr Nat)} {major : Expr Nat}
    (hs : (appsSpine e).2 = []) : recCall (.const r ls) pre major ≠ e := by
  intro h
  have h1 := congrArg Prod.snd (congrArg appsSpine h)
  rw [appsSpine_recCall] at h1
  simp only at h1
  rw [hs] at h1
  exact List.cons_ne_nil major [] (List.append_eq_nil.mp h1).2

/-- iota-witness at the UNREDUCED spine: `parRedWitness` transports a witness
    forward along `ParRedArgs`; `iotaSpine`'s constructor instead carries the
    witness at the REDUCED spine (`hlhs`), so the source-side witness for the
    `hι` coverage premise is rebuilt at the unreduced args `pre`/`fields` and
    the drifted recursor levels `lsR`. The ctor-telescope fields are
    re-derived exactly as `parRedWitness` does (`applyTel_isPiTel` plus the
    level-blind `directRecConstHead`/`resultConstHead` transports); `lsC` is
    unconstrained in `IotaWitness`, so it is filled directly. The constructor
    spine `ctorParams ++ fields` is split at `nparams` from the unreduced
    `fields`, whose length equals the reduced spine's. -/
def iotaWitness_of_spine {E : ResolvedEnv} (w : IotaWitness E)
    (lsR lsC : List Level) (pre fields : List (Expr Nat))
    (hlsR : eqNList w.ls lsR)
    (hpreLen : pre.length = w.preMajor.length)
    (hfieldsLen : fields.length = (w.ctorParams ++ w.fields).length) :
    Σ' (w' : IotaWitness E),
      iotaLhsOf w' = recCall (.const w.recRef lsR) pre
        (foldApps (.const w.ctorRef lsC) fields) := by
  have hfl : fields.length = w.nparams + w.fields.length := by
    rw [hfieldsLen, List.length_append, w.hctorParams]
  have htkLen : (pre.take w.nparams).length = w.nparams := by
    simp only [List.length_take, hpreLen, w.hpre]; omega
  have hcpLen : (fields.take w.nparams).length = w.nparams := by
    simp only [List.length_take, hfl]; omega
  have hdpLen : (fields.drop w.nparams).length = w.fields.length := by
    simp only [List.length_drop, hfl]; omega
  -- 00 §20.6 (see `parRedWitness`): `ctorAfter'` is re-derived at the
  -- recursor-side view `instantiateLevels lsR w.ctorMember.mtype`.
  have htelC : isPiTel (w.nparams + w.fields.length)
      (instantiateLevels lsR w.ctorMember.mtype) = true :=
    peelPis_isPiTel _ _ (peelPis_instantiateLevels lsR _ _ w.hpeel)
  have htelCn : isPiTel w.nparams
      (instantiateLevels lsR w.ctorMember.mtype) = true :=
    isPiTel_le (by omega) htelC
  have ⟨ctorAfter', hca'⟩ :=
    applyTel_isPiTel w.nparams (instantiateLevels lsR w.ctorMember.mtype)
      (pre.take w.nparams) htkLen htelCn
  have hctorTel' : isPiTel w.kinds.length ctorAfter' = true := by
    have hk : w.kinds.length = w.fields.length := w.hlen
    rw [hk]
    exact isPiTel_of_applyTel w.nparams w.fields.length
      (instantiateLevels lsR w.ctorMember.mtype) (pre.take w.nparams) htkLen
      (Nat.add_comm w.nparams w.fields.length ▸ htelC) hca'
  have hpeelK : peelPis (w.nparams + w.kinds.length) w.ctorMember.mtype =
      some (w.ctorDoms, w.ctorResult) := by
    rw [w.hlen]; exact w.hpeel
  have hpad :
      directRecConstHead
        (List.replicate w.nparams RecKind.plain ++ w.kinds)
        (instantiateLevels lsR w.ctorMember.mtype) = true := by
    rw [directRecConstHead_instantiateLevels]
    exact directRecConstHead_plain_prefix_of_analyzeFields
      w.familyRef w.nparams w.kinds w.ctorMember.mtype hpeelK w.hkinds
  have hfamTel' : directRecConstHead w.kinds ctorAfter' = true :=
    directRecConstHead_applyTel w.kinds (pre.take w.nparams)
      (instantiateLevels lsR w.ctorMember.mtype) ctorAfter' hca'
      (by rw [htkLen, w.hlen]; exact htelC)
      (by rw [htkLen]; exact hpad)
  have hpadRes :
      resultConstHead
        (List.replicate w.nparams RecKind.plain ++ w.kinds)
        (instantiateLevels lsR w.ctorMember.mtype) = true := by
    rw [resultConstHead_instantiateLevels]
    exact resultConstHead_of_peelPis
      (List.replicate w.nparams RecKind.plain ++ w.kinds)
      w.ctorMember.mtype
      (by
        rw [List.length_append, List.length_replicate]
        exact hpeelK)
      (isFamilyApp_spineHeadConst w.hfamApp)
  have hresTel' : resultConstHead w.kinds ctorAfter' = true :=
    resultConstHead_applyTel w.kinds (pre.take w.nparams)
      (instantiateLevels lsR w.ctorMember.mtype) ctorAfter' hca'
      (by rw [htkLen, w.hlen]; exact htelC)
      (by rw [htkLen]; exact hpadRes)
  have hlt : w.nparams + 1 + w.ctorIdx < pre.length := by
    rw [hpreLen, w.hpre]; have := w.hidx; omega
  exact ⟨{
    recRef := w.recRef
    ctorRef := w.ctorRef
    ls := lsR
    lsC := lsC
    recMember := w.recMember
    ctorMember := w.ctorMember
    hrec := w.hrec
    hctor := w.hctor
    hrecK := w.hrecK
    hctorK := w.hctorK
    preMajor := pre
    fields := fields.drop w.nparams
    ctorParams := fields.take w.nparams
    kinds := w.kinds
    minor := pre[w.nparams + 1 + w.ctorIdx]'hlt
    hlen := by rw [hdpLen]; exact w.hlen
    familyRef := w.familyRef
    famMember := w.famMember
    hfam := w.hfam
    hfamK := w.hfamK
    nparams := w.nparams
    nindices := w.nindices
    nMinors := w.nMinors
    ctorIdx := w.ctorIdx
    hctorParams := hcpLen
    hnpar := by rw [hdpLen]; exact w.hnpar
    hnidx := w.hnidx
    hnmin := w.hnmin
    hidx := w.hidx
    hctorIdx := w.hctorIdx
    hrecIdx := w.hrecIdx
    hpre := hpreLen.trans w.hpre
    hminor := List.getElem?_eq_getElem hlt
    ctorDoms := w.ctorDoms
    ctorResult := w.ctorResult
    hpeel := by rw [hdpLen]; exact w.hpeel
    hfamApp := w.hfamApp
    hkinds := w.hkinds
    recDoms := w.recDoms
    recBody := w.recBody
    hpeelRec := w.hpeelRec
    hrecBody := w.hrecBody
    hmajorTy := w.hmajorTy
    hrecClosed := w.hrecClosed
    hctorClosed := w.hctorClosed
    hlsLen := (eqNList_length _ _ hlsR).symm.trans w.hlsLen
    ctorAfterParams := ctorAfter'
    hctorAfter := hca'
    hctorTel := hctorTel'
    hfamTel := hfamTel'
    hresTel := hresTel'
  }, by
    simp only [iotaLhsOf, ctorMajor, ctorSpine, recCall, List.take_append_drop]⟩

/-- THE ENDPOINT TRANSFER: a deep-normal annotated term's erasure is
    `ParRed`-inert modulo `eqExprN`. The only structural arms are the
    `hStepFnA`-inertia-violating ones (contradicted) or `eqExprN`-absorbed
    level drift. -/
def deepNormalA_parRed_eqExprN {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hNS : NoUnitStructA E)
    (hι : ∀ {e : ExprA} {rhs : Expr Nat},
      DerivedIota (eraseEnv E) (erase e) rhs → ∃ e', I.fn e = some e') :
    {Γ : LCtxA} → {e : ExprA} → DeepNormalA E I Γ e →
    {N' : Expr Nat} → ParRed (eraseEnv E) n (eraseCtx Γ) (erase e) N' →
    eqExprN N' (erase e)
  | Γ, .bvar i, hd, _, hP => by
      generalize hsrc : erase (.bvar i) = src at hP
      cases hP with
      | refl _ _ => subst hsrc; exact eqExprN_refl _
      | bvarZeta _ i' _ _ _ h _ =>
          simp only [erase] at hsrc
          injection hsrc with hi
          subst i'
          rw [get?_eraseCtx] at h
          cases hg : Γ.get? i with
          | none =>
              rw [hg, Option.map_none'] at h
              exact Option.noConfusion h
          | some d =>
              cases d with
              | assumption _ =>
                  rw [hg, Option.map_some'] at h
                  simp only [eraseDecl] at h
                  injection h with hc
                  exact LocalDecl.noConfusion hc
              | letBinding A' v' =>
                  have hval : lookupValueA Γ i = some (liftA 0 (i + 1) v') := by
                    simp only [lookupValueA, hg]
                  have hs : hStepFnA E I.fn Γ (.bvar i) =
                      some (liftA 0 (i + 1) v') := hval
                  have hstep : hStepFnA E I.fn Γ (.bvar i) = none := hd
                  rw [hs] at hstep
                  exact Option.noConfusion hstep
      | iotaSpine _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          exact absurd hsrc.symm (recCall_ne_of_spineNil rfl)
      | _ => exact absurd hsrc (by simp [erase])
  | Γ, .sort l, hd, _, hP => by
      generalize hsrc : erase (.sort l) = src at hP
      cases hP with
      | refl _ _ => subst hsrc; exact eqExprN_refl _
      | sortEq _ l₁ _ h =>
          simp only [erase] at hsrc
          injection hsrc with hll
          subst l₁
          exact .sort (eqN_symm h)
      | iotaSpine _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          exact absurd hsrc.symm (recCall_ne_of_spineNil rfl)
      | _ => exact absurd hsrc (by simp [erase])
  | Γ, .const r ls, hd, _, hP => by
      generalize hsrc : erase (.const r ls) = src at hP
      cases hP with
      | refl _ _ => subst hsrc; exact eqExprN_refl _
      | consts _ r' ls' _ h =>
          simp only [erase] at hsrc
          injection hsrc with hr hls
          subst r'; subst ls'
          exact .const (eqNList_symm h)
      | delta _ r' ls' _ _ hres hbody htr =>
          simp only [erase] at hsrc
          injection hsrc with hr hls
          subst r'; subst ls'
          obtain ⟨mA, hmA, hmE⟩ := members_of_eraseEnv hres
          subst hmE
          have htrA : transparent mA.mclass = true := htr
          simp only [eraseMember] at hbody
          cases hbd : mA.bodyA with
          | none =>
              rw [hbd, Option.map_none'] at hbody
              exact Option.noConfusion hbody
          | some bA =>
              rw [hbd, Option.map_some'] at hbody
              have hs : hStepFnA E I.fn Γ (.const r ls) =
                  some (instantiateLevelsA ls bA) := by
                simp only [hStepFnA, hmA, htrA, hbd, Option.map_some',
                  eq_self_iff_true, if_true]
              have hstep : hStepFnA E I.fn Γ (.const r ls) = none := hd
              rw [hs] at hstep
              exact Option.noConfusion hstep
      | iotaSpine _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          exact absurd hsrc.symm (recCall_ne_of_spineNil rfl)
      | _ => exact absurd hsrc (by simp [erase])
  | Γ, .app f a, hd, _, hP => by
      obtain ⟨hhead, hfN, haN⟩ := hd
      generalize hsrc : erase (.app f a) = src at hP
      cases hP with
      | refl _ _ => subst hsrc; exact eqExprN_refl _
      | app _ _ _ _ _ hf ha =>
          simp only [erase] at hsrc
          injection hsrc with hfE haE
          subst hfE; subst haE
          exact .app (deepNormalA_parRed_eqExprN hNS hι hfN hf)
            (deepNormalA_parRed_eqExprN hNS hι haN ha)
      | beta _ _ _ _ _ _ _ _ _ =>
          simp only [erase] at hsrc
          injection hsrc with hf' _
          obtain ⟨A, u, b, rfl⟩ := lam_of_erase_lam hf'
          have hs : hStepFnA E I.fn Γ (.app (.lam A u b) a) =
              some (instantiate0A a b) := hStepFnA_app_lam _ _ _ _ _ _ _
          rw [hs] at hhead
          exact Option.noConfusion hhead
      | iotaSpine _ w2 lsR lsC hlsR _ pre pre' fields fields' hf ha hpreLen
          hfieldsLen _ =>
          have hlenP : pre.length = w2.preMajor.length :=
            (parRedArgs_length hf).trans hpreLen
          have hlenF : fields.length = (w2.ctorParams ++ w2.fields).length :=
            (parRedArgs_length ha).trans hfieldsLen
          obtain ⟨w', hw'l⟩ :=
            iotaWitness_of_spine w2 lsR lsC pre fields hlsR hlenP hlenF
          have hd' : DerivedIota (eraseEnv E) (erase (.app f a))
              (iotaRhsOf w') := (hw'l.trans hsrc.symm) ▸ .of w'
          obtain ⟨e', hif⟩ := hι hd'
          have hsp : (appsSpineA f).1 = .const w2.recRef lsR := by
            have h1 := congrArg Prod.fst (congrArg appsSpine hsrc)
            rw [appsSpine_recCall] at h1
            have h2 := congrArg Prod.fst (appsSpineA_erase (.app f a))
            rw [h2] at h1
            exact erase_eq_const h1
          have hrel := IotaIfaceA.rel_of_pos I E Γ
            (nonlam_of_spineHead_const hsp) (deepNormalA_head hfN)
            (structPosA_false_of_noUnitStruct hNS f) hif
          rw [hrel.2] at hhead
          exact Option.noConfusion hhead
      | _ => exact absurd hsrc (by simp [erase])
  | Γ, .lam A u b, hd, _, hP => by
      obtain ⟨hdA, hdb⟩ := hd
      generalize hsrc : erase (.lam A u b) = src at hP
      cases hP with
      | refl _ _ => subst hsrc; exact eqExprN_refl _
      | lam _ A' _ b' _ hA hb =>
          simp only [erase] at hsrc
          injection hsrc with hAe hbe
          subst A'; subst b'
          exact .lam (deepNormalA_parRed_eqExprN hNS hι hdA hA)
            (deepNormalA_parRed_eqExprN hNS hι hdb hb)
      | iotaSpine _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          exact absurd hsrc.symm (recCall_ne_of_spineNil rfl)
      | _ => exact absurd hsrc (by simp [erase])
  | Γ, .pi A u B v, hd, _, hP => by
      obtain ⟨hdA, hdb⟩ := hd
      generalize hsrc : erase (.pi A u B v) = src at hP
      cases hP with
      | refl _ _ => subst hsrc; exact eqExprN_refl _
      | pi _ A' _ b' _ hA hb =>
          simp only [erase] at hsrc
          injection hsrc with hAe hbe
          subst A'; subst b'
          exact .pi (deepNormalA_parRed_eqExprN hNS hι hdA hA)
            (deepNormalA_parRed_eqExprN hNS hι hdb hb)
      | iotaSpine _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          exact absurd hsrc.symm (recCall_ne_of_spineNil rfl)
      | _ => exact absurd hsrc (by simp [erase])
  | Γ, .letE A v b, hd, _, _ => by
      have hs : hStepFnA E I.fn Γ (.letE A v b) = some (instantiate0A v b) := rfl
      have hstep : hStepFnA E I.fn Γ (.letE A v b) = none := hd
      rw [hs] at hstep
      exact Option.noConfusion hstep
  | Γ, .lit t, hd, _, _ => by
      have hs : hStepFnA E I.fn Γ (.lit t) = some (natExpandA t) := rfl
      have hstep : hStepFnA E I.fn Γ (.lit t) = none := hd
      rw [hs] at hstep
      exact Option.noConfusion hstep

end Rcic.Declarative.Ann

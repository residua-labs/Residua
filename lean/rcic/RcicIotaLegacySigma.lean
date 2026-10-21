import rcic.RcicIotaSRRows
import rcic.RcicIotaLegacyShapes
import rcic.RcicTypedScopeCheck

/-!
# DT-019 S2 (d) — the σ-correspondence: admission's open schema instantiates to the legacy reduct

The typed root's ι witness carries `schema`, admission's `iotaOpenRhs` computed in the
canonical equation context (parameters, motive, minors, indices, then the fields, all as
bound variables), and its reduct is `instPrefix (preMajor ++ fields) (instantiateLevels ls
schema)`. The legacy witness's reduct is `rhsArgs`' syntactic walk over the stored
constructor telescope already instantiated at the redex (`ctorAfterParams`, then each field
in turn). The two are the same term: with

  σ e := instPrefix (preMajor ++ fields) (instantiateLevels ls e)

σ commutes with Π (`instTel` under the binder), with `instantiate0` (the walk's field
substitution), with `foldApps`, and with `familyIdx` at a constant head; σ sends the
recursor head at canonical levels to the redex's head, the context bvars to `preMajor`,
the field bvars to `fields`, the minor bvar to the minor, and the lifted raw telescope to
`ctorAfterParams`. The two walks are then matched step by step (`iotaArgs_sigma`); the
only environment fact used is that the family head is not transparent, so the typed
walk's `piTelescopeFuel` on a DirectRec domain returns the domain itself.

The glm-nofunrec 3b-2b item (`iotaArgs = rhsArgsS` against `iotaOpenRhs`) is this file's
content, stated directly against the legacy `rhsArgs`.

`closure_claim` 0.
-/

namespace Rcic.Declarative

/-! ## (1) σ and its commutations -/

/-- the redex-side instance of a schema-side term. -/
def sigmaInst (ls : List Level) (L : List (Expr Nat)) (e : Expr Nat) : Expr Nat :=
  instPrefix L (instantiateLevels ls e)

/-- σ under one binder. -/
def sigmaInst1 (ls : List Level) (L : List (Expr Nat)) (e : Expr Nat) : Expr Nat :=
  instTel L (instantiateLevels ls e)

theorem sigmaInst_pi (ls : List Level) (L : List (Expr Nat)) (A B : Expr Nat) :
    sigmaInst ls L (.pi A B) = .pi (sigmaInst ls L A) (sigmaInst1 ls L B) := by
  simp only [sigmaInst, sigmaInst1, instantiateLevels, instPrefix_pi]

theorem instPrefix_instantiate0 : (L : List (Expr Nat)) → (v B : Expr Nat) →
    instPrefix L (instantiate0 v B) = instantiate0 (instPrefix L v) (instTel L B)
  | [], _, _ => rfl
  | a :: as, v, B => by
      rw [instPrefix_cons, instantiate0_instantiate, instPrefix_instantiate0 as, instPrefix_cons,
        instTel_cons, lift_lift_merge 1 as.length 0 0 (Nat.le_refl 0) (Nat.zero_le _)]

theorem sigmaInst_instantiate0 (ls : List Level) (L : List (Expr Nat)) (v B : Expr Nat) :
    sigmaInst ls L (instantiate0 v B) =
      instantiate0 (sigmaInst ls L v) (sigmaInst1 ls L B) := by
  simp only [sigmaInst, sigmaInst1, instantiate0]
  rw [instantiateLevels_instantiate]
  exact instPrefix_instantiate0 L _ _

theorem sigmaInst_foldApps (ls : List Level) (L : List (Expr Nat)) (f : Expr Nat)
    (xs : List (Expr Nat)) :
    sigmaInst ls L (foldApps f xs) = foldApps (sigmaInst ls L f) (xs.map (sigmaInst ls L)) := by
  simp only [sigmaInst]
  rw [foldApps_instantiateLevels, instPrefix_foldApps, List.map_map]
  rfl

theorem sigmaInst_bvar (ls : List Level) (L : List (Expr Nat)) (k : Nat) :
    sigmaInst ls L (.bvar k) = instPrefix L (.bvar k) := rfl

theorem sigmaInst_recHead (ls : List Level) (L : List (Expr Nat)) (r n : Nat)
    (hlen : ls.length = n) :
    sigmaInst ls L (.const r (canonRecLevels n)) = .const r ls := by
  simp only [sigmaInst, instantiateLevels, instPrefix_const, canonRecLevels]
  rw [famLevels_instLevel ls hlen]

theorem familyIdx_instPrefix_const (np : Nat) : (L : List (Expr Nat)) → (A : Expr Nat) →
    {r : Nat} → {ls' : List Level} → (appsSpine A).1 = .const r ls' →
    (familyIdx np A).map (instPrefix L) = familyIdx np (instPrefix L A)
  | [], _, _, _, _ => map_instPrefix_nil _
  | a :: as, A, r, ls', h => by
      rw [← map_instPrefix_cons, ← familyIdx_instantiate_const as.length (lift 0 as.length a) np h,
        instPrefix_cons]
      exact familyIdx_instPrefix_const np as _
        (by rw [appsSpine_instantiate_const _ _ r ls' A h])

theorem sigmaInst_familyIdx (ls : List Level) (L : List (Expr Nat)) (np : Nat) {A : Expr Nat}
    {r : Nat} {ls' : List Level} (h : (appsSpine A).1 = .const r ls') :
    (familyIdx np A).map (sigmaInst ls L) = familyIdx np (sigmaInst ls L A) := by
  simp only [sigmaInst]
  rw [← familyIdx_instPrefix_const np L (instantiateLevels ls A) (r := r)
    (ls' := ls'.map (instLevel ls)) (by rw [appsSpine_instantiateLevels, h]; rfl),
    familyIdx_instantiateLevels, List.map_map]
  rfl

theorem sigmaInst_shifted (ls : List Level) (L : List (Expr Nat)) (n off : Nat) :
    ((List.range n).reverse.map (fun i => (Expr.bvar (i + off) : Expr Nat))).map (sigmaInst ls L) =
      ((List.range n).reverse.map (fun i => (Expr.bvar (i + off) : Expr Nat))).map (instPrefix L) := by
  rw [List.map_map, List.map_map]
  rfl

theorem sigmaInst_preMajorBvars (ls : List Level) (preMajor fields : List (Expr Nat))
    (np nMinors ni : Nat) (hpre : preMajor.length = np + 1 + nMinors + ni) :
    (preMajorBvars np nMinors ni fields.length).map (sigmaInst ls (preMajor ++ fields)) =
      preMajor := by
  simp only [preMajorBvars]
  rw [sigmaInst_shifted, instPrefix_shiftedSpine (preMajor ++ fields) (np + 1 + nMinors + ni)
    fields.length 0 (by simp only [List.length_append, hpre]; omega)]
  rw [List.drop_zero, ← hpre, List.take_left]

theorem sigmaInst_fieldBvars (ls : List Level) (preMajor fields : List (Expr Nat)) :
    (fieldBvars fields.length).map (sigmaInst ls (preMajor ++ fields)) = fields := by
  rw [fieldBvars_eq_shifted, sigmaInst_shifted, instPrefix_shiftedSpine (preMajor ++ fields)
    fields.length 0 preMajor.length (by simp only [List.length_append]; omega)]
  rw [List.drop_left, List.take_length]

theorem sigmaInst_minor (ls : List Level) (preMajor fields : List (Expr Nat))
    {np nMinors ni ctorIdx : Nat} {minor : Expr Nat}
    (hpre : preMajor.length = np + 1 + nMinors + ni) (hidx : ctorIdx < nMinors)
    (hminor : preMajor[np + 1 + ctorIdx]? = some minor) :
    sigmaInst ls (preMajor ++ fields) (.bvar (fields.length + ni + (nMinors - 1 - ctorIdx))) =
      minor := by
  rw [sigmaInst_bvar]
  apply instPrefix_bvar_lt
  · simp only [List.length_append]; omega
  · have hi : (preMajor ++ fields).length - 1 - (fields.length + ni + (nMinors - 1 - ctorIdx)) =
        np + 1 + ctorIdx := by
      simp only [List.length_append]; omega
    rw [hi, List.getElem?_append_left (by omega)]
    exact hminor

/-! ## (2) the initial telescope: `applyTel` at the parameters is `instPrefix` -/

theorem instDomsT_length : (k : Nat) → (s : Expr Nat) → (ds : List (Expr Nat)) →
    (instDomsT k s ds).length = ds.length
  | _, _, [] => rfl
  | k, s, _ :: ds => by
      simp only [instDomsT, List.length_cons, instDomsT_length (k + 1) (lift 0 1 s) ds]

theorem applyTel_policyPi_instPrefix : (ps D1 : List (Expr Nat)) → ps.length = D1.length →
    (X : Expr Nat) → applyTel ps (policyPi D1 X) = some (instPrefix ps X)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | p :: ps, d :: D1, h, X => by
      simp only [List.length_cons] at h
      have hl : ps.length = D1.length := Nat.succ.inj h
      simp only [policyPi, applyTel_cons_pi, instantiate0]
      rw [instantiate_policyPi D1 0 p X, Nat.zero_add,
        applyTel_policyPi_instPrefix ps _ (by rw [instDomsT_length]; exact hl), instPrefix_cons, hl]

theorem instPrefix_append_lift (as bs : List (Expr Nat)) (e : Expr Nat) :
    instPrefix (as ++ bs) (lift 0 bs.length e) = instPrefix as e := by
  rw [instPrefix_append_instTelK bs as, instPrefix_eq_instTelK bs, instPrefix_eq_instTelK as]
  have h := instTelK_lift_mid bs.length 0 as e
  rw [Nat.add_zero] at h
  rw [h, instTelK_lift_cancel 0 bs]

/-- the lifted raw field telescope, under σ, is the legacy `ctorAfterParams`. -/
theorem sigmaInst_tel0 {E : ResolvedEnv} (w : IotaWitness E) :
    sigmaInst w.ls (w.preMajor ++ w.fields)
      (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
        (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) = w.ctorAfterParams := by
  have hmt : w.ctorMember.mtype = policyPi w.ctorDoms w.ctorResult :=
    policyPi_of_peelPis _ _ w.hpeel
  have hdl : w.ctorDoms.length = w.nparams + w.fields.length := peelPis_length _ _ w.hpeel
  have hpre := w.hpre
  have hca := w.hctorAfter
  rw [hmt, instantiateLevels_policyPi,
    ← List.take_append_drop w.nparams (w.ctorDoms.map (instantiateLevels w.ls)), policyPi_append,
    applyTel_policyPi_instPrefix _ _
      (by simp only [List.length_take, List.length_map, hdl, hpre]; omega),
    Option.some.injEq] at hca
  rw [← hca]
  -- the left side
  have hsplit : w.preMajor ++ w.fields =
      w.preMajor.take w.nparams ++ (w.preMajor.drop w.nparams ++ w.fields) := by
    rw [← List.append_assoc, List.take_append_drop]
  have hK : (w.preMajor.drop w.nparams ++ w.fields).length =
      w.fields.length + 1 + w.nMinors + w.nindices := by
    simp only [List.length_append, List.length_drop, hpre]; omega
  simp only [sigmaInst]
  rw [← lift_instantiateLevels, hsplit, ← hK, instPrefix_append_lift, ctorFieldTelRaw,
    ← policyPi_eq_foldr, instantiateLevels_policyPi, List.map_drop]

/-! ## (3) the family-headed DirectRec domains of a telescope -/

/-- the DirectRec domains of the first `ks.length` Π's are applications of the family. -/
def DirectFamHead (fam : Nat) : List RecKind → Expr Nat → Prop
  | [], _ => True
  | .plain :: ks, .pi _ B => DirectFamHead fam ks B
  | .directRec :: ks, .pi A B => (∃ ls, (appsSpine A).1 = .const fam ls) ∧ DirectFamHead fam ks B
  | _ :: _, _ => True

theorem directFamHead_instantiate (fam j : Nat) (v : Expr Nat) :
    (ks : List RecKind) → (T : Expr Nat) → isPiTel ks.length T = true →
    DirectFamHead fam ks T → DirectFamHead fam ks (instantiate j v T)
  | [], _, _, _ => trivial
  | k :: ks, .pi A B, htel, h => by
      simp only [List.length_cons, isPiTel] at htel
      cases k with
      | plain => exact directFamHead_instantiate fam (j + 1) (lift 0 1 v) ks B htel h
      | directRec =>
          obtain ⟨⟨ls, hA⟩, hB⟩ := h
          exact ⟨⟨ls, by rw [appsSpine_instantiate_const j v fam ls A hA]⟩,
            directFamHead_instantiate fam (j + 1) (lift 0 1 v) ks B htel hB⟩
  | _ :: _, .bvar _, htel, _ => by cases htel
  | _ :: _, .sort _, htel, _ => by cases htel
  | _ :: _, .const _ _, htel, _ => by cases htel
  | _ :: _, .app _ _, htel, _ => by cases htel
  | _ :: _, .lam _ _, htel, _ => by cases htel
  | _ :: _, .letE _ _ _, htel, _ => by cases htel
  | _ :: _, .lit _, htel, _ => by cases htel

theorem directFamHead_lift (fam c a : Nat) :
    (ks : List RecKind) → (T : Expr Nat) → isPiTel ks.length T = true →
    DirectFamHead fam ks T → DirectFamHead fam ks (lift c a T)
  | [], _, _, _ => trivial
  | k :: ks, .pi A B, htel, h => by
      simp only [List.length_cons, isPiTel] at htel
      cases k with
      | plain => exact directFamHead_lift fam (c + 1) a ks B htel h
      | directRec =>
          obtain ⟨⟨ls, hA⟩, hB⟩ := h
          exact ⟨⟨ls, by rw [appsSpine_lift, hA]; rfl⟩,
            directFamHead_lift fam (c + 1) a ks B htel hB⟩
  | _ :: _, .bvar _, htel, _ => by cases htel
  | _ :: _, .sort _, htel, _ => by cases htel
  | _ :: _, .const _ _, htel, _ => by cases htel
  | _ :: _, .app _ _, htel, _ => by cases htel
  | _ :: _, .lam _ _, htel, _ => by cases htel
  | _ :: _, .letE _ _ _, htel, _ => by cases htel
  | _ :: _, .lit _, htel, _ => by cases htel

theorem isPiTel_policyPi : (ds : List (Expr Nat)) → (R : Expr Nat) →
    isPiTel ds.length (policyPi ds R) = true
  | [], _ => rfl
  | _ :: ds, R => by
      simp only [List.length_cons, policyPi, isPiTel]
      exact isPiTel_policyPi ds R

theorem directFamHead_of_analyzeFields (fam : Nat) :
    (D : List (Expr Nat)) → (R : Expr Nat) → {ks : List RecKind} →
    analyzeFields fam D = some ks → DirectFamHead fam ks (policyPi D R)
  | [], _, ks, h => by
      simp only [analyzeFields, Option.some.injEq] at h
      rw [← h]
      trivial
  | T :: D, R, ks, h => by
      simp only [analyzeFields] at h
      cases ha : analyzeField fam T with
      | none => simp only [ha] at h <;> cases h
      | some k =>
          cases hr : analyzeFields fam D with
          | none => simp only [ha, hr] at h <;> cases h
          | some ks' =>
              simp only [ha, hr, Option.some.injEq] at h
              rw [← h]
              have ih := directFamHead_of_analyzeFields fam D R hr
              unfold analyzeField at ha
              cases k with
              | plain => exact ih
              | directRec =>
                  refine ⟨?_, ih⟩
                  by_cases ho : occursConst fam T = false
                  · rw [ho] at ha
                    simp only [Bool.not_false, if_true, Option.some.injEq] at ha
                    cases ha
                  · have ho' : occursConst fam T = true := by
                      cases hx : occursConst fam T with
                      | false => exact absurd hx ho
                      | true => rfl
                    rw [ho'] at ha
                    simp only [Bool.not_true, Bool.false_eq_true, if_false] at ha
                    by_cases hfa : isFamilyApp fam T = true
                    · obtain ⟨ls, args, hsp, _⟩ := isFamilyApp_spine hfa
                      exact ⟨ls, by rw [hsp]⟩
                    · rw [if_neg hfa] at ha
                      cases ha

/-! ## (4) the two walks agree under σ -/

theorem transparentBody_none_of_class {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hcls : transparent m.mclass = false) (ls : List Level) :
    transparentBody E r ls = none := by
  simp only [transparentBody, hm, hcls, Bool.false_eq_true, if_false]

theorem sigmaInst_recCallField (ls : List Level) (L : List (Expr Nat)) {R R' : Expr Nat}
    {P P' : List (Expr Nat)} (hR : sigmaInst ls L R = R') (hP : P.map (sigmaInst ls L) = P')
    (np nM : Nat) (f A : Expr Nat) {r : Nat} {ls' : List Level}
    (hA : (appsSpine A).1 = .const r ls') :
    sigmaInst ls L (recCallField R P np nM f A) =
      recCallField R' P' np nM (sigmaInst ls L f) (sigmaInst ls L A) := by
  simp only [recCallField, recPrefix]
  rw [sigmaInst_foldApps, hR, List.map_append, List.map_append, List.map_take, hP,
    sigmaInst_familyIdx ls L np hA, List.map_cons, List.map_nil]

/-- the typed walk's arguments, under σ, are the legacy walk's arguments. -/
theorem iotaArgs_sigma {E : ResolvedEnv} {fam : Nat}
    (hfam : ∀ ls, transparentBody E fam ls = none)
    {fuel np nMinors : Nat} (ls : List Level) (L : List (Expr Nat)) {R R' : Expr Nat}
    {P P' : List (Expr Nat)} (hR : sigmaInst ls L R = R') (hP : P.map (sigmaInst ls L) = P') :
    (ks : List RecKind) → (fs : List (Expr Nat)) → (tel : Expr Nat) →
    isPiTel ks.length tel = true → DirectFamHead fam ks tel →
    {args : List (Expr Nat)} →
    iotaArgs E fuel R P np nMinors (ks.map shapeOfKind) fs tel = some args →
    args.map (sigmaInst ls L) =
      rhsArgs R' P' np nMinors (fs.map (sigmaInst ls L)) ks (sigmaInst ls L tel)
  | [], [], tel, _, _, args, h => by
      simp only [List.map_nil, iotaArgs, Option.some.injEq] at h
      rw [← h]
      rfl
  | [], _ :: _, _, _, _, _, h => by
      simp only [List.map_nil, iotaArgs] at h <;> cases h
  | k :: _, [], _, _, _, _, h => by
      cases k <;> simp only [List.map_cons, shapeOfKind, iotaArgs] at h <;> cases h
  | .plain :: ks, f :: fs, .pi A B, htel, hd, args, h => by
      simp only [List.length_cons, isPiTel] at htel
      simp only [List.map_cons, shapeOfKind, iotaArgs] at h
      cases hrest : iotaArgs E fuel R P np nMinors (ks.map shapeOfKind) fs (instantiate0 f B) with
      | none => simp only [hrest, Option.map_none'] at h <;> cases h
      | some rest =>
          simp only [hrest, Option.map_some', Option.some.injEq] at h
          rw [← h, sigmaInst_pi, List.map_cons, List.map_cons]
          show _ = _ :: rhsArgs R' P' np nMinors _ ks (instantiate0 _ _)
          rw [← sigmaInst_instantiate0,
            iotaArgs_sigma hfam ls L hR hP ks fs (instantiate0 f B)
              (isPiTel_instantiate 0 f ks.length B htel)
              (directFamHead_instantiate fam 0 f ks B htel hd) hrest]
  | .directRec :: ks, f :: fs, .pi A B, htel, hd, args, h => by
      simp only [List.length_cons, isPiTel] at htel
      obtain ⟨⟨ls'', hA⟩, hB⟩ := hd
      have hsA : appsSpine A = (.const fam ls'', (appsSpine A).2) := Prod.ext hA rfl
      cases fuel with
      | zero => simp only [List.map_cons, shapeOfKind, iotaArgs, piTelescopeFuel] at h <;> cases h
      | succ fuel =>
      cases fuel with
      | zero =>
          simp only [List.map_cons, shapeOfKind, iotaArgs, piTelescopeFuel, whnfFuel] at h <;> cases h
      | succ fuel =>
      simp only [List.map_cons, shapeOfKind, iotaArgs,
        piTelescopeFuel_famHead hsA (hfam ls'') fuel] at h
      cases hrest : iotaArgs E (fuel + 2) R P np nMinors (ks.map shapeOfKind) fs
          (instantiate0 f B) with
      | none => simp only [hrest, Option.map_none'] at h <;> cases h
      | some rest =>
          simp only [hrest, Option.map_some', Option.some.injEq] at h
          rw [← h, sigmaInst_pi, List.map_cons, List.map_cons, List.map_cons]
          show _ = _ :: recCallField R' P' np nMinors _ _ ::
            rhsArgs R' P' np nMinors _ ks (instantiate0 _ _)
          rw [← sigmaInst_instantiate0, sigmaInst_recCallField ls L hR hP np nMinors f A hA,
            iotaArgs_sigma hfam ls L hR hP ks fs (instantiate0 f B)
              (isPiTel_instantiate 0 f ks.length B htel)
              (directFamHead_instantiate fam 0 f ks B htel hB) hrest]
  | _ :: _, _ :: _, .bvar _, htel, _, _, _ => by cases htel
  | _ :: _, _ :: _, .sort _, htel, _, _, _ => by cases htel
  | _ :: _, _ :: _, .const _ _, htel, _, _, _ => by cases htel
  | _ :: _, _ :: _, .app _ _, htel, _, _, _ => by cases htel
  | _ :: _, _ :: _, .lam _ _, htel, _, _, _ => by cases htel
  | _ :: _, _ :: _, .letE _ _ _, htel, _, _, _ => by cases htel
  | _ :: _, _ :: _, .lit _, htel, _, _, _ => by cases htel

/-- **the σ-correspondence**: a legacy witness's reduct is the instance, at its arguments, of
    admission's open schema computed at the legacy kinds. -/
theorem iotaRhsOf_eq_sigma {E : ResolvedEnv} (w : IotaWitness E) {fuel : Nat} {schema : Expr Nat}
    (hsch : iotaOpenRhs E fuel (.const w.recRef (canonRecLevels w.recMember.arity))
      (.bvar (w.fields.length + w.nindices + (w.nMinors - 1 - w.ctorIdx)))
      (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
      w.nparams w.nMinors (w.kinds.map shapeOfKind) (fieldBvars w.fields.length)
      (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
        (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) = some schema) :
    instPrefix (w.preMajor ++ w.fields) (instantiateLevels w.ls schema) = iotaRhsOf w := by
  have hfam : ∀ ls, transparentBody E w.familyRef ls = none :=
    transparentBody_none_of_class w.hfam (by rw [w.hfamK]; rfl)
  simp only [iotaOpenRhs] at hsch
  cases hargs : iotaArgs E fuel (.const w.recRef (canonRecLevels w.recMember.arity))
      (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
      w.nparams w.nMinors (w.kinds.map shapeOfKind) (fieldBvars w.fields.length)
      (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
        (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) with
  | none => simp only [hargs, Option.map_none'] at hsch <;> cases hsch
  | some args =>
      simp only [hargs, Option.map_some', Option.some.injEq] at hsch
      rw [← hsch]
      change sigmaInst w.ls (w.preMajor ++ w.fields) (foldApps _ args) = _
      have hdl : w.ctorDoms.length = w.nparams + w.fields.length := peelPis_length _ _ w.hpeel
      have hkl : w.kinds.length = (w.ctorDoms.drop w.nparams).length := by
        rw [List.length_drop, hdl, w.hlen]; omega
      have htel0 : isPiTel w.kinds.length
          (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
            (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) = true := by
        apply isPiTel_lift
        rw [ctorFieldTelRaw, ← policyPi_eq_foldr, hkl]
        exact isPiTel_policyPi _ _
      have hdfh : DirectFamHead w.familyRef w.kinds
          (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
            (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) := by
        apply directFamHead_lift
        · rw [ctorFieldTelRaw, ← policyPi_eq_foldr, hkl]
          exact isPiTel_policyPi _ _
        · rw [ctorFieldTelRaw, ← policyPi_eq_foldr]
          exact directFamHead_of_analyzeFields w.familyRef _ _ w.hkinds
      rw [sigmaInst_foldApps, sigmaInst_minor w.ls w.preMajor w.fields w.hpre w.hidx w.hminor,
        iotaArgs_sigma hfam w.ls (w.preMajor ++ w.fields)
          (sigmaInst_recHead w.ls _ w.recRef w.recMember.arity w.hlsLen)
          (sigmaInst_preMajorBvars w.ls w.preMajor w.fields w.nparams w.nMinors w.nindices w.hpre)
          w.kinds (fieldBvars w.fields.length) _ htel0 hdfh hargs,
        sigmaInst_fieldBvars, sigmaInst_tel0]
      rfl

end Rcic.Declarative

#print axioms Rcic.Declarative.iotaRhsOf_eq_sigma
#print axioms Rcic.Declarative.iotaArgs_sigma
#print axioms Rcic.Declarative.sigmaInst_tel0

import rcic.RcicF8XBinderWf

/-!
# `RcicF8XTile` — the X tile on the admissible fragment (S4)

S0 §9 (#7026), cc's ruling of 2026-10-14 on #7035 (Stratum B needs `CtxWfT`, so the tile is
`XProcWf`-shaped), and the independent audit of 2026-10-14 (#7063/#7070): suppliers are PARTIAL
(S3b), so the tile answers or refuses. `xTile? X hΓ c hadm` is S3b's `xValley?`; what S4 adds:

* **S1's fragment is inside S3's**: a Π-spined input (S1's `piSpinedTc c = true`, the whole of
  Stratum A) flattens into links that all have Π endpoints and are Π-spined (`flattenTc_spined`),
  so every segment is a single Π-spined link and `xAdm c = true` (`xAdm_of_piSpined`);
* **Stratum A never asks a supplier**: on such an input the tile ANSWERS for every supplier
  bundle (`xTile?_isSome_of_piSpined`), in particular for `Suppliers.declining hsep`, which
  inhabits the bundle given `SepAll E n` — so the tile and its pins are not vacuous;
* the contract (`xTile_contract`) is `XContractWf`'s clause on every answer.

The complement of `xAdm` is the named remainder: W-X-SUBST, W-X-WK and W-X-LEVELS.
D2a supplies native level-conversion valleys; X admission and supplier routing remain separate
obligations. A declined supplier request is the dynamic refusal (`none`). The sealed unconditional `XProc`'s
Stratum-B part has no supplier on this route (not proven false: `JTileS0.no_jproc_supplier`
refutes the unconditional J, not X). The call edges are classified in `S3D_EDGES_DESIGN.md`.

Pins: the real ηK `request` (Stratum A) is answered by the declining suppliers and the answer's
leaves are strictly below the ORIGINAL removed D inputs (`EtaKAnnot.X_outputs_edge`'s shape);
the β fixture's answers, if any, keep strict provenance. `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)} {Γ : LCtx}

/-! ### Stratum-A inputs flatten into Π-spined links with Π endpoints -/

/-- every link has Π endpoints and is Π-spined. -/
def Flat.spined : {A B : Expr Nat} → Flat R Γ A B → Bool
  | _, _, .nil _ => true
  | _, _, @Flat.cons _ _ _ _ A M _ l _ rest => isPi A && isPi M && piSpinedTc l && rest.spined

theorem Flat.append_spined : {A M B : Expr Nat} → (f : Flat R Γ A M) → (g : Flat R Γ M B) →
    (f.append g).spined = (f.spined && g.spined)
  | _, _, _, .nil _, g => by simp only [Flat.append, Flat.spined, Bool.true_and]
  | _, _, _, .cons l hl rest, g => by
      simp only [Flat.append, Flat.spined, rest.append_spined g, Bool.and_assoc]

/-- Π-spinedness survives turning a link around. -/
theorem linkSymm_piSpined : {Γ : LCtx} → {A B : Expr Nat} → (l : EvTc R Γ A B) →
    (hl : isLink l = true) → piSpinedTc (linkSymm l hl) = piSpinedTc l
  | _, _, _, .ofCv u c, _ => by simp only [linkSymm, piSpinedTc, piSpinedCv]
  | _, _, _, .piCod .., _ => by simp only [linkSymm, piSpinedTc]
  | _, _, _, @EvTc.subst0 _ _ _ Γ₀ A₀ A₀' t v j c hget hv, _ => by
      simp only [linkSymm, piSpinedTc]
      rw [Bool.and_comm (isPi A₀') (isPi A₀)]
  | _, _, _, @EvTc.substLet _ _ _ Γ₀ A₀ A₀' t w0 j c hget hv, _ => by
      simp only [linkSymm, piSpinedTc]
      rw [Bool.and_comm (isPi A₀') (isPi A₀)]
  | _, _, _, @EvTc.wk _ _ _ Γ₀ A₀ B₀ d k l, hl => by
      simp only [linkSymm, piSpinedTc]
      rw [linkSymm_piSpined l (by simpa only [isLink] using hl), Bool.and_comm (isPi B₀) (isPi A₀)]
  | _, _, _, .lit .., hl => nomatch hl
  | _, _, _, .refl .., hl => nomatch hl
  | _, _, _, .symm .., hl => nomatch hl
  | _, _, _, .trans .., hl => nomatch hl

theorem Flat.symm_spined : {A B : Expr Nat} → (f : Flat R Γ A B) → f.spined = true →
    f.symm.spined = true
  | _, _, .nil _, _ => rfl
  | _, _, @Flat.cons _ _ _ _ A M B l hl rest, h => by
      simp only [Flat.spined, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hA, hM⟩, hl'⟩, hr⟩ := h
      simp only [Flat.symm, Flat.append_spined, rest.symm_spined hr, Flat.spined,
        linkSymm_piSpined, hA, hM, hl', Bool.and_self, Bool.true_and, Bool.and_true]

theorem Flat.wk_spined (d : LocalDecl) (k : Nat) : {A B : Expr Nat} → (f : Flat R Γ A B) →
    (f.wk d k).spined = f.spined
  | _, _, .nil _ => rfl
  | _, _, @Flat.cons _ _ _ _ A M B l hl rest => by
      simp only [Flat.wk, Flat.spined, isPi_lift, piSpinedTc, rest.wk_spined d k]
      cases hA : isPi A <;> cases hM : isPi M <;> simp

theorem piSpinedCv_castIdx {a b T T' : Expr Nat} (h : T = T') (c : EvCv R Γ a b T) :
    piSpinedCv (EvCv.castIdx h c) = piSpinedCv c := by
  subst h; rfl

theorem flattenCv_spined (u : Level) : {Γ : LCtx} → {a b T : Expr Nat} → (c : EvCv R Γ a b T) →
    (hT : T = .sort u) → piSpinedCv c = true → isPi a = true → isPi b = true →
    (flattenCv u c hT).spined = true
  | _, _, _, _, @EvCv.trans _ _ _ _ _ m _ _ c₁ c₂, hT, hp, ha, hb => by
      have hp' := hp
      simp only [piSpinedCv, Bool.and_eq_true] at hp'
      obtain ⟨⟨hm, hp1⟩, hp2⟩ := hp'
      simp only [flattenCv, Flat.append_spined, flattenCv_spined u c₁ hT hp1 ha hm,
        flattenCv_spined u c₂ hT hp2 hm hb, Bool.and_self]
  | _, _, _, _, .symm c, hT, hp, ha, hb => by
      simp only [flattenCv]
      exact (flattenCv u c hT).symm_spined
        (flattenCv_spined u c hT (by simpa only [piSpinedCv] using hp) hb ha)
  | _, _, _, _, .refl _, _, _, _, _ => rfl
  | _, _, _, _, .lit h hsub, hT, hp, ha, hb => by
      simp only [flattenCv, Flat.spined, piSpinedTc, piSpinedCv_castIdx, hp, ha, hb,
        Bool.and_self, Bool.true_and, Bool.and_true]
  | _, _, _, _, .tyConv u' c cA, hT, hp, ha, hb => by
      simp only [flattenCv, Flat.spined, piSpinedTc, piSpinedCv_castIdx, hp, ha, hb,
        Bool.and_self, Bool.true_and, Bool.and_true]
  | _, _, _, _, .wk d k c, hT, hp, ha, hb => by
      simp only [flattenCv, Flat.spined, piSpinedTc, piSpinedCv_castIdx, hp, ha, hb,
        Bool.and_self, Bool.true_and, Bool.and_true]
  | _, _, _, _, .esub j u' c hget hv hvT, hT, hp, ha, hb => by
      simp only [flattenCv, Flat.spined, piSpinedTc, piSpinedCv_castIdx, hp, ha, hb,
        Bool.and_self, Bool.true_and, Bool.and_true]
  | _, _, _, _, .subst0 j c hget hv, hT, hp, ha, hb => by
      simp only [flattenCv, Flat.spined, piSpinedTc, piSpinedCv_castIdx, hp, ha, hb,
        Bool.and_self, Bool.true_and, Bool.and_true]
  | _, _, _, _, .substLet j c hget hv, hT, hp, ha, hb => by
      simp only [flattenCv, Flat.spined, piSpinedTc, piSpinedCv_castIdx, hp, ha, hb,
        Bool.and_self, Bool.true_and, Bool.and_true]
  -- carrier amendment (#7118, D lane): level conversions are never Π-spined (W-X-LEVELS),
  -- and a `rety` node is one `ofCv` link whose spine is its body's.
  | _, _, _, _, .sorts .., _, hp, _, _ => nomatch hp
  | _, _, _, _, .consts .., _, hp, _, _ => nomatch hp
  | _, _, _, _, .rety c cA, hT, hp, ha, hb => by
      simp only [flattenCv, Flat.spined, piSpinedTc, piSpinedCv_castIdx, hp, ha, hb,
        Bool.and_self, Bool.true_and, Bool.and_true]

theorem flattenT_spined : {Γ : LCtx} → {A B : Expr Nat} → (d : TyConvT E n Γ A B) →
    (hsub : ∃ r ∈ R, SubEq (.tc d) r) → piSpinedT d = true → isPi A = true → isPi B = true →
    (flattenT d hsub).spined = true
  | _, _, _, .refl _ _, _, _, _, _ => by simp only [flattenT, Flat.spined]
  | _, _, _, .of _ _ _ u h, hsub, hp, ha, hb => by
      simp only [flattenT, Flat.spined, piSpinedTc, piSpinedCv, ha, hb, Bool.true_and,
        Bool.and_true]
      simpa only [piSpinedT] using hp
  | _, _, _, .trans _ _ M _ d₁ d₂, hsub, hp, ha, hb => by
      have hp' := hp
      simp only [piSpinedT, Bool.and_eq_true] at hp'
      obtain ⟨⟨hm, hp1⟩, hp2⟩ := hp'
      simp only [flattenT, Flat.append_spined, flattenT_spined d₁ _ hp1 ha hm,
        flattenT_spined d₂ _ hp2 hm hb, Bool.and_self]

theorem flattenTc_spined : {Γ : LCtx} → {A B : Expr Nat} → (c : EvTc R Γ A B) →
    piSpinedTc c = true → isPi A = true → isPi B = true → (flattenTc c).spined = true
  | _, _, _, .lit d hsub, hp, ha, hb =>
      flattenT_spined d hsub (by simpa only [piSpinedTc] using hp) ha hb
  | _, _, _, .ofCv u c, hp, ha, hb =>
      flattenCv_spined u c rfl (by simpa only [piSpinedTc] using hp) ha hb
  | _, _, _, .refl _ _, _, _, _ => rfl
  | _, _, _, .symm c, hp, ha, hb => by
      simp only [flattenTc]
      exact (flattenTc c).symm_spined
        (flattenTc_spined c (by simpa only [piSpinedTc] using hp) hb ha)
  | _, _, _, @EvTc.trans _ _ _ _ _ M _ c₁ c₂, hp, ha, hb => by
      have hp' := hp
      simp only [piSpinedTc, Bool.and_eq_true] at hp'
      obtain ⟨⟨hm, hp1⟩, hp2⟩ := hp'
      simp only [flattenTc, Flat.append_spined, flattenTc_spined c₁ hp1 ha hm,
        flattenTc_spined c₂ hp2 hm hb, Bool.and_self]
  | _, _, _, .piCod u hA c, hp, ha, hb => by
      simp only [flattenTc, Flat.spined, piSpinedTc, isPi, Bool.and_self, Bool.true_and]
  | _, _, _, .subst0 j c hget hv, hp, ha, hb => by
      simp only [flattenTc, Flat.spined, hp, ha, hb, Bool.and_self, Bool.true_and, Bool.and_true]
  | _, _, _, .substLet j c hget hv, hp, ha, hb => by
      simp only [flattenTc, Flat.spined, hp, ha, hb, Bool.and_self, Bool.true_and, Bool.and_true]
  | _, _, _, @EvTc.wk _ _ _ Γ₀ A₀ B₀ d k h, hp, ha, hb => by
      have hp' := hp
      simp only [piSpinedTc, Bool.and_eq_true] at hp'
      obtain ⟨⟨hA0, hB0⟩, hph⟩ := hp'
      simp only [flattenTc, Flat.wk_spined]
      exact flattenTc_spined h hph hA0 hB0

/-- a spined chain segments into single Π-spined links, each an admissible segment. -/
theorem segmentF_adm_of_spined : (N : Nat) → {P Q : Expr Nat} → (f : Flat R Γ P Q) →
    (hQ : isPi Q = true) → f.length ≤ N → f.spined = true → (Flat.segmentF N f hQ).adm = true
  | 0, _, _, .nil _, _, _, _ => rfl
  | _ + 1, _, _, .nil _, _, _, _ => rfl
  | 0, _, _, .cons _ _ _, _, hN, _ => by simp only [Flat.length] at hN; omega
  | N + 1, _, _, @Flat.cons _ _ _ _ A M B l hl rest, hQ, hN, hs => by
      simp only [Flat.spined, Bool.and_eq_true] at hs
      obtain ⟨⟨⟨hA, hM⟩, hl'⟩, hr⟩ := hs
      obtain ⟨M₁, M₂, hMeq⟩ := isPi_true hM
      subst hMeq
      simp only [Flat.segmentF, Flat.splitPi, Segs.adm, Flat.segAdm, hl', Bool.true_or,
        Bool.true_and]
      exact segmentF_adm_of_spined N rest hQ (by simp only [Flat.length] at hN; omega) hr

/-- S1's fragment is inside S3's: every Π-spined input is admissible. -/
theorem xAdm_of_piSpined {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hp : piSpinedTc c = true) : xAdm c = true := by
  simp only [xAdm, Flat.segment]
  exact segmentF_adm_of_spined _ (flattenTc c) rfl (Nat.le_refl _) (flattenTc_spined c hp rfl rfl)

/-! ### Stratum A consults no supplier -/

/-- every segment is one Π-spined link. -/
def Segs.stratumA : {P Q : Expr Nat} → Segs R Γ P Q → Bool
  | _, _, .nil _ => true
  | _, _, .cons (.cons l _ (.nil _)) _ rest => piSpinedTc l && rest.stratumA
  | _, _, .cons (.nil _) _ _ => false
  | _, _, .cons (.cons _ _ (.cons _ _ _)) _ _ => false

theorem segmentF_stratumA_of_spined : (N : Nat) → {P Q : Expr Nat} → (f : Flat R Γ P Q) →
    (hQ : isPi Q = true) → f.length ≤ N → f.spined = true →
    (Flat.segmentF N f hQ).stratumA = true
  | 0, _, _, .nil _, _, _, _ => rfl
  | _ + 1, _, _, .nil _, _, _, _ => rfl
  | 0, _, _, .cons _ _ _, _, hN, _ => by simp only [Flat.length] at hN; omega
  | N + 1, _, _, @Flat.cons _ _ _ _ A M B l hl rest, hQ, hN, hs => by
      simp only [Flat.spined, Bool.and_eq_true] at hs
      obtain ⟨⟨⟨hA, hM⟩, hl'⟩, hr⟩ := hs
      obtain ⟨M₁, M₂, hMeq⟩ := isPi_true hM
      subst hMeq
      simp only [Flat.segmentF, Flat.splitPi, Segs.stratumA, hl', Bool.true_and]
      exact segmentF_stratumA_of_spined N rest hQ (by simp only [Flat.length] at hN; omega) hr

/-- a single Π-spined link is answered by Stratum A, whatever the suppliers. -/
theorem xSeg_isSome_of_spined (X : Suppliers E n) (hΓ : CtxWfT E n Γ) {P M : Expr Nat}
    (l : EvTc R Γ P M) (hl : isLink l = true) (hadm : (Flat.cons l hl (Flat.nil M)).segAdm = true)
    (hp : piSpinedTc l = true) {A B A' B' : Expr Nat} (hP : P = .pi A B) (hM : M = .pi A' B') :
    (xSeg X hΓ (Flat.cons l hl (Flat.nil M)) hadm hP hM).isSome = true := by
  rw [xSeg, dif_pos hp]
  rfl

theorem isSome_map' {α β : Type} (f : α → β) (o : Option α) : (o.map f).isSome = o.isSome := by
  cases o <;> rfl

/-- a Stratum-A segmentation is answered, whatever the suppliers. -/
theorem xSegs_isSome_of_stratumA (X : Suppliers E n) (hΓ : CtxWfT E n Γ) : {P Q : Expr Nat} →
    (s : Segs R Γ P Q) → (hadm : s.adm = true) → s.stratumA = true →
    ∀ {A B A' B' : Expr Nat} (hP : P = .pi A B) (hQ : Q = .pi A' B'),
    (xSegs X hΓ s hadm hP hQ).isSome = true
  | _, _, .nil _, _, _, A, B, A', B', hP, hQ => by
      subst hP
      injection hQ with h1 h2
      subst h1; subst h2
      rfl
  | _, _, @Segs.cons _ _ _ _ P M Q p hM rest, hadm, hsA, A, B, A', B', hP, hQ => by
      cases p with
      | nil _ => simp only [Segs.stratumA, Bool.false_eq_true] at hsA
      | cons l hl rest' =>
          cases rest' with
          | cons _ _ _ => simp only [Segs.stratumA, Bool.false_eq_true] at hsA
          | nil _ =>
              simp only [Segs.stratumA, Bool.and_eq_true] at hsA
              obtain ⟨hp, hsA'⟩ := hsA
              have h' : (Flat.cons l hl (Flat.nil M)).segAdm = true ∧ rest.adm = true := by
                simpa only [Segs.adm, Bool.and_eq_true] using hadm
              obtain ⟨A₁, B₁, hM'⟩ := isPi_true hM
              have h1 := xSeg_isSome_of_spined X hΓ l hl h'.1 hp hP hM'
              have h2 := xSegs_isSome_of_stratumA X hΓ rest h'.2 hsA' hM' hQ
              subst hM'
              rw [xSegs]
              simp only [isPiD]
              split
              · rfl
              · rename_i hne
                exfalso
                rcases e1 : xSeg X hΓ (Flat.cons l hl (Flat.nil _)) h'.1 hP rfl with _ | ⟨o₁, bd₁⟩
                · rw [e1] at h1; simp at h1
                · rcases e2 : xSegs X hΓ rest h'.2 rfl hQ with _ | ⟨o₂, bd₂⟩
                  · rw [e2] at h2; simp at h2
                  · exact hne o₁ bd₁ o₂ bd₂ e1 e2

/-! ### the tile -/

/-- the X tile on provenance in a well-formed context, on the admissible fragment, bounded:
    an answer or a refusal (a supplier declined). -/
def xTile? (X : Suppliers E n) (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hadm : xAdm c = true) :
    Option (BOut R Γ A B A' B' c.leaves) :=
  xValley? X hΓ c hadm

/-- `XProcWf`'s shape on admissible inputs: the components, or a refusal. -/
def xTile (X : Suppliers E n) (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hadm : xAdm c = true) :
    Option (EvTc R Γ A A' × EvTc R (.assumption A :: Γ) B B') :=
  xValley X hΓ c hadm

/-- `XContractWf`'s clause on every answer. -/
theorem xTile_contract (X : Suppliers E n) (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hadm : xAdm c = true)
    (o : EvTc R Γ A A' × EvTc R (.assumption A :: Γ) B B') (ho : xTile X hΓ c hadm = some o) :
    ∀ ℓ ∈ o.1.leaves ++ o.2.leaves, ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ' :=
  xValley_contract X hΓ c hadm o ho

/-- Stratum A is answered by every supplier bundle: the tile consults no supplier there. -/
theorem xTile?_isSome_of_piSpined (X : Suppliers E n) (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hp : piSpinedTc c = true) :
    (xTile? X hΓ c (xAdm_of_piSpined c hp)).isSome = true := by
  simp only [xTile?, xValley?, isSome_map']
  exact xSegs_isSome_of_stratumA X hΓ _ _
    (segmentF_stratumA_of_spined _ (flattenTc c) rfl (Nat.le_refl _) (flattenTc_spined c hp rfl rfl))
    rfl rfl

theorem xTile_isSome_of_piSpined (X : Suppliers E n) (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hp : piSpinedTc c = true) :
    (xTile X hΓ c (xAdm_of_piSpined c hp)).isSome = true := by
  simp only [xTile, xValley, isSome_map']
  exact xTile?_isSome_of_piSpined X hΓ c hp

/-! ### pins -/

section Pins
open EtaKAnnot EtaKAnnot.Pins

/-- the etaK fixture's request is Π-spined (S1) hence admissible — both routes agree. -/
theorem pin_request_xAdm_of_piSpined : xAdm request = true :=
  xAdm_of_piSpined request pin_request_piSpined

/-- every answer of the tile on the etaK request keeps `X_outputs_edge`'s fact: its leaves are
    strictly below an ORIGINAL removed D input (S1's `pin_request_edge` through the one entry
    point). -/
theorem pin_request_edge_tile (X : Suppliers emptyEnv 0) :
    ∀ o, xTile X CtxWfT.nil request pin_request_xAdm = some o →
    OM3_edge (callerAtoms dL dR cL cR frame) ((o.1.leaves ++ o.2.leaves) ++ frame) := fun o ho =>
  om3_edge_of_strictLeaves (List.cons_ne_nil _ _) (fun ℓ hℓ => by
    obtain ⟨ℓ', hm, hs⟩ := xTile_contract X CtxWfT.nil request pin_request_xAdm o ho ℓ hℓ
    obtain ⟨root, hr, ht⟩ := annotRequest_strict dL dR cL cR ℓ' hm
    exact ⟨root, hr, subEq_trans_subOf hs ht⟩)

/-- and the declining suppliers DO answer it (Stratum A): the pin above is not vacuous. -/
theorem pin_request_answered (hsep : SepAll emptyEnv 0) :
    (xTile (Suppliers.declining hsep) CtxWfT.nil request pin_request_xAdm).isSome = true :=
  xTile_isSome_of_piSpined (Suppliers.declining hsep) CtxWfT.nil request pin_request_piSpined

/-- the β fixture's answers, if any, keep strict provenance: every output leaf is `SubEq` the
    one input leaf `.tc betaMiddleT`. -/
theorem pin_betaMiddle_tile_contract (X : Suppliers emptyEnv 0) :
    ∀ o, xTile X CtxWfT.nil (EvTc.lit betaMiddleT ⟨.tc betaMiddleT, .head _, .inl rfl⟩ :
        EvTc [Jd.tc betaMiddleT] [] piX piX) pin_betaMiddle_xAdm = some o →
    ∀ ℓ ∈ o.1.leaves ++ o.2.leaves, SubEq ℓ (.tc betaMiddleT) := by
  intro o ho ℓ hℓ
  obtain ⟨ℓ', hm, hs⟩ := xTile_contract X CtxWfT.nil _ pin_betaMiddle_xAdm o ho ℓ hℓ
  simp only [EvTc.leaves, List.mem_cons, List.not_mem_nil, or_false] at hm
  subst hm
  exact hs

end Pins

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.Flat.spined
#print axioms Rcic.Declarative.F8Measure.Flat.append_spined
#print axioms Rcic.Declarative.F8Measure.linkSymm_piSpined
#print axioms Rcic.Declarative.F8Measure.Flat.symm_spined
#print axioms Rcic.Declarative.F8Measure.Flat.wk_spined
#print axioms Rcic.Declarative.F8Measure.piSpinedCv_castIdx
#print axioms Rcic.Declarative.F8Measure.flattenCv_spined
#print axioms Rcic.Declarative.F8Measure.flattenT_spined
#print axioms Rcic.Declarative.F8Measure.flattenTc_spined
#print axioms Rcic.Declarative.F8Measure.segmentF_adm_of_spined
#print axioms Rcic.Declarative.F8Measure.xAdm_of_piSpined
#print axioms Rcic.Declarative.F8Measure.Segs.stratumA
#print axioms Rcic.Declarative.F8Measure.segmentF_stratumA_of_spined
#print axioms Rcic.Declarative.F8Measure.xSeg_isSome_of_spined
#print axioms Rcic.Declarative.F8Measure.isSome_map'
#print axioms Rcic.Declarative.F8Measure.xSegs_isSome_of_stratumA
#print axioms Rcic.Declarative.F8Measure.xTile?
#print axioms Rcic.Declarative.F8Measure.xTile
#print axioms Rcic.Declarative.F8Measure.xTile_contract
#print axioms Rcic.Declarative.F8Measure.xTile?_isSome_of_piSpined
#print axioms Rcic.Declarative.F8Measure.xTile_isSome_of_piSpined
#print axioms Rcic.Declarative.F8Measure.pin_request_xAdm_of_piSpined
#print axioms Rcic.Declarative.F8Measure.pin_request_edge_tile
#print axioms Rcic.Declarative.F8Measure.pin_request_answered
#print axioms Rcic.Declarative.F8Measure.pin_betaMiddle_tile_contract

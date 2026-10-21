import rcic.RcicF8XValley

/-! # RcicF8XAdmLit — the entry lemma `xAdm_lit` (#7156 item 8)

For every `TyConvT` literal, `xAdm (EvTc.lit d hsub) = true`: `flattenT` emits only
`ofCv u (EvCv.lit …)` links (`TyConvT` has only `refl`/`of`/`trans`) and
`bCv (.lit ..) = true`, so every link is a `bLink`, every segment `segAdm`. Hence
`xAdm = false` (W-X-SUBST / W-X-WK / W-X-LEVELS) is reached only through
provenance inputs with lazy `wk`/`esub`/`subst0`/`sorts`/`consts` nodes — i.e. on
the mutual recursion's re-entry, not under piRow's quantifier at the entry.

Teeth: a lazy `wk` node over the same β literal is refused; the mutant `bCv`
that marks `.lit` false wrongly refuses the β literal (Stratum B) that the landed
`pin_betaMiddle_xAdm` admits. `closure_claim = 0`. -/

namespace Rcic.Declarative.F8Measure

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)} {Γ : LCtx}

/-- `bPrefix` distributes over `append`. -/
theorem Flat.append_bPrefix : {A M B : Expr Nat} → (f : Flat R Γ A M) →
    (g : Flat R Γ M B) → (f.append g).bPrefix = (f.bPrefix && g.bPrefix)
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons l hl rest, g => by
      simp only [Flat.append, Flat.bPrefix, Flat.append_bPrefix rest g,
        Bool.and_assoc]

/-- every link a `TyConvT` literal flattens to is an `ofCv` of an `EvCv.lit`, hence
    a `bLink`: the whole flattened chain is a `bPrefix`. -/
theorem flattenT_bPrefix : {Γ : LCtx} → {A B : Expr Nat} →
    (d : TyConvT E n Γ A B) → (hsub : ∃ r ∈ R, SubEq (.tc d) r) →
    (flattenT d hsub).bPrefix = true
  | _, _, _, .refl _ _, _ => by simp only [flattenT, Flat.bPrefix]
  | _, _, _, .of _ _ _ _ _, _ => by
      simp only [flattenT, Flat.bPrefix, bLink, bCv, Bool.true_and]
  | _, _, _, .trans _ _ _ _ d₁ d₂, hsub => by
      have ih₁ := flattenT_bPrefix d₁ (certOfChild (tcChildFst d₁ d₂) hsub)
      have ih₂ := flattenT_bPrefix d₂ (certOfChild (tcChildSnd d₁ d₂) hsub)
      simp only [flattenT, Flat.append_bPrefix, ih₁, ih₂, Bool.and_true]

/-- `splitPi` splits a `bPrefix` into two `bPrefix`es. -/
theorem Flat.splitPi_bPrefix : {A₀ C : Expr Nat} → (f : Flat R Γ A₀ C) →
    (hC : isPi C = true) → f.bPrefix = true →
    (f.splitPi hC).2.2.1.bPrefix = true ∧ (f.splitPi hC).2.2.2.bPrefix = true
  | _, _, .nil _, _, _ => ⟨rfl, rfl⟩
  | _, _, @Flat.cons _ _ _ _ A M B l hl rest, hC, h => by
      have h' : bLink l = true ∧ rest.bPrefix = true := by
        simpa only [Flat.bPrefix, Bool.and_eq_true] using h
      have ih := rest.splitPi_bPrefix hC h'.2
      cases M <;> simp only [Flat.splitPi, Flat.bPrefix, Bool.and_eq_true,
        Bool.and_true] <;>
        first | exact ⟨⟨h'.1, ih.1⟩, ih.2⟩ | exact ⟨h'.1, h'.2⟩

/-- a `bPrefix` chain is an admissible segment: a single link may also be
    Π-spined, but `bLink` alone already passes the disjunct. -/
theorem Flat.segAdm_of_bPrefix : {P M : Expr Nat} → (p : Flat R Γ P M) →
    p.bPrefix = true → p.segAdm = true
  | _, _, .nil _, _ => rfl
  | _, _, .cons l hl (.nil _), h => by
      have h' : bLink l = true := by
        simpa only [Flat.bPrefix, Bool.and_true] using h
      simp only [Flat.segAdm, h', Bool.or_true]
  | _, _, .cons l hl (.cons l' hl' rest'), h => by
      simpa only [Flat.segAdm] using h

/-- every segment of a `bPrefix` chain is admissible. -/
theorem Flat.segmentF_adm_of_bPrefix : (N : Nat) → {P Q : Expr Nat} →
    (f : Flat R Γ P Q) → (hQ : isPi Q = true) → f.bPrefix = true →
    (Flat.segmentF N f hQ).adm = true
  | _, _, _, .nil _, _, _ => by simp only [Flat.segmentF, Segs.adm]
  | 0, _, _, .cons l hl rest, hQ, h => by
      simp only [Flat.segmentF, Segs.adm, Bool.and_true]
      exact Flat.segAdm_of_bPrefix _ h
  | N + 1, _, _, .cons l hl rest, hQ, h => by
      have hs := Flat.splitPi_bPrefix _ hQ h
      simp only [Flat.segmentF, Segs.adm, Bool.and_eq_true]
      exact ⟨Flat.segAdm_of_bPrefix _ hs.1,
        Flat.segmentF_adm_of_bPrefix N _ hQ hs.2⟩

/-- THE ENTRY LEMMA: every `TyConvT` literal between Π endpoints is an admissible
    X input. `xAdm = false` is therefore reachable only through provenance nodes
    introduced by the mutual recursion (lazy `wk`, `esub`, `subst0`, sorts,
    consts), never at piRow's entry quantifier. -/
theorem xAdm_lit {A B A' B' : Expr Nat} (d : TyConvT E n Γ (.pi A B) (.pi A' B'))
    (hsub : ∃ r ∈ R, SubEq (.tc d) r) : xAdm (EvTc.lit d hsub) = true := by
  simp only [xAdm, flattenTc]
  exact Flat.segmentF_adm_of_bPrefix _ (flattenT d hsub) rfl
    (flattenT_bPrefix d hsub)

section Pins

/-- the landed β literal is a Stratum-B instance of the entry lemma (consistency
    with the landed `pin_betaMiddle_xAdm`). -/
theorem xAdm_lit_betaMiddle :
    xAdm (EvTc.lit betaMiddleT ⟨.tc betaMiddleT, .head _, .inl rfl⟩ :
      EvTc [Jd.tc betaMiddleT] [] piX piX) = true :=
  xAdm_lit _ _

/-- the weakening declaration of the lazy-input tooth. -/
def litWkDecl : LocalDecl := .assumption (.sort .zero)

/-- TOOTH (non-literal input): the same β literal under ONE lazy weakening at
    cutoff 1 is refused by `xAdm` (`insertAt d 1 [] = [d]`, `lift 1 1 piX = piX`,
    both rfl). -/
theorem pin_xAdm_wk1_lit_false :
    xAdm (EvTc.wk litWkDecl 1
      (EvTc.lit betaMiddleT ⟨.tc betaMiddleT, .head _, .inl rfl⟩) :
      EvTc [Jd.tc betaMiddleT] [litWkDecl] piX piX) = false := by
  simp only [xAdm, betaMiddleT, flattenTc, flattenT, Flat.append, Flat.wk,
    Flat.segment, Flat.segmentF, Flat.length, Flat.splitPi, Segs.adm,
    Flat.segAdm, Flat.bPrefix, bLink, bCv, isPi_lift, isPi, Bool.false_and,
    Bool.and_false, Bool.and_self, Bool.and_true, Bool.true_and]

/-- MUTANT: `bCv` with the `.lit` arm marked `false` — every other arm
    unchanged. -/
def bCvMut : {Γ : LCtx} → {a b T : Expr Nat} → EvCv R Γ a b T → Bool
  | _, _, _, _, .lit _ _ => false
  | _, _, _, _, .refl _ => true
  | _, _, _, _, .symm c => bCvMut c
  | _, _, _, _, .trans c₁ c₂ => bCvMut c₁ && bCvMut c₂
  | _, _, _, _, .tyConv _ c _ => bCvMut c
  | _, _, _, _, .rety c _ => bCvMut c
  | _, _, _, _, .wk _ k c =>
      match k with
      | 0 => bCvMut c
      | _ + 1 => false
  | _, _, _, _, .esub .. => false
  | _, _, _, _, .subst0 .. => false
  | _, _, _, _, .substLet .. => false
  | _, _, _, _, .sorts .. => false
  | _, _, _, _, .consts .. => false

/-- the mutant link Bool: `bLink`'s arms over `bCvMut`/`bLinkMut`. -/
def bLinkMut : {Γ : LCtx} → {A B : Expr Nat} → EvTc R Γ A B → Bool
  | _, _, _, .ofCv _ c => bCvMut c
  | _, _, _, .wk _ k l =>
      match k with
      | 0 => bLinkMut l
      | _ + 1 => false
  | _, _, _, .piCod .. => false
  | _, _, _, .subst0 .. => false
  | _, _, _, .substLet .. => false
  | _, _, _, .lit .. => false
  | _, _, _, .refl .. => false
  | _, _, _, .symm .. => false
  | _, _, _, .trans .. => false

/-- the mutant prefix Bool. -/
def Flat.bPrefixMut : {A B : Expr Nat} → Flat R Γ A B → Bool
  | _, _, .nil _ => true
  | _, _, .cons l _ rest => bLinkMut l && rest.bPrefixMut

/-- the mutant segment-admissibility Bool. -/
def Flat.segAdmMut : {P M : Expr Nat} → Flat R Γ P M → Bool
  | _, _, .nil _ => true
  | _, _, .cons l _ (.nil _) => piSpinedTc l || bLinkMut l
  | _, _, .cons l _ (.cons l' hl' rest') => bLinkMut l && (Flat.cons l' hl' rest').bPrefixMut

/-- the mutant segment-list-admissibility Bool. -/
def Segs.admMut : {P Q : Expr Nat} → Segs R Γ P Q → Bool
  | _, _, .nil _ => true
  | _, _, .cons p _ rest => p.segAdmMut && rest.admMut

/-- the mutant X admissibility. -/
def xAdmMut {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B')) : Bool :=
  ((flattenTc c).segment rfl).admMut

/-- the mutant marks every `lit` conversion false. -/
theorem bCvMut_lit {Γ : LCtx} {a b T : Expr Nat} (h : ConvT E n Γ a b T)
    (hsub : ∃ r ∈ R, SubEq (.cv h) r) : bCvMut (EvCv.lit h hsub) = false := rfl

/-- the mutant wrongly refuses the β literal that `xAdm` (and `xAdm_lit`)
    admits: the lemma's content is the `.lit` arm of `bCv`. -/
theorem mutant_refuses_betaMiddle :
    xAdmMut (EvTc.lit betaMiddleT ⟨.tc betaMiddleT, .head _, .inl rfl⟩ :
      EvTc [Jd.tc betaMiddleT] [] piX piX) = false := by
  simp only [xAdmMut, betaMiddleT, flattenTc, flattenT, Flat.append,
    Flat.segment, Flat.segmentF, Flat.length, Flat.splitPi, Segs.admMut,
    Flat.segAdmMut, Flat.bPrefixMut, bLinkMut, bCvMut, piSpinedTc, piSpinedT,
    piSpinedConv, isPi, Bool.false_and, Bool.and_false, Bool.and_self,
    Bool.and_true, Bool.true_and, Bool.or_false]

end Pins

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.Flat.append_bPrefix
#print axioms Rcic.Declarative.F8Measure.flattenT_bPrefix
#print axioms Rcic.Declarative.F8Measure.Flat.splitPi_bPrefix
#print axioms Rcic.Declarative.F8Measure.Flat.segAdm_of_bPrefix
#print axioms Rcic.Declarative.F8Measure.Flat.segmentF_adm_of_bPrefix
#print axioms Rcic.Declarative.F8Measure.xAdm_lit
#print axioms Rcic.Declarative.F8Measure.xAdm_lit_betaMiddle
#print axioms Rcic.Declarative.F8Measure.litWkDecl
#print axioms Rcic.Declarative.F8Measure.pin_xAdm_wk1_lit_false
#print axioms Rcic.Declarative.F8Measure.bCvMut
#print axioms Rcic.Declarative.F8Measure.bLinkMut
#print axioms Rcic.Declarative.F8Measure.Flat.bPrefixMut
#print axioms Rcic.Declarative.F8Measure.Flat.segAdmMut
#print axioms Rcic.Declarative.F8Measure.Segs.admMut
#print axioms Rcic.Declarative.F8Measure.xAdmMut
#print axioms Rcic.Declarative.F8Measure.bCvMut_lit
#print axioms Rcic.Declarative.F8Measure.mutant_refuses_betaMiddle

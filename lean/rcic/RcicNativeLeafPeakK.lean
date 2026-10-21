import rcic.RcicNativeCertifiedKRows
import rcic.RcicNativeCertifiedKControl
import rcic.RcicNativeLeafJoinL

/-!
# RcicNativeLeafPeakK — the #7604 consumer over the enlarged relation

`RcicNativeLeafPeakConfluence` (#7604) consumes `LeafPeakDiamond` over the K-free carriers
`CStep`/`CStar`; #7606 refuted that oracle.  The consumer's recursions never inspect a
certificate, so they re-run verbatim over `CStepK`/`CStarK`: endpoint typings
(`CStarK.leftTyped`/`rightTyped`), coherence (`CoherentK`, `coherentK_trans`,
`coherentK_reindex`), the pure-leaf stars (`LeafStarK`, `PureLeaf` is on the step and
unchanged), the oracle `LeafPeakJoinK`/`LeafPeakDiamondK`, adjust-then-step
(`RStepK`/`RStarK`), `rDiamondK`, `stripRK`, `confluenceRK`, and
`starConfluenceK_of_leafPeakDiamondK` on coherent inputs.

**Positive control.**  `unit_leafPeakJoinK`: #7606's peak — the certified η step and the
certified λ/ι step out of `λp:True. True.rec M (Sort 0) p` — is joined in the enlarged
relation by ONE step, the natively certified η-K node `unitKEtaCStepK` on the η side and
reflexivity on the other, with every decoration equality `rfl`.  The K-free relation has
no such join of any length (`admitted_unit_no_valley`).

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-! ### carriers -/

/-- Source typing of a star. -/
def CStarK.leftTyped (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {a b A : Expr Nat} → CStarK E n PEq Γ a b A → HasTyT E n Γ a A
  | _, _, _, .refl _ _ _ h => h
  | _, _, _, .tail s _ => s.leftTyped L hΓ

/-- Target typing of a star. -/
def CStarK.rightTyped : {Γ : LCtx} → {a b A : Expr Nat} → CStarK E n PEq Γ a b A →
    HasTyT E n Γ b A
  | _, _, _, _, .refl _ _ _ h => h
  | _, _, _, _, .tail _ hs => hs.rightTyped

/-- Index transport of a star. -/
def CStarK.reindex {Γ : LCtx} {A A' : Expr Nat} (hcT : TyConvT E n Γ A A') :
    {a b : Expr Nat} → CStarK E n PEq Γ a b A → CStarK E n PEq Γ a b A'
  | _, _, .refl _ a _ h => .refl Γ a A' (hasTyT_of_tyConvT h hcT)
  | _, _, .tail s hs => .tail (s.reindex hcT) (hs.reindex hcT)

/-- One step as a star. -/
def CStarK.ofStep (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b A : Expr Nat}
    (s : CStepK E n PEq Γ a b A) : CStarK E n PEq Γ a b A :=
  .tail s (.refl Γ b A (s.rightTyped L hΓ))

end Rcic.Declarative.NativeValleys

namespace Rcic.Declarative.NativeValleys.LeafPeakKAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

open LeafJoinAudit (PureLeaf)

/-! ### coherence -/

/-- Reindexing keeps the source decoration. -/
theorem reindexK_left_deco (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e e' T T' : Expr Nat} (s : CStepK E n PEq Γ e e' T) (hc : TyConvT E n Γ T T') :
    decoOf ((s.reindex hc).leftTyped L hΓ) = decoOf (s.leftTyped L hΓ) := by
  simp only [CStepK.reindex, CStepK.leftTyped, parRedT_hasTy_left, parRedT_typed,
    decoOf_hasTyT_of_tyConvT]

/-- Reindexing keeps the target decoration. -/
theorem reindexK_right_deco (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e e' T T' : Expr Nat} (s : CStepK E n PEq Γ e e' T) (hc : TyConvT E n Γ T T') :
    decoOf ((s.reindex hc).rightTyped L hΓ) = decoOf (s.rightTyped L hΓ) := by
  simp only [CStepK.reindex, CStepK.rightTyped, parRedT_hasTy_right, parRedT_typed,
    decoOf_hasTyT_of_tyConvT]

/-- Adjacent interfaces agree. -/
def CoherentK (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {a b T : Expr Nat} → CStarK E n PEq Γ a b T → Prop
  | _, _, _, .refl .. => True
  | _, _, _, .tail s ss =>
      decoOf (s.rightTyped L hΓ) = decoOf (ss.leftTyped L hΓ) ∧ CoherentK L hΓ ss

/-- Coherent stars concatenate when the interface agrees. -/
theorem coherentK_trans (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {a b c T : Expr Nat} → (s : CStarK E n PEq Γ a b T) → (t : CStarK E n PEq Γ b c T) →
    CoherentK L hΓ s → CoherentK L hΓ t →
    decoOf s.rightTyped = decoOf (t.leftTyped L hΓ) →
    CoherentK L hΓ (s.trans t) ∧
      decoOf ((s.trans t).leftTyped L hΓ) = decoOf (s.leftTyped L hΓ) ∧
      decoOf (s.trans t).rightTyped = decoOf t.rightTyped
  | _, _, _, _, .refl .., t, _, ht, hm => by
      simp only [CStarK.trans, CStarK.leftTyped, CStarK.rightTyped, CoherentK] at hm ⊢
      exact ⟨ht, hm.symm, by trivial⟩
  | _, _, _, _, .tail s ss, t, hs, ht, hm => by
      simp only [CStarK.trans, CStarK.leftTyped, CStarK.rightTyped, CoherentK] at hm hs ⊢
      obtain ⟨h₁, h₂, h₃⟩ := coherentK_trans L hΓ ss t hs.2 ht hm
      exact ⟨⟨hs.1.trans h₂.symm, h₁⟩, by trivial, h₃⟩

/-- Coherence survives reindexing, with both endpoint decorations. -/
theorem coherentK_reindex (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {T T' : Expr Nat} (hc : TyConvT E n Γ T T') :
    {a b : Expr Nat} → (s : CStarK E n PEq Γ a b T) → CoherentK L hΓ s →
    CoherentK L hΓ (s.reindex hc) ∧
      decoOf ((s.reindex hc).leftTyped L hΓ) = decoOf (s.leftTyped L hΓ) ∧
      decoOf (s.reindex hc).rightTyped = decoOf s.rightTyped
  | _, _, .refl .., _ => by
      simp only [CStarK.reindex, CStarK.leftTyped, CStarK.rightTyped, CoherentK,
        decoOf_hasTyT_of_tyConvT]
      exact ⟨trivial, by trivial, by trivial⟩
  | _, _, .tail s ss, hs => by
      simp only [CoherentK] at hs
      obtain ⟨h₁, h₂, h₃⟩ := coherentK_reindex L hΓ hc ss hs.2
      simp only [CStarK.reindex, CStarK.leftTyped, CStarK.rightTyped, CoherentK]
      exact ⟨⟨(reindexK_right_deco L hΓ s hc).trans (hs.1.trans h₂.symm), h₁⟩,
        reindexK_left_deco L hΓ s hc, h₃⟩

/-- Stars of pure irrelevance steps. -/
inductive LeafStarK : {Γ : LCtx} → {a b T : Expr Nat} → CStarK E n PEq Γ a b T → Prop
  | refl {Γ : LCtx} {a A : Expr Nat} {h : HasTyT E n Γ a A} : LeafStarK (.refl Γ a A h)
  | tail {Γ : LCtx} {a b c A : Expr Nat} {s : CStepK E n PEq Γ a b A}
      {ss : CStarK E n PEq Γ b c A} (hs : PureLeaf s.step) (ht : LeafStarK ss) :
      LeafStarK (.tail s ss)

/-! ### the oracle -/

/-- The join of two steps out of the feet of a leaf peak, in the enlarged relation. -/
structure LeafPeakJoinK (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {m₁ m₂ d e T : Expr Nat}
    (p : CStepK E n PEq Γ m₁ d T) (q : CStepK E n PEq Γ m₂ e T) where
  centre : Expr Nat
  dAdj : Expr Nat
  eAdj : Expr Nat
  leftAdj : CStarK E n PEq Γ d dAdj T
  rightAdj : CStarK E n PEq Γ e eAdj T
  leftAdjLeaf : LeafStarK leftAdj
  rightAdjLeaf : LeafStarK rightAdj
  leftAdjCoherent : CoherentK L hΓ leftAdj
  rightAdjCoherent : CoherentK L hΓ rightAdj
  left : CStepK E n PEq Γ dAdj centre T
  right : CStepK E n PEq Γ eAdj centre T
  leftSource : decoOf (leftAdj.leftTyped L hΓ) = decoOf (p.rightTyped L hΓ)
  rightSource : decoOf (rightAdj.leftTyped L hΓ) = decoOf (q.rightTyped L hΓ)
  leftAdjInterface : decoOf leftAdj.rightTyped = decoOf (left.leftTyped L hΓ)
  rightAdjInterface : decoOf rightAdj.rightTyped = decoOf (right.leftTyped L hΓ)
  target : decoOf (left.rightTyped L hΓ) = decoOf (right.rightTyped L hΓ)

/-- The K-enlarged leaf-peak diamond. -/
def LeafPeakDiamondK (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b m₁ m₂ d e T : Expr Nat}
    (l₁ : CStarK E n PEq Γ b m₁ T) (l₂ : CStarK E n PEq Γ b m₂ T),
    LeafStarK l₁ → LeafStarK l₂ → CoherentK L hΓ l₁ → CoherentK L hΓ l₂ →
    decoOf (l₁.leftTyped L hΓ) = decoOf (l₂.leftTyped L hΓ) →
    (p : CStepK E n PEq Γ m₁ d T) → (q : CStepK E n PEq Γ m₂ e T) →
    decoOf l₁.rightTyped = decoOf (p.leftTyped L hΓ) →
    decoOf l₂.rightTyped = decoOf (q.leftTyped L hΓ) →
    LeafPeakJoinK L hΓ p q

/-! ### adjust-then-step -/

/-- A coherent pure-leaf star then one certified step, with the interface. -/
structure RStepK (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (b d T : Expr Nat) where
  mid : Expr Nat
  adj : CStarK E n PEq Γ b mid T
  step : CStepK E n PEq Γ mid d T
  adjLeaf : LeafStarK adj
  adjCoherent : CoherentK L hΓ adj
  interface : decoOf adj.rightTyped = decoOf (step.leftTyped L hΓ)

namespace RStepK

variable {L : LeafIface E n PEq} {Γ : LCtx} {hΓ : CtxWfT E n Γ}

/-- Source typing. -/
def leftTyped {b d T : Expr Nat} (r : RStepK L hΓ b d T) : HasTyT E n Γ b T :=
  r.adj.leftTyped L hΓ

/-- Target typing. -/
def rightTyped {b d T : Expr Nat} (r : RStepK L hΓ b d T) : HasTyT E n Γ d T :=
  r.step.rightTyped L hΓ

/-- Flatten. -/
def toCStarK {b d T : Expr Nat} (r : RStepK L hΓ b d T) : CStarK E n PEq Γ b d T :=
  r.adj.trans (CStarK.ofStep L hΓ r.step)

/-- A step with the empty adjustment. -/
def ofStep {b d T : Expr Nat} (s : CStepK E n PEq Γ b d T) : RStepK L hΓ b d T where
  mid := b
  adj := .refl Γ b T (s.leftTyped L hΓ)
  step := s
  adjLeaf := .refl
  adjCoherent := True.intro
  interface := by simp only [CStarK.rightTyped]

end RStepK

/-- Stars of adjust-then-step. -/
inductive RStarK (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    Expr Nat → Expr Nat → Expr Nat → Type
  | refl (a T : Expr Nat) (h : HasTyT E n Γ a T) : RStarK L hΓ a a T
  | tail {a b c T : Expr Nat} (r : RStepK L hΓ a b T) (rs : RStarK L hΓ b c T) :
      RStarK L hΓ a c T

namespace RStarK

variable {L : LeafIface E n PEq} {Γ : LCtx} {hΓ : CtxWfT E n Γ}

/-- Source typing. -/
def leftTyped : {a c T : Expr Nat} → RStarK L hΓ a c T → HasTyT E n Γ a T
  | _, _, _, .refl _ _ h => h
  | _, _, _, .tail r _ => r.leftTyped

/-- Target typing. -/
def rightTyped : {a c T : Expr Nat} → RStarK L hΓ a c T → HasTyT E n Γ c T
  | _, _, _, .refl _ _ h => h
  | _, _, _, .tail _ rs => rs.rightTyped

/-- Adjacent interfaces agree. -/
def Coherent : {a c T : Expr Nat} → RStarK L hΓ a c T → Prop
  | _, _, _, .refl .. => True
  | _, _, _, .tail r rs => decoOf r.rightTyped = decoOf rs.leftTyped ∧ Coherent rs

/-- Flatten. -/
def toCStarK : {a c T : Expr Nat} → RStarK L hΓ a c T → CStarK E n PEq Γ a c T
  | _, _, _, .refl a T h => .refl Γ a T h
  | _, _, _, .tail r rs => r.toCStarK.trans rs.toCStarK

/-- A star of the enlarged relation as adjust-then-steps with empty adjustments. -/
def ofCStarK : {a c T : Expr Nat} → CStarK E n PEq Γ a c T → RStarK L hΓ a c T
  | _, _, _, .refl _ a T h => .refl a T h
  | _, _, _, .tail s ss => .tail (RStepK.ofStep s) (ofCStarK ss)

theorem ofCStarK_leftTyped : {a c T : Expr Nat} → (s : CStarK E n PEq Γ a c T) →
    (ofCStarK (L := L) (hΓ := hΓ) s).leftTyped = s.leftTyped L hΓ
  | _, _, _, .refl .. => rfl
  | _, _, _, .tail _ _ => rfl

theorem ofCStarK_rightTyped : {a c T : Expr Nat} → (s : CStarK E n PEq Γ a c T) →
    (ofCStarK (L := L) (hΓ := hΓ) s).rightTyped = s.rightTyped
  | _, _, _, .refl .. => by simp only [ofCStarK, rightTyped, CStarK.rightTyped]
  | _, _, _, .tail _ ss => by
      simp only [ofCStarK, rightTyped, CStarK.rightTyped]
      exact ofCStarK_rightTyped ss

theorem ofCStarK_coherent : {a c T : Expr Nat} → (s : CStarK E n PEq Γ a c T) →
    CoherentK L hΓ s → (ofCStarK (L := L) (hΓ := hΓ) s).Coherent
  | _, _, _, .refl .., _ => True.intro
  | _, _, _, .tail _ ss, h => by
      simp only [CoherentK] at h
      exact ⟨by rw [ofCStarK_leftTyped ss]; exact h.1, ofCStarK_coherent ss h.2⟩

end RStarK

/-! ### diamond, strip, confluence -/

/-- The diamond of `RStepK` from the oracle. -/
def rDiamondK (L : LeafIface E n PEq) (D : LeafPeakDiamondK L) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d e T : Expr Nat} (r₁ : RStepK L hΓ b d T) (r₂ : RStepK L hΓ b e T)
    (hsrc : decoOf r₁.leftTyped = decoOf r₂.leftTyped) :
    Σ' (f : Expr Nat) (s₁ : RStepK L hΓ d f T) (s₂ : RStepK L hΓ e f T),
      decoOf s₁.leftTyped = decoOf r₁.rightTyped ∧
      decoOf s₂.leftTyped = decoOf r₂.rightTyped ∧
      decoOf s₁.rightTyped = decoOf s₂.rightTyped :=
  let j := D hΓ r₁.adj r₂.adj r₁.adjLeaf r₂.adjLeaf r₁.adjCoherent r₂.adjCoherent hsrc
    r₁.step r₂.step r₁.interface r₂.interface
  ⟨j.centre,
    ⟨j.dAdj, j.leftAdj, j.left, j.leftAdjLeaf, j.leftAdjCoherent, j.leftAdjInterface⟩,
    ⟨j.eAdj, j.rightAdj, j.right, j.rightAdjLeaf, j.rightAdjCoherent, j.rightAdjInterface⟩,
    j.leftSource, j.rightSource, j.target⟩

/-- Strip, recursion on the original star's tail. -/
def stripRK (L : LeafIface E n PEq) (D : LeafPeakDiamondK L) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d T : Expr Nat} (r : RStepK L hΓ b d T) :
    {e : Expr Nat} → (t : RStarK L hΓ b e T) → t.Coherent →
      decoOf r.leftTyped = decoOf t.leftTyped →
      Σ' (f : Expr Nat) (s : RStarK L hΓ d f T) (u : RStepK L hΓ e f T),
        s.Coherent ∧
        decoOf s.leftTyped = decoOf r.rightTyped ∧
        decoOf u.leftTyped = decoOf t.rightTyped ∧
        decoOf s.rightTyped = decoOf u.rightTyped
  | _, .refl _ _ _, _, hsrc =>
      ⟨d, .refl d T r.rightTyped, r, True.intro, rfl, hsrc, rfl⟩
  | _, .tail q qs, hcoh, hsrc =>
      let j := rDiamondK L D hΓ r q hsrc
      let hnext : decoOf j.2.2.1.leftTyped = decoOf qs.leftTyped :=
        j.2.2.2.2.1.trans hcoh.1
      let rec_ := stripRK L D hΓ j.2.2.1 qs hcoh.2 hnext
      ⟨rec_.1, .tail j.2.1 rec_.2.1, rec_.2.2.1,
        ⟨j.2.2.2.2.2.trans rec_.2.2.2.2.1.symm, rec_.2.2.2.1⟩,
        j.2.2.2.1, rec_.2.2.2.2.2.1, rec_.2.2.2.2.2.2⟩

/-- Confluence of two coherent `RStarK`s with one source decoration. -/
def confluenceRK (L : LeafIface E n PEq) (D : LeafPeakDiamondK L) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {b d T : Expr Nat} :
    (s : RStarK L hΓ b d T) → {e : Expr Nat} → (t : RStarK L hΓ b e T) →
      s.Coherent → t.Coherent → decoOf s.leftTyped = decoOf t.leftTyped →
      Σ' (f : Expr Nat) (s' : RStarK L hΓ d f T) (t' : RStarK L hΓ e f T),
        s'.Coherent ∧ t'.Coherent ∧
        decoOf s'.leftTyped = decoOf s.rightTyped ∧
        decoOf t'.leftTyped = decoOf t.rightTyped ∧
        decoOf s'.rightTyped = decoOf t'.rightTyped
  | .refl _ _ _, e, t, _, ht, hsrc =>
      ⟨e, t, .refl e T t.rightTyped, ht, True.intro, hsrc.symm, rfl, rfl⟩
  | .tail p ps, _, t, hs, ht, hsrc =>
      let j := stripRK L D hΓ p t ht hsrc
      let hnext : decoOf ps.leftTyped = decoOf j.2.1.leftTyped :=
        hs.1.symm.trans j.2.2.2.2.1.symm
      let rec_ := confluenceRK L D hΓ ps j.2.1 hs.2 j.2.2.2.1 hnext
      ⟨rec_.1, rec_.2.1, .tail j.2.2.1 rec_.2.2.1,
        rec_.2.2.2.1,
        ⟨j.2.2.2.2.2.2.symm.trans rec_.2.2.2.2.2.2.1.symm, rec_.2.2.2.2.1⟩,
        rec_.2.2.2.2.2.1, j.2.2.2.2.2.1, rec_.2.2.2.2.2.2.2⟩

/-- Star confluence in the enlarged relation on coherent inputs sharing the source
    decoration (the repair to a common source typing is K-free machinery, `#7600`, and is
    not re-derived here). -/
def starConfluenceK_of_leafPeakDiamondK (L : LeafIface E n PEq) (D : LeafPeakDiamondK L)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b c T : Expr Nat}
    (s : CStarK E n PEq Γ a b T) (t : CStarK E n PEq Γ a c T)
    (hs : CoherentK L hΓ s) (ht : CoherentK L hΓ t)
    (hsrc : decoOf (s.leftTyped L hΓ) = decoOf (t.leftTyped L hΓ)) :
    Σ' (f : Expr Nat), CStarK E n PEq Γ b f T ×' CStarK E n PEq Γ c f T :=
  let j := confluenceRK L D hΓ (RStarK.ofCStarK s) (RStarK.ofCStarK t)
    (RStarK.ofCStarK_coherent s hs) (RStarK.ofCStarK_coherent t ht)
    (by rw [RStarK.ofCStarK_leftTyped, RStarK.ofCStarK_leftTyped]; exact hsrc)
  ⟨j.1, j.2.1.toCStarK, j.2.2.1.toCStarK⟩

/-! ### the positive control: #7606's peak joins in one K step -/

section Control

open StarStripUnitPeakAudit CertifiedKControlAudit
open CoherentCanonicalAudit (nativeLeafIface)

/-- The η step of the unit peak, in the enlarged relation. -/
def unitEtaStepK :
    CStepK trueEnvU 0 (Rcic.Declarative.ProofLeaf trueEnvU 0) [] unitExpanded unitPartialRec
      unitIndex :=
  CStepK.ofCStep unitEtaStep

/-- The λ/ι step of the unit peak, in the enlarged relation. -/
def unitLamStepK :
    CStepK trueEnvU 0 (Rcic.Declarative.ProofLeaf trueEnvU 0) [] unitExpanded unitContracted
      unitIndex :=
  CStepK.ofCStep unitLamStep

/-- The reflexive step at the computed λ. -/
def unitContractedRefl :
    CStepK trueEnvU 0 (Rcic.Declarative.ProofLeaf trueEnvU 0) [] unitContracted unitContracted
      unitIndex :=
  ⟨.refl [] unitContracted unitIndex (unitLamStepK.rightTyped (nativeLeafIface trueEnvU 0) .nil),
    .refl (.refl [] unitContracted unitIndex
      (unitLamStepK.rightTyped (nativeLeafIface trueEnvU 0) .nil))⟩

/-- The unit peak joins in the enlarged relation: no adjustment, the η-K node on the η
    side, reflexivity on the λ side; every equality definitional. -/
def unit_leafPeakJoinK :
    LeafPeakJoinK (nativeLeafIface trueEnvU 0) .nil unitEtaStepK unitLamStepK where
  centre := unitContracted
  dAdj := unitPartialRec
  eAdj := unitContracted
  leftAdj := .refl [] unitPartialRec unitIndex
    (unitEtaStepK.rightTyped (nativeLeafIface trueEnvU 0) .nil)
  rightAdj := .refl [] unitContracted unitIndex
    (unitLamStepK.rightTyped (nativeLeafIface trueEnvU 0) .nil)
  leftAdjLeaf := .refl
  rightAdjLeaf := .refl
  leftAdjCoherent := True.intro
  rightAdjCoherent := True.intro
  left := unitKEtaCStepK
  right := unitContractedRefl
  leftSource := rfl
  rightSource := rfl
  leftAdjInterface := by simp only [CStarK.rightTyped]; rfl
  rightAdjInterface := by simp only [CStarK.rightTyped]; rfl
  target := rfl

end Control

#print axioms CStarK.leftTyped
#print axioms CStarK.rightTyped
#print axioms CStarK.reindex
#print axioms CStarK.ofStep
#print axioms reindexK_left_deco
#print axioms reindexK_right_deco
#print axioms CoherentK
#print axioms coherentK_trans
#print axioms coherentK_reindex
#print axioms LeafStarK
#print axioms LeafPeakJoinK
#print axioms LeafPeakDiamondK
#print axioms RStepK
#print axioms RStepK.leftTyped
#print axioms RStepK.rightTyped
#print axioms RStepK.toCStarK
#print axioms RStepK.ofStep
#print axioms RStarK
#print axioms RStarK.leftTyped
#print axioms RStarK.rightTyped
#print axioms RStarK.Coherent
#print axioms RStarK.toCStarK
#print axioms RStarK.ofCStarK
#print axioms RStarK.ofCStarK_leftTyped
#print axioms RStarK.ofCStarK_rightTyped
#print axioms RStarK.ofCStarK_coherent
#print axioms rDiamondK
#print axioms stripRK
#print axioms confluenceRK
#print axioms starConfluenceK_of_leafPeakDiamondK
#print axioms unitEtaStepK
#print axioms unitLamStepK
#print axioms unitContractedRefl
#print axioms unit_leafPeakJoinK

end Rcic.Declarative.NativeValleys.LeafPeakKAudit

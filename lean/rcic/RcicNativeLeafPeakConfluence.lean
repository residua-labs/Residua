import rcic.RcicNativeLeafJoinL
import rcic.RcicNativePiInjConfluence

/-!
# RcicNativeLeafPeakConfluence — the consumer of the leaf-adjusted diamond

`RcicNativeLeafJoinL` names `CoherentDiamondAdj` (a peak joins after each reduct first
moves along a star of pure irrelevance steps) as the shape the η/leaf peak satisfies in
both orientations, and observes that strip cannot consume it.  This module gives the
consumer, and states the exact oracle it needs.

**The relation.**  `RStep L hΓ b d T` is "leaf-adjust, then step": a coherent star of pure
irrelevance steps `b ⇒* m` followed by one certified step `m ⇒ d`, with the decoration
interface between them.  `RStar` is its star with the adjacent-interface coherence.  Every
coherent `CStar` is an `RStar` with empty adjustments (`RStar.ofCStar`) and every `RStar`
flattens to a `CStar` (`RStar.toCStar`), so confluence of `RStar` is confluence of `CStar`.

**The oracle.**  Two `RStep`s out of one `b` have sources `m₁`, `m₂` joined by a PEAK of
leaf stars `m₁ ⇐* b ⇒* m₂`, not a common source.  The oracle `LeafPeakDiamond` therefore
takes such a peak (coherent, decoration-sharing at `b`) and two steps out of its feet, and
returns a `LeafAdjJoin` of the two steps: FORWARD leaf adjustments out of the reducts, one
step each, the equalities as before.  At the trivial peak it is exactly
`CoherentDiamondAdj` (`coherentDiamondAdj_of_leafPeakDiamond`); the consumer never reverses
a leaf star (reversal would need let-value context transport), the oracle's rows do.

**The consumer.**  `rDiamond` is the diamond of `RStep` from the oracle; `stripR` and
`confluenceR` are the textbook recursions on the original `RStar` (the generated leg in
the other argument, as in `stripOf` / `confluenceOf`), carrying the four decoration
equalities; `starConfluence_of_leafPeakDiamond` repairs two arbitrary `CStar`s to a common
source decoration (`coherentStarOf_typing`), runs `confluenceR`, and flattens: this is
`StepTransferProducerAudit.StarConfluence`.  Hence `piInj_of_leafPeakDiamond`: Π-injectivity
from the leaf-peak diamond, `SortRetype` and `ZeroSortCoherence`, with no `CDiamond`.

`etaLeaf_leafPeakJoin` is the η/leaf peak at a NONTRIVIAL leaf peak: the leaf step itself
as the left foot (its reduct unstepped), the η step at the right foot; it joins with the
reverse leaf as the forward adjustment.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.LeafPeakAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

open DecoStarAudit (Coherent)
open LeafJoinAudit (LeafStar PureLeaf LeafAdjJoin CoherentDiamondAdj)
open StepTransferProducerAudit (StarConfluence)

/-! ### the oracle -/

/-- The join of two certified steps out of the two FEET of a leaf peak: forward leaf
    adjustments of the reducts, one certified step each, the equalities of `LeafAdjJoin`
    read at the adjusted sources.  `LeafAdjJoin` is the instance `m₁ = m₂`. -/
structure LeafPeakJoin (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {m₁ m₂ d e T : Expr Nat}
    (p : CStep E n PEq Γ m₁ d T) (q : CStep E n PEq Γ m₂ e T) where
  centre : Expr Nat
  dAdj : Expr Nat
  eAdj : Expr Nat
  leftAdj : CStar E n PEq Γ d dAdj T
  rightAdj : CStar E n PEq Γ e eAdj T
  leftAdjLeaf : LeafStar leftAdj
  rightAdjLeaf : LeafStar rightAdj
  leftAdjCoherent : Coherent L hΓ leftAdj
  rightAdjCoherent : Coherent L hΓ rightAdj
  left : CStep E n PEq Γ dAdj centre T
  right : CStep E n PEq Γ eAdj centre T
  leftSource : decoOf (leftAdj.leftTyped L hΓ) = decoOf (p.rightTyped L hΓ)
  rightSource : decoOf (rightAdj.leftTyped L hΓ) = decoOf (q.rightTyped L hΓ)
  leftAdjInterface : decoOf leftAdj.rightTyped = decoOf (left.leftTyped L hΓ)
  rightAdjInterface : decoOf rightAdj.rightTyped = decoOf (right.leftTyped L hΓ)
  target : decoOf (left.rightTyped L hΓ) = decoOf (right.rightTyped L hΓ)

/-- The leaf-peak diamond: a coherent peak of pure irrelevance stars `m₁ ⇐* b ⇒* m₂`,
    sharing the decoration of `b`, and two certified steps out of its feet, join after
    forward leaf adjustment of the reducts.  The exact remaining statement for the leaf
    rows. -/
def LeafPeakDiamond (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b m₁ m₂ d e T : Expr Nat}
    (l₁ : CStar E n PEq Γ b m₁ T) (l₂ : CStar E n PEq Γ b m₂ T),
    LeafStar l₁ → LeafStar l₂ → Coherent L hΓ l₁ → Coherent L hΓ l₂ →
    decoOf (l₁.leftTyped L hΓ) = decoOf (l₂.leftTyped L hΓ) →
    (p : CStep E n PEq Γ m₁ d T) → (q : CStep E n PEq Γ m₂ e T) →
    decoOf l₁.rightTyped = decoOf (p.leftTyped L hΓ) →
    decoOf l₂.rightTyped = decoOf (q.leftTyped L hΓ) →
    LeafPeakJoin L hΓ p q

/-- At the trivial peak the oracle is `CoherentDiamondAdj`. -/
def coherentDiamondAdj_of_leafPeakDiamond (L : LeafIface E n PEq)
    (D : LeafPeakDiamond L) : CoherentDiamondAdj L :=
  fun {Γ} hΓ {b _ _ T} p q hd =>
    let j := D hΓ (.refl Γ b T (p.leftTyped L hΓ)) (.refl Γ b T (q.leftTyped L hΓ))
      .refl .refl True.intro True.intro hd p q (by simp only [CStar.rightTyped])
      (by simp only [CStar.rightTyped])
    { centre := j.centre, dAdj := j.dAdj, eAdj := j.eAdj, leftAdj := j.leftAdj,
      rightAdj := j.rightAdj, leftAdjLeaf := j.leftAdjLeaf, rightAdjLeaf := j.rightAdjLeaf,
      leftAdjCoherent := j.leftAdjCoherent, rightAdjCoherent := j.rightAdjCoherent,
      left := j.left, right := j.right, leftSource := j.leftSource,
      rightSource := j.rightSource, leftAdjInterface := j.leftAdjInterface,
      rightAdjInterface := j.rightAdjInterface, target := j.target }

/-! ### adjust-then-step -/

/-- A coherent star of pure irrelevance steps followed by one certified step, with the
    decoration interface between them. -/
structure RStep (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (b d T : Expr Nat) where
  mid : Expr Nat
  adj : CStar E n PEq Γ b mid T
  step : CStep E n PEq Γ mid d T
  adjLeaf : LeafStar adj
  adjCoherent : Coherent L hΓ adj
  interface : decoOf adj.rightTyped = decoOf (step.leftTyped L hΓ)

namespace RStep

variable {L : LeafIface E n PEq} {Γ : LCtx} {hΓ : CtxWfT E n Γ}

/-- Source typing: the adjustment's. -/
def leftTyped {b d T : Expr Nat} (r : RStep L hΓ b d T) : HasTyT E n Γ b T :=
  r.adj.leftTyped L hΓ

/-- Target typing: the step's. -/
def rightTyped {b d T : Expr Nat} (r : RStep L hΓ b d T) : HasTyT E n Γ d T :=
  r.step.rightTyped L hΓ

/-- Flatten: the adjustment followed by the step. -/
def toCStar {b d T : Expr Nat} (r : RStep L hΓ b d T) : CStar E n PEq Γ b d T :=
  r.adj.trans (CStar.ofStep L hΓ r.step)

/-- A certified step with the empty adjustment. -/
def ofStep {b d T : Expr Nat} (s : CStep E n PEq Γ b d T) : RStep L hΓ b d T where
  mid := b
  adj := .refl Γ b T (s.leftTyped L hΓ)
  step := s
  adjLeaf := .refl
  adjCoherent := True.intro
  interface := by simp only [CStar.rightTyped]

theorem ofStep_leftTyped {b d T : Expr Nat} (s : CStep E n PEq Γ b d T) :
    (ofStep (L := L) (hΓ := hΓ) s).leftTyped = s.leftTyped L hΓ := rfl

theorem ofStep_rightTyped {b d T : Expr Nat} (s : CStep E n PEq Γ b d T) :
    (ofStep (L := L) (hΓ := hΓ) s).rightTyped = s.rightTyped L hΓ := rfl

end RStep

/-- Stars of adjust-then-step. -/
inductive RStar (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    Expr Nat → Expr Nat → Expr Nat → Type
  | refl (a T : Expr Nat) (h : HasTyT E n Γ a T) : RStar L hΓ a a T
  | tail {a b c T : Expr Nat} (r : RStep L hΓ a b T) (rs : RStar L hΓ b c T) : RStar L hΓ a c T

namespace RStar

variable {L : LeafIface E n PEq} {Γ : LCtx} {hΓ : CtxWfT E n Γ}

/-- Source typing. -/
def leftTyped : {a c T : Expr Nat} → RStar L hΓ a c T → HasTyT E n Γ a T
  | _, _, _, .refl _ _ h => h
  | _, _, _, .tail r _ => r.leftTyped

/-- Target typing. -/
def rightTyped : {a c T : Expr Nat} → RStar L hΓ a c T → HasTyT E n Γ c T
  | _, _, _, .refl _ _ h => h
  | _, _, _, .tail _ rs => rs.rightTyped

/-- Adjacent interfaces agree; the final typing participates in the last interface. -/
def Coherent : {a c T : Expr Nat} → RStar L hΓ a c T → Prop
  | _, _, _, .refl .. => True
  | _, _, _, .tail r rs => decoOf r.rightTyped = decoOf rs.leftTyped ∧ Coherent rs

/-- Flatten to a certified star. -/
def toCStar : {a c T : Expr Nat} → RStar L hΓ a c T → CStar E n PEq Γ a c T
  | _, _, _, .refl a T h => .refl Γ a T h
  | _, _, _, .tail r rs => r.toCStar.trans rs.toCStar

/-- A certified star as a star of adjust-then-steps with empty adjustments. -/
def ofCStar : {a c T : Expr Nat} → CStar E n PEq Γ a c T → RStar L hΓ a c T
  | _, _, _, .refl _ a T h => .refl a T h
  | _, _, _, .tail s ss => .tail (RStep.ofStep s) (ofCStar ss)

theorem ofCStar_leftTyped : {a c T : Expr Nat} → (s : CStar E n PEq Γ a c T) →
    (ofCStar (L := L) (hΓ := hΓ) s).leftTyped = s.leftTyped L hΓ
  | _, _, _, .refl .. => rfl
  | _, _, _, .tail _ _ => rfl

theorem ofCStar_rightTyped : {a c T : Expr Nat} → (s : CStar E n PEq Γ a c T) →
    (ofCStar (L := L) (hΓ := hΓ) s).rightTyped = s.rightTyped
  | _, _, _, .refl .. => by simp only [ofCStar, rightTyped, CStar.rightTyped]
  | _, _, _, .tail _ ss => by
      simp only [ofCStar, rightTyped, CStar.rightTyped]
      exact ofCStar_rightTyped ss

/-- Coherence transfers from the certified star. -/
theorem ofCStar_coherent : {a c T : Expr Nat} → (s : CStar E n PEq Γ a c T) →
    DecoStarAudit.Coherent L hΓ s → (ofCStar (L := L) (hΓ := hΓ) s).Coherent
  | _, _, _, .refl .., _ => True.intro
  | _, _, _, .tail _ ss, h =>
      ⟨by rw [ofCStar_leftTyped ss]; exact h.1, ofCStar_coherent ss h.2⟩

end RStar

/-! ### the diamond, strip and confluence of adjust-then-step -/

/-- The diamond of `RStep` from the oracle: the two adjustments form the leaf peak. -/
def rDiamond (L : LeafIface E n PEq) (D : LeafPeakDiamond L) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d e T : Expr Nat} (r₁ : RStep L hΓ b d T) (r₂ : RStep L hΓ b e T)
    (hsrc : decoOf r₁.leftTyped = decoOf r₂.leftTyped) :
    Σ' (f : Expr Nat) (s₁ : RStep L hΓ d f T) (s₂ : RStep L hΓ e f T),
      decoOf s₁.leftTyped = decoOf r₁.rightTyped ∧
      decoOf s₂.leftTyped = decoOf r₂.rightTyped ∧
      decoOf s₁.rightTyped = decoOf s₂.rightTyped :=
  let j := D hΓ r₁.adj r₂.adj r₁.adjLeaf r₂.adjLeaf r₁.adjCoherent r₂.adjCoherent hsrc
    r₁.step r₂.step r₁.interface r₂.interface
  ⟨j.centre,
    ⟨j.dAdj, j.leftAdj, j.left, j.leftAdjLeaf, j.leftAdjCoherent, j.leftAdjInterface⟩,
    ⟨j.eAdj, j.rightAdj, j.right, j.rightAdjLeaf, j.rightAdjCoherent, j.rightAdjInterface⟩,
    j.leftSource, j.rightSource, j.target⟩

/-- Strip: an adjust-then-step against a coherent `RStar`.  The recursion is on the
    original star's tail; the generated single `RStep` is the other argument. -/
def stripR (L : LeafIface E n PEq) (D : LeafPeakDiamond L) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d T : Expr Nat} (r : RStep L hΓ b d T) :
    {e : Expr Nat} → (t : RStar L hΓ b e T) → t.Coherent →
      decoOf r.leftTyped = decoOf t.leftTyped →
      Σ' (f : Expr Nat) (s : RStar L hΓ d f T) (u : RStep L hΓ e f T),
        s.Coherent ∧
        decoOf s.leftTyped = decoOf r.rightTyped ∧
        decoOf u.leftTyped = decoOf t.rightTyped ∧
        decoOf s.rightTyped = decoOf u.rightTyped
  | _, .refl _ _ _, _, hsrc =>
      ⟨d, .refl d T r.rightTyped, r, True.intro, rfl, hsrc, rfl⟩
  | _, .tail q qs, hcoh, hsrc =>
      let j := rDiamond L D hΓ r q hsrc
      let hnext : decoOf j.2.2.1.leftTyped = decoOf qs.leftTyped :=
        j.2.2.2.2.1.trans hcoh.1
      let rec_ := stripR L D hΓ j.2.2.1 qs hcoh.2 hnext
      ⟨rec_.1, .tail j.2.1 rec_.2.1, rec_.2.2.1,
        ⟨j.2.2.2.2.2.trans rec_.2.2.2.2.1.symm, rec_.2.2.2.1⟩,
        j.2.2.2.1,
        rec_.2.2.2.2.2.1,
        rec_.2.2.2.2.2.2⟩

/-- Confluence of two coherent `RStar`s with one source decoration.  The recursion is on
    the original first star's tail. -/
def confluenceR (L : LeafIface E n PEq) (D : LeafPeakDiamond L) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {b d T : Expr Nat} :
    (s : RStar L hΓ b d T) → {e : Expr Nat} → (t : RStar L hΓ b e T) →
      s.Coherent → t.Coherent → decoOf s.leftTyped = decoOf t.leftTyped →
      Σ' (f : Expr Nat) (s' : RStar L hΓ d f T) (t' : RStar L hΓ e f T),
        s'.Coherent ∧ t'.Coherent ∧
        decoOf s'.leftTyped = decoOf s.rightTyped ∧
        decoOf t'.leftTyped = decoOf t.rightTyped ∧
        decoOf s'.rightTyped = decoOf t'.rightTyped
  | .refl _ _ _, e, t, _, ht, hsrc =>
      ⟨e, t, .refl e T t.rightTyped, ht, True.intro, hsrc.symm, rfl, rfl⟩
  | .tail p ps, _, t, hs, ht, hsrc =>
      let j := stripR L D hΓ p t ht hsrc
      let hnext : decoOf ps.leftTyped = decoOf j.2.1.leftTyped :=
        hs.1.symm.trans j.2.2.2.2.1.symm
      let rec_ := confluenceR L D hΓ ps j.2.1 hs.2 j.2.2.2.1 hnext
      ⟨rec_.1, rec_.2.1, .tail j.2.2.1 rec_.2.2.1,
        rec_.2.2.2.1,
        ⟨j.2.2.2.2.2.2.symm.trans rec_.2.2.2.2.2.2.1.symm, rec_.2.2.2.2.1⟩,
        rec_.2.2.2.2.2.1,
        j.2.2.2.2.2.1,
        rec_.2.2.2.2.2.2.2⟩

/-- Star confluence from the leaf-peak diamond: repair both input stars to the first
    star's actual source typing (`coherentStarOf_typing`), lift to `RStar`, run
    `confluenceR`, flatten. -/
def starConfluence_of_leafPeakDiamond (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : LeafPeakDiamond L) : StarConfluence E n PEq :=
  fun {Γ} hΓ {a _ _ T} s t =>
    let h := s.leftTyped L hΓ
    let left := StepTransferAudit.coherentStarOf_typing hW L hΓ s h
    let right := StepTransferAudit.coherentStarOf_typing hW L hΓ t h
    let rs : RStar L hΓ a _ T := RStar.ofCStar left.1
    let rt : RStar L hΓ a _ T := RStar.ofCStar right.1
    let j := confluenceR L D hΓ rs rt (RStar.ofCStar_coherent left.1 left.2.1)
      (RStar.ofCStar_coherent right.1 right.2.1)
      (by rw [RStar.ofCStar_leftTyped, RStar.ofCStar_leftTyped]; exact left.2.2.trans right.2.2.symm)
    ⟨j.1, j.2.1.toCStar, j.2.2.1.toCStar⟩

/-- Π-injectivity from the leaf-peak diamond, `SortRetype` and `ZeroSortCoherence`; no
    `CDiamond`, no `CoherentDiamond`. -/
def piInj_of_leafPeakDiamond (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : LeafPeakDiamond L) (sr : SortRetype E n)
    (zsc : HostPropAudit.ZeroSortCoherence E n) : PiInj E n :=
  PiInjConfluenceAudit.piInj_of_confluence_sortRetype hW L
    (starConfluence_of_leafPeakDiamond hW L D) sr zsc

/-- Native valleys for every native conversion from the leaf-peak diamond. -/
def valleyOf_leafPeakDiamond (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : LeafPeakDiamond L) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T : Expr Nat}
    (c : ConvT E n Γ a b T) : CValley E n PEq Γ a b T :=
  StepTransferProducerAudit.valleyOf_confluence hW L (starConfluence_of_leafPeakDiamond hW L D) hΓ c

/-! ### the η/leaf peak at a nontrivial leaf peak -/

/-- The forward leaf step `b ⇒ d` of the η/leaf fixture is a pure irrelevance step. -/
theorem etaLeafLamStep_pureLeaf (L : LeafIface E n PEq) : PureLeaf (etaLeafLamStep L) :=
  .lam (.app (.app .refl .peq) .refl)

/-- The reflexive step at the leaf step's reduct `d`. -/
def etaLeafDRefl :
    CStep E n PEq etaLeafCtx (.lam etaLeafP etaLeafBody') (.lam etaLeafP etaLeafBody')
      (.pi etaLeafP (.sort .zero)) :=
  ⟨.refl etaLeafCtx (.lam etaLeafP etaLeafBody') _ etaLeafD_ty,
    .refl (.refl etaLeafCtx (.lam etaLeafP etaLeafBody') _ etaLeafD_ty)⟩

/-- The η/leaf peak as a leaf-peak instance: the left foot is the leaf step's reduct `d`
    (unstepped), the right foot is `b` itself with the η step.  The join adjusts `d` back
    to `b` by the reverse leaf and contracts by η; the η side is reflexive. -/
def etaLeaf_leafPeakJoin (L : LeafIface E n PEq) :
    LeafPeakJoin L etaLeafCtx_wf etaLeafDRefl LeafJoinAudit.etaLeafEtaCStep where
  centre := etaLeafF
  dAdj := .lam etaLeafP etaLeafBody
  eAdj := etaLeafF
  leftAdj := .tail (LeafJoinAudit.etaLeafRevStep L) (.refl etaLeafCtx _ _ etaLeafB_ty)
  rightAdj := .refl etaLeafCtx etaLeafF _ etaLeafF_ty
  leftAdjLeaf := .tail (LeafJoinAudit.etaLeafRevLamStep_pureLeaf L) .refl
  rightAdjLeaf := .refl
  leftAdjCoherent := by
    simp only [Coherent, LeafJoinAudit.etaLeafRevStep, CStep.rightTyped, CStar.leftTyped,
      parRedT_hasTy_right, parRedT_typed, LeafJoinAudit.etaLeafRevLamStep, and_self]
  rightAdjCoherent := True.intro
  left := LeafJoinAudit.etaLeafEtaCStep
  right := LeafJoinAudit.etaLeafFRefl
  leftSource := by
    simp only [LeafJoinAudit.etaLeafRevStep, etaLeafDRefl, CStep.rightTyped, CStep.leftTyped,
      CStar.leftTyped, parRedT_hasTy_right, parRedT_hasTy_left, parRedT_typed,
      hasTyT_of_tyConvT, LeafJoinAudit.etaLeafRevLamStep, LeafJoinAudit.etaLeafRevBodyStep,
      LeafJoinAudit.etaLeafRevInnerStep, etaLeafD_ty, etaLeafBody'_ty, etaLeafXY_ty,
      etaLeafX_var₁, etaLeafY_var₁, decoOf,
      deco_subsingleton_bvar rfl (decoOf (L.typed (LeafJoinAudit.etaLeafRevLeaf L)).1) (.bvar 0)]
  rightSource := by
    simp only [LeafJoinAudit.etaLeafFRefl, CStep.rightTyped, CStep.leftTyped, CStar.leftTyped,
      parRedT_hasTy_right, parRedT_hasTy_left, parRedT_typed, etaLeafEtaStep]
  leftAdjInterface := by
    simp only [LeafJoinAudit.etaLeafEtaCStep, CStar.rightTyped, CStep.leftTyped,
      parRedT_hasTy_left, parRedT_typed, etaLeafEtaStep]
  rightAdjInterface := by
    simp only [LeafJoinAudit.etaLeafFRefl, CStar.rightTyped, CStep.leftTyped,
      parRedT_hasTy_left, parRedT_typed]
  target := by
    simp only [LeafJoinAudit.etaLeafEtaCStep, LeafJoinAudit.etaLeafFRefl, CStep.rightTyped,
      parRedT_hasTy_right, parRedT_typed, etaLeafEtaStep]

#print axioms LeafPeakJoin
#print axioms LeafPeakDiamond
#print axioms coherentDiamondAdj_of_leafPeakDiamond
#print axioms RStep
#print axioms RStep.leftTyped
#print axioms RStep.rightTyped
#print axioms RStep.toCStar
#print axioms RStep.ofStep
#print axioms RStep.ofStep_leftTyped
#print axioms RStep.ofStep_rightTyped
#print axioms RStar
#print axioms RStar.leftTyped
#print axioms RStar.rightTyped
#print axioms RStar.Coherent
#print axioms RStar.toCStar
#print axioms RStar.ofCStar
#print axioms RStar.ofCStar_leftTyped
#print axioms RStar.ofCStar_rightTyped
#print axioms RStar.ofCStar_coherent
#print axioms rDiamond
#print axioms stripR
#print axioms confluenceR
#print axioms starConfluence_of_leafPeakDiamond
#print axioms piInj_of_leafPeakDiamond
#print axioms valleyOf_leafPeakDiamond
#print axioms etaLeafLamStep_pureLeaf
#print axioms etaLeafDRefl
#print axioms etaLeaf_leafPeakJoin

end Rcic.Declarative.NativeValleys.LeafPeakAudit

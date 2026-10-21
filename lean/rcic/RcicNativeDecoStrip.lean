import rcic.RcicNativeValleyDeco

/-!
# RcicNativeDecoStrip — conditional strip and confluence with decoration interfaces

This file adds a coherence predicate to the existing `CStar`; the steps,
certificates, endpoint typings, and star constructors are unchanged.  The
predicate compares the actual target typing of each step with the actual
source typing of its remaining star.

`CoherentDiamond` is an explicit hypothesis, not a constructed theorem.  It
requires equal input source decorations and returns both joining-leg source
interfaces as well as equal target decorations.  `stripOf` and `confluenceOf`
construct the corresponding coherent joins from precisely that hypothesis.

The strip recursion consumes the original second star's tail.  The confluence
recursion consumes the original first star's tail.  Generated joining steps
and stars occur only in other arguments; no claim compares their `sizeOf`
with the input derivations.  No `Uniq`, `Retype`, Π-injectivity, or decoration
transfer hypothesis is used.

Dependency pin: `0849f7ec411705d9657d52c4c91bd97f2e1ab624`.
`closure_claim = 0`: this is conditional algebra, not a construction of CR_D.
-/

namespace Rcic.Declarative.NativeValleys.DecoStarAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- Every adjacent pair in an existing certified star agrees on the
decoration of its shared term.  The final reflexive typing participates in
the last interface, so it also fixes the star's target decoration. -/
def Coherent (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {a b T : Expr Nat} → CStar E n PEq Γ a b T → Prop
  | _, _, _, .refl .. => True
  | _, _, _, .tail s ss =>
      decoOf (s.rightTyped L hΓ) = decoOf (ss.leftTyped L hΓ) ∧
        Coherent L hΓ ss

/-- A one-step join with the two source interfaces needed by strip, and
agreement at its common target.  It bundles existing `CStep`s. -/
structure StepJoin (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d e T : Expr Nat}
    (p : CStep E n PEq Γ b d T) (q : CStep E n PEq Γ b e T) where
  centre : Expr Nat
  left : CStep E n PEq Γ d centre T
  right : CStep E n PEq Γ e centre T
  leftSource : decoOf (left.leftTyped L hΓ) = decoOf (p.rightTyped L hΓ)
  rightSource : decoOf (right.leftTyped L hΓ) = decoOf (q.rightTyped L hΓ)
  target : decoOf (left.rightTyped L hΓ) = decoOf (right.rightTyped L hΓ)

/-- The exact coherent decorated diamond premise consumed below.  Stating
this type does not construct an inhabitant or discharge any row. -/
def CoherentDiamond (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx}, (hΓ : CtxWfT E n Γ) → ∀ {b d e T : Expr Nat}
    (p : CStep E n PEq Γ b d T) (q : CStep E n PEq Γ b e T),
      decoOf (p.leftTyped L hΓ) = decoOf (q.leftTyped L hΓ) → StepJoin L hΓ p q

/-- Strip's result: a coherent star on the step side and one certified step
on the star side, with both source interfaces and equal target decorations. -/
structure StripJoin (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d e T : Expr Nat}
    (p : CStep E n PEq Γ b d T) (s : CStar E n PEq Γ b e T) where
  centre : Expr Nat
  left : CStar E n PEq Γ d centre T
  right : CStep E n PEq Γ e centre T
  leftCoherent : Coherent L hΓ left
  leftSource : decoOf (left.leftTyped L hΓ) = decoOf (p.rightTyped L hΓ)
  rightSource : decoOf (right.leftTyped L hΓ) = decoOf s.rightTyped
  target : decoOf left.rightTyped = decoOf (right.rightTyped L hΓ)

/-- A coherent join of two existing certified stars. -/
structure StarJoin (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d e T : Expr Nat}
    (s : CStar E n PEq Γ b d T) (t : CStar E n PEq Γ b e T) where
  centre : Expr Nat
  left : CStar E n PEq Γ d centre T
  right : CStar E n PEq Γ e centre T
  leftCoherent : Coherent L hΓ left
  rightCoherent : Coherent L hΓ right
  leftSource : decoOf (left.leftTyped L hΓ) = decoOf s.rightTyped
  rightSource : decoOf (right.leftTyped L hΓ) = decoOf t.rightTyped
  target : decoOf left.rightTyped = decoOf right.rightTyped

/-- Conditional strip on the original star.  In the tail case the recursive
call uses `qs`, a literal substar of the input; the generated joining step is
the other argument.  Each equality used at this call is displayed below. -/
def stripOf (L : LeafIface E n PEq) (D : CoherentDiamond L)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d T : Expr Nat}
    (p : CStep E n PEq Γ b d T) :
    {e : Expr Nat} → (s : CStar E n PEq Γ b e T) → Coherent L hΓ s →
      decoOf (p.leftTyped L hΓ) = decoOf (s.leftTyped L hΓ) →
      StripJoin L hΓ p s
  | _, .refl _ _ _ _, _, hsource =>
      { centre := d
        left := .refl Γ d T (p.rightTyped L hΓ)
        right := p
        leftCoherent := True.intro
        leftSource := rfl
        rightSource := by
          simpa only [CStar.leftTyped, CStar.rightTyped] using hsource
        target := by simp only [CStar.rightTyped] }
  | _, .tail q qs, hcoh, hsource => by
      let j := D hΓ p q hsource
      have hnext : decoOf (j.right.leftTyped L hΓ) = decoOf (qs.leftTyped L hΓ) :=
        j.rightSource.trans hcoh.1
      let r := stripOf L D hΓ j.right qs hcoh.2 hnext
      exact
        { centre := r.centre
          left := .tail j.left r.left
          right := r.right
          leftCoherent := ⟨j.target.trans r.leftSource.symm, r.leftCoherent⟩
          leftSource := j.leftSource
          rightSource := by simpa only [CStar.rightTyped] using r.rightSource
          target := by simpa only [CStar.rightTyped] using r.target }

/-- Conditional confluence on the original first star.  Strip generates the
other recursive argument; `ps`, the first recursive argument, is the original
input's literal tail.  Both output stars retain their source interfaces. -/
def confluenceOf (L : LeafIface E n PEq) (D : CoherentDiamond L)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d T : Expr Nat} :
    (s : CStar E n PEq Γ b d T) → {e : Expr Nat} →
      (t : CStar E n PEq Γ b e T) → Coherent L hΓ s → Coherent L hΓ t →
      decoOf (s.leftTyped L hΓ) = decoOf (t.leftTyped L hΓ) →
      StarJoin L hΓ s t
  | .refl _ _ _ _, e, t, _, ht, hsource =>
      { centre := e
        left := t
        right := .refl Γ e T t.rightTyped
        leftCoherent := ht
        rightCoherent := True.intro
        leftSource := by
          simpa only [CStar.leftTyped, CStar.rightTyped] using hsource.symm
        rightSource := rfl
        target := by simp only [CStar.rightTyped] }
  | .tail p ps, _, t, hs, ht, hsource => by
      let j := stripOf L D hΓ p t ht hsource
      have hnext : decoOf (ps.leftTyped L hΓ) = decoOf (j.left.leftTyped L hΓ) :=
        hs.1.symm.trans j.leftSource.symm
      let r := confluenceOf L D hΓ ps j.left hs.2 j.leftCoherent hnext
      exact
        { centre := r.centre
          left := r.left
          right := .tail j.right r.right
          leftCoherent := r.leftCoherent
          rightCoherent := ⟨j.target.symm.trans r.rightSource.symm, r.rightCoherent⟩
          leftSource := by simpa only [CStar.rightTyped] using r.leftSource
          rightSource := j.rightSource
          target := by simpa only [CStar.rightTyped] using r.target }

#print axioms Coherent
#print axioms CoherentDiamond
#print axioms stripOf
#print axioms confluenceOf

end Rcic.Declarative.NativeValleys.DecoStarAudit

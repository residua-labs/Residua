import rcic.RcicNativeStepTransferProducer

/-!
# An asymmetric coherent local premise with a descending consumer

`AsymmetricDiamond` relaxes the left joining leg of `CoherentDiamond` to
an arbitrary coherent certified star. Its right joining leg remains a
certified step. Both source decoration interfaces and the common target
decoration are retained. This is a local two-step-peak premise, not a
star-confluence oracle.

`ShortRightDiamond` states the same usable boundary entirely with the
existing `CStar`: both joining legs are coherent stars with all three
decoration equalities, and the right star contains at most one step.
`stepOf_short` constructs the corresponding right `CStep`. A reflexive
star becomes a certified reflexive step; a one-step star uses its head,
with its final coherence equality supplying the target interface.

The strip recursion decreases `length` of the original second star.
The confluence recursion decreases `length` of the original first star.
Generated left joining stars are concatenated or passed as other
arguments, never used to justify descent. This proof therefore consumes
the asymmetric premise without comparing generated and input derivation
sizes. No environment termination or ordinary `CDiamond` is assumed.

Unrestricted coherent star legs, even with these same three endpoint
equalities, give only local confluence. They do not supply the bounded
right leg used by this recursion and do not generally imply confluence.
This module claims a precise structural-recursion-compatible weakening,
not a logically weakest hypothesis among all possible confluence proofs.

The quantifier over `(p, q)` is ordered. A concrete row with a long left
join and a short right join is covered in that orientation. A row with
only a known long right join does not supply this contract, nor does a
proof that one unspecified side can be short. In particular, an eta row
whose lambda side takes several steps is covered only when that side is
the left leg; its reversed ordered row remains a separate obligation.
There is no claimed construction of either eta orientation here.

All stars, steps, valleys, decorations, context packages, and the final
native-valley producer are the existing ones. The only premises added
below are the explicitly displayed local-peak contracts. None of them is
constructed by defining its type. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.CoherentConsumerAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

open DecoStarAudit (Coherent StripJoin StarJoin)
open StepTransferRowsAudit (coherent_trans)

/-- Number of certified step nodes in an existing star. Only the original
input star measured here is a recursive subject of either consumer. -/
def length {Γ : LCtx} : {a b T : Expr Nat} → CStar E n PEq Γ a b T → Nat
  | _, _, _, .refl .. => 0
  | _, _, _, .tail _ ss => Nat.succ (length ss)

/-- The literal tail is smaller by exactly one step node. -/
theorem length_tail {Γ : LCtx} {a b c T : Expr Nat}
    (p : CStep E n PEq Γ a b T) (ss : CStar E n PEq Γ b c T) :
    length (.tail p ss) = Nat.succ (length ss) := rfl

/-- An exact syntactic bound on the existing right joining star. -/
def AtMostOne {Γ : LCtx} : {a b T : Expr Nat} → CStar E n PEq Γ a b T → Prop
  | _, _, _, .refl .. => True
  | _, _, _, .tail _ (.refl ..) => True
  | _, _, _, .tail _ (.tail ..) => False

/-- Normalize a coherent star containing at most one step to an existing
certified step, preserving its actual two endpoint decorations. -/
def stepOf_short (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {a b T : Expr Nat} → (s : CStar E n PEq Γ a b T) →
    AtMostOne s → Coherent L hΓ s →
      Σ' (p : CStep E n PEq Γ a b T),
        decoOf (p.leftTyped L hΓ) = decoOf (s.leftTyped L hΓ) ∧
        decoOf (p.rightTyped L hΓ) = decoOf s.rightTyped
  | _, _, _, .refl _ a T h, _, _ =>
      ⟨⟨.refl Γ a T h, .refl (.refl Γ a T h)⟩, rfl,
        by simp only [CStar.rightTyped, CStep.rightTyped, parRedT_hasTy_right, parRedT_typed]⟩
  | _, _, _, .tail p (.refl _ _ _ _), _, hs =>
      ⟨p, rfl, by simpa only [CStar.rightTyped, CStar.leftTyped] using hs.1⟩
  | _, _, _, .tail _ (.tail ..), hs, _ => False.elim hs

/-- The existing coherent `StarJoin`, specialized to the two one-step
input stars. This is an abbreviation, with no new structure or projections.
No consumer is claimed without the explicit right-leg bound below. -/
abbrev StarStepJoin (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b d e T : Expr Nat}
    (p : CStep E n PEq Γ b d T) (q : CStep E n PEq Γ b e T) : Type :=
  StarJoin L hΓ (CStar.ofStep L hΓ p) (CStar.ofStep L hΓ q)

/-- A fully explicit star-leg local premise. The left star is unrestricted;
the right star has at most one certified step. Defining this interface does
not construct its inhabitants or discharge any constructor row. -/
def ShortRightDiamond (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx}, (hΓ : CtxWfT E n Γ) → ∀ {b d e T : Expr Nat}
    (p : CStep E n PEq Γ b d T) (q : CStep E n PEq Γ b e T),
      decoOf (p.leftTyped L hΓ) = decoOf (q.leftTyped L hΓ) →
        Σ' (j : StarStepJoin L hΓ p q), AtMostOne j.right

/-- The existing `StripJoin`, specialized to a one-step second input star.
Its left leg has arbitrary finite length; its right leg is an existing
certified step, which may itself be reflexive. No structure is duplicated. -/
abbrev AsymmetricStepJoin (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {b d e T : Expr Nat}
    (p : CStep E n PEq Γ b d T) (q : CStep E n PEq Γ b e T) : Type :=
  StripJoin L hΓ p (CStar.ofStep L hΓ q)

/-- A local step/step peak contract, with all three required decoration
interfaces and an arbitrary coherent left joining star. -/
def AsymmetricDiamond (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx}, (hΓ : CtxWfT E n Γ) → ∀ {b d e T : Expr Nat}
    (p : CStep E n PEq Γ b d T) (q : CStep E n PEq Γ b e T),
      decoOf (p.leftTyped L hΓ) = decoOf (q.leftTyped L hΓ) →
        AsymmetricStepJoin L hΓ p q

/-- The star-leg formulation supplies the normalized local premise by an
actual construction on its bounded right star. -/
def asymmetricOf_shortRight (L : LeafIface E n PEq) (D : ShortRightDiamond L) :
    AsymmetricDiamond L := by
  intro Γ hΓ b d e T p q hs
  let j := D hΓ p q hs
  let r := stepOf_short L hΓ j.1.right j.2 j.1.rightCoherent
  exact
    { centre := j.1.centre
      left := j.1.left
      right := r.1
      leftCoherent := j.1.leftCoherent
      leftSource := by
        simpa only [CStar.ofStep, CStar.rightTyped, CStar.leftTyped] using j.1.leftSource
      rightSource := by
        simpa only [CStar.ofStep, CStar.rightTyped, CStar.leftTyped] using
          r.2.1.trans j.1.rightSource
      target := j.1.target.trans r.2.2.symm }

/-- Conversely, the normalized local premise supplies both star legs with
the exact right-leg bound. The two formulations have the same consumers. -/
def shortRightOf_asymmetric (L : LeafIface E n PEq) (D : AsymmetricDiamond L) :
    ShortRightDiamond L := by
  intro Γ hΓ b d e T p q hs
  let j := D hΓ p q hs
  exact
    ⟨{ centre := j.centre
       left := j.left
       right := CStar.ofStep L hΓ j.right
       leftCoherent := j.leftCoherent
       rightCoherent := ⟨rfl, True.intro⟩
       leftSource := by
         simpa only [CStar.ofStep, CStar.rightTyped, CStar.leftTyped] using j.leftSource
       rightSource := by
         simpa only [CStar.ofStep, CStar.rightTyped, CStar.leftTyped] using j.rightSource
       target := by
         simpa only [CStar.ofStep, CStar.rightTyped, CStar.leftTyped] using j.target },
      by simpa only [CStar.ofStep, AtMostOne] using True.intro⟩

/-- The previous coherent single-step diamond supplies this asymmetric
premise. No converse or unconditional local-peak construction is claimed. -/
def asymmetricOf_coherentDiamond (L : LeafIface E n PEq)
    (D : DecoStarAudit.CoherentDiamond L) : AsymmetricDiamond L := by
  intro Γ hΓ b d e T p q hs
  let j := D hΓ p q hs
  exact
    { centre := j.centre
      left := CStar.ofStep L hΓ j.left
      right := j.right
      leftCoherent := ⟨rfl, True.intro⟩
      leftSource := by
        simpa only [CStar.ofStep, CStar.rightTyped, CStar.leftTyped] using j.leftSource
      rightSource := by
        simpa only [CStar.ofStep, CStar.rightTyped, CStar.leftTyped] using j.rightSource
      target := by
        simpa only [CStar.ofStep, CStar.rightTyped, CStar.leftTyped] using j.target }

/-- Strip for the asymmetric local premise. The only recursive call takes
`qs`, the literal tail of the original second input. Concatenation accepts
the arbitrarily long generated left leg without any recursive call on it. -/
def stripOf_asymmetric (L : LeafIface E n PEq) (D : AsymmetricDiamond L)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {b d e T : Expr Nat} → (p : CStep E n PEq Γ b d T) →
    (s : CStar E n PEq Γ b e T) → Coherent L hΓ s →
      decoOf (p.leftTyped L hΓ) = decoOf (s.leftTyped L hΓ) →
        StripJoin L hΓ p s
  | _, d, _, T, p, .refl _ _ _ _, _, hsource =>
      { centre := d
        left := .refl Γ d T (p.rightTyped L hΓ)
        right := p
        leftCoherent := True.intro
        leftSource := rfl
        rightSource := by
          simpa only [CStar.leftTyped, CStar.rightTyped] using hsource
        target := by simp only [CStar.rightTyped] }
  | _, _, _, _, p, .tail q qs, hs, hsource => by
      let j := D hΓ p q hsource
      have hrsource : decoOf (j.right.leftTyped L hΓ) = decoOf (q.rightTyped L hΓ) := by
        simpa only [CStar.ofStep, CStar.rightTyped] using j.rightSource
      have hnext : decoOf (j.right.leftTyped L hΓ) = decoOf (qs.leftTyped L hΓ) :=
        hrsource.trans hs.1
      let r := stripOf_asymmetric L D hΓ j.right qs hs.2 hnext
      let joined := coherent_trans L hΓ j.left r.left
        j.leftCoherent r.leftCoherent (j.target.trans r.leftSource.symm)
      exact
        { centre := r.centre
          left := j.left.trans r.left
          right := r.right
          leftCoherent := joined.1
          leftSource := joined.2.1.trans j.leftSource
          rightSource := by simpa only [CStar.rightTyped] using r.rightSource
          target := joined.2.2.trans r.target }
termination_by b d e T p s _ _ => length s
decreasing_by all_goals (simp only [length]; omega)

/-- Confluence for the asymmetric local premise. The only recursive call
takes `ps`, the literal tail of the original first input. The star returned
by strip is the other argument and is not used to justify descent. -/
def confluenceOf_asymmetric (L : LeafIface E n PEq) (D : AsymmetricDiamond L)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {b d e T : Expr Nat} → (s : CStar E n PEq Γ b d T) →
    (t : CStar E n PEq Γ b e T) → Coherent L hΓ s → Coherent L hΓ t →
      decoOf (s.leftTyped L hΓ) = decoOf (t.leftTyped L hΓ) →
        StarJoin L hΓ s t
  | _, _, e, T, .refl _ _ _ _, t, _, ht, hsource =>
      { centre := e
        left := t
        right := .refl Γ e T t.rightTyped
        leftCoherent := ht
        rightCoherent := True.intro
        leftSource := by
          simpa only [CStar.leftTyped, CStar.rightTyped] using hsource.symm
        rightSource := rfl
        target := by simp only [CStar.rightTyped] }
  | _, _, _, _, .tail p ps, t, hs, ht, hsource => by
      let j := stripOf_asymmetric L D hΓ p t ht hsource
      have hnext : decoOf (ps.leftTyped L hΓ) = decoOf (j.left.leftTyped L hΓ) :=
        hs.1.symm.trans j.leftSource.symm
      let r := confluenceOf_asymmetric L D hΓ ps j.left hs.2 j.leftCoherent hnext
      exact
        { centre := r.centre
          left := r.left
          right := .tail j.right r.right
          leftCoherent := r.leftCoherent
          rightCoherent := ⟨j.target.symm.trans r.rightSource.symm, r.rightCoherent⟩
          leftSource := by simpa only [CStar.rightTyped] using r.leftSource
          rightSource := j.rightSource
          target := by simpa only [CStar.rightTyped] using r.target }
termination_by b d e T s t _ _ _ => length s
decreasing_by all_goals (simp only [length]; omega)

/-- The all-three-equalities star-leg premise directly feeds strip through
the constructed normalization of its at-most-one right joining star. -/
def stripOf_shortRight (L : LeafIface E n PEq) (D : ShortRightDiamond L)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d e T : Expr Nat}
    (p : CStep E n PEq Γ b d T) (s : CStar E n PEq Γ b e T)
    (hs : Coherent L hΓ s)
    (hsource : decoOf (p.leftTyped L hΓ) = decoOf (s.leftTyped L hΓ)) :
    StripJoin L hΓ p s :=
  stripOf_asymmetric L (asymmetricOf_shortRight L D) hΓ p s hs hsource

/-- The same explicit short-right premise directly feeds coherent-star
confluence; all recursion and interface proofs are above. -/
def confluenceOf_shortRight (L : LeafIface E n PEq) (D : ShortRightDiamond L)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d e T : Expr Nat}
    (s : CStar E n PEq Γ b d T) (t : CStar E n PEq Γ b e T)
    (hs : Coherent L hΓ s) (ht : Coherent L hΓ t)
    (hsource : decoOf (s.leftTyped L hΓ) = decoOf (t.leftTyped L hΓ)) :
    StarJoin L hΓ s t :=
  confluenceOf_asymmetric L (asymmetricOf_shortRight L D) hΓ s t hs ht hsource

/-- The published source repair gives actual coherent input stars at one
source decoration. The asymmetric consumer therefore constructs ordinary
fixed-index star confluence from the displayed local premise. -/
def starConfluenceOf_asymmetric (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : AsymmetricDiamond L) : StepTransferProducerAudit.StarConfluence E n PEq := by
  intro Γ hΓ a b c T s t
  let h := s.leftTyped L hΓ
  let left := StepTransferAudit.coherentStarOf_typing hW L hΓ s h
  let right := StepTransferAudit.coherentStarOf_typing hW L hΓ t h
  let j := confluenceOf_asymmetric L D hΓ left.1 right.1
    left.2.1 right.2.1 (left.2.2.trans right.2.2.symm)
  exact ⟨j.centre, j.left, j.right⟩

/-- The concrete native producer, including its existing context package
construction and original-conversion recursion, consumes the star
confluence just constructed. No separate confluence oracle is supplied. -/
def valleyOf_asymmetric (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : AsymmetricDiamond L) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (c : ConvT E n Γ a b T) : CValley E n PEq Γ a b T :=
  StepTransferProducerAudit.valleyOf_confluence hW L
    (starConfluenceOf_asymmetric hW L D) hΓ c

/-- The same actual producer from the all-three-equalities coherent star
variant, with its explicit at-most-one right-leg bound. -/
def valleyOf_shortRight (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : ShortRightDiamond L) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (c : ConvT E n Γ a b T) : CValley E n PEq Γ a b T :=
  valleyOf_asymmetric hW L (asymmetricOf_shortRight L D) hΓ c

#print axioms stepOf_short
#print axioms asymmetricOf_shortRight
#print axioms shortRightOf_asymmetric
#print axioms asymmetricOf_coherentDiamond
#print axioms stripOf_asymmetric
#print axioms confluenceOf_asymmetric
#print axioms stripOf_shortRight
#print axioms confluenceOf_shortRight
#print axioms starConfluenceOf_asymmetric
#print axioms valleyOf_asymmetric
#print axioms valleyOf_shortRight

end Rcic.Declarative.NativeValleys.CoherentConsumerAudit

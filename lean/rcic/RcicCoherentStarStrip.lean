import rcic.RcicCoherentConsumer

/-!
# Confluence from an explicit coherent step-versus-star premise

`StarStrip` requires a coherent join of one original certified step and
an arbitrary coherent original star with the same source decoration.
Both joining legs may have arbitrary finite length. The existing
`StarJoin` records both source interfaces and the common target
decoration; no new join or star structure is introduced.

This is a step-versus-star postponement premise, not a local step/step
diamond. A local row with two star joining legs supplies only its
one-step-input instance. This module does not construct the premise from
such local rows, with or without a bound of two on their joining lengths.

`confluenceOf_starStrip` decreases the explicit `CoherentConsumerAudit.length`
of its first original input star. In the tail case the premise receives
the original head `p` and original second star `t`; the only recursive
call receives the literal original tail `ps` as its decreasing argument.
Generated stars are other arguments or are concatenated using the
published `coherent_trans`, including its endpoint decoration laws.

The final two adapters use the published source repair and native-valley
producer. They retain the displayed `StarStrip` argument: this premise
remains unconstructed, and no unconditional confluence or closure result
is asserted. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.CoherentStarStripAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

open DecoStarAudit (Coherent StarJoin)
open StepTransferRowsAudit (coherent_trans)

/-- The exact unconstructed step-versus-star residual. Its result is the
existing `StarJoin`, with both coherent star legs, both actual source
decoration interfaces, and equal actual target decorations. The single
step input is embedded by the existing `CStar.ofStep`. -/
abbrev StarStrip (L : LeafIface E n PEq) : Type :=
  ∀ {Γ : LCtx}, (hΓ : CtxWfT E n Γ) → ∀ {b d e T : Expr Nat}
    (p : CStep E n PEq Γ b d T) (t : CStar E n PEq Γ b e T),
      Coherent L hΓ t →
      decoOf (p.leftTyped L hΓ) = decoOf (t.leftTyped L hΓ) →
        StarJoin L hΓ (CStar.ofStep L hΓ p) t

/-- Consume precisely `StarStrip`. The premise is called on the original
head and original second star; recursion decreases only the literal tail
of the original first star. No generated joining leg is measured. -/
def confluenceOf_starStrip (L : LeafIface E n PEq) (D : StarStrip L)
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
      let j := D hΓ p t ht hsource
      have hleft : decoOf (j.left.leftTyped L hΓ) =
          decoOf (p.rightTyped L hΓ) := by
        simpa only [CStar.ofStep, CStar.rightTyped] using j.leftSource
      have hnext : decoOf (ps.leftTyped L hΓ) =
          decoOf (j.left.leftTyped L hΓ) :=
        hs.1.symm.trans hleft.symm
      let r := confluenceOf_starStrip L D hΓ ps j.left
        hs.2 j.leftCoherent hnext
      let joined := coherent_trans L hΓ j.right r.right
        j.rightCoherent r.rightCoherent
        (j.target.symm.trans r.rightSource.symm)
      exact
        { centre := r.centre
          left := r.left
          right := j.right.trans r.right
          leftCoherent := r.leftCoherent
          rightCoherent := joined.1
          leftSource := by simpa only [CStar.rightTyped] using r.leftSource
          rightSource := joined.2.1.trans j.rightSource
          target := r.target.trans joined.2.2.symm }
termination_by b d e T s t _ _ _ => CoherentConsumerAudit.length s
decreasing_by all_goals (simp only [CoherentConsumerAudit.length]; omega)

/-- Source repair supplies coherent input stars whose actual source
decorations both equal the first input's source typing. Applying the
preceding consumer constructs the published fixed-index `StarConfluence`
operation, conditional on the still explicit step-versus-star premise. -/
def starConfluenceOf_starStrip (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : StarStrip L) : StepTransferProducerAudit.StarConfluence E n PEq := by
  intro Γ hΓ a b c T s t
  let h := s.leftTyped L hΓ
  let left := StepTransferAudit.coherentStarOf_typing hW L hΓ s h
  let right := StepTransferAudit.coherentStarOf_typing hW L hΓ t h
  let j := confluenceOf_starStrip L D hΓ left.1 right.1
    left.2.1 right.2.1 (left.2.2.trans right.2.2.symm)
  exact ⟨j.centre, j.left, j.right⟩

/-- The existing native-valley producer consumes the confluence operation
constructed above. `D` remains a required unconstructed argument; the
producer's recursion on original native conversions is unchanged. -/
def valleyOf_starStrip (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : StarStrip L) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (c : ConvT E n Γ a b T) : CValley E n PEq Γ a b T :=
  StepTransferProducerAudit.valleyOf_confluence hW L
    (starConfluenceOf_starStrip hW L D) hΓ c

#print axioms StarStrip
#print axioms confluenceOf_starStrip
#print axioms starConfluenceOf_starStrip
#print axioms valleyOf_starStrip

end Rcic.Declarative.NativeValleys.CoherentStarStripAudit

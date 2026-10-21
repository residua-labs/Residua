import rcic.RcicNativeDecoIdentity
import rcic.RcicNativeValleyDecoBook

/-!
# Source-decoration repair through coherent certified stars

The source-only contract does not need the stronger literal-to-literal
identity step with independently prescribed endpoint decorations. Given an
actual typing of `lit t` at the requested index, its own expansion typing
builds one certified expansion step with exactly the requested source
decoration. Outer typing conversions are followed by `CStep.reindex`.

The only recursive call is on the original `HasTyT.conv` child. Its
decreasing argument is `sizeOf h`; neither a diamond nor type uniqueness,
Pi injectivity, sort uniqueness, or a retyping hypothesis is used.

The direct literal-expansion row is single-step. For all literal-source
steps, `literalStarOf_typing` constructs a coherent star. At a proof leaf
it expands first, then uses the published nonliteral identity repair at
the expansion. At `iotaSpine` it appends the last iota hop after the
recursive repair of the original spine child; that hop's native
certificate is the inverse of the original child's certificate followed
by the original root certificate. No standalone iota refiring theorem is
assumed. At `conv` the requested typing is moved backwards along the
original chain and the repaired star is moved forwards.

Inputs are actual typings, so no choice axiom is used to extract a typing
from the proposition-valued realizer in `StepDecoTransfer`. The output
prescribes the source decoration only. No global diamond or star
confluence is assumed or constructed here.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.StepTransferRowsAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

open DecoStarAudit (Coherent)

/-- Concatenation preserves coherence and its endpoint decorations when
the two input stars agree at their shared term. The source equality needs
the interface hypothesis in the reflexive case because `CStar.trans`
discards the first reflexive star. -/
theorem coherent_trans (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {a b c T : Expr Nat} → (s : CStar E n PEq Γ a b T) →
    (t : CStar E n PEq Γ b c T) → Coherent L hΓ s → Coherent L hΓ t →
    decoOf s.rightTyped = decoOf (t.leftTyped L hΓ) →
      Coherent L hΓ (s.trans t) ∧
      decoOf ((s.trans t).leftTyped L hΓ) = decoOf (s.leftTyped L hΓ) ∧
      decoOf (s.trans t).rightTyped = decoOf t.rightTyped
  | _, _, _, _, .refl .., _, _, ht, hm => by
      simp only [CStar.trans, CStar.leftTyped, CStar.rightTyped] at *
      exact ⟨ht, hm.symm, True.intro⟩
  | _, _, _, _, .tail p ps, t, hs, ht, hm => by
      simp only [CStar.rightTyped] at hm
      let r := coherent_trans L hΓ ps t hs.2 ht hm
      simp only [CStar.trans, Coherent, CStar.leftTyped, CStar.rightTyped]
      exact ⟨⟨hs.1.trans r.2.1.symm, r.1⟩, True.intro, r.2.2⟩

/-- Reindexing a coherent star preserves coherence and both endpoint
decorations. The recursive call is on the original star's tail. -/
theorem coherent_reindex (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {T T' : Expr Nat} (hc : TyConvT E n Γ T T') :
    {a b : Expr Nat} → (s : CStar E n PEq Γ a b T) → Coherent L hΓ s →
      Coherent L hΓ (s.reindex hc) ∧
      decoOf ((s.reindex hc).leftTyped L hΓ) = decoOf (s.leftTyped L hΓ) ∧
      decoOf (s.reindex hc).rightTyped = decoOf s.rightTyped
  | _, _, .refl _ _ _ h, _ => by
      simp only [CStar.reindex, Coherent, CStar.leftTyped, CStar.rightTyped]
      exact ⟨True.intro, decoOf_hasTyT_of_tyConvT h hc, decoOf_hasTyT_of_tyConvT h hc⟩
  | _, _, .tail p ps, hs => by
      let r := coherent_reindex L hΓ hc ps hs.2
      have hm := (DecoReindexAudit.reindex_right_deco L hΓ p hc).trans
        (hs.1.trans r.2.1.symm)
      simp only [CStar.reindex, Coherent, CStar.leftTyped, CStar.rightTyped]
      exact ⟨⟨hm, r.1⟩, DecoReindexAudit.reindex_left_deco L hΓ p hc, r.2.2⟩

/-- Rebuild the single literal-expansion step from the requested source
typing, including all of that typing's outer conversion wrappers. -/
def expansionStepOf_typing (L : LeafIface E n PEq) {Γ : LCtx} :
    {t : Nat} → {T : Expr Nat} → (h : HasTyT E n Γ (.lit t) T) →
    Σ' (s : CStep E n PEq Γ (.lit t) (natExpand t) T),
      stepDeco L s.step = decoOf h
  | t, T, .lit _ _ _ hexp =>
      ⟨⟨.lit Γ t T hexp,
        .lit (.lit Γ t (natExpand t) T (.of t) hexp)⟩, rfl⟩
  | t, _, .conv _ _ A B u h hc => by
      let s := expansionStepOf_typing L h
      refine ⟨s.1.reindex (.of Γ A B u hc), ?_⟩
      simpa only [stepDeco_reindex, decoOf] using s.2
  termination_by t T h => sizeOf h
  decreasing_by all_goals (simp; omega)

private theorem natExpand_nonliteral (t k : Nat) : natExpand t ≠ .lit k := by
  cases t with
  | zero => intro h; cases h
  | succ t => intro h; cases h

private def literalStarCore (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {a b T : Expr Nat} → (p : ParRedT PEq E n Γ a b T) → Certified p →
    (t : Nat) → a = .lit t → (h : HasTyT E n Γ a T) →
      Σ' (s : CStar E n PEq Γ a b T),
        Coherent L hΓ s ∧ decoOf (s.leftTyped L hΓ) = decoOf h
  | _, _, _, .refl _ a T _, _, _, _, h =>
      ⟨.refl Γ a T h, True.intro, rfl⟩
  | _, _, _, .sortEq .., _, _, hs, _ => by cases hs
  | _, _, _, .consts .., _, _, hs, _ => by cases hs
  | _, _, _, .bvarZeta .., _, _, hs, _ => by cases hs
  | _, _, _, .delta .., _, _, hs, _ => by cases hs
  | _, _, _, .app .., _, _, hs, _ => by cases hs
  | _, _, _, .beta .., _, _, hs, _ => by cases hs
  | _, _, _, .lam .., _, _, hs, _ => by cases hs
  | _, _, _, .pi .., _, _, hs, _ => by cases hs
  | _, _, _, .letE .., _, _, hs, _ => by cases hs
  | _, _, _, .zeta .., _, _, hs, _ => by cases hs
  | _, _, _, .iotaSpine _ a m b T p hI _ hb, cp, t, hs, h => by
      cases cp with
      | iotaSpine c cs =>
          let r := literalStarCore hW L hΓ p cs t hs h
          let hm : HasTyT E n Γ m T := r.1.rightTyped
          let cI : ConvT E n Γ m b T :=
            .trans Γ m a b T (.symm Γ a m T cs.root) c
          let q : CStep E n PEq Γ m b T :=
            ⟨.iotaSpine Γ m m b T (.refl Γ m T hm) hI hm hb,
              .iotaSpine cI (.refl (.refl Γ m T hm))⟩
          let tail := CStar.ofStep L hΓ q
          have ht : Coherent L hΓ tail := ⟨rfl, True.intro⟩
          have hi : decoOf r.1.rightTyped = decoOf (tail.leftTyped L hΓ) := rfl
          let joined := coherent_trans L hΓ r.1 tail r.2.1 ht hi
          exact ⟨r.1.trans tail, joined.1, joined.2.1.trans r.2.2⟩
  | _, _, _, .iotaStarK .., cp, _, _, _ => False.elim cp.noK
  | _, _, _, .iotaStarKEta .., cp, _, _, _ => False.elim cp.noKEta
  | _, _, _, .lit .., _, _, _, h => by
      let r := expansionStepOf_typing L h
      exact ⟨CStar.ofStep L hΓ r.1, ⟨rfl, True.intro⟩,
        (decoOf_leftTyped L hΓ r.1).trans r.2⟩
  | _, _, _, .eta .., _, _, hs, _ => by cases hs
  | _, _, _, .peq _ a b T hpq, _, t, hs, h => by
      subst a
      let expanded := expansionStepOf_typing L h
      let he : HasTyT E n Γ (natExpand t) T := expanded.1.rightTyped L hΓ
      let q : CStep E n PEq Γ (natExpand t) b T :=
        CStep.irr L (L.prop hpq) he (L.typed hpq).2
      let repaired := DecoIdentityAudit.coherentStarOf_nonliteral hW L hΓ he q
        (natExpand_nonliteral t)
      exact ⟨.tail expanded.1 repaired.1,
        ⟨repaired.2.2.1.symm, repaired.2.1⟩,
        (decoOf_leftTyped L hΓ expanded.1).trans expanded.2⟩
  | _, _, _, .conv _ a b A T p hc, cp, t, hs, h => by
      cases cp with
      | conv _ cs =>
          let hA : HasTyT E n Γ a A := hasTyT_of_tyConvT h hc.symmT
          let r := literalStarCore hW L hΓ p cs t hs hA
          let moved := coherent_reindex L hΓ hc r.1 r.2.1
          exact ⟨r.1.reindex hc, moved.1,
            moved.2.1.trans (r.2.2.trans (decoOf_hasTyT_of_tyConvT h hc.symmT))⟩
  termination_by _ _ _ p _ _ _ _ => sizeOf p
  decreasing_by all_goals (simp; omega)

/-- Every certified step with a literal source admits a coherent-star
repair at the same endpoints and index, with any actual requested source
typing. No law on `LeafIface.typed`/`ofIrr` is required. The only recursive
calls in `literalStarCore` descend through the original `iotaSpine` and
`conv` children. The requested typing is not a decreasing argument. -/
def literalStarOf_typing (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t : Nat} {b T : Expr Nat}
    (q : CStep E n PEq Γ (.lit t) b T) (h : HasTyT E n Γ (.lit t) T) :
    Σ' (s : CStar E n PEq Γ (.lit t) b T),
      Coherent L hΓ s ∧ decoOf (s.leftTyped L hΓ) = decoOf h :=
  literalStarCore hW L hΓ q.step q.cert t rfl h

#print axioms coherent_trans
#print axioms coherent_reindex
#print axioms expansionStepOf_typing
#print axioms literalStarOf_typing

end Rcic.Declarative.NativeValleys.StepTransferRowsAudit

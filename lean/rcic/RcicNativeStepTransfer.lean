import rcic.RcicNativeStepTransferRows

/-!
# Coherent-star replacement for single-step decoration transfer

`coherentStepOf_typing` is constructed for every admitted environment and
every lawful existing `LeafIface`. It prescribes only the actual source
typing's decoration. It returns an existing coherent `CStar`, not the
single `CStep` demanded by `StepDecoTransfer`.

The construction combines the published nonliteral identity repair with
the literal-source construction in `RcicNativeStepTransferRows`. It uses
no diamond, type uniqueness, Pi injectivity, retyping hypothesis, or new
leaf law. Its input is an actual typing; the assembler already has such
typings in its steps, so no choice from a proposition-valued existential
is needed.

An original star is then repaired by induction on its original tail. The
new tail is requested at the repaired head star's actual target typing.
This supplies the adjacent decoration equality even when the head repair
changes its original target decoration. The index remains fixed.

The last definition actually feeds those repaired stars into the published
`DecoStarAudit.confluenceOf`. `CoherentDiamond` remains its explicit input;
it is not derived from the weaker `CDiamondD` in this module.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.StepTransferAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

open DecoStarAudit (Coherent)

/-- The source-only coherent-star replacement, for all source terms and
all certified steps. The literal case uses its own expansion and original
step recursion; every other constructor uses the published identity repair. -/
def coherentStepOf_typing (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b e T : Expr Nat}
    (h : HasTyT E n Γ b T) (q : CStep E n PEq Γ b e T) :
    Σ' (s : CStar E n PEq Γ b e T),
      Coherent L hΓ s ∧ decoOf (s.leftTyped L hΓ) = decoOf h := by
  cases b
  all_goals first
    | exact StepTransferRowsAudit.literalStarOf_typing hW L hΓ q h
    | let r := DecoIdentityAudit.coherentStarOf_nonliteral hW L hΓ h q
        (by intro t heq; cases heq)
      exact ⟨r.1, r.2.1, r.2.2.1⟩

/-- Repair every interface of an original certified star. The sole
recursive call uses its original tail `ps`, while the supplied typing is
the repaired head star's actual right typing at the same index. -/
def coherentStarOf_typing (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {a b T : Expr Nat} → (s : CStar E n PEq Γ a b T) →
    (h : HasTyT E n Γ a T) →
      Σ' (s' : CStar E n PEq Γ a b T),
        Coherent L hΓ s' ∧ decoOf (s'.leftTyped L hΓ) = decoOf h
  | _, _, _, .refl _ a T _, h =>
      ⟨.refl _ a T h, True.intro, rfl⟩
  | _, _, _, .tail p ps, h => by
      let head := coherentStepOf_typing hW L hΓ h p
      let tail := coherentStarOf_typing hW L hΓ ps head.1.rightTyped
      let joined := StepTransferRowsAudit.coherent_trans L hΓ head.1 tail.1
        head.2.1 tail.2.1 tail.2.2.symm
      exact ⟨head.1.trans tail.1, joined.1, joined.2.1.trans head.2.2⟩

/-- Ordinary fixed-index star confluence from the coherent decorated
diamond alone. Both repaired input stars begin at one actual source
typing, so the published coherent confluence theorem applies directly. -/
def confluenceOf_coherentDiamond (hW : EnvWfT E) (L : LeafIface E n PEq)
    (D : DecoStarAudit.CoherentDiamond L)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b c T : Expr Nat}
    (s : CStar E n PEq Γ a b T) (t : CStar E n PEq Γ a c T) :
    CValley E n PEq Γ b c T := by
  let h := s.leftTyped L hΓ
  let left := coherentStarOf_typing hW L hΓ s h
  let right := coherentStarOf_typing hW L hΓ t h
  let joined := DecoStarAudit.confluenceOf L D hΓ left.1 right.1
    left.2.1 right.2.1 (left.2.2.trans right.2.2.symm)
  exact ⟨joined.centre, joined.left, joined.right⟩

#print axioms coherentStepOf_typing
#print axioms coherentStarOf_typing
#print axioms confluenceOf_coherentDiamond

end Rcic.Declarative.NativeValleys.StepTransferAudit

import rcic.RcicCoherentCanonical
import rcic.RcicCoherentConsumer

/-!
# Canonical literal source transfer and same-target coherent joins

For the public `ProofLeaf` with `nativeLeafIface`, every certified step
whose source is a literal admits an actual single-step source-decoration
repair at its original index. The requested typing is an input. At a
proof leaf, the canonical interface returns this typing verbatim; no
expansion or identity repair is needed. The only recursive cases follow
the original `iotaSpine` and `conv` children. Neither the generated step
nor the transported requested typing is a decreasing argument.

This rules out a pointwise canonical literal-source counterexample to
source-only `StepDecoTransfer`: from any proposition-valued realization
of the requested decoration, `literal_transfer_exists` proves existence
of a repaired certified step. It does not extract a Type-valued witness
from a Prop-valued existential using choice.

Stored right typings are a different issue. For a common nonliteral
target, `stepJoin_same_nonliteral_target` constructs the existing
single-step `StepJoin` using the published identity constructor. For a
common literal target, `asymmetricJoin_same_literal_target` expands each
literal using its own actual typing and changes decoration at the
nonliteral expansion with that identity constructor. This produces a
two-step left star and a one-step right leg with every required source,
coherence, and target equation. It is an actual row, not an oracle.

No admitted counterexample to the canonical `CoherentDiamond` is claimed
here. A literal obstruction would have to exclude every alternative
one-step join of differently decorated literal targets, including
canonical proof leaves beneath conversions and possible iota spines.
The absence of a literal-to-literal identity constructor, or failure of
the two direct expansion targets to agree, does not prove that exclusion.
The source-transfer construction below removes source-only mismatch as
a candidate obstruction at literal roots. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.CoherentLiteralAudit

variable {E : ResolvedEnv} {n : Nat}

open CoherentCanonicalAudit (nativeLeafIface)
open DecoStarAudit (Coherent StepJoin)
open CoherentConsumerAudit (AsymmetricStepJoin)

/-- The recursion follows the original certified literal-source step.
Canonical proof leaves use the supplied source typing exactly. -/
private def literalStepCore {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {a b T : Expr Nat} → (p : ParRedT (ProofLeaf E n) E n Γ a b T) → Certified p →
    (t : Nat) → a = .lit t → (h : HasTyT E n Γ a T) →
      Σ' (q : CStep E n (ProofLeaf E n) Γ a b T),
        stepDeco (nativeLeafIface E n) q.step = decoOf h
  | _, _, _, .refl _ a T _, _, _, _, h =>
      ⟨⟨.refl Γ a T h, .refl (.refl Γ a T h)⟩, rfl⟩
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
          let r := literalStepCore hΓ p cs t hs h
          let q : CStep E n (ProofLeaf E n) Γ a b T :=
            ⟨.iotaSpine Γ a m b T r.1.step hI
                (r.1.rightTyped (nativeLeafIface E n) hΓ) hb,
              .iotaSpine c r.1.cert⟩
          exact ⟨q, r.2⟩
  | _, _, _, .iotaStarK .., cp, _, _, _ => False.elim cp.noK
  | _, _, _, .iotaStarKEta .., cp, _, _, _ => False.elim cp.noKEta
  | _, _, _, .lit .., _, _, _, h =>
      StepTransferRowsAudit.expansionStepOf_typing (nativeLeafIface E n) h
  | _, _, _, .eta .., _, _, hs, _ => by cases hs
  | _, _, _, .peq _ _ _ _ hpq, _, _, _, h =>
      ⟨CStep.irr (nativeLeafIface E n) hpq.hT h hpq.hq, rfl⟩
  | _, _, _, .conv _ _ _ A _ p hc, cp, t, hs, h => by
      cases cp with
      | conv _ cs =>
          let hA : HasTyT E n Γ _ A := hasTyT_of_tyConvT h hc.symmT
          let r := literalStepCore hΓ p cs t hs hA
          exact ⟨r.1.reindex hc,
            (stepDeco_reindex (nativeLeafIface E n) r.1 hc).trans
              (r.2.trans (decoOf_hasTyT_of_tyConvT h hc.symmT))⟩
  termination_by _ _ _ p _ _ _ _ => sizeOf p
  decreasing_by all_goals (simp; omega)

/-- Actual canonical single-step source repair for every literal-source
step, at the same endpoints and index. No environment-wide assumption
is necessary for this construction. -/
def literalStepOf_typing {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {t : Nat} {b T : Expr Nat}
    (q : CStep E n (ProofLeaf E n) Γ (.lit t) b T)
    (h : HasTyT E n Γ (.lit t) T) :
    Σ' (q' : CStep E n (ProofLeaf E n) Γ (.lit t) b T),
      stepDeco (nativeLeafIface E n) q'.step = decoOf h :=
  literalStepCore hΓ q.step q.cert t rfl h

/-- A proposition-valued source realization implies a proposition-valued
existence of the repaired step. Elimination stays in Prop; no choice
extractor is used. Hence no pointwise no-alternate-step counterexample
exists for a canonical literal source with a realized decoration. -/
theorem literal_transfer_exists {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {t : Nat} {b T : Expr Nat}
    (q : CStep E n (ProofLeaf E n) Γ (.lit t) b T) (d : Deco (.lit t))
    (hd : ∃ h : HasTyT E n Γ (.lit t) T, decoOf h = d) :
    ∃ q' : CStep E n (ProofLeaf E n) Γ (.lit t) b T,
      stepDeco (nativeLeafIface E n) q'.step = d := by
  obtain ⟨h, hh⟩ := hd
  let r := literalStepOf_typing hΓ q h
  exact ⟨r.1, r.2.trans hh⟩

section SameTargetRows

variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- A difference between stored right typings cannot obstruct a coherent
single-step join when the common target is nonliteral. The published
identity step takes those exact two typings as its two interfaces. -/
def stepJoin_same_nonliteral_target (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b e T : Expr Nat}
    (p q : CStep E n PEq Γ b e T) (hnlit : ∀ t : Nat, e ≠ .lit t) :
    StepJoin L hΓ p q := by
  let j := DecoIdentityAudit.identityStepOf_nonliteral hW L hΓ
    (p.rightTyped L hΓ) (q.rightTyped L hΓ) hnlit
  exact
    { centre := e
      left := j.1
      right := ⟨.refl Γ e T (q.rightTyped L hΓ),
        .refl (.refl Γ e T (q.rightTyped L hΓ))⟩
      leftSource := j.2.1
      rightSource := rfl
      target := j.2.2 }

private theorem natExpand_nonliteral (t k : Nat) : natExpand t ≠ .lit k := by
  cases t
  all_goals intro h; cases h

/-- Actual same-literal-target asymmetric row for every existing leaf
interface. Each literal first expands at its own requested decoration;
the left expansion then takes the existing identity step to the right
expansion's decoration. The output has two left steps and one right step. -/
def asymmetricJoin_same_literal_target (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b T : Expr Nat} {t : Nat}
    (p q : CStep E n PEq Γ b (.lit t) T) : AsymmetricStepJoin L hΓ p q := by
  let l := StepTransferRowsAudit.expansionStepOf_typing L (p.rightTyped L hΓ)
  let r := StepTransferRowsAudit.expansionStepOf_typing L (q.rightTyped L hΓ)
  let j := DecoIdentityAudit.identityStepOf_nonliteral hW L hΓ
    (l.1.rightTyped L hΓ) (r.1.rightTyped L hΓ) (natExpand_nonliteral t)
  exact
    { centre := natExpand t
      left := .tail l.1 (.tail j.1 (.refl Γ (natExpand t) T (r.1.rightTyped L hΓ)))
      right := r.1
      leftCoherent := ⟨j.2.1.symm, ⟨j.2.2, True.intro⟩⟩
      leftSource := (decoOf_leftTyped L hΓ l.1).trans l.2
      rightSource := by
        simpa only [CStar.ofStep, CStar.rightTyped] using
          (decoOf_leftTyped L hΓ r.1).trans r.2
      target := by simp only [CStar.rightTyped] }

/-- The left leg of the concrete same-literal-target row has exactly two
star step nodes. The internal identity constructor is not a recursive
subject of the strip or confluence consumer. -/
theorem asymmetricJoin_same_literal_target_length
    (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b T : Expr Nat} {t : Nat}
    (p q : CStep E n PEq Γ b (.lit t) T) :
    CoherentConsumerAudit.length (asymmetricJoin_same_literal_target hW L hΓ p q).left = 2 := rfl

end SameTargetRows

#print axioms literalStepOf_typing
#print axioms literal_transfer_exists
#print axioms stepJoin_same_nonliteral_target
#print axioms asymmetricJoin_same_literal_target
#print axioms asymmetricJoin_same_literal_target_length

end Rcic.Declarative.NativeValleys.CoherentLiteralAudit

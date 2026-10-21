import rcic.RcicNativeValleyEtaLeaf
import rcic.RcicNativeValleyDeco

/-!
# A lawful proof-leaf interface need not return the supplied decoration

This module gives concrete typed witnesses in `emptyEnv`, at level arity
zero and in the empty context.  Both are admitted by the existing
`EnvWfT.empty` and `CtxWfT.nil` constructors.

The interface below stores native proof typings, but its `ofIrr` operation
rechooses a lambda domain's sort as `max u 0`.  Native sort equality makes
this a valid typing of exactly the same term at exactly the same type.
The two sort expressions remain distinct in the existing `Deco` datatype.

Consequently even the source typing of an actual `CStep.irr` need not
have the decoration of the source typing passed to that operation.  This
is the specific missing roundtrip law at `csubstMixed`'s `peq` branch:
it supplies the substituted typing to `L.ofIrr`, then source extraction
reads `L.typed` from the newly formed leaf.

This counterexample concerns the abstract interface's annotation choices;
it is not a countermodel to native conversion confluence or a discharge
of the eta-leaf fixture's `NotProof` assumptions.

Dependency pin: `0849f7ec4117`.
`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.DecoLeafIfaceAudit

private theorem max_zero_eq (u : Level) : eqN u (.max u .zero) := by
  intro ρ
  cases h : eval ρ u <;> simp [eval, h]

private def rechooseLamSort {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → HasTyT E n Γ e T → HasTyT E n Γ e T
  | _, _, _, .lam Γ A u body B hA hb =>
      .lam Γ A (.max u .zero) body B
        (.conv Γ A (.sort u) (.sort (.max u .zero)) (.succ u) hA
          (.sorts Γ u (.max u .zero) (max_zero_eq u))) hb
  | _, _, _, .conv Γ e A B u h hc =>
      .conv Γ e A B u (rechooseLamSort h) hc
  | _, _, _, h => h

private abbrev NativeProofData (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (p q P : Expr Nat) : Type :=
  HasTyT E n Γ P (.sort .zero) × (HasTyT E n Γ p P × HasTyT E n Γ q P)

private def rechoosingIface (E : ResolvedEnv) (n : Nat) :
    LeafIface E n (NativeProofData E n) where
  typed := fun h => h.2
  conv := fun h => .irr _ _ _ _ h.1 h.2.1 h.2.2
  prop := fun h => h.1
  ofIrr := fun hP hp hq => ⟨hP, rechooseLamSort hp, rechooseLamSort hq⟩

private def identityProp :
    HasTyT emptyEnv 0 [] (.pi etaLeafP etaLeafP) (.sort .zero) :=
  .conv [] (.pi etaLeafP etaLeafP) (.sort (.imax .zero .zero)) (.sort .zero)
    (.succ (.imax .zero .zero))
    (.pi [] etaLeafP .zero etaLeafP .zero (etaLeafP_ty []) (etaLeafP_ty _))
    (.sorts [] (.imax .zero .zero) .zero (eqN_imax_zero_right .zero))

private def identityProof :
    HasTyT emptyEnv 0 [] (.lam etaLeafP (.bvar 0)) (.pi etaLeafP etaLeafP) :=
  .lam [] etaLeafP .zero (.bvar 0) etaLeafP (etaLeafP_ty []) (.bvar _ 0 _ rfl)

/-- A fully instantiated lawful leaf interface and a closed native proof
whose actual certified irrelevance step extracts a different source
decoration from the typing supplied to `CStep.irr`.  Thus `LeafIface`
alone does not imply the decoration roundtrip required by the mixed
substitution proof-leaf branch. -/
theorem irr_source_deco_counterexample :
    ∃ (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
      (L : LeafIface emptyEnv 0 PEq) (P p : Expr Nat)
      (hP : HasTyT emptyEnv 0 [] P (.sort .zero))
      (hp : HasTyT emptyEnv 0 [] p P),
      decoOf ((CStep.irr L hP hp hp).leftTyped L .nil) ≠ decoOf hp := by
  refine ⟨NativeProofData emptyEnv 0, rechoosingIface emptyEnv 0,
    .pi etaLeafP etaLeafP, .lam etaLeafP (.bvar 0), identityProp, identityProof, ?_⟩
  change
    Deco.lam etaLeafP (.bvar 0) (.max .zero .zero)
        (decoOf (etaLeafP_ty (E := emptyEnv) (n := 0) [])) (.bvar 0) ≠
      Deco.lam etaLeafP (.bvar 0) .zero
        (decoOf (etaLeafP_ty (E := emptyEnv) (n := 0) [])) (.bvar 0)
  intro hd
  injection hd with _ _ hu _ _
  cases hu

end Rcic.Declarative.NativeValleys.DecoLeafIfaceAudit

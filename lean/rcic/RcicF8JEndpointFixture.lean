import rcic.RcicF8EvParStar
/-! Additional Q1 scope control. Canonical XTileQ1 declarations and J0 refutations
are owned by landed RcicF8EvParStar (#7042). Fable Q1 credited; no duplicate bodies.
This module retains only the aggregate counterexample. closure_claim=0. -/
namespace Rcic.Declarative.XTileQ1
/-- so Γ-unconditional DT009 at a SORT index is false: a `ConvT … (.sort .zero)` whose
    left endpoint is typable at no type. -/
theorem dt009_sort_index_fails_without_ctxWf :
    ∃ (Γ : LCtx) (a b : Expr Nat),
      Nonempty (ConvT emptyEnv 0 Γ a b (.sort .zero)) ∧
      Nonempty (HasTyT emptyEnv 0 Γ b (.sort .zero)) ∧
      ∀ T, ¬ Nonempty (HasTyT emptyEnv 0 Γ a T) :=
  ⟨illCtx, P₁, P₂, ⟨conv_sort0⟩, ⟨P₂_prop⟩, P₁_untypable⟩

end Rcic.Declarative.XTileQ1

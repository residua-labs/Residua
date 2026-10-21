import rcic.RcicNativeValleyDeco
import rcic.RcicNativeValleyRows
import rcic.RcicNativeDecoReindex

/-!
# RcicNativeDecoRows — local application rows with their decoration premises

The actual `appSide` builder has a controlled target decoration: its shared
codomain and the two child targets determine it.  Thus already-constructed
child joins with matching target decorations give that equality at the parent.

Argument source-decoration agreement also derives a conversion between
the original argument indices through the existing `uniqD`. Reindexing an
already-supplied joining leg along that chain preserves its target decoration.
No source-interface equation for that joining leg is needed for this operation.
The stronger source and target interfaces needed for coherent strip recursion
remain separate obligations.

No global diamond or induction hypothesis is assumed or supplied here.  In
particular, the constructions do not apply an induction hypothesis to the
larger steps produced by `exchangeD`.  No `Uniq`, `Retype`, or Π-injectivity
assumption is used.  The existing `Deco`, `appSide`, `row_app_app`, `uniqD`, and
`CStep.reindex` definitions are reused unchanged.

Dependency pin: `0849f7ec411705d9657d52c4c91bd97f2e1ab624`.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.DecoRowsAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

open DecoReindexAudit (reindex_right_deco decoOf_tyConvT)

/-- Target-decoration calculation for the existing application-side builder.
The domains and function indices need not agree with another side's. -/
theorem appSide_target_deco (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f₁ g a a₁ a₃ A B T₀ : Expr Nat} {v : Level}
    (hf₁ : ParRedT PEq E n Γ f f₁ T₀)
    (hc : TyConvT E n Γ T₀ (.pi A B))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (ha₁ : ParRedT PEq E n Γ a a₁ A) (ca₁ : Certified ha₁)
    (pf : CStep E n PEq Γ f₁ g T₀) (pa : CStep E n PEq Γ a₁ a₃ A) :
    decoOf ((appSide hW L hΓ hf₁ hc hB ha₁ ca₁ pf pa).rightTyped L hΓ) =
      .app g a₃ B (decoOf (pf.rightTyped L hΓ)) (decoOf (pa.rightTyped L hΓ)) := by
  unfold appSide
  dsimp only
  simp only [CStep.reindex, CStep.rightTyped, parRedT_hasTy_right,
    parRedT_typed, decoOf_tyConvT, decoOf]

/-- The existing `app × app` row, equipped with equal output target
decorations.  Its codomain is shared syntactically; its child joins and their
target-decoration equalities are supplied explicitly.  This constructs one
row and does not supply a decorated recursive diamond. -/
def row_app_app_same_deco (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f₁ f₂ a a₁ a₂ A₁ B T₀₁ A₂ T₀₂ : Expr Nat} {v₁ v₂ : Level}
    (hf₁ : ParRedT PEq E n Γ f f₁ T₀₁)
    (hc₁ : TyConvT E n Γ T₀₁ (.pi A₁ B))
    (hB₁ : HasTyT E n (.assumption A₁ :: Γ) B (.sort v₁))
    (ha₁ : ParRedT PEq E n Γ a a₁ A₁) (ca₁ : Certified ha₁)
    (hf₂ : ParRedT PEq E n Γ f f₂ T₀₂)
    (hc₂ : TyConvT E n Γ T₀₂ (.pi A₂ B))
    (hB₂ : HasTyT E n (.assumption A₂ :: Γ) B (.sort v₂))
    (ha₂ : ParRedT PEq E n Γ a a₂ A₂) (ca₂ : Certified ha₂)
    (jf : Join E n PEq Γ f₁ f₂ T₀₁ T₀₂)
    (ja : Join E n PEq Γ a₁ a₂ A₁ A₂)
    (hdf : decoOf (jf.2.1.rightTyped L hΓ) = decoOf (jf.2.2.rightTyped L hΓ))
    (hda : decoOf (ja.2.1.rightTyped L hΓ) = decoOf (ja.2.2.rightTyped L hΓ)) :
    Σ' (j : Join E n PEq Γ (.app f₁ a₁) (.app f₂ a₂)
        (instantiate0 a B) (instantiate0 a B)),
      decoOf (j.2.1.rightTyped L hΓ) = decoOf (j.2.2.rightTyped L hΓ) := by
  refine ⟨row_app_app hW L hΓ hf₁ hc₁ hB₁ ha₁ ca₁ hf₂ hc₂ hB₂ ha₂ ca₂ jf ja, ?_⟩
  rcases jf with ⟨g, pf, qf⟩
  rcases ja with ⟨a₃, pa, qa⟩
  change decoOf ((appSide hW L hΓ hf₁ hc₁ hB₁ ha₁ ca₁ pf pa).rightTyped L hΓ) =
    decoOf ((appSide hW L hΓ hf₂ hc₂ hB₂ ha₂ ca₂ qf qa).rightTyped L hΓ)
  rw [appSide_target_deco, appSide_target_deco, hdf, hda]

/-- Realign an already-given argument join to the second argument step's
index. The original argument source decorations give the index conversion
through `uniqD`; root reindexing preserves the supplied target equality.
No joining-leg source-interface premise or recursive diamond call is needed. -/
noncomputable def realign_argument_join (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a a₁ a₂ a₃ A₁ A₂ : Expr Nat}
    (p : CStep E n PEq Γ a a₁ A₁) (q : CStep E n PEq Γ a a₂ A₂)
    (pa : CStep E n PEq Γ a₁ a₃ A₁) (qa : CStep E n PEq Γ a₂ a₃ A₂)
    (hsource : decoOf (p.leftTyped L hΓ) = decoOf (q.leftTyped L hΓ))
    (htarget : decoOf (pa.rightTyped L hΓ) = decoOf (qa.rightTyped L hΓ)) :
    Σ' (pa₂ : CStep E n PEq Γ a₁ a₃ A₂),
      decoOf (pa₂.rightTyped L hΓ) = decoOf (qa.rightTyped L hΓ) := by
  let hc : TyConvT E n Γ A₁ A₂ :=
    uniqD hW (p.leftTyped L hΓ) (q.leftTyped L hΓ) hsource
  exact ⟨pa.reindex hc, (reindex_right_deco L hΓ pa hc).trans htarget⟩

#print axioms appSide_target_deco
#print axioms row_app_app_same_deco
#print axioms realign_argument_join

end Rcic.Declarative.NativeValleys.DecoRowsAudit

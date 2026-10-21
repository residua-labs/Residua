import rcic.RcicCoherentCanonical
import rcic.RcicNativeDecoRows

/-!
# The application builder's exact coherent source interfaces

`ParRedT.app` stores its target typing independently of its child targets.
The landed `appSide` rebuilds its source decoration from the joining child
sources and its written codomain. Therefore original coherent child joins
alone do not establish the two parent source-interface equations.

This module computes those interfaces, gives a conditional `app × app`
row with the exact additional decoration equations, and supplies an admitted
`emptyEnv` fixture where the existing builder's source interface fails even
though the original parent source decorations agree and both original child
joins are genuinely coherent. The fixture reuses the public unequal-typing
decoration witness from `DecoReindexAudit`.

The conditional row explicitly assumes matching original child indices.
Its only child calls are on the two original function steps and the two
original argument steps. No generated or retyped step is a child argument.
No global diamond, type-uniqueness, Pi row, or retyping premise is used.
The builder obstruction is not a refutation of `CoherentDiamond`.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.CoherentAppAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- Package exactly an existing application constructor and its original
child certificates. The target typing is the constructor's stored premise. -/
def appNode {Γ : LCtx} {f f' a a' A B T₀ : Expr Nat} {v w : Level}
    (sf : CStep E n PEq Γ f f' T₀) (sa : CStep E n PEq Γ a a' A)
    (hc : TyConvT E n Γ T₀ (.pi A B))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hTy : HasTyT E n Γ (instantiate0 a B) (.sort w))
    (hr : HasTyT E n Γ (.app f' a') (instantiate0 a B))
    (c : ConvT E n Γ (.app f a) (.app f' a') (instantiate0 a B)) :
    CStep E n PEq Γ (.app f a) (.app f' a') (instantiate0 a B) :=
  ⟨.app Γ f f' a a' A B T₀ v w sf.step hc hB hTy sa.step hr,
    .app c sf.cert sa.cert⟩

/-- The actual application source decoration reads the original child
sources and the written codomain, independently of the stored target typing. -/
theorem appNode_source_deco (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {f f' a a' A B T₀ : Expr Nat} {v w : Level}
    (sf : CStep E n PEq Γ f f' T₀) (sa : CStep E n PEq Γ a a' A)
    (hc : TyConvT E n Γ T₀ (.pi A B))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hTy : HasTyT E n Γ (instantiate0 a B) (.sort w))
    (hr : HasTyT E n Γ (.app f' a') (instantiate0 a B))
    (c : ConvT E n Γ (.app f a) (.app f' a') (instantiate0 a B)) :
    decoOf ((appNode sf sa hc hB hTy hr c).leftTyped L hΓ) =
      .app f a B (decoOf (sf.leftTyped L hΓ)) (decoOf (sa.leftTyped L hΓ)) := by
  simp only [appNode, CStep.leftTyped, parRedT_hasTy_left, parRedT_typed,
    decoOf_hasTyT_of_tyConvT, decoOf]

/-- The actual application target is exactly the independently stored typing. -/
theorem appNode_rightTyped (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {f f' a a' A B T₀ : Expr Nat} {v w : Level}
    (sf : CStep E n PEq Γ f f' T₀) (sa : CStep E n PEq Γ a a' A)
    (hc : TyConvT E n Γ T₀ (.pi A B))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hTy : HasTyT E n Γ (instantiate0 a B) (.sort w))
    (hr : HasTyT E n Γ (.app f' a') (instantiate0 a B))
    (c : ConvT E n Γ (.app f a) (.app f' a') (instantiate0 a B)) :
    (appNode sf sa hc hB hTy hr c).rightTyped L hΓ = hr := rfl

/-- The landed builder's source decoration is assembled from the joining
children. This is independent of any stored target typing of the input node. -/
theorem appSide_source_deco (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f₁ g a a₁ a₃ A B T₀ : Expr Nat} {v : Level}
    (hf₁ : ParRedT PEq E n Γ f f₁ T₀)
    (hc : TyConvT E n Γ T₀ (.pi A B))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (ha₁ : ParRedT PEq E n Γ a a₁ A) (ca₁ : Certified ha₁)
    (pf : CStep E n PEq Γ f₁ g T₀) (pa : CStep E n PEq Γ a₁ a₃ A) :
    decoOf ((appSide hW L hΓ hf₁ hc hB ha₁ ca₁ pf pa).leftTyped L hΓ) =
      .app f₁ a₁ B (decoOf (pf.leftTyped L hΓ)) (decoOf (pa.leftTyped L hΓ)) := by
  unfold appSide
  dsimp only
  simp only [CStep.reindex, CStep.leftTyped, parRedT_hasTy_left,
    parRedT_typed, decoOf_hasTyT_of_tyConvT, decoOf]

/-- After supplying the actual child source interfaces, the missing parent
interface is exactly the displayed equation on the stored target decoration. -/
theorem appSide_source_interface_iff (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f₁ g a a₁ a₃ A B T₀ : Expr Nat} {v : Level}
    (sf : CStep E n PEq Γ f f₁ T₀) (sa : CStep E n PEq Γ a a₁ A)
    (hc : TyConvT E n Γ T₀ (.pi A B))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hr : HasTyT E n Γ (.app f₁ a₁) (instantiate0 a B))
    (pf : CStep E n PEq Γ f₁ g T₀) (pa : CStep E n PEq Γ a₁ a₃ A)
    (hfs : decoOf (pf.leftTyped L hΓ) = decoOf (sf.rightTyped L hΓ))
    (has : decoOf (pa.leftTyped L hΓ) = decoOf (sa.rightTyped L hΓ)) :
    (decoOf ((appSide hW L hΓ sf.step hc hB sa.step sa.cert pf pa).leftTyped L hΓ) =
        decoOf hr) ↔
      (.app f₁ a₁ B (decoOf (sf.rightTyped L hΓ))
        (decoOf (sa.rightTyped L hΓ)) = decoOf hr) := by
  rw [appSide_source_deco, hfs, has]

/-- A coherent `app × app` row when the original child indices agree.
The two local child producers are applied only to the original child pairs,
using equalities extracted from the actual parent source decorations.
The stored-target equations are the exact additional premises identified
by `appSide_source_interface_iff`; no complete parent row is assumed. -/
def stepJoin_app_app_same_indices (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f₁ f₂ a a₁ a₂ A B T₀ : Expr Nat} {v₁ w₁ v₂ w₂ : Level}
    (pf : CStep E n PEq Γ f f₁ T₀) (qf : CStep E n PEq Γ f f₂ T₀)
    (pa : CStep E n PEq Γ a a₁ A) (qa : CStep E n PEq Γ a a₂ A)
    (hc₁ : TyConvT E n Γ T₀ (.pi A B))
    (hc₂ : TyConvT E n Γ T₀ (.pi A B))
    (hB₁ : HasTyT E n (.assumption A :: Γ) B (.sort v₁))
    (hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v₂))
    (hTy₁ : HasTyT E n Γ (instantiate0 a B) (.sort w₁))
    (hTy₂ : HasTyT E n Γ (instantiate0 a B) (.sort w₂))
    (hr₁ : HasTyT E n Γ (.app f₁ a₁) (instantiate0 a B))
    (hr₂ : HasTyT E n Γ (.app f₂ a₂) (instantiate0 a B))
    (c₁ : ConvT E n Γ (.app f a) (.app f₁ a₁) (instantiate0 a B))
    (c₂ : ConvT E n Γ (.app f a) (.app f₂ a₂) (instantiate0 a B))
    (hsource :
      decoOf ((appNode pf pa hc₁ hB₁ hTy₁ hr₁ c₁).leftTyped L hΓ) =
      decoOf ((appNode qf qa hc₂ hB₂ hTy₂ hr₂ c₂).leftTyped L hΓ))
    (ihf : decoOf (pf.leftTyped L hΓ) = decoOf (qf.leftTyped L hΓ) →
      DecoStarAudit.StepJoin L hΓ pf qf)
    (iha : decoOf (pa.leftTyped L hΓ) = decoOf (qa.leftTyped L hΓ) →
      DecoStarAudit.StepJoin L hΓ pa qa)
    (hparent₁ : .app f₁ a₁ B (decoOf (pf.rightTyped L hΓ))
      (decoOf (pa.rightTyped L hΓ)) = decoOf hr₁)
    (hparent₂ : .app f₂ a₂ B (decoOf (qf.rightTyped L hΓ))
      (decoOf (qa.rightTyped L hΓ)) = decoOf hr₂) :
    DecoStarAudit.StepJoin L hΓ
      (appNode pf pa hc₁ hB₁ hTy₁ hr₁ c₁)
      (appNode qf qa hc₂ hB₂ hTy₂ hr₂ c₂) := by
  have hd :
      Deco.app f a B (decoOf (pf.leftTyped L hΓ)) (decoOf (pa.leftTyped L hΓ)) =
      Deco.app f a B (decoOf (qf.leftTyped L hΓ)) (decoOf (qa.leftTyped L hΓ)) := by
    simpa only [appNode_source_deco] using hsource
  injection hd with _ _ _ hdf hda
  let jf := ihf hdf
  let ja := iha hda
  refine
    { centre := .app jf.centre ja.centre
      left := appSide hW L hΓ pf.step hc₁ hB₁ pa.step pa.cert jf.left ja.left
      right := appSide hW L hΓ qf.step hc₂ hB₂ qa.step qa.cert jf.right ja.right
      leftSource := ?_
      rightSource := ?_
      target := ?_ }
  · rw [appSide_source_deco, jf.leftSource, ja.leftSource]
    exact hparent₁
  · rw [appSide_source_deco, jf.rightSource, ja.rightSource]
    exact hparent₂
  · rw [DecoRowsAudit.appSide_target_deco, DecoRowsAudit.appSide_target_deco,
      jf.target, ja.target]

/-- In the admitted empty environment and empty context, there are two
actual application steps with the same source decoration and genuine
coherent joins of their original children, for which the existing
`appSide` builder fails its left source interface. Both steps are
identities as term reductions; only their stored target typings differ.
This refutes automatic coherence of this builder, not existence of some
other coherent join for the peak. -/
theorem admitted_appSide_source_obstruction :
    let L := CoherentCanonicalAudit.nativeLeafIface emptyEnv 0
    Nonempty (EnvWfT emptyEnv) ∧
      ∃ (f a A B T₀ : Expr Nat) (v w : Level)
        (sf : CStep emptyEnv 0 (ProofLeaf emptyEnv 0) [] f f T₀)
        (sa : CStep emptyEnv 0 (ProofLeaf emptyEnv 0) [] a a A)
        (hc : TyConvT emptyEnv 0 [] T₀ (.pi A B))
        (hB : HasTyT emptyEnv 0 [.assumption A] B (.sort v))
        (hTy : HasTyT emptyEnv 0 [] (instantiate0 a B) (.sort w))
        (hr₀ hr₁ : HasTyT emptyEnv 0 [] (.app f a) (instantiate0 a B))
        (c : ConvT emptyEnv 0 [] (.app f a) (.app f a) (instantiate0 a B))
        (jf : DecoStarAudit.StepJoin L .nil sf sf)
        (ja : DecoStarAudit.StepJoin L .nil sa sa),
        decoOf ((appNode sf sa hc hB hTy hr₁ c).leftTyped L .nil) =
          decoOf ((appNode sf sa hc hB hTy hr₀ c).leftTyped L .nil) ∧
        decoOf ((appSide .empty L .nil sf.step hc hB sa.step sa.cert
          jf.left ja.left).leftTyped L .nil) ≠
            decoOf ((appNode sf sa hc hB hTy hr₁ c).rightTyped L .nil) := by
  let L := CoherentCanonicalAudit.nativeLeafIface emptyEnv 0
  obtain ⟨_, a, A, h₀, h₁, hne, _⟩ :=
    DecoReindexAudit.admitted_reindex_not_transfer
  obtain ⟨u, hA⟩ := tySort (E := emptyEnv) .empty .nil h₀
  let B := lift 0 1 A
  let f := Expr.lam A (.bvar 0)
  let hb : HasTyT emptyEnv 0 [.assumption A] (.bvar 0) B :=
    .bvar _ 0 _ rfl
  let hf : HasTyT emptyEnv 0 [] f (.pi A B) :=
    .lam [] A u (.bvar 0) B hA hb
  let hB : HasTyT emptyEnv 0 [.assumption A] B (.sort u) :=
    hasTyTWeaken (.assumption A) (envClosed_of_envWfT (.empty : EnvWfT emptyEnv))
      (c := 0) hA
  let hr₀ : HasTyT emptyEnv 0 [] (.app f a) (instantiate0 a B) :=
    .app [] f a A B hf h₀
  let hr₁ : HasTyT emptyEnv 0 [] (.app f a) (instantiate0 a B) :=
    .app [] f a A B hf h₁
  obtain ⟨w, hTy⟩ := tySort (E := emptyEnv) .empty .nil hr₀
  let sf : CStep emptyEnv 0 (ProofLeaf emptyEnv 0) [] f f (.pi A B) :=
    ⟨.refl [] f (.pi A B) hf, .refl (.refl [] f (.pi A B) hf)⟩
  let sa : CStep emptyEnv 0 (ProofLeaf emptyEnv 0) [] a a A :=
    ⟨.refl [] a A h₀, .refl (.refl [] a A h₀)⟩
  let jf : DecoStarAudit.StepJoin L .nil sf sf :=
    CoherentCanonicalAudit.stepJoin_refl_left L .nil hf (.refl [] f (.pi A B) hf) sf rfl
  let ja : DecoStarAudit.StepJoin L .nil sa sa :=
    CoherentCanonicalAudit.stepJoin_refl_left L .nil h₀ (.refl [] a A h₀) sa rfl
  refine ⟨⟨.empty⟩, f, a, A, B, .pi A B, u, w, sf, sa, .refl [] (.pi A B),
    hB, hTy, hr₀, hr₁, .refl [] (.app f a) (instantiate0 a B) hr₀, jf, ja, rfl, ?_⟩
  intro heq
  rw [appSide_source_deco] at heq
  change Deco.app f a B (decoOf hf) (decoOf h₀) =
    Deco.app f a B (decoOf hf) (decoOf h₁) at heq
  injection heq with _ _ _ _ ha
  exact hne ha

end Rcic.Declarative.NativeValleys.CoherentAppAudit

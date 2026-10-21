import rcic.RcicCoherentAppRows
import rcic.RcicCoherentConsumer

/-!
# Coherent star rows from existing joins with a common target decoration

The existing nonliteral identity construction repairs the two source
interfaces of an already constructed join while preserving its target
decorations. This yields actual coherent star legs with all three
interfaces. It does not require the stored target typings of either
original node to agree with structural typings of their child targets.

The application instance reuses `row_app_app_same_deco` with independent
original function and argument indices. The supplied child joins are
results for those original children. This row calls no recursive diamond;
its caller must produce the two original child joins with their displayed
target equations. The two source repairs each add an identity step, so
this construction does not supply the one-step `StepJoin` contract or the
short-right premise of `RcicCoherentConsumer`.

No unrestricted star/step-peak consumer is asserted. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.CoherentStarRowsAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- Repair both source interfaces of a concrete join with equal target
decorations, retaining that target equation in the existing `StarJoin`.
Both repair calls use the existing nonliteral identity construction; no
recursive diamond is invoked on either produced step. -/
def starJoin_of_targetCompatible (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d e T : Expr Nat}
    (p : CStep E n PEq Γ b d T) (q : CStep E n PEq Γ b e T)
    (j : Join E n PEq Γ d e T T)
    (hd : decoOf (j.2.1.rightTyped L hΓ) = decoOf (j.2.2.rightTyped L hΓ))
    (hnd : ∀ t : Nat, d ≠ .lit t) (hne : ∀ t : Nat, e ≠ .lit t) :
    CoherentConsumerAudit.StarStepJoin L hΓ p q := by
  let left := DecoIdentityAudit.coherentStarOf_nonliteral hW L hΓ
    (p.rightTyped L hΓ) j.2.1 hnd
  let right := DecoIdentityAudit.coherentStarOf_nonliteral hW L hΓ
    (q.rightTyped L hΓ) j.2.2 hne
  exact
    { centre := j.1
      left := left.1
      right := right.1
      leftCoherent := left.2.1
      rightCoherent := right.2.1
      leftSource := by
        simpa only [CStar.ofStep, CStar.rightTyped] using left.2.2.1
      rightSource := by
        simpa only [CStar.ofStep, CStar.rightTyped] using right.2.2.1
      target := left.2.2.2.trans (hd.trans right.2.2.2.symm) }

/-- A coherent star `app × app` row with independent original child
indices. The common written codomain and the two child target equations
feed the landed application builder; the constructed identity prefixes
then handle both arbitrary stored parent target typings. -/
def starJoin_app_app (hW : EnvWfT E) (L : LeafIface E n PEq)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f f₁ f₂ a a₁ a₂ A₁ A₂ B T₀₁ T₀₂ : Expr Nat}
    {v₁ w₁ v₂ w₂ : Level}
    (pf : CStep E n PEq Γ f f₁ T₀₁) (qf : CStep E n PEq Γ f f₂ T₀₂)
    (pa : CStep E n PEq Γ a a₁ A₁) (qa : CStep E n PEq Γ a a₂ A₂)
    (hc₁ : TyConvT E n Γ T₀₁ (.pi A₁ B))
    (hc₂ : TyConvT E n Γ T₀₂ (.pi A₂ B))
    (hB₁ : HasTyT E n (.assumption A₁ :: Γ) B (.sort v₁))
    (hB₂ : HasTyT E n (.assumption A₂ :: Γ) B (.sort v₂))
    (hTy₁ : HasTyT E n Γ (instantiate0 a B) (.sort w₁))
    (hTy₂ : HasTyT E n Γ (instantiate0 a B) (.sort w₂))
    (hr₁ : HasTyT E n Γ (.app f₁ a₁) (instantiate0 a B))
    (hr₂ : HasTyT E n Γ (.app f₂ a₂) (instantiate0 a B))
    (c₁ : ConvT E n Γ (.app f a) (.app f₁ a₁) (instantiate0 a B))
    (c₂ : ConvT E n Γ (.app f a) (.app f₂ a₂) (instantiate0 a B))
    (jf : Join E n PEq Γ f₁ f₂ T₀₁ T₀₂)
    (ja : Join E n PEq Γ a₁ a₂ A₁ A₂)
    (hdf : decoOf (jf.2.1.rightTyped L hΓ) = decoOf (jf.2.2.rightTyped L hΓ))
    (hda : decoOf (ja.2.1.rightTyped L hΓ) = decoOf (ja.2.2.rightTyped L hΓ)) :
    CoherentConsumerAudit.StarStepJoin L hΓ
      (CoherentAppAudit.appNode pf pa hc₁ hB₁ hTy₁ hr₁ c₁)
      (CoherentAppAudit.appNode qf qa hc₂ hB₂ hTy₂ hr₂ c₂) := by
  let j := DecoRowsAudit.row_app_app_same_deco hW L hΓ
    pf.step hc₁ hB₁ pa.step pa.cert qf.step hc₂ hB₂ qa.step qa.cert jf ja hdf hda
  exact starJoin_of_targetCompatible hW L hΓ
    (CoherentAppAudit.appNode pf pa hc₁ hB₁ hTy₁ hr₁ c₁)
    (CoherentAppAudit.appNode qf qa hc₂ hB₂ hTy₂ hr₂ c₂)
    j.1 j.2 (fun _ h => Expr.noConfusion h) (fun _ h => Expr.noConfusion h)

end Rcic.Declarative.NativeValleys.CoherentStarRowsAudit

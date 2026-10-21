import rcic.RcicNativeValleyCert
import rcic.RcicParRedTSubst

/-!
# Primitive beta retyping from supplied codomain evidence

This helper consumes the concrete native codomain chain `cB` and outer chain
`cOut`. It constructs neither chain and invokes no Pi row, type uniqueness,
diamond, or valley supplier. The body and argument children are reflexive.

Drafted against native branch `4d3b74e05355f478a03a44166399794a0a68d2a4`.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- Primitive beta can be presented at `T` using a supplied codomain chain
    under the written binder and a supplied outer result chain. The argument
    is used at the original domain `A`; no domain comparison is required. -/
def beta_retype_of_codomain_chain (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A body arg B₀ B' T : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hb : HasTyT E n (.assumption A :: Γ) body B₀)
    (ha : HasTyT E n Γ arg A)
    (cB : TyConvT E n (.assumption A :: Γ) B₀ B')
    (cOut : TyConvT E n Γ (instantiate0 arg B') T) :
    CStep E n PEq Γ (.app (.lam A body) arg) (instantiate0 arg body) T := by
  let hcl := envClosed_of_envWfT hW
  let hinst := envMembersSubstStable_of_envWfT hW
  let hΓA : CtxWfT E n (.assumption A :: Γ) :=
    .assumption Γ A u hΓ hA
  obtain ⟨v, hB⟩ := regularT_of_envWfT hW (substLetT_of_envWfT hW)
    (constsRightDataT_of_envWfT hW) hΓA hb
  have hTy : HasTyT E n Γ (instantiate0 arg B₀) (.sort v) :=
    hasTyT_subst0S hcl hinst hB ha
  have hred : HasTyT E n Γ (instantiate0 arg body) (instantiate0 arg B₀) :=
    hasTyT_subst0S hcl hinst hb ha
  let cBeta : ConvT E n Γ (.app (.lam A body) arg)
      (instantiate0 arg body) (instantiate0 arg B₀) :=
    .beta Γ A body arg B₀ u hA hb ha
  let s : CStep E n PEq Γ (.app (.lam A body) arg)
      (instantiate0 arg body) (instantiate0 arg B₀) :=
    ⟨.beta Γ A body body arg arg B₀ u v v hA hB hTy
        (.refl _ body B₀ hb) (.refl Γ arg A ha) hred,
      .beta cBeta (.refl (.refl _ body B₀ hb)) (.refl (.refl Γ arg A ha))⟩
  have cSub : TyConvT E n Γ (instantiate0 arg B₀) (instantiate0 arg B') := by
    have haSub : HasTyT E n (substRemove arg 0 (.assumption A :: Γ))
        (lift 0 0 arg) (lift 0 0 A) := by
      simpa only [substRemove_zero_cons, lift_zero] using ha
    have hc := tyConvT_substS hcl hinst arg A (j := 0) cB
      List.getElem?_cons_zero haSub
    simpa only [substRemove_zero_cons, lift_zero, instantiate0] using hc
  exact s.reindex (.trans Γ _ _ _ cSub cOut)

end Rcic.Declarative.NativeValleys

#print axioms Rcic.Declarative.NativeValleys.beta_retype_of_codomain_chain

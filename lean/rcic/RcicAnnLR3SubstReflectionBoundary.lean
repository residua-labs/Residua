import rcic.RcicAnnLR3LetSubstBoundary

/-!
# The converse raw substitution laws also fail

These two short corollaries reuse the supplied normal-variable and local-let
fixtures.  They concern arbitrary `SubstTyA`, not the injective context
insertions used by `WkSpecA` worlds.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3SubstReflectionBoundary

open Rcic.Declarative EqLargeFixture LR3 LR3NormalSubstBoundary LR3LetSubstBoundary

def RawNormalSubstReflectA3 (H : HeadLayerA3 env (iotaIfaceA env) 0) : Prop :=
  ∀ (Γ Δ : LCtxA) (σ : SubstA) (a A : ExprA),
    CtxWfA env (iotaIfaceA env) 0 Γ → CtxWfA env (iotaIfaceA env) 0 Δ →
    SubstTyA env (iotaIfaceA env) 0 Δ σ Γ → HasTyA env (iotaIfaceA env) 0 Γ a A →
    H.normal Δ (substA σ a) → H.normal Γ a

def RawHeadSubstReflectA3 (H : HeadLayerA3 env (iotaIfaceA env) 0) : Prop :=
  ∀ (Γ Δ : LCtxA) (σ : SubstA) (a b' T : ExprA),
    CtxWfA env (iotaIfaceA env) 0 Γ → CtxWfA env (iotaIfaceA env) 0 Δ →
    SubstTyA env (iotaIfaceA env) 0 Δ σ Γ → HasTyA env (iotaIfaceA env) 0 Γ a T →
    H.step Δ (substA σ a) b' (substA σ T) →
    ∃ b, H.step Γ a b T ∧ substA σ b = b'

theorem contextual_not_rawNormalSubstReflectA3 :
    ¬ RawNormalSubstReflectA3 (contextualHeadLayerA3 env (iotaIfaceA env) 0) := by
  intro h
  exact normalA3_no_head
    (h letContext [] normalSubst (.bvar 0) domain letContextWf .nil normalSubstTyped
      sourceTyped substitutedSourceNormal) localHead

theorem contextual_not_rawHeadSubstReflectA3 :
    ¬ RawHeadSubstReflectA3 (contextualHeadLayerA3 env (iotaIfaceA env) 0) := by
  intro h
  obtain ⟨b, hs, _⟩ :=
    h context [] redexSubst (.bvar 0) closedProof domain contextWf .nil redexSubstTyped
      majorTyped substitutedAssumptionHead
  exact normalA3_no_head assumptionNormal hs

#print axioms RawNormalSubstReflectA3
#print axioms RawHeadSubstReflectA3
#print axioms contextual_not_rawNormalSubstReflectA3
#print axioms contextual_not_rawHeadSubstReflectA3

end Rcic.Declarative.Ann.LR3SubstReflectionBoundary

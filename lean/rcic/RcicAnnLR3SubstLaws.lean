import rcic.RcicAnnLR3HeadLayer
import rcic.RcicAnnKTransport

/-!
# Constructive substitution laws available to every LR3 arm

An arbitrary typed substitution transports the conversion supplied by a
head step.  It need not transport a step to a directed chain: the value
field of `SubstTyA` is itself symmetric conversion data.

The stage-1 K arm has the stronger exact-step law.  It composes the landed
`KStage.Frame.subst` supply with the actual contextual LR3 K constructor.
The guard is still expressed in the unchanged earlier conversion layer.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

/-- The general transport law has a typed conversion as its conclusion. -/
def HeadSubstConvA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (Γ Δ : LCtxA) (σ : SubstA) (a b T : ExprA),
    CtxWfA E I n Γ → SubstTyA E I n Δ σ Γ → H.step Γ a b T →
    Nonempty (ConvA E I n Δ (substA σ a) (substA σ b) (substA σ T))

/-- Soundness of the supplied layer and the landed typed-substitution
theorem prove this law for every certified LR3 layer. -/
theorem headSubstConvA3_of_sound {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (H : HeadLayerA3 E I n) (hE : EnvClosedA E) (hI : IotaLiftA I)
    (hR : IotaRecHeadA E I) (hIS : IotaSubstA I) : HeadSubstConvA3 E I n H := by
  intro Γ Δ σ a b T hΓ hσ hs
  obtain ⟨hc⟩ := H.sound hE hI hR hIS hΓ hs
  exact ⟨convA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hσ hc⟩

theorem contextualHeadLayerA3_substConv {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) :
    HeadSubstConvA3 E I n (contextualHeadLayerA3 E I n) :=
  headSubstConvA3_of_sound (contextualHeadLayerA3 E I n) hE hI hR hIS

/-- Exact substitution for supplied K frames, as a separate predicate on H.
This states no exact substitution theorem for the other head constructors. -/
def KHeadSubstA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (Γ Δ : LCtxA) (σ : SubstA) (s : KStage.Shape),
    CtxWfA E I n Γ → SubstTyA E I n Δ σ Γ →
    Nonempty (KStage.Frame E I n Γ s) →
    H.step Δ (substA σ s.source) (substA σ s.minor) (substA σ s.resultType)

theorem contextualHeadLayerA3_kSubst {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) :
    KHeadSubstA3 E I n (contextualHeadLayerA3 E I n) := by
  intro Γ Δ σ s hΓ hσ hw
  obtain ⟨w⟩ := hw
  have hs : HeadA3 E I n Δ (s.map (substMapA σ)).source
      (s.map (substMapA σ)).minor (s.map (substMapA σ)).resultType :=
    .k (s.map (substMapA σ)) (w.subst hE hI hR hIS hΓ hσ)
  rw [KStage.Shape.map_source, KStage.Shape.map_resultType] at hs
  exact hs

#print axioms HeadSubstConvA3
#print axioms headSubstConvA3_of_sound
#print axioms contextualHeadLayerA3_substConv
#print axioms KHeadSubstA3
#print axioms contextualHeadLayerA3_kSubst

end Rcic.Declarative.Ann.LR3

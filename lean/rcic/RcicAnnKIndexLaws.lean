import rcic.RcicAnnFamWk
import rcic.RcicAnnSubstTy

/-!
# Transport of the existing annotated K index witnesses

The index guard is an actual dependent argument walk: `ConvArgsA` records
conversion at each left-instantiated domain, and `ParConvA` also records
conversion between the two instantiated domains. Both witnesses survive a
typed parallel substitution using the existing annotated conversion laws.

These lemmas keep the interface `I` fixed. They neither define a new iota
function nor discharge the lift/substitution laws for a changed function.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.KIndexLaws

open Rcic.Declarative

variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- Successful telescope application commutes with parallel substitution. -/
theorem applyTel_subst (σ : SubstA) {xs : List ExprA} {T U : ExprA}
    (h : applyTelA xs T = some U) :
    applyTelA (xs.map (substA σ)) (substA σ T) = some (substA σ U) :=
  (substMapA σ).applyTelA_some xs h

/-- Type-conversion witnesses transport through an actual typed substitution. -/
def tyConv_subst (hE : EnvClosedA E) (hI : IotaLiftA I)
    (hR : IotaRecHeadA E I) (hIS : IotaSubstA I)
    {Δ Γ : LCtxA} {σ : SubstA} (hσ : SubstTyA E I n Δ σ Γ) :
    {A B : ExprA} → TyConvA E I n Γ A B →
      TyConvA E I n Δ (substA σ A) (substA σ B)
  | _, _, .refl _ _ => .refl _ _
  | _, _, .of _ _ _ l l' u hAl hlu hBl hl'u hc =>
      .of _ _ _ l l' u
        (hasTyA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hσ hAl) hlu
        (hasTyA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hσ hBl) hl'u
        (convA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hσ hc)
  | _, _, .trans _ _ _ _ hAB hBC =>
      .trans _ _ _ _ (tyConv_subst hE hI hR hIS hσ hAB)
        (tyConv_subst hE hI hR hIS hσ hBC)

/-- The dependent pointwise index guard survives typed substitution. -/
theorem convArgs_subst (hE : EnvClosedA E) (hI : IotaLiftA I)
    (hR : IotaRecHeadA E I) (hIS : IotaSubstA I)
    {Δ Γ : LCtxA} {σ : SubstA} (hσ : SubstTyA E I n Δ σ Γ) :
    ∀ {T : ExprA} {xs ys : List ExprA}, ConvArgsA E I n Γ T xs ys →
      ConvArgsA E I n Δ (substA σ T)
        (xs.map (substA σ)) (ys.map (substA σ))
  | _, _, _, .nil _ => .nil _
  | _, _, _, .cons A u B v f f' fs fs' hc hs => by
      rw [substA_pi, List.map_cons, List.map_cons]
      refine .cons _ u _ v _ _ _ _
        (hc.elim fun c =>
          ⟨convA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hσ c⟩) ?_
      rw [← substA_instantiate0A]
      exact convArgs_subst hE hI hR hIS hσ hs

/-- Both instantiated telescope domains and the argument conversions transport. -/
theorem parConv_subst (hE : EnvClosedA E) (hI : IotaLiftA I)
    (hR : IotaRecHeadA E I) (hIS : IotaSubstA I)
    {Δ Γ : LCtxA} {σ : SubstA} (hσ : SubstTyA E I n Δ σ Γ) :
    ∀ {T T' : ExprA} {xs ys : List ExprA}, ParConvA E I n Γ T T' xs ys →
      ParConvA E I n Δ (substA σ T) (substA σ T')
        (xs.map (substA σ)) (ys.map (substA σ))
  | _, _, _, _, .nil _ _ => .nil _ _
  | _, _, _, _, .cons A u B v A' u' B' v' f f' fs fs' hc hd hs => by
      rw [substA_pi, substA_pi, List.map_cons, List.map_cons]
      refine .cons _ u _ v _ u' _ v' _ _ _ _
        (hc.elim fun c =>
          ⟨convA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hσ c⟩)
        (hd.elim fun d => ⟨tyConv_subst hE hI hR hIS hσ d⟩) ?_
      rw [← substA_instantiate0A, ← substA_instantiate0A]
      exact parConv_subst hE hI hR hIS hσ hs

/-- The same guard weakens along any admissible weakening specification. -/
theorem convArgs_weaken (hE : EnvClosedA E) (hI : IotaLiftA I)
    {Γ : LCtxA} (ρ : WkSpecA) (hρ : WkSpecA.ok ρ Γ)
    {T : ExprA} {xs ys : List ExprA} (h : ConvArgsA E I n Γ T xs ys) :
    ConvArgsA E I n (wkCtxA ρ Γ) (wkExprA ρ T)
      (xs.map (wkExprA ρ)) (ys.map (wkExprA ρ)) :=
  convArgsA_wk hE hI ρ hρ h

/-- Two-sided telescope witnesses weaken by the landed argument-walk law. -/
theorem parConv_weaken (hE : EnvClosedA E) (hI : IotaLiftA I)
    {Γ : LCtxA} (ρ : WkSpecA) (hρ : WkSpecA.ok ρ Γ)
    {T T' : ExprA} {xs ys : List ExprA} (h : ParConvA E I n Γ T T' xs ys) :
    ParConvA E I n (wkCtxA ρ Γ) (wkExprA ρ T) (wkExprA ρ T')
      (xs.map (wkExprA ρ)) (ys.map (wkExprA ρ)) :=
  parConvA_wk hE hI ρ hρ h

end Rcic.Declarative.Ann.KIndexLaws

#print axioms Rcic.Declarative.Ann.KIndexLaws.applyTel_subst
#print axioms Rcic.Declarative.Ann.KIndexLaws.tyConv_subst
#print axioms Rcic.Declarative.Ann.KIndexLaws.convArgs_subst
#print axioms Rcic.Declarative.Ann.KIndexLaws.parConv_subst
#print axioms Rcic.Declarative.Ann.KIndexLaws.convArgs_weaken
#print axioms Rcic.Declarative.Ann.KIndexLaws.parConv_weaken

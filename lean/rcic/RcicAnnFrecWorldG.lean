import rcic.RcicAnnFrecWorld
import rcic.RcicAnnLREnvG
import rcic.RcicAnnTelTyG
import rcic.RcicAnnSemTelG
import rcic.RcicAnnTelIntroG
import rcic.RcicAnnFamClauseG
import rcic.RcicAnnFamBuildG
import rcic.RcicAnnFamSemG
import rcic.RcicAnnCtorSemG
import rcic.RcicAnnEnvWfG
import rcic.RcicAnnRecTelG
import rcic.RcicAnnFrecDomSynG
import rcic.RcicAnnFrecArmG
import rcic.RcicAnnIotaWfG
import rcic.RcicAnnLRRowsG
/-!
# R-NoFunRec-1 step 1 (1c-ε2d-L3b-1): the extension world of a function-recursive field's inner binders

A telescope of inner binders is a Kripke world (`telWorldA`): its context is the telescope's, its
weakening the lift by the binders' count. At that world the bound variables are related to themselves
along the weakened Π-telescope (`argsRelKA_bvarsAg`), and a function-recursive field's domain and
induction-hypothesis binder are built telescopes over the same binders (`frecDomA_eq_piTelA`,
`frecIHA_eq_piTelA`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section World
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- THE BOUND VARIABLES ARE RELATED TO THEMSELVES ALONG THE WEAKENED TELESCOPE (R-NoFunRec-1 step 1
    (1c-ε2d-L3b-1)): at the world of a Π-telescope's own binders, the variables are a related argument
    list along the telescope lifted past them (`LRRelA_bvarg` at each binder). -/
theorem argsRelKA_bvarsAg (hE : EnvClosedA E) (hI : IotaLiftA I) (hIC : IotaConstHeadA I) (hK : PropKeyA E I n) {k : Nat}
    (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) → {Θ₁ : LCtxA} → TelTyA E I n Θ₁ ds →
    Nonempty (CtxWfA E I n (telCtxA ds ++ Θ₁)) → IsPiTelA ds.length (piTelA ds B w).1 →
    {R : ExprA → ExprA → Prop} →
    LRTyAg E I n ρ₀ k (telCtxA ds ++ Θ₁) (liftNA ds.length (piTelA ds B w).1) R →
    ArgsRelKAg E I n ρ₀ k (telCtxA ds ++ Θ₁) (liftNA ds.length (piTelA ds B w).1)
      (paramLocalsA ds.length) (paramLocalsA ds.length)
  | [], _, _, _, _, _, _ => .nil _
  | (D, u) :: ds, Θ₁, .cons _ _ _ _ hD tl, hΓ, hpi, R, hR => by
      have hlen : (telCtxA ((D, u) :: ds)).length = ds.length + 1 := by
        rw [telCtxA_length, List.length_cons]
      have hAty := hasTyA_liftN hE hI hD (telCtxA ((D, u) :: ds))
      rw [hlen, liftNA_sort, liftNA_eq] at hAty
      have hlk := lookupTypeA_telCtxA_head D u ds Θ₁
      have hpiE : liftNA (ds.length + 1) (piTelA ((D, u) :: ds) B w).1 =
          .pi (liftA 0 (ds.length + 1) D) u (liftA 1 (ds.length + 1) (piTelA ds B w).1)
            (piTelA ds B w).2 := by
        rw [liftNA_eq]; rfl
      simp only [List.length_cons] at hR ⊢
      rw [hpiE] at hR ⊢
      obtain ⟨hv, hpi'⟩ := hpi
      obtain ⟨⟨RD, hRD⟩, hcod⟩ := LRTyA_pi_peelg hΓ hR hv
      have hrel : LRRelAg E I n ρ₀ k (telCtxA ((D, u) :: ds) ++ Θ₁) (liftA 0 (ds.length + 1) D)
          (.bvar ds.length) (.bvar ds.length) :=
        LRRelA_bvarg hE hI hIC hK hΓ (lookupValueA_telCtxA_head D u ds Θ₁) ⟨RD, hRD⟩
          ⟨.bvar _ ds.length _ u hlk hAty⟩
      obtain ⟨RC, hRC⟩ := hcod _ _ hrel
      rw [instantiate0A_bvar_liftA_gap, ← liftNA_eq] at hRC
      refine .cons _ _ _ _ _ _ _ _ hrel ?_
      rw [instantiate0A_bvar_liftA_gap, ← liftNA_eq]
      have e := telCtxA_cons_append (D, u) ds Θ₁
      have := argsRelKA_bvarsAg hE hI hIC hK B w ds (Θ₁ := .assumption D :: Θ₁) tl
        (by rw [← e]; exact hΓ) hpi' (R := RC) (by rw [← e]; exact hRC)
      rw [← e] at this
      exact this

/-- THE VARIABLES, RELATED ALONG AN EQUAL TELESCOPE: if the Π-telescope `T` over the binders `ds` is
    valid and equal to `T'`, the bound variables are related to themselves along `T'` lifted past the
    binders (at the world `telWorldA ds`). -/
theorem argsRelKA_bvarsA_of_lrEqAg (hE : EnvClosedA E) (hEN : EnvNormClosedA E)
    (hNCT : EnvNormCtorTypeA E) (hI : IotaLiftA I) (hIC : IotaConstHeadA I) (hK : PropKeyA E I n)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) (B : ExprA) (w : Level)
    (hw : isZero w = false) {ds : List (ExprA × Level)} {s : Level}
    (hT : HasTyA E I n Γ (piTelA ds B w).1 (.sort s))
    (hv : ∃ R, LRTyAg E I n ρ₀ k Γ (piTelA ds B w).1 R) {T' : ExprA}
    (hT' : IsPiTelA ds.length T') (heq : LREqAg E I n ρ₀ k Γ (piTelA ds B w).1 T') :
    ArgsRelKAg E I n ρ₀ k (telCtxA ds ++ Γ) (liftNA ds.length T') (paramLocalsA ds.length)
      (paramLocalsA ds.length) := by
  obtain ⟨⟨tl⟩, -⟩ := telTyA_of_hasTy_piTelA B w ds hT
  have hok : WkOkA E I n (telWorldA ds) Γ := wkOkA_telWorldA tl hΓ
  obtain ⟨R, hR⟩ := hv
  obtain ⟨R', hR', -⟩ := LRTyA_wkg hE hEN hI hR (telWorldA ds) hok
  rw [wkCtxA_telWorldA, wkExprA_telWorldA] at hR'
  have hctx : Nonempty (CtxWfA E I n (telCtxA ds ++ Γ)) := by
    have := hok.2; rwa [wkCtxA_telWorldA] at this
  have hV := argsRelKA_bvarsAg hE hI hIC hK (ρ₀ := ρ₀) (k := k) B w ds tl hctx
    (isPiTelA_piTelA B w hw ds) hR'
  have hq := LREqA_wkg hE hEN hI heq (telWorldA ds) hok
  rw [wkCtxA_telWorldA, wkExprA_telWorldA, wkExprA_telWorldA] at hq
  exact argsRelKA_of_lrEqAg hNCT hctx hV (isPiTelA_liftN_aux ds.length _ (isPiTelA_piTelA B w hw ds))
    (isPiTelA_liftN_aux ds.length _ hT') (Nat.le_of_eq (paramLocalsA_length ds.length)) hq

/-- arguments related along a function-recursive field's domain are related along the induction
    hypothesis's binder at the field (they read the same inner binders). -/
theorem argsRelKA_frecDomA_closedg {k : Nat} {Γ : LCtxA} (f : Nat) (ls : List Level) (w : Level)
    (idx : List ExprA) (ds : List (ExprA × Level)) (pl : List ExprA) (σ : SubstA) (B' : ExprA)
    (w' : Level) {as as' : List ExprA}
    (h : ArgsRelKAg E I n ρ₀ k Γ (frecDomA f ls w pl σ ds idx).1 as as') (hl : as.length = ds.length) :
    ArgsRelKAg E I n ρ₀ k Γ (piTelA (substTelA σ ds) B' w').1 as as' := by
  rw [frecDomA_eq_piTelA] at h
  have := argsRelKA_piTelA_bodyg (E := E) (I := I) (n := n) (ρ₀ := ρ₀) _ B' w w' (substTelA σ ds)
    SubstA.id (by rwa [substA_id]) (by rw [substTelA_length]; exact hl)
  rwa [substA_id] at this

end World

#print axioms argsRelKA_bvarsAg
#print axioms argsRelKA_bvarsA_of_lrEqAg
#print axioms argsRelKA_frecDomA_closedg

end Rcic.Declarative.Ann

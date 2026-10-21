import rcic.RcicAnnFrecBeta
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
import rcic.RcicAnnFrecWorldG
import rcic.RcicAnnFrecArmG
import rcic.RcicAnnIotaWfG
import rcic.RcicAnnLRRowsG
/-!
# R-NoFunRec-1 step 1 (1c-ε2d-L3b-3b): a λ-telescope applied to its arguments, in substitution form

The λ-wrapped recursor call at a function-recursive field is a λ-telescope over the field domain's
inner binders. Its full application to related arguments is the call at those arguments: a chain of
typed β-steps, one per binder. The steps are built in substitution form — a λ-telescope under a typed
substitution `τ` is `lamTelA (substTelA τ ds) (substA (upNA m τ) b)` — by induction on the typed binders
(`lamTel_chain`), the head step lifted through the remaining applications from the explicit Π-telescope
(`tyHRedA_spine`), so no application inversion is needed. A weakening is such a substitution
(`wkSubstA`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section Beta
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- a chain at `A` expands the relation on the left. -/
theorem LRRelA_expand_chain_leftg (hE : EnvClosedA E) (hI : IotaLiftA I) {k : Nat} {Γ : LCtxA} {A : ExprA} :
    {a N : ExprA} → TmChainA E I n Γ A a N → ∀ {b : ExprA}, LRRelAg E I n ρ₀ k Γ A N b →
      LRRelAg E I n ρ₀ k Γ A a b
  | _, _, .refl _ _, _, h => h
  | _, _, .cons _ _ _ ha hs t, _, h =>
      LRRelA_expand_leftg hE hI ⟨⟨ha⟩, ⟨hs⟩⟩ (LRRelA_expand_chain_leftg hE hI t h)

/-- a chain at `A` expands the relation on the right. -/
theorem LRRelA_expand_chain_rightg (hE : EnvClosedA E) (hI : IotaLiftA I) {k : Nat} {Γ : LCtxA} {A : ExprA} :
    {b N : ExprA} → TmChainA E I n Γ A b N → ∀ {a : ExprA}, LRRelAg E I n ρ₀ k Γ A a N →
      LRRelAg E I n ρ₀ k Γ A a b
  | _, _, .refl _ _, _, h => h
  | _, _, .cons _ _ _ ha hs t, _, h =>
      LRRelA_expand_rightg hE hI ⟨⟨ha⟩, ⟨hs⟩⟩ (LRRelA_expand_chain_rightg hE hI t h)

/-- THE RELATION EXPANDS ALONG THE λ-TELESCOPE'S APPLICATION, on the left: related at the body under the
    arguments, the application is related there. -/
theorem lrRelA_lamTel_apps_leftg (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {k : Nat} {Θ : LCtxA} {ds : List (ExprA × Level)} (htel : TelTyA E I n Θ ds)
    {b B : ExprA} {w : Level} (hB : HasTyA E I n (telCtxA ds ++ Θ) B (.sort w))
    (hb : HasTyA E I n (telCtxA ds ++ Θ) b B) {Δ : LCtxA} (hΔ : CtxWfA E I n Δ) {τ : SubstA}
    (hτ : SubstTyA E I n Δ τ Θ) {as : List ExprA} (hl : as.length = ds.length)
    (hargs : ConvArgsA E I n Δ (substA τ (piTelA ds B w).1) as as) {y : ExprA}
    (h : LRRelAg E I n ρ₀ k Δ (substA (consListA as τ) B) (substA (consListA as τ) b) y) :
    LRRelAg E I n ρ₀ k Δ (substA (consListA as τ) B)
      (foldAppsA (lamTelA (substTelA τ ds) (substA (upNA ds.length τ) b)) as) y := by
  obtain ⟨c⟩ := lamTel_chain hE hI hR hIS htel hB hb hΔ hτ hl hargs
  exact LRRelA_expand_chain_leftg hE hI c h

/-- on the right, the chain at its own type moved to the relation's by a type conversion. -/
theorem lrRelA_lamTel_apps_rightg (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {k : Nat} {Θ : LCtxA} {ds : List (ExprA × Level)} (htel : TelTyA E I n Θ ds)
    {b B : ExprA} {w : Level} (hB : HasTyA E I n (telCtxA ds ++ Θ) B (.sort w))
    (hb : HasTyA E I n (telCtxA ds ++ Θ) b B) {Δ : LCtxA} (hΔ : CtxWfA E I n Δ) {τ : SubstA}
    (hτ : SubstTyA E I n Δ τ Θ) {as : List ExprA} (hl : as.length = ds.length)
    (hargs : ConvArgsA E I n Δ (substA τ (piTelA ds B w).1) as as) {A x : ExprA}
    (hc : Nonempty (TyConvA E I n Δ (substA (consListA as τ) B) A))
    (h : LRRelAg E I n ρ₀ k Δ A x (substA (consListA as τ) b)) :
    LRRelAg E I n ρ₀ k Δ A x
      (foldAppsA (lamTelA (substTelA τ ds) (substA (upNA ds.length τ) b)) as) := by
  obtain ⟨c⟩ := lamTel_chain hE hI hR hIS htel hB hb hΔ hτ hl hargs
  obtain ⟨c'⟩ := tmChainA_tyConv hc c
  exact LRRelA_expand_chain_rightg hE hI c' h

/-- RELATED ARGUMENTS TAKE TWO EQUAL VALID TELESCOPES TO EQUAL INSTANCES (R-NoFunRec-1 step 1
    (1c-ε2d-L3b-3c)): along `T`, then the left arguments at `T` and the right arguments at `T'`: the
    instances are equal. At each Π, the codomains' equality at the left argument twice (`eqKA_pi_invg`),
    then the right telescope's own codomain equality between the two related arguments. -/
theorem lrEqA_applyTelAg (hEN : EnvNormCtorTypeA E) {k : Nat} {Γ : LCtxA}
    (hΓ : Nonempty (CtxWfA E I n Γ)) :
    {T : ExprA} → {as as' : List ExprA} → ArgsRelKAg E I n ρ₀ k Γ T as as' → {T' : ExprA} → {len : Nat} →
    IsPiTelA len T → IsPiTelA len T' → as.length ≤ len → (∃ R, LRTyAg E I n ρ₀ k Γ T R) →
    LREqAg E I n ρ₀ k Γ T T' → ∀ {C C' : ExprA}, applyTelA as T = some C → applyTelA as' T' = some C' →
    LREqAg E I n ρ₀ k Γ C C'
  | _, _, _, .nil _, T', _, _, _, _, _, heq, C, C', hC, hC' => by
      injection hC with hC; injection hC' with hC'
      subst hC; subst hC'
      exact heq
  | _, _, _, .cons A u B v f f' fs fs' h hs, T', len, hpiL, hpiR, hlen, hv, heq, C, C', hC, hC' => by
      cases len with
      | zero => exact absurd hlen (Nat.not_succ_le_zero _)
      | succ len =>
          match T', hpiR with
          | .pi A' u' B' v', ⟨hv', hB'⟩ =>
              obtain ⟨hvL, hBL⟩ := hpiL
              have heq' := heq
              rw [LREqA_eqg] at heq'
              obtain ⟨_, _, _, hDeq, RD, hD, hCe⟩ := eqKA_pi_invg hvL heq'
              have hρ : WkOkA E I n [] Γ := ⟨trivial, hΓ⟩
              have hAA : LREqAg E I n ρ₀ k Γ A A' := by rw [LREqA_eqg]; exact hDeq [] hρ
              obtain ⟨R, hR, hff⟩ := LRRelA_refl_leftg hEN h
              have hD0 : LRTyAg E I n ρ₀ k Γ A (RD []) := by rw [LRTyA_eqg]; exact hD [] hρ
              rw [LRTyA_uniqueg hR hD0] at hff
              have hBB : LREqAg E I n ρ₀ k Γ (instantiate0A f B) (instantiate0A f B') := by
                rw [LREqA_eqg]; exact hCe [] hρ f f hff
              obtain ⟨R', hR'⟩ := LREqA_validg hEN heq hv
              rw [LRTyA_eqg] at hR'
              have hnp' : ¬ IsPropTy E I Γ (.pi A' u' B' v') := fun h' => by
                rw [(isPropTy_pi_iff E I Γ A' u' B' v').1 h'] at hv'
                cases hv'
              obtain ⟨RD', RC', hD', hC'', hCeq', _⟩ := tyKA_pi_invg hR' hnp'
              have hf' : LRRelAg E I n ρ₀ k Γ A' f f' := LRRelA_transport'g hEN hAA h
              obtain ⟨R'', hR'', hff'⟩ := hf'
              have hD0' : LRTyAg E I n ρ₀ k Γ A' (RD' []) := by rw [LRTyA_eqg]; exact hD' [] hρ
              rw [LRTyA_uniqueg hR'' hD0'] at hff'
              have hstep : LREqAg E I n ρ₀ k Γ (instantiate0A f B') (instantiate0A f' B') := by
                rw [LREqA_eqg]; exact hCeq' [] hρ f f' hff'
              obtain ⟨hv₁, hcod⟩ := LRTyA_pi_peelg hΓ (by rw [← LRTyA_eqg] at hR'; exact hR') hv'
              obtain ⟨R₀, hR₀⟩ := hv
              obtain ⟨_, hcodL⟩ := LRTyA_pi_peelg hΓ hR₀ hvL
              obtain ⟨RC₁, hRC₁⟩ := hcodL f f' h
              exact lrEqA_applyTelAg hEN hΓ hs (isPiTelA_instantiate len 0 f B hBL)
                (isPiTelA_instantiate len 0 f' B' hB') (Nat.le_of_succ_le_succ hlen) ⟨RC₁, hRC₁⟩
                (LREqA_transg hEN hBB hstep) hC hC'

/-- RIGHT ARGUMENTS OF RELATED ARGUMENTS ARE TYPED ALONG THE TELESCOPE with themselves substituted: the
    left tail's relation moves along the codomains' equality at the related pair. -/
theorem convArgsA_right_of_argsRelKAg (hEN : EnvNormCtorTypeA E) {k : Nat} {Γ : LCtxA}
    (hΓ : Nonempty (CtxWfA E I n Γ)) :
    {T : ExprA} → {as as' : List ExprA} → ArgsRelKAg E I n ρ₀ k Γ T as as' → {len : Nat} →
    IsPiTelA len T → as.length ≤ len → (∃ R, LRTyAg E I n ρ₀ k Γ T R) →
    Nonempty (ConvArgsA E I n Γ T as' as')
  | _, _, _, .nil _, _, _, _, _ => ⟨.nil _⟩
  | _, _, _, .cons A u B v f f' fs fs' h hs, len, hpi, hlen, hv => by
      cases len with
      | zero => exact absurd hlen (Nat.not_succ_le_zero _)
      | succ len =>
          obtain ⟨hvz, hBp⟩ := hpi
          obtain ⟨R₀, hR₀⟩ := hv
          have hρ : WkOkA E I n [] Γ := ⟨trivial, hΓ⟩
          have hR₀' := hR₀
          rw [LRTyA_eqg] at hR₀'
          have hnp : ¬ IsPropTy E I Γ (.pi A u B v) := fun h' => by
            rw [(isPropTy_pi_iff E I Γ A u B v).1 h'] at hvz
            cases hvz
          obtain ⟨RD, RC, hD, hC, hCeq, _⟩ := tyKA_pi_invg hR₀' hnp
          obtain ⟨R, hR, hff⟩ := h
          have hD0 : LRTyAg E I n ρ₀ k Γ A (RD []) := by rw [LRTyA_eqg]; exact hD [] hρ
          rw [LRTyA_uniqueg hR hD0] at hff
          have hstep : LREqAg E I n ρ₀ k Γ (instantiate0A f B) (instantiate0A f' B) := by
            rw [LREqA_eqg]; exact hCeq [] hρ f f' hff
          have hKt := argsRelKA_of_lrEqAg hEN hΓ hs (isPiTelA_instantiate len 0 f B hBp)
            (isPiTelA_instantiate len 0 f' B hBp) (Nat.le_of_succ_le_succ hlen) hstep
          obtain ⟨_, hcod⟩ := LRTyA_pi_peelg hΓ hR₀ hvz
          have hrr : LRRelAg E I n ρ₀ k Γ A f' f' :=
            LRRelA_refl_leftg hEN
              (LRRelA_symmg hEN ⟨R, hR, (by rw [LRTyA_uniqueg hR hD0]; exact hff)⟩)
          obtain ⟨RC', hRC'⟩ := hcod f' f' hrr
          obtain ⟨ih⟩ := convArgsA_right_of_argsRelKAg hEN hΓ hKt (isPiTelA_instantiate len 0 f' B hBp)
            (by rw [argsRelKA_lengthg hKt]; exact Nat.le_of_succ_le_succ (by
              rw [← argsRelKA_lengthg hs]; exact hlen)) ⟨RC', hRC'⟩
          obtain ⟨c⟩ := LRRelA_convg hrr
          exact ⟨.cons _ _ _ _ _ _ _ _ ⟨c⟩ ih⟩

/-- the same telescope: related non-empty argument lists take it to equal instances (the first step's
    codomain equality at the related pair is the telescope's own). -/
theorem lrEqA_applyTelA_selfg (hEN : EnvNormCtorTypeA E) {k : Nat} {Γ : LCtxA}
    (hΓ : Nonempty (CtxWfA E I n Γ)) :
    {T : ExprA} → {as as' : List ExprA} → ArgsRelKAg E I n ρ₀ k Γ T as as' → {len : Nat} →
    IsPiTelA len T → 0 < as.length → as.length ≤ len → (∃ R, LRTyAg E I n ρ₀ k Γ T R) →
    ∀ {C C' : ExprA}, applyTelA as T = some C → applyTelA as' T = some C' →
    LREqAg E I n ρ₀ k Γ C C'
  | _, _, _, .nil _, _, _, h0, _, _, _, _, _, _ => absurd h0 (Nat.lt_irrefl 0)
  | _, _, _, .cons A u B v f f' fs fs' h hs, len, hpi, _, hlen, hv, C, C', hC, hC' => by
      cases len with
      | zero => exact absurd hlen (Nat.not_succ_le_zero _)
      | succ len =>
          obtain ⟨hvz, hBp⟩ := hpi
          obtain ⟨R₀, hR₀⟩ := hv
          have hρ : WkOkA E I n [] Γ := ⟨trivial, hΓ⟩
          have hR₀' := hR₀
          rw [LRTyA_eqg] at hR₀'
          have hnp : ¬ IsPropTy E I Γ (.pi A u B v) := fun h' => by
            rw [(isPropTy_pi_iff E I Γ A u B v).1 h'] at hvz
            cases hvz
          obtain ⟨RD, RC, hD, hC₀, hCeq, _⟩ := tyKA_pi_invg hR₀' hnp
          obtain ⟨R, hR, hff⟩ := h
          have hD0 : LRTyAg E I n ρ₀ k Γ A (RD []) := by rw [LRTyA_eqg]; exact hD [] hρ
          rw [LRTyA_uniqueg hR hD0] at hff
          have hstep : LREqAg E I n ρ₀ k Γ (instantiate0A f B) (instantiate0A f' B) := by
            rw [LREqA_eqg]; exact hCeq [] hρ f f' hff
          obtain ⟨_, hcod⟩ := LRTyA_pi_peelg hΓ hR₀ hvz
          obtain ⟨RC₁, hRC₁⟩ := hcod f f' ⟨R, hR, (by rw [LRTyA_uniqueg hR hD0]; exact hff)⟩
          exact lrEqA_applyTelAg hEN hΓ hs (isPiTelA_instantiate len 0 f B hBp)
            (isPiTelA_instantiate len 0 f' B hBp) (Nat.le_of_succ_le_succ hlen) ⟨RC₁, hRC₁⟩ hstep hC hC'

/-- related arguments along a telescope are pointwise convertible along it (escape at each step). -/
theorem convArgsA_of_argsRelKAg {k : Nat} {Γ : LCtxA} : ∀ {T : ExprA} {xs ys : List ExprA},
    ArgsRelKAg E I n ρ₀ k Γ T xs ys → ConvArgsA E I n Γ T xs ys
  | _, _, _, .nil T => .nil T
  | _, _, _, .cons A u B v f f' fs fs' h hs =>
      .cons A u B v f f' fs fs' (LRRelA_convg h) (convArgsA_of_argsRelKAg hs)

end Beta

#print axioms LRRelA_expand_chain_leftg
#print axioms LRRelA_expand_chain_rightg
#print axioms lrRelA_lamTel_apps_leftg
#print axioms lrRelA_lamTel_apps_rightg
#print axioms lrEqA_applyTelAg
#print axioms convArgsA_of_argsRelKAg
#print axioms lrEqA_applyTelA_selfg

#print axioms convArgsA_right_of_argsRelKAg

end Rcic.Declarative.Ann

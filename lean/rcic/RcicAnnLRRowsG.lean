import rcic.RcicAnnLRRows
import rcic.RcicAnnLRFundBindG
/-!
# DT-025/A-6 S1-g.2 — the guarded fundamental theorem in the judgment's own context

THE IDENTITY PAIR IS VALID (`ValidSubstA_idg`), hence every typed term is related to
itself at its type in its own context (`fund_selfg`), and every conversion relates its
sides (`fund_convg`) — over the guarded relation `TyKAg`. The two Type-level rows main's
`RcicAnnLRRows` derives from these are pass-1 facts and are NOT copied (call main's).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section Rows
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-! ## (1) the identity pair -/

theorem ValidSubstA_extg {k : Nat} {Δ Γ : LCtxA} {σ τ σ' τ' : SubstA}
    (hσ : ∀ i, σ i = τ i) (hσ' : ∀ i, σ' i = τ' i) (h : ValidSubstAg E I n ρ₀ k Δ σ σ' Γ) :
    ValidSubstAg E I n ρ₀ k Δ τ τ' Γ := by
  refine ⟨fun i A hA => ?_, fun i A v hA hv => ?_⟩
  · have := h.1 i A hA
    rw [substA_ext hσ A, substA_ext hσ' A, hσ i, hσ' i] at this
    exact this
  · have := h.2 i A v hA hv
    rw [substA_ext hσ A, substA_ext hσ v, substA_ext hσ' v, hσ i] at this
    exact this

/-- the identity pair is valid in a well-formed context, above a height of its derivation. -/
theorem ValidSubstA_idg (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I) (hS : EnvSemAg E I n ρ₀)
    (hρ : PosValA ρ₀) (hK : PropKeyA E I n) :
    {Γ : LCtxA} → CtxWfA E I n Γ →
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ValidSubstAg E I n ρ₀ k Γ SubstA.id SubstA.id Γ
  | _, .nil => ⟨0, fun _ _ => ValidSubstA_nilg [] SubstA.id SubstA.id⟩
  | _, .assumption (Γ := Γ) (A := A) (u := u) hΓ hA => by
      obtain ⟨k₁, h₁⟩ := ValidSubstA_idg hE hI hIS hEN hNC hR hS hρ hK hΓ
      obtain ⟨k₂, h₂⟩ := (fundAg hE hI hIS hEN hNC hR hS hρ hK).1 hA
      refine ⟨max k₁ k₂, fun k hk => ?_⟩
      have hid := h₁ k (le_max_of_le₁ hk)
      have hAA := (h₂ k (le_max_of_le₂ hk) Γ SubstA.id SubstA.id ⟨hΓ⟩ hid).2
      simp only [substA_id] at hAA
      obtain ⟨heA, hvA, _, tA, _, _⟩ := LRRelA_sort_elimg hAA
      have heA' : LREqAg E I n ρ₀ k Γ (substA SubstA.id A) (substA SubstA.id A) := by
        rw [substA_id]; exact heA
      have hvA' : ∃ R, LRTyAg E I n ρ₀ k Γ (substA SubstA.id A) R := by rw [substA_id]; exact hvA
      have tA' : Nonempty (HasTyA E I n Γ (substA SubstA.id A) (.sort u)) := by rw [substA_id]; exact tA
      have := ValidSubstA_upg hE hI hEN hNC (iotaConstHeadA_of_recHead hR) hK ⟨hΓ⟩ hid heA' hvA' tA'
      rw [substA_id] at this
      exact ValidSubstA_extg SubstA.id_up SubstA.id_up this
  | _, .letBinding (Γ := Γ) (A := A) (v := v) (u := u) hΓ hA hv => by
      obtain ⟨k₁, h₁⟩ := ValidSubstA_idg hE hI hIS hEN hNC hR hS hρ hK hΓ
      obtain ⟨k₂, h₂⟩ := (fundAg hE hI hIS hEN hNC hR hS hρ hK).1 hA
      obtain ⟨k₃, h₃⟩ := (fundAg hE hI hIS hEN hNC hR hS hρ hK).1 hv
      refine ⟨max k₁ (max k₂ k₃), fun k hk => ?_⟩
      have hid := h₁ k (le_max_of_le₁ hk)
      have hAA := (h₂ k (le_max_of_le₁ (le_max_of_le₂ hk)) Γ SubstA.id SubstA.id ⟨hΓ⟩ hid).2
      have hvv := (h₃ k (le_max_of_le₂ (le_max_of_le₂ hk)) Γ SubstA.id SubstA.id ⟨hΓ⟩ hid).2
      simp only [substA_id] at hAA hvv
      obtain ⟨heA, _, _, tA, _, _⟩ := LRRelA_sort_elimg hAA
      have heA' : LREqAg E I n ρ₀ k Γ (substA SubstA.id A) (substA SubstA.id A) := by
        rw [substA_id]; exact heA
      have hvv' : LRRelAg E I n ρ₀ k Γ (substA SubstA.id A) (substA SubstA.id v) (substA SubstA.id v) := by
        rw [substA_id, substA_id]; exact hvv
      have tA' : Nonempty (HasTyA E I n Γ (substA SubstA.id A) (.sort u)) := by rw [substA_id]; exact tA
      have := ValidSubstA_upLetg hE hI hEN hNC ⟨hΓ⟩ hid heA' hvv' tA'
      rw [substA_id, substA_id] at this
      exact ValidSubstA_extg SubstA.id_up SubstA.id_up this

/-! ## (2) the corollaries: the theorem in the judgment's own context -/

theorem fund_selfg (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I) (hS : EnvSemAg E I n ρ₀)
    (hρ : PosValA ρ₀) (hK : PropKeyA E I n)
    {Γ : LCtxA} {e A : ExprA} (hΓ : CtxWfA E I n Γ) (h : HasTyA E I n Γ e A) :
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → LRRelAg E I n ρ₀ k Γ A e e := by
  obtain ⟨k₁, h₁⟩ := ValidSubstA_idg hE hI hIS hEN hNC hR hS hρ hK hΓ
  obtain ⟨k₂, h₂⟩ := (fundAg hE hI hIS hEN hNC hR hS hρ hK).1 h
  refine ⟨max k₁ k₂, fun k hk => ?_⟩
  have := (h₂ k (le_max_of_le₂ hk) Γ SubstA.id SubstA.id ⟨hΓ⟩ (h₁ k (le_max_of_le₁ hk))).2
  simpa only [substA_id] using this

theorem fund_convg (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I) (hS : EnvSemAg E I n ρ₀)
    (hρ : PosValA ρ₀) (hK : PropKeyA E I n)
    {Γ : LCtxA} {a b A : ExprA} (hΓ : CtxWfA E I n Γ) (h : ConvA E I n Γ a b A) :
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → LRRelAg E I n ρ₀ k Γ A a b := by
  obtain ⟨k₁, h₁⟩ := ValidSubstA_idg hE hI hIS hEN hNC hR hS hρ hK hΓ
  obtain ⟨k₂, h₂⟩ := (fundAg hE hI hIS hEN hNC hR hS hρ hK).2 h
  refine ⟨max k₁ k₂, fun k hk => ?_⟩
  have := (h₂ k (le_max_of_le₂ hk) Γ SubstA.id SubstA.id ⟨hΓ⟩ (h₁ k (le_max_of_le₁ hk))).2
  simpa only [substA_id] using this

/-! ## (3) inversion of the type equality at a Type-level pi (restored for E2, which calls it;
    by the copy rule it mentions `EqKA`) -/

theorem eqKA_pi_invg {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA}
    {D : ExprA} {u : Level} {C : ExprA} {v : Level} {D' : ExprA} {u' : Level} {C' : ExprA} {v' : Level}
    (hz : isZero v = false) (h : EqKAg E I n ρ₀ k LE LT Γ (.pi D u C v) (.pi D' u' C' v')) :
    eqN u u' ∧ eqN v v' ∧ Nonempty (HasTyA E I n Γ D (.sort u)) ∧
    (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D')) ∧
    ∃ RD : WkSpecA → ExprA → ExprA → Prop,
      (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ)) ∧
      (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C'))) := by
  cases h with
  | sort hA _ _ _ _ =>
      have e := whTyA_det hA (whTyA_self hA) (hStepFnA_sort E I.fn Γ _) (hStepFnA_pi E I.fn Γ D u C v)
      cases e
  | pi hA hB hu hv hDty _ _ _ RD hD hDeq hC _ =>
      have e1 := whTyA_det hA (whTyA_self hA) (hStepFnA_pi E I.fn Γ _ _ _ _) (hStepFnA_pi E I.fn Γ D u C v)
      have e2 := whTyA_det hB (whTyA_self hB) (hStepFnA_pi E I.fn Γ _ _ _ _) (hStepFnA_pi E I.fn Γ D' u' C' v')
      cases e1; cases e2
      exact ⟨hu, hv, hDty, hDeq, RD, hD, hC⟩
  | fam hA _ hnA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA (whTyA_self hA) hnA (hStepFnA_pi E I.fn Γ D u C v)
      exact absurd e (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | stuck hA _ hN _ _ =>
      have e := whTyA_det hA (whTyA_self hA) hN.1 (hStepFnA_pi E I.fn Γ D u C v)
      subst e
      have := (isPropTy_pi_iff E I Γ D u C v).1 (tripleLikeA_pi_isProp hN)
      rw [this] at hz
      cases hz

end Rows

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.ValidSubstA_idg
#print axioms Rcic.Declarative.Ann.fund_selfg
#print axioms Rcic.Declarative.Ann.fund_convg
#print axioms Rcic.Declarative.Ann.eqKA_pi_invg

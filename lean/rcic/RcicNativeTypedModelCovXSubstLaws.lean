import rcic.RcicNativeTypedModelCovXInterface

/-!
# Structural and K-free model transport for the new substitution package

These operations rearrange already supplied edges. They consume no type
observation or type-view existence theorem. The environment model transport
composes the landed covariant typing and let-coherence transport laws.
It does not identify the old and new recursive relations.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovRelAudit
open TypedModelKTransportAudit TypedModelKFragmentAudit TypedModelKAudit TypedModelKIndexFreeAudit

variable {E : ResolvedEnv} {C : CovTyping E} {M N : CtxModelT E}
  {R : Readback} {n : Nat}

/-- A diagonal uses an existing diagonal edge, not relation reflexivity. -/
theorem RelSubstAtCovX.diagL {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (h : RelSubstAtCovX C M R n Δ ρ ρ' σ σ' Γ) :
    RelSubstAtCovX C M R n Δ ρ ρ σ σ Γ where
  typedL := h.typedL
  typedR := h.typedL
  conv := fun i A hA => by
    obtain ⟨hi⟩ := h.typedL.1 i A hA
    exact ⟨.refl _ _ _ hi⟩
  envL := h.envL
  envR := h.envL
  vars := by
    intro i A hA c hc
    have hr := (h.vars i A hA c (Or.inl (hc.elim id id))).2.2.1
    exact ⟨hr, hr, hr, hr⟩
  lets := by
    intro i v A hv hA c hc
    have obs : ρ i c ∨ ρ' i c ∨ M.Ap ρ v c ∨ M.Ap ρ' v c := by
      rcases hc with hc | hc | hc | hc
      · exact Or.inl hc
      · exact Or.inl hc
      · exact Or.inr (Or.inr (Or.inl hc))
      · exact Or.inr (Or.inr (Or.inl hc))
    have hr := (h.lets i v A hv hA c obs).2.2.1
    exact ⟨hr, hr, hr, hr⟩

/-- Re-pairing the two supplied valuations retains all four edges and both
coherence guards; it never asserts a new model observation. -/
theorem RelSubstAtCovX.envs {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (h : RelSubstAtCovX C M R n Δ ρ ρ' σ σ' Γ)
    (θ θ' : EnvT) (hθ : θ = ρ ∨ θ = ρ') (hθ' : θ' = ρ ∨ θ' = ρ') :
    RelSubstAtCovX C M R n Δ θ θ' σ σ' Γ := by
  have varSide : ∀ η, η = ρ ∨ η = ρ' → ∀ i c, η i c → ρ i c ∨ ρ' i c := by
    intro η he i c hc
    rcases he with rfl | rfl
    · exact Or.inl hc
    · exact Or.inr hc
  have valSide : ∀ η, η = ρ ∨ η = ρ' → ∀ v c,
      M.Ap η v c → M.Ap ρ v c ∨ M.Ap ρ' v c := by
    intro η he v c hc
    rcases he with rfl | rfl
    · exact Or.inl hc
    · exact Or.inr hc
  have envSide : ∀ η, η = ρ ∨ η = ρ' → EnvTypedCovAtP C M Γ η := by
    intro η he
    rcases he with rfl | rfl
    · exact h.envL
    · exact h.envR
  refine ⟨h.typedL, h.typedR, h.conv, envSide θ hθ, envSide θ' hθ', ?_, ?_⟩
  · intro i A hA c hc
    exact h.vars i A hA c (hc.elim (varSide θ hθ i c) (varSide θ' hθ' i c))
  · intro i v A hv hA c hc
    apply h.lets i v A hv hA c
    rcases hc with hc | hc | hc | hc
    · exact (varSide θ hθ i c hc).imp_right Or.inl
    · exact (varSide θ' hθ' i c hc).imp_right Or.inl
    · exact Or.inr (Or.inr (valSide θ hθ v c hc))
    · exact Or.inr (Or.inr (valSide θ' hθ' v c hc))

/-- The model changes only at the landed environment guards and let gate. -/
theorem RelSubstAtCovX.modelMap {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (h : RelSubstAtCovX C M R n Δ ρ ρ' σ σ' Γ)
    (hB : ∀ i, ModelAgreementAtT M N (.bvar i))
    (hV : ValueAgreementT M N Γ) (hT : TypeAgreementT M N Γ) :
    RelSubstAtCovX C N R n Δ ρ ρ' σ σ' Γ where
  typedL := h.typedL
  typedR := h.typedR
  conv := h.conv
  envL := (envTypedCovAtP_congr hB hV hT).mp h.envL
  envR := (envTypedCovAtP_congr hB hV hT).mp h.envR
  vars := h.vars
  lets := fun i v A hv hA c hc => h.lets i v A hv hA c
    ((or_congr Iff.rfl (or_congr Iff.rfl
      (or_congr (hV i v hv ρ c) (hV i v hv ρ' c)))).mpr hc)

theorem relSubstAtCovX_congr {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (hB : ∀ i, ModelAgreementAtT M N (.bvar i))
    (hV : ValueAgreementT M N Γ) (hT : TypeAgreementT M N Γ) :
    RelSubstAtCovX C M R n Δ ρ ρ' σ σ' Γ ↔
      RelSubstAtCovX C N R n Δ ρ ρ' σ σ' Γ :=
  ⟨fun h => h.modelMap hB hV hT,
    fun h => h.modelMap (fun i => modelAgreementAtT_symm (hB i))
      (fun i v hv => modelAgreementAtT_symm (hV i v hv))
      (fun i A hA => modelAgreementAtT_symm (hT i A hA))⟩

/-- K-free equivalence transports observations and coherent environments,
while retaining the new relation on both sides of the equivalence. -/
theorem relSubstAtCovX_approxTK_iff_of_kFree {Ξ Δ Γ : LCtx}
    {ρ ρ' : EnvT} {σ σ' : SubstT}
    (hV : KFreeValuesT E Γ) (hT : KFreeTypesT E Γ) :
    RelSubstAtCovX C (ctxModelT_approxTK E n Ξ) R n Δ ρ ρ' σ σ' Γ ↔
      RelSubstAtCovX C (ctxModelT_approxT E) R n Δ ρ ρ' σ σ' Γ :=
  relSubstAtCovX_congr (fun i => modelAgreementAtT_kFree (kFreeT_bvar E i))
    (valueAgreementT_approxTK_of_kFree hV) (typeAgreementT_approxTK_of_kFree hT)

theorem fundTyAtCovX_approxTK_iff_of_kFree {Ξ Γ : LCtx} {e A : Expr Nat}
    (hV : KFreeValuesT E Γ) (hT : KFreeTypesT E Γ) (he : KFreeT E e) :
    FundTyAtCovX C (ctxModelT_approxTK E n Ξ) R n Γ e A ↔
      FundTyAtCovX C (ctxModelT_approxT E) R n Γ e A := by
  have hm := modelAgreementAtT_kFree (n := n) (Γ := Ξ) he
  constructor
  · intro h Δ ρ ρ' σ σ' hΔ hSub c hc
    exact h hΔ ((relSubstAtCovX_approxTK_iff_of_kFree hV hT).mpr hSub) c
      ((or_congr (hm ρ c) (hm ρ' c)).mpr hc)
  · intro h Δ ρ ρ' σ σ' hΔ hSub c hc
    exact h hΔ ((relSubstAtCovX_approxTK_iff_of_kFree hV hT).mp hSub) c
      ((or_congr (hm ρ c) (hm ρ' c)).mp hc)

theorem fundConvAtCovX_approxTK_iff_of_kFree {Ξ Γ : LCtx} {a b A : Expr Nat}
    (hV : KFreeValuesT E Γ) (hT : KFreeTypesT E Γ)
    (ha : KFreeT E a) (hb : KFreeT E b) :
    FundConvAtCovX C (ctxModelT_approxTK E n Ξ) R n Γ a b A ↔
      FundConvAtCovX C (ctxModelT_approxT E) R n Γ a b A := by
  have hma := modelAgreementAtT_kFree (n := n) (Γ := Ξ) ha
  have hmb := modelAgreementAtT_kFree (n := n) (Γ := Ξ) hb
  constructor
  · intro h Δ ρ ρ' σ σ' hΔ hSub c hc
    exact h hΔ ((relSubstAtCovX_approxTK_iff_of_kFree hV hT).mpr hSub) c
      ((or_congr (hma ρ c) (hmb ρ' c)).mpr hc)
  · intro h Δ ρ ρ' σ σ' hΔ hSub c hc
    exact h hΔ ((relSubstAtCovX_approxTK_iff_of_kFree hV hT).mp hSub) c
      ((or_congr (hma ρ c) (hmb ρ' c)).mp hc)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_SUBST_LAWS_ROOTS
#print axioms RelSubstAtCovX.diagL
#print axioms RelSubstAtCovX.envs
#print axioms RelSubstAtCovX.modelMap
#print axioms relSubstAtCovX_congr
#print axioms relSubstAtCovX_approxTK_iff_of_kFree
#print axioms fundTyAtCovX_approxTK_iff_of_kFree
#print axioms fundConvAtCovX_approxTK_iff_of_kFree
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_SUBST_LAWS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXAudit

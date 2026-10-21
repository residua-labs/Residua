import rcic.RcicNativeTypedModelCovYEnvironment

/-!
# Related substitutions with hereditary environment typing

Every stored square carries ONE actual semantic code for all four edges.
That is an explicit strengthened package field, not an inferred coherence
theorem for existentially chosen relation codes. The two substitution
instances of the native type are both retained. Both environment fields use
the hereditary entry target, and both actual `CtxEnvM` fields survive.

The structural operations below rearrange stored evidence only. They do not
derive native conversion symmetry from relation symmetry or silently assume
model substitution or raw type observation laws. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovRelAudit

variable {E : ResolvedEnv} {C : CovTyping E} {Q : LCtx → CtxModelT E}
  {R : Readback} {n : Nat}

/-- Four actual edges share their displayed type-code witness, while the
native type index remains the appropriate substitution instance on each side. -/
def CovYSquare (C : CovTyping E) (R : Readback) (n : Nat) (Δ : LCtx)
    (x x' y y' A A' : Expr Nat) (c : CptT) : Prop :=
  ∃ a : CptT,
    LRSCoreCovY C R n Δ x y' A c a ∧ LRSCoreCovY C R n Δ x' y A' c a ∧
    LRSCoreCovY C R n Δ x y A c a ∧ LRSCoreCovY C R n Δ x' y' A' c a

theorem CovYSquare.swap {Δ : LCtx} {x x' y y' A A' : Expr Nat} {c : CptT}
    (h : CovYSquare C R n Δ x x' y y' A A' c) :
    CovYSquare C R n Δ x' x y' y A' A c := by
  obtain ⟨a, h₁, h₂, h₃, h₄⟩ := h
  exact ⟨a, h₂, h₁, h₄, h₃⟩

theorem CovYSquare.diagL {Δ : LCtx} {x x' y y' A A' : Expr Nat} {c : CptT}
    (h : CovYSquare C R n Δ x x' y y' A A' c) :
    CovYSquare C R n Δ x x y y A A c := by
  obtain ⟨a, _, _, hxy, _⟩ := h
  exact ⟨a, hxy, hxy, hxy, hxy⟩

theorem covYSquare_bot (C : CovTyping E) (R : Readback) (n : Nat) (Δ : LCtx)
    (x x' y y' A A' : Expr Nat) : CovYSquare C R n Δ x x' y y' A A' .bot :=
  ⟨.bot, lrSCoreCovY_bot C _ _ _ _ _, lrSCoreCovY_bot C _ _ _ _ _,
    lrSCoreCovY_bot C _ _ _ _ _, lrSCoreCovY_bot C _ _ _ _ _⟩

/-- The repaired package keeps native substitution and conversion, two
hereditary source environments, and all four variable/let edges. -/
structure RelSubstAtCovY (C : CovTyping E) (Q : LCtx → CtxModelT E) (R : Readback)
    (n : Nat) (Δ : LCtx) (ρ ρ' : EnvT) (σ σ' : SubstT) (Γ : LCtx) : Prop where
  typedL : TypedSubstT E n Δ σ Γ
  typedR : TypedSubstT E n Δ σ' Γ
  conv : ConvSubstT E n Δ σ σ' Γ
  envL : EnvTypedCovYAt C Q R n Γ ρ
  envR : EnvTypedCovYAt C Q R n Γ ρ'
  vars : ∀ i A, lookupType Γ i = some A → ∀ c, ρ i c ∨ ρ' i c →
    CovYSquare C R n Δ (σ i) (σ' i) (σ i) (σ' i) (substT σ A) (substT σ' A) c
  lets : ∀ i v A, lookupValue Γ i = some v → lookupType Γ i = some A →
    ∀ c, ρ i c ∨ ρ' i c ∨ (Q Γ).Ap ρ v c ∨ (Q Γ).Ap ρ' v c →
    CovYSquare C R n Δ (σ i) (σ' i) (substT σ v) (substT σ' v)
      (substT σ A) (substT σ' A) c

theorem RelSubstAtCovY.ctxEnvs {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (h : RelSubstAtCovY C Q R n Δ ρ ρ' σ σ' Γ) :
    CtxEnvM (Q Γ) Γ ρ ∧ CtxEnvM (Q Γ) Γ ρ' := ⟨h.envL.2, h.envR.2⟩

/-- The empty package reuses landed native evidence and has no normalization
or code-coherence premise. -/
theorem relSubstAtCovY_nil (C : CovTyping E) (Q : LCtx → CtxModelT E) (R : Readback)
    (n : Nat) (Δ : LCtx) (ρ ρ' : EnvT) (σ σ' : SubstT) :
    RelSubstAtCovY C Q R n Δ ρ ρ' σ σ' [] := by
  have old := TypedModelCovXAudit.relSubstAtCovX_nil C (Q []) R n Δ ρ ρ' σ σ'
  exact ⟨old.typedL, old.typedR, old.conv,
    envTypedCovYAt_nil C Q R n ρ, envTypedCovYAt_nil C Q R n ρ',
    fun _ _ h => Option.noConfusion h, fun _ _ _ h => Option.noConfusion h⟩

/-- Native reverse conversion is supplied separately. Semantic edge reversal
only swaps the stored square and its common code witness. -/
theorem RelSubstAtCovY.swap {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (h : RelSubstAtCovY C Q R n Δ ρ ρ' σ σ' Γ)
    (hrev : ConvSubstT E n Δ σ' σ Γ) : RelSubstAtCovY C Q R n Δ ρ' ρ σ' σ Γ where
  typedL := h.typedR
  typedR := h.typedL
  conv := hrev
  envL := h.envR
  envR := h.envL
  vars := fun i A hA c hc => (h.vars i A hA c hc.symm).swap
  lets := by
    intro i v A hv hA c hc
    apply CovYSquare.swap
    apply h.lets i v A hv hA c
    rcases hc with hl | hr | hl | hr
    · exact Or.inr (Or.inl hl)
    · exact Or.inl hr
    · exact Or.inr (Or.inr (Or.inr hl))
    · exact Or.inr (Or.inr (Or.inl hr))

/-- The diagonal edge is already stored; no reflexivity of a relation at
an independently chosen semantic code is needed. -/
theorem RelSubstAtCovY.diagL {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (h : RelSubstAtCovY C Q R n Δ ρ ρ' σ σ' Γ) :
    RelSubstAtCovY C Q R n Δ ρ ρ σ σ Γ where
  typedL := h.typedL
  typedR := h.typedL
  conv := fun i A hA => by
    obtain ⟨ht⟩ := h.typedL.1 i A hA
    exact ⟨.refl _ _ _ ht⟩
  envL := h.envL
  envR := h.envL
  vars := fun i A hA c hc => (h.vars i A hA c (Or.inl (hc.elim id id))).diagL
  lets := by
    intro i v A hv hA c hc
    apply CovYSquare.diagL
    apply h.lets i v A hv hA c
    rcases hc with hl | hr | hl | hr
    · exact Or.inl hl
    · exact Or.inl hr
    · exact Or.inr (Or.inr (Or.inl hl))
    · exact Or.inr (Or.inr (Or.inl hr))

/-- The environments may be re-paired from the two actual supplied choices.
All let observations still pass through their original source-model gate. -/
theorem RelSubstAtCovY.envs {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (h : RelSubstAtCovY C Q R n Δ ρ ρ' σ σ' Γ)
    (θ θ' : EnvT) (hθ : θ = ρ ∨ θ = ρ') (hθ' : θ' = ρ ∨ θ' = ρ') :
    RelSubstAtCovY C Q R n Δ θ θ' σ σ' Γ := by
  have envSide : ∀ η, η = ρ ∨ η = ρ' → EnvTypedCovYAt C Q R n Γ η := by
    intro η he
    rcases he with rfl | rfl
    · exact h.envL
    · exact h.envR
  have obsSide : ∀ (P : EnvT → Prop) η, η = ρ ∨ η = ρ' → P η → P ρ ∨ P ρ' := by
    intro P η he hp
    exact he.elim (fun hη => Or.inl (hη ▸ hp)) (fun hη => Or.inr (hη ▸ hp))
  refine ⟨h.typedL, h.typedR, h.conv, envSide θ hθ, envSide θ' hθ', ?_, ?_⟩
  · intro i A hA c hc
    exact h.vars i A hA c (hc.elim
      (obsSide (fun η => η i c) θ hθ) (obsSide (fun η => η i c) θ' hθ'))
  · intro i v A hv hA c hc
    apply h.lets i v A hv hA c
    rcases hc with hl | hr | hl | hr
    · exact (obsSide (fun η => η i c) θ hθ hl).imp_right Or.inl
    · exact (obsSide (fun η => η i c) θ' hθ' hr).imp_right Or.inl
    · exact Or.inr (Or.inr (obsSide (fun η => (Q Γ).Ap η v c) θ hθ hl))
    · exact Or.inr (Or.inr (obsSide (fun η => (Q Γ).Ap η v c) θ' hθ' hr))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_SUBST_ROOTS
#print axioms CovYSquare
#print axioms CovYSquare.swap
#print axioms CovYSquare.diagL
#print axioms covYSquare_bot
#print axioms RelSubstAtCovY
#print axioms RelSubstAtCovY.ctxEnvs
#print axioms relSubstAtCovY_nil
#print axioms RelSubstAtCovY.swap
#print axioms RelSubstAtCovY.diagL
#print axioms RelSubstAtCovY.envs
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_SUBST_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYAudit

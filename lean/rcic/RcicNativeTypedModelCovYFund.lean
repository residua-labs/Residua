import rcic.RcicNativeTypedModelCovYSubst
import rcic.RcicNativeTypedModelCovYTransport
import rcic.RcicNativeTypedModelCovXActions

/-!
# Fundamental motives over hereditary source environments

The indexed relation is kept explicit. `CovYRelated` merely hides an actual
finite code; it has no asserted code-coherence or PER theorem. The source
environment fields and actual let coherence are those of `RelSubstAtCovY`.

These motives assert relatedness. A same-code hereditary escape is separately
measured, rather than smuggled into the variable case: the environment-entry
code and the relation square's code are different stored witnesses in general.
The concrete controls supply their complete relation and realization results
at a common actual code. Consumers below are not general constructor supplies.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovRelAudit
open TypedModelCovNormSubstAudit TypedModelCovXAudit

variable {E : ResolvedEnv} {C : CovTyping E} {Q : LCtx → CtxModelT E}
  {R : Readback} {n : Nat}

/-- An actual finite code witness, without an existential-code PER claim. -/
def CovYRelated (C : CovTyping E) (R : Readback) (n : Nat) (Γ : LCtx)
    (x y A : Expr Nat) (c : CptT) : Prop :=
  ∃ a : CptT, LRSCoreCovY C R n Γ x y A c a

theorem covYRelated_bot (C : CovTyping E) (Γ : LCtx) (x y A : Expr Nat) :
    CovYRelated C R n Γ x y A .bot :=
  ⟨.bot, lrSCoreCovY_bot C Γ x y A .bot⟩

theorem covYRelated_type_readback_iff (C : CovTyping E)
    (hL : ReadbackLaws E R) (hD : DetR R)
    {Γ : LCtx} {A A₀ x y : Expr Nat} (hr : RedR R Γ A A₀) (c : CptT) :
    CovYRelated C R n Γ x y A c ↔ CovYRelated C R n Γ x y A₀ c := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, (lrSCoreCovY_type_readback_iff C hL hD hr c a).mp h⟩
  · rintro ⟨a, h⟩
    exact ⟨a, (lrSCoreCovY_type_readback_iff C hL hD hr c a).mpr h⟩

theorem covYRelated_expand_red_both (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {x x' y y' A : Expr Nat} {c : CptT}
    (hx : RedR R Γ x x') (hy : RedR R Γ y y')
    (h : CovYRelated C R n Γ x' y' A c) : CovYRelated C R n Γ x y A c := by
  obtain ⟨a, h⟩ := h
  exact ⟨a, lrSCoreCovY_expand_red_both C hL a hx hy h⟩

def FundTyAtCovY (C : CovTyping E) (Q : LCtx → CtxModelT E) (R : Readback)
    (n : Nat) (Γ : LCtx) (e A : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCovY C Q R n Δ ρ ρ' σ σ' Γ →
    ∀ c, (Q Γ).Ap ρ e c ∨ (Q Γ).Ap ρ' e c →
      CovYRelated C R n Δ (substT σ e) (substT σ' e) (substT σ A) c

def FundConvAtCovY (C : CovTyping E) (Q : LCtx → CtxModelT E) (R : Readback)
    (n : Nat) (Γ : LCtx) (x y A : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCovY C Q R n Δ ρ ρ' σ σ' Γ →
    ∀ c, (Q Γ).Ap ρ x c ∨ (Q Γ).Ap ρ' y c →
      CovYRelated C R n Δ (substT σ x) (substT σ' y) (substT σ A) c

/-- The global target is named, not supplied by the concrete controls. -/
def FundamentalCovYAt (C : CovTyping E) (Q : LCtx → CtxModelT E)
    (R : Readback) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {e A : Expr Nat},
    HasTyT E n Γ e A → FundTyAtCovY C Q R n Γ e A) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {x y A : Expr Nat},
    ConvT E n Γ x y A → FundConvAtCovY C Q R n Γ x y A)

/-- Stronger concrete suppliers may retain one literal code for all target
contexts, substitutions, and either-side observations. -/
def FundTyCodeAtCovY (C : CovTyping E) (Q : LCtx → CtxModelT E) (R : Readback)
    (n : Nat) (Γ : LCtx) (e A : Expr Nat) (a : CptT) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCovY C Q R n Δ ρ ρ' σ σ' Γ →
    ∀ c, (Q Γ).Ap ρ e c ∨ (Q Γ).Ap ρ' e c →
      LRSCoreCovY C R n Δ (substT σ e) (substT σ' e) (substT σ A) c a

def FundConvCodeAtCovY (C : CovTyping E) (Q : LCtx → CtxModelT E) (R : Readback)
    (n : Nat) (Γ : LCtx) (x y A : Expr Nat) (a : CptT) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCovY C Q R n Δ ρ ρ' σ σ' Γ →
    ∀ c, (Q Γ).Ap ρ x c ∨ (Q Γ).Ap ρ' y c →
      LRSCoreCovY C R n Δ (substT σ x) (substT σ' y) (substT σ A) c a

theorem fundTyAtCovY_of_code {Γ : LCtx} {e A : Expr Nat} {a : CptT}
    (h : FundTyCodeAtCovY C Q R n Γ e A a) : FundTyAtCovY C Q R n Γ e A :=
  fun hΔ hS c hc => ⟨a, h hΔ hS c hc⟩

theorem fundConvAtCovY_of_code {Γ : LCtx} {x y A : Expr Nat} {a : CptT}
    (h : FundConvCodeAtCovY C Q R n Γ x y A a) : FundConvAtCovY C Q R n Γ x y A :=
  fun hΔ hS c hc => ⟨a, h hΔ hS c hc⟩

/-- The first stored square edge supplies variables; the hereditary source
guard is retained without converting it back to a raw guard. -/
theorem fundCovY_bvar {Γ : LCtx} (hM : CovAtomicModelLaws (Q Γ))
    (i : Nat) (A : Expr Nat) (hA : lookupType Γ i = some A) :
    FundTyAtCovY C Q R n Γ (.bvar i) A := by
  intro Δ ρ ρ' σ σ' _ hS c hc
  have ho : c = .bot ∨ ρ i c ∨ ρ' i c :=
    hc.elim (fun h => (hM.bvar_inv h).imp_right Or.inl)
      (fun h => (hM.bvar_inv h).imp_right Or.inr)
  rcases ho with rfl | hv
  · exact covYRelated_bot C _ _ _ _
  · obtain ⟨a, h, _⟩ := hS.vars i A hA c hv
    exact ⟨a, h⟩

theorem fundCovY_refl {Γ : LCtx} {x A : Expr Nat}
    (h : FundTyAtCovY C Q R n Γ x A) : FundConvAtCovY C Q R n Γ x x A := h

/-- Local zeta uses the actual let square and actual source-model evidence. -/
theorem fundCovY_zetaLocal {Γ : LCtx} (hM : CovAtomicModelLaws (Q Γ))
    {i : Nat} {v A : Expr Nat} (hv : lookupValue Γ i = some v)
    (hA : lookupType Γ i = some A) : FundConvAtCovY C Q R n Γ (.bvar i) v A := by
  intro Δ ρ ρ' σ σ' _ hS c hc
  rcases hc with ho | ho
  · rcases hM.bvar_inv ho with rfl | hvar
    · exact covYRelated_bot C _ _ _ _
    · obtain ⟨a, h, _⟩ := hS.lets i v A hv hA c (Or.inl hvar)
      exact ⟨a, h⟩
  · obtain ⟨a, h, _⟩ := hS.lets i v A hv hA c (Or.inr (Or.inr (Or.inr ho)))
    exact ⟨a, h⟩

/-- A supplied old sort leaf transports by composition. Its actual code gate
comes from the displayed old view, never from an untested typing hypothesis. -/
theorem covYRelated_of_covX_sort (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) {Γ : LCtx} {A x y : Expr Nat} {l : Level} {c : CptT}
    (hr : RedR R Γ A (.sort l)) (h : LRSCoreCovX C R n Γ x y A c) :
    CovYRelated C R n Γ x y A c := by
  have hv := (lrSCoreCovX_iff_at_view C hL hNU (.sort l hr) c).mp h
  refine ⟨sortCode l, lrSCoreCovY_of_old_leaf C ?_ hv.1 hv.2⟩
  intro d g he
  rcases sortCode_prop_or_sort l with hp | hs
  · rw [hp] at he; cases he
  · rw [hs] at he; cases he

/-- The full atomic sort case composes the imported proof at an empty source
package. Its construction never requires a raw guard for the new context. -/
theorem fundCovY_sort (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hS : CovTypingIncludesS C) {Γ : LCtx} (hM : CovAtomicModelLaws (Q Γ)) (l : Level) :
    FundTyAtCovY C Q R n Γ (.sort l) (.sort (.succ l)) := by
  intro Δ ρ ρ' σ σ' hΔ _ c hc
  apply covYRelated_of_covX_sort C hL hNU (.refl _)
  exact fundCovX_sort (R := R) hM hS (Γ := []) l hΔ
    (relSubstAtCovX_nil C (Q Γ) R n Δ ρ ρ' σ σ') c hc

theorem fundCovY_sorts (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hS : CovTypingIncludesS C) {Γ : LCtx} (hM : CovAtomicModelLaws (Q Γ))
    (l l' : Level) :
    FundConvAtCovY C Q R n Γ (.sort l) (.sort l') (.sort (.succ l)) := by
  intro Δ ρ ρ' σ σ' hΔ _ c hc
  apply covYRelated_of_covX_sort C hL hNU (.refl _)
  exact fundCovX_sorts (R := R) hM hS (Γ := []) l l' hΔ
    (relSubstAtCovX_nil C (Q Γ) R n Δ ρ ρ' σ σ') c hc

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_FUND_ROOTS
#print axioms CovYRelated
#print axioms covYRelated_bot
#print axioms covYRelated_type_readback_iff
#print axioms covYRelated_expand_red_both
#print axioms FundTyAtCovY
#print axioms FundConvAtCovY
#print axioms FundamentalCovYAt
#print axioms FundTyCodeAtCovY
#print axioms FundConvCodeAtCovY
#print axioms fundTyAtCovY_of_code
#print axioms fundConvAtCovY_of_code
#print axioms fundCovY_bvar
#print axioms fundCovY_refl
#print axioms fundCovY_zetaLocal
#print axioms covYRelated_of_covX_sort
#print axioms fundCovY_sort
#print axioms fundCovY_sorts
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_FUND_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYAudit

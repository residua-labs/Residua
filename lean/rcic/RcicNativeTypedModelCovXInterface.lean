import rcic.RcicNativeTypedModelCovXCoherence
import rcic.RcicNativeTypedModelCovXPER
import rcic.RcicNativeTypedModelCovXExpansion
import rcic.RcicNativeTypedModelCovNormSubst

/-!
# Extensional relation interface and guarded related substitutions

This is a new candidate interface, not a restatement of a landed theorem.
The native substitution and covariant environment components are unchanged;
the four variable/let edges use the new relation. In particular both actual
`CtxEnvM` guards are retained. Native reverse conversion is an explicit input
to swapping a package; the finite-view PER does not manufacture it.

The fundamental motives keep observations at either endpoint. Existence of
finite views is not assumed globally. The finite-view experiment is tested
separately, so defining these motives is not counted as supplying a case.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovRelAudit
open TypedModelCovNormSubstAudit

variable {E : ResolvedEnv} {C : CovTyping E} {M : CtxModelT E}
  {R : Readback} {n : Nat}

/-- The wrapper inherits symmetry constructively from its actual view. -/
theorem lrSCoreCovX_symm (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {x y A : Expr Nat} {c : CptT}
    (h : LRSCoreCovX C R n Γ x y A c) : LRSCoreCovX C R n Γ y x A c := by
  rcases h with hb | ⟨v, hv⟩
  · exact Or.inl hb
  · exact lrSCoreCovX_of_view C v (lrSCoreCovXAt_symm C hL hNU hW hS hT v hΓ hv)

/-- Two existential view witnesses compose by the proved coherence theorem.
No middle-term observation or raw type compact is needed. -/
theorem lrSCoreCovX_trans (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {x y z A : Expr Nat} {c : CptT}
    (hxy : LRSCoreCovX C R n Γ x y A c)
    (hyz : LRSCoreCovX C R n Γ y z A c) : LRSCoreCovX C R n Γ x z A c := by
  rcases hxy with hb | ⟨v, hv⟩
  · exact Or.inl hb
  · exact lrSCoreCovX_of_view C v (lrSCoreCovXAt_trans C hL hNU hW hS hT v hΓ hv
      ((lrSCoreCovX_iff_at_view C hL hNU v c).mp hyz))

/-- Endpoint expansion is inherited without choosing a new type view. -/
theorem lrSCoreCovX_expand_red_both (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {x x' y y' A : Expr Nat} {c : CptT}
    (hx : RedR R Γ x x') (hy : RedR R Γ y y')
    (h : LRSCoreCovX C R n Γ x' y' A c) : LRSCoreCovX C R n Γ x y A c := by
  rcases h with hb | ⟨v, hv⟩
  · exact Or.inl hb
  · exact lrSCoreCovX_of_view C v (lrSCoreCovXAt_expand_red_both C hL v hx hy hv)

/-- Four edges, at the two actual substitution instances of the type. -/
def CovXSquare (C : CovTyping E) (R : Readback) (n : Nat) (Δ : LCtx)
    (x x' y y' A A' : Expr Nat) (c : CptT) : Prop :=
  LRSCoreCovX C R n Δ x y' A c ∧ LRSCoreCovX C R n Δ x' y A' c ∧
  LRSCoreCovX C R n Δ x y A c ∧ LRSCoreCovX C R n Δ x' y' A' c

theorem CovXSquare.swap {Δ : LCtx} {x x' y y' A A' : Expr Nat} {c : CptT}
    (h : CovXSquare C R n Δ x x' y y' A A' c) :
    CovXSquare C R n Δ x' x y' y A' A c :=
  ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

/-- Related substitutions retain the landed native and environment guards.
Only their semantic edges have changed. -/
structure RelSubstAtCovX (C : CovTyping E) (M : CtxModelT E) (R : Readback)
    (n : Nat) (Δ : LCtx) (ρ ρ' : EnvT) (σ σ' : SubstT) (Γ : LCtx) : Prop where
  typedL : TypedSubstT E n Δ σ Γ
  typedR : TypedSubstT E n Δ σ' Γ
  conv : ConvSubstT E n Δ σ σ' Γ
  envL : EnvTypedCovAtP C M Γ ρ
  envR : EnvTypedCovAtP C M Γ ρ'
  vars : ∀ i A, lookupType Γ i = some A → ∀ c, ρ i c ∨ ρ' i c →
    CovXSquare C R n Δ (σ i) (σ' i) (σ i) (σ' i) (substT σ A) (substT σ' A) c
  lets : ∀ i v A, lookupValue Γ i = some v → lookupType Γ i = some A →
    ∀ c, ρ i c ∨ ρ' i c ∨ M.Ap ρ v c ∨ M.Ap ρ' v c →
    CovXSquare C R n Δ (σ i) (σ' i) (substT σ v) (substT σ' v)
      (substT σ A) (substT σ' A) c

theorem RelSubstAtCovX.ctxEnvs {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (h : RelSubstAtCovX C M R n Δ ρ ρ' σ σ' Γ) :
    CtxEnvM M Γ ρ ∧ CtxEnvM M Γ ρ' := ⟨h.envL.2, h.envR.2⟩

/-- Empty-context native and environment components are reused from the
landed package. There is no view or normalization premise here. -/
theorem relSubstAtCovX_nil (C : CovTyping E) (M : CtxModelT E) (R : Readback)
    (n : Nat) (Δ : LCtx) (ρ ρ' : EnvT) (σ σ' : SubstT) :
    RelSubstAtCovX C M R n Δ ρ ρ' σ σ' [] := by
  have h := relSubstAtCov_nil C M R n Δ ρ ρ' σ σ'
  exact ⟨h.typedL, h.typedR, h.conv, h.envL, h.envR,
    fun _ _ he => Option.noConfusion he, fun _ _ _ he => Option.noConfusion he⟩

/-- Package reversal separates native conversion from semantic edge reversal.
This theorem does not claim the reverse-native premise is a new supplier. -/
theorem RelSubstAtCovX.swap {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (h : RelSubstAtCovX C M R n Δ ρ ρ' σ σ' Γ)
    (hrev : ConvSubstT E n Δ σ' σ Γ) : RelSubstAtCovX C M R n Δ ρ' ρ σ' σ Γ where
  typedL := h.typedR
  typedR := h.typedL
  conv := hrev
  envL := h.envR
  envR := h.envL
  vars := fun i A hA c hc => (h.vars i A hA c hc.symm).swap
  lets := by
    intro i v A hv hA c hc
    apply CovXSquare.swap (h.lets i v A hv hA c ?_)
    rcases hc with hc | hc | hc | hc
    · exact Or.inr (Or.inl hc)
    · exact Or.inl hc
    · exact Or.inr (Or.inr (Or.inr hc))
    · exact Or.inr (Or.inr (Or.inl hc))

/-- The typing motive tests the new relation at the substituted native type. -/
def FundTyAtCovX (C : CovTyping E) (M : CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) (e A : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCovX C M R n Δ ρ ρ' σ σ' Γ →
    ∀ c, M.Ap ρ e c ∨ M.Ap ρ' e c →
      LRSCoreCovX C R n Δ (substT σ e) (substT σ' e) (substT σ A) c

/-- Neither endpoint is required to have the other's compact observation. -/
def FundConvAtCovX (C : CovTyping E) (M : CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) (a b A : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCovX C M R n Δ ρ ρ' σ σ' Γ →
    ∀ c, M.Ap ρ a c ∨ M.Ap ρ' b c →
      LRSCoreCovX C R n Δ (substT σ a) (substT σ' b) (substT σ A) c

def FundamentalCovXAt (C : CovTyping E) (M : CtxModelT E) (R : Readback)
    (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {e A : Expr Nat},
    HasTyT E n Γ e A → FundTyAtCovX C M R n Γ e A) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {a b A : Expr Nat},
    ConvT E n Γ a b A → FundConvAtCovX C M R n Γ a b A)

/-- Variables use the retained four-edge package, with no type observation. -/
theorem fundCovX_bvar (hM : CovAtomicModelLaws M) {Γ : LCtx}
    (i : Nat) (A : Expr Nat) (hA : lookupType Γ i = some A) :
    FundTyAtCovX C M R n Γ (.bvar i) A := by
  intro Δ ρ ρ' σ σ' _ hS c hc
  have ho : c = .bot ∨ ρ i c ∨ ρ' i c :=
    hc.elim (fun h => (hM.bvar_inv h).imp_right Or.inl)
      (fun h => (hM.bvar_inv h).imp_right Or.inr)
  exact ho.elim (fun hb => Or.inl hb) (fun hv => (hS.vars i A hA c hv).1)

/-- Refl consumes exactly its native typing child. -/
theorem fundCovX_refl {Γ : LCtx} {a A : Expr Nat}
    (h : FundTyAtCovX C M R n Γ a A) : FundConvAtCovX C M R n Γ a a A := h

/-- Local zeta reads the let edge already present in the coherent package. -/
theorem fundCovX_zetaLocal (hM : CovAtomicModelLaws M) {Γ : LCtx}
    {i : Nat} {v A : Expr Nat} (hv : lookupValue Γ i = some v)
    (hA : lookupType Γ i = some A) : FundConvAtCovX C M R n Γ (.bvar i) v A := by
  intro Δ ρ ρ' σ σ' _ hS c hc
  rcases hc with ho | ho
  · rcases hM.bvar_inv ho with hb | hvar
    · exact Or.inl hb
    · exact (hS.lets i v A hv hA c (Or.inl hvar)).1
  · exact (hS.lets i v A hv hA c (Or.inr (Or.inr (Or.inr ho)))).1

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_INTERFACE_ROOTS
#print axioms lrSCoreCovX_symm
#print axioms lrSCoreCovX_trans
#print axioms lrSCoreCovX_expand_red_both
#print axioms CovXSquare
#print axioms CovXSquare.swap
#print axioms RelSubstAtCovX
#print axioms RelSubstAtCovX.ctxEnvs
#print axioms relSubstAtCovX_nil
#print axioms RelSubstAtCovX.swap
#print axioms FundTyAtCovX
#print axioms FundConvAtCovX
#print axioms FundamentalCovXAt
#print axioms fundCovX_bvar
#print axioms fundCovX_refl
#print axioms fundCovX_zetaLocal
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_INTERFACE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXAudit

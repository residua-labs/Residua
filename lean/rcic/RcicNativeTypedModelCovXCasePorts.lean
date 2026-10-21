import rcic.RcicNativeTypedModelCovXSubstLaws
import rcic.RcicNativeTypedModelCovXActions
import rcic.RcicNativeTypedModelCovXBoundary

/-!
# Exact surviving conversion ports after extensional Pi

These are algebraic consumers of already supplied child motives. They do
not assert a complete constructor step or an induction hypothesis at a
generated derivation. In a native induction the callers must supply those
motives from the actual children.

Fixed-type PER removes the old raw observed-type and type-diagonal ports.
It does not manufacture native type-index transport, reverse native
substitution conversion, or observations of a transitivity middle term.
The ports below name those distinctions explicitly. Their reflexive/sort
controls are supplied; no general supplier is claimed.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovRelAudit TypedModelKAudit

variable {E : ResolvedEnv} {C : CovTyping E} {M : CtxModelT E}
  {R : Readback} {n : Nat}

/-- A type-index transport at the exact substitutions consumed by a case.
There is no raw type-observation premise. -/
def CovXTypeTransportFor (C : CovTyping E) (M : CtxModelT E) (R : Readback)
    (n : Nat) (Γ : LCtx) (A B : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCovX C M R n Δ ρ ρ' σ σ' Γ →
    CovXTypeTransportAt C R n Δ (substT σ A) (substT σ B)

theorem covXTypeTransportFor_refl (C : CovTyping E) (M : CtxModelT E)
    (R : Readback) (n : Nat) (Γ : LCtx) (A : Expr Nat) :
    CovXTypeTransportFor C M R n Γ A A := by
  intro Δ ρ ρ' σ σ' hΔ hSub x y c h
  exact h

/-- Source observation coverage needed to use both genuine conversion
children. This is a model-only condition, not a relation-edge conclusion. -/
def CovXMiddleObservationFor (C : CovTyping E) (M : CtxModelT E) (R : Readback)
    (n : Nat) (Γ : LCtx) (x y z : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCovX C M R n Δ ρ ρ' σ σ' Γ →
    ∀ c, M.Ap ρ x c ∨ M.Ap ρ' z c → M.Ap ρ y c ∨ M.Ap ρ' y c

theorem covXMiddleObservationFor_refl (C : CovTyping E) (M : CtxModelT E)
    (R : Readback) (n : Nat) (Γ : LCtx) (a : Expr Nat) :
    CovXMiddleObservationFor C M R n Γ a a a := by
  intro Δ ρ ρ' σ σ' hΔ hSub c h
  exact h

/-- Semantic type conversion needs its exact relation type transport,
not the refuted raw observation port. -/
theorem fundTyAtCovX_type_transport {Γ : LCtx} {e A B : Expr Nat}
    (hT : CovXTypeTransportFor C M R n Γ A B)
    (he : FundTyAtCovX C M R n Γ e A) : FundTyAtCovX C M R n Γ e B := by
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  exact hT hΔ hSub _ _ c (he hΔ hSub c hc)

theorem fundConvAtCovX_type_transport {Γ : LCtx} {x y A B : Expr Nat}
    (hT : CovXTypeTransportFor C M R n Γ A B)
    (he : FundConvAtCovX C M R n Γ x y A) : FundConvAtCovX C M R n Γ x y B := by
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  exact hT hΔ hSub _ _ c (he hΔ hSub c hc)

/-- Symmetry consumes reverse native substitution conversion and type
transport from the right substitution instance. Neither is inferred from
the fixed-index PER. -/
theorem fundConvAtCovX_symm_of_ports (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Γ : LCtx} {x y A : Expr Nat}
    (hRev : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
      RelSubstAtCovX C M R n Δ ρ ρ' σ σ' Γ → ConvSubstT E n Δ σ' σ Γ)
    (hType : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
      RelSubstAtCovX C M R n Δ ρ ρ' σ σ' Γ →
      CovXTypeTransportAt C R n Δ (substT σ' A) (substT σ A))
    (hChild : FundConvAtCovX C M R n Γ x y A) : FundConvAtCovX C M R n Γ y x A := by
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  have hxy := hChild hΔ (hSub.swap (hRev hΔ hSub)) c hc.symm
  exact hType hΔ hSub _ _ c (lrSCoreCovX_symm C hL hNU hW hS hT hΔ hxy)

/-- Fundamental transitivity retains middle observation coverage even
though relation transitivity itself has no such premise. -/
theorem fundConvAtCovX_trans_of_middle (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Γ : LCtx} {x y z A : Expr Nat}
    (hMid : CovXMiddleObservationFor C M R n Γ x y z)
    (hLeft : FundConvAtCovX C M R n Γ x y A)
    (hRight : FundConvAtCovX C M R n Γ y z A) : FundConvAtCovX C M R n Γ x z A := by
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  have compose : ∀ θ, θ = ρ ∨ θ = ρ' → M.Ap θ y c →
      LRSCoreCovX C R n Δ (substT σ x) (substT σ' z) (substT σ A) c := by
    intro θ hθ ho
    have hp := hSub.envs θ θ hθ hθ
    exact lrSCoreCovX_trans C hL hNU hW hS hT hΔ
      (hLeft hΔ hp.diagL c (Or.inr ho)) (hRight hΔ hp c (Or.inl ho))
  exact (hMid hΔ hSub c hc).elim (compose ρ (Or.inl rfl)) (compose ρ' (Or.inr rfl))

/-- The type/middle ports are fully inhabited at an actual nonbottom sort
observation, in any target context and under the unchanged model. This is
not an Eq/Nat inhabitant of the separately retained global PER premises. -/
theorem covX_sort_ports_control (C : CovTyping E) (n : Nat) (Ξ : LCtx) :
    CovXTypeTransportFor C (ctxModelT_approxTK E n Ξ) R n []
      (.sort (.succ .zero)) (.sort (.succ .zero)) ∧
    CovXMiddleObservationFor C (ctxModelT_approxTK E n Ξ) R n []
      (.sort .zero) (.sort .zero) (.sort .zero) ∧
    RelSubstAtCovX C (ctxModelT_approxTK E n Ξ) R n []
      EnvT.bot EnvT.bot SubstT.id SubstT.id [] ∧
    ApproxTK E n Ξ EnvT.bot (.sort .zero) .prop ∧ (.prop : CptT) ≠ .bot := by
  refine ⟨covXTypeTransportFor_refl C _ R n [] _,
    covXMiddleObservationFor_refl C _ R n [] _,
    relSubstAtCovX_nil C _ R n [] _ _ _ _, ?_, fun h => CptT.noConfusion h⟩
  simpa only [sortCode_zero] using approxTK_sort_code E n Ξ EnvT.bot .zero

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_CASE_PORTS_ROOTS
#print axioms CovXTypeTransportFor
#print axioms covXTypeTransportFor_refl
#print axioms CovXMiddleObservationFor
#print axioms covXMiddleObservationFor_refl
#print axioms fundTyAtCovX_type_transport
#print axioms fundConvAtCovX_type_transport
#print axioms fundConvAtCovX_symm_of_ports
#print axioms fundConvAtCovX_trans_of_middle
#print axioms covX_sort_ports_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_CASE_PORTS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXAudit

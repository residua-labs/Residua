import rcic.RcicF8DTileViaS
import rcic.RcicF8XValleyVia

/-!
The single D-owned partial ViaS interface and its total D1 realization.
#7257 consumes these names; it must not redeclare them. No X traversal or
supplier demand changes here. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure
open Rcic.Syn
variable {E : ResolvedEnv} {n : Nat}

abbrev DProcViaSP (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {a b c T : Expr Nat}, CtxWfViaS E n Γ →
    EvParStar R Γ a b T → EvParStar R Γ a c T →
    Option (Σ' d : Expr Nat, EvParStar R Γ b d T × EvParStar R Γ c d T)

def DContractViaSP (D : ∀ R : List (Jd E n), DProcViaSP R) : Prop :=
  ∀ R {Γ : LCtx} {a b c T : Expr Nat} (v : CtxWfViaS E n Γ)
    (s₁ : EvParStar R Γ a b T) (s₂ : EvParStar R Γ a c T)
    (out : Σ' d : Expr Nat, EvParStar R Γ b d T × EvParStar R Γ c d T),
    D R v s₁ s₂ = some out → ∀ ℓ ∈ out.2.1.leaves ++ out.2.2.leaves,
      ∃ k ∈ s₁.leaves ++ s₂.leaves, SubEq ℓ k

def DProcViaSP.toWfP (D : ∀ R : List (Jd E n), DProcViaSP R) :
    ∀ R : List (Jd E n), DProcWfP R :=
  fun R {_ _ _ _ _} hΓ s₁ s₂ => D R (.ofWf hΓ) s₁ s₂

theorem DContractViaSP.toWfP {D : ∀ R : List (Jd E n), DProcViaSP R}
    (hD : DContractViaSP D) : DContractWfP (DProcViaSP.toWfP D) := by
  intro R Γ a b c T hΓ s₁ s₂ out hout
  exact hD R (.ofWf hΓ) s₁ s₂ out hout

/-- Canonical supplier: a positive answer on every ViaS source input. -/
def d1ViaSP (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) :
    ∀ R : List (Jd E n), DProcViaSP R :=
  fun _ {_ _ _ _ _} v s₁ s₂ => some (dProcViaS hW su v s₁ s₂)

theorem d1ViaSP_contract (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) :
    DContractViaSP (d1ViaSP hW su) := by
  intro R Γ a b c T v s₁ s₂ out hout
  cases Option.some.inj hout
  exact dContractViaS hW su R v s₁ s₂

/-- Coverage is independent of the conditional leaf contract. -/
theorem d1ViaSP_some (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) {Γ : LCtx} (v : CtxWfViaS E n Γ) {a b c T : Expr Nat}
    (s₁ : EvParStar R Γ a b T) (s₂ : EvParStar R Γ a c T) :
    d1ViaSP hW su R v s₁ s₂ = some (dProcViaS hW su v s₁ s₂) := rfl

theorem d1ViaSP_ofWf (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b c T : Expr Nat}
    (s₁ : EvParStar R Γ a b T) (s₂ : EvParStar R Γ a c T) :
    d1ViaSP hW su R (.ofWf hΓ) s₁ s₂ = some (dProcWf hW su hΓ s₁ s₂) := rfl

theorem d1ViaSP_toWfP (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) :
    DProcViaSP.toWfP (d1ViaSP hW su) = d1WfP hW su := rfl

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.DProcViaSP
#print axioms Rcic.Declarative.F8Measure.DContractViaSP
#print axioms Rcic.Declarative.F8Measure.DProcViaSP.toWfP
#print axioms Rcic.Declarative.F8Measure.DContractViaSP.toWfP
#print axioms Rcic.Declarative.F8Measure.d1ViaSP
#print axioms Rcic.Declarative.F8Measure.d1ViaSP_contract
#print axioms Rcic.Declarative.F8Measure.d1ViaSP_some
#print axioms Rcic.Declarative.F8Measure.d1ViaSP_ofWf
#print axioms Rcic.Declarative.F8Measure.d1ViaSP_toWfP

import rcic.RcicF8CtxWfViaS

/-!
The ONE source-context D object (#7267). Only the premise of the Π producer
travels along the stack. The five-arm table, step reader and structural fold
are shared with D1. No target execution supplies source data. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure
open Rcic.Syn
variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- WK-2 supplies the one context-sensitive row, using source payloads. -/
def structPiJoinAtViaS (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (v : CtxWfViaS E n Γ) : StructPiJoinAt R Γ :=
  ⟨structPiJoinViaS hW su v, structPiJoinViaS_sound hW su v⟩

/-- The shared table read at the original source. -/
def dStepDiamondViaS (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (v : CtxWfViaS E n Γ) : DStepDiamondAt R Γ :=
  dStepDiamondAt (structPiJoinAtViaS hW su v)

/-- Total D on all stars of the landed five-kind carrier, at their source. -/
def dProcViaS (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (v : CtxWfViaS E n Γ) {a b c T : Expr Nat}
    (s₁ : EvParStar R Γ a b T) (s₂ : EvParStar R Γ a c T) :
    Σ' d : Expr Nat, EvParStar R Γ b d T × EvParStar R Γ c d T :=
  dProcAt (dStepDiamondViaS hW su v) s₁ s₂

/-- Every closing leaf remains supported by the original source inputs. -/
theorem dContractViaS (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (R : List (Jd E n)) {Γ : LCtx} (v : CtxWfViaS E n Γ) {a b c T : Expr Nat}
    (s₁ : EvParStar R Γ a b T) (s₂ : EvParStar R Γ a c T) :
    ∀ ℓ ∈ (dProcViaS hW su v s₁ s₂).2.1.leaves ++
      (dProcViaS hW su v s₁ s₂).2.2.leaves,
      ∃ k ∈ s₁.leaves ++ s₂.leaves, SubEq ℓ k :=
  dContractAt (dStepDiamondViaS hW su v) s₁ s₂

/-- Complete payload-bearing sigma agreement, by definitional equality. -/
theorem dProcViaS_ofWf (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b c T : Expr Nat}
    (s₁ : EvParStar R Γ a b T) (s₂ : EvParStar R Γ a c T) :
    dProcViaS hW su (.ofWf hΓ) s₁ s₂ = dProcWf hW su hΓ s₁ s₂ := rfl

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.structPiJoinAtViaS
#print axioms Rcic.Declarative.F8Measure.dStepDiamondViaS
#print axioms Rcic.Declarative.F8Measure.dProcViaS
#print axioms Rcic.Declarative.F8Measure.dContractViaS
#print axioms Rcic.Declarative.F8Measure.dProcViaS_ofWf

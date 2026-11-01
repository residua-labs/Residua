import rcic.RcicF3RecFieldMaskRules
import rcic.RcicF3RecFieldMaskLambda

/-!
# The bounded typing induction produces recursive-local masking

The proof recurses on the actual HasTyT derivation, retaining every
original LOKt/LOKc edge and both original fitting environments. Its
syntactic mode is a conclusion selector, not an assumed classification.
The lambda case uses one fixed body mode at all reached arguments. Let
values are first compared at their clean actual annotation; conversion
transports the two original decoded types.

A bounded clean type therefore has the same denotation at the original
and masked assignments. No fit is claimed for the masked assignment. The
local Context input records actual recursive lookup Origins; constructing
it from a complete admitted normalized tuple, and extracting typed
normalized domains from all reader traces, are separate composition
steps. This theorem is bounded at the supplied full sigma and K, not an
all-universe-vector frame producer. Full terminal keys are unrestricted.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldMask
open Rcic.Declarative RawFamily RecFieldOrigin

/-- Every branch is produced from the original typed rule. No semantic
classification callback and no masked fitting environment is supplied. -/
theorem of_typing (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n) :
    {Γ : LCtx} → {e A : Expr Nat} → (d : HasTyT E n Γ e A) → LOKt σ 4 K d →
    (marks : Marks) → (ρ η : Nat → PSet.{4}) →
    Fits (mkM P (table P μ fd C)) σ Γ ρ →
    Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρ →
    Context P μ fd C σ marks Γ ρ η → occursConst fd.fref e = false →
    Holds P μ fd C σ marks ρ η e A
  | _, _, _, .sort _ _, _, _, _, _, _, _, _, _ => Equiv.rfl
  | Γ, _, _, .bvar _ i A hi, _, marks, ρ, η, _, _, hctx, _ =>
      bvar P μ fd C σ marks Γ ρ η hctx i A hi
  | _, _, _, .const _ _ _ _ _ _ _, _, _, _, _, _, _, _, _ => Equiv.rfl
  | Γ, _, _, .pi _ A u B v dA dB, hd, marks, ρ, η, hρC, hρD, hctx, hfree => by
      have hfree' : occursConst fd.fref A = false ∧ occursConst fd.fref B = false :=
        Bool.or_eq_false_iff.mp hfree
      let MC := mkM P (table P μ fd C)
      let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
      have rA := of_typing P μ fd C σ K hEC hED dA hd.2.2.1
        marks ρ η hρC hρD hctx hfree'.1
      have eA := typed_type P μ fd C σ K hEC marks ρ η hρC dA hd.2.2.1 rA
      have sameA : den MC σ ρ A = den MD σ ρ A :=
        PiIndependent.den_free P μ fd.fref (ofFrame P μ fd C)
          (ofFrame P μ fd (RawFamilyEnlarge.enlarge fd C)) σ A hfree'.1 ρ
      change Equiv (piVal MC (den MC σ ρ A) (fun x => den MC σ (vcons x ρ) B))
        (piVal MC (den MC σ η A) (fun x => den MC σ (vcons x η) B))
      apply piVal_congr_on MC eA (den_resp MC σ ρ B) (den_resp MC σ η B)
      intro x hx
      have hxD : x ∈ Ed MD (den MD σ ρ A) := by
        change x ∈ Ed MC (den MD σ ρ A)
        rw [← sameA]
        exact hx
      have hfC : Fits MC σ (.assumption A :: Γ) (vcons x ρ) := ⟨hρC, hx⟩
      have hfD : Fits MD σ (.assumption A :: Γ) (vcons x ρ) := ⟨hρD, hxD⟩
      have hr := context_ordinary P μ fd C σ marks Γ ρ η hctx
        (.assumption A) x x Equiv.rfl
      have rB := of_typing P μ fd C σ K hEC hED dB hd.2.2.2
        (ordinary marks) (vcons x ρ) (vcons x η) hfC hfD hr hfree'.2
      exact typed_type P μ fd C σ K hEC (ordinary marks)
        (vcons x ρ) (vcons x η) hfC dB hd.2.2.2 rB
  | Γ, _, _, .lam _ A u body B dA db, hd, marks, ρ, η, hρC, hρD, hctx, hfree => by
      have hfree' : occursConst fd.fref A = false ∧ occursConst fd.fref body = false :=
        Bool.or_eq_false_iff.mp hfree
      let MC := mkM P (table P μ fd C)
      let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
      have rA := of_typing P μ fd C σ K hEC hED dA hd.1
        marks ρ η hρC hρD hctx hfree'.1
      have eA := typed_type P μ fd C σ K hEC marks ρ η hρC dA hd.1 rA
      have sameA : den MC σ ρ A = den MD σ ρ A :=
        PiIndependent.den_free P μ fd.fref (ofFrame P μ fd C)
          (ofFrame P μ fd (RawFamilyEnlarge.enlarge fd C)) σ A hfree'.1 ρ
      apply lambda_case P μ fd C σ marks ρ η A body B hfree'.1 eA
      intro x hx
      have hxD : x ∈ Ed MD (den MD σ ρ A) := by
        change x ∈ Ed MC (den MD σ ρ A)
        rw [← sameA]
        exact hx
      exact of_typing P μ fd C σ K hEC hED db hd.2
        (ordinary marks) (vcons x ρ) (vcons x η) ⟨hρC, hx⟩ ⟨hρD, hxD⟩
        (context_ordinary P μ fd C σ marks Γ ρ η hctx
          (.assumption A) x x Equiv.rfl) hfree'.2
  | _, _, _, .app _ f a A B df da, hd, marks, ρ, η, hρC, hρD, hctx, hfree => by
      have hfree' : occursConst fd.fref f = false ∧ occursConst fd.fref a = false :=
        Bool.or_eq_false_iff.mp hfree
      have rf := of_typing P μ fd C σ K hEC hED df hd.1
        marks ρ η hρC hρD hctx hfree'.1
      have ra := of_typing P μ fd C σ K hEC hED da hd.2
        marks ρ η hρC hρD hctx hfree'.2
      exact application_case P μ fd C σ K hEC hED marks ρ η hρC hρD
        f a A B hfree'.1 hfree'.2 df hd.1 da hd.2 rf ra
  | Γ, _, _, .letE _ A u value B body dA dv db, hd, marks, ρ, η, hρC, hρD, hctx, hfree => by
      have hfree' : (occursConst fd.fref A = false ∧ occursConst fd.fref value = false) ∧
          occursConst fd.fref body = false := by
        simpa only [occursConst, Bool.or_eq_false_iff] using hfree
      let MC := mkM P (table P μ fd C)
      let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
      have rv := of_typing P μ fd C σ K hEC hED dv hd.2.1
        marks ρ η hρC hρD hctx hfree'.1.2
      have ev := clean_typed P μ fd C σ K hEC marks ρ η hρC
        hfree'.1.1 dv hd.2.1 rv
      have sameV : den MC σ ρ value = den MD σ ρ value :=
        PiIndependent.den_free P μ fd.fref (ofFrame P μ fd C)
          (ofFrame P μ fd (RawFamilyEnlarge.enlarge fd C)) σ value hfree'.1.2 ρ
      have hfC : Fits MC σ (.letBinding A value :: Γ) (vcons (den MC σ ρ value) ρ) :=
        ⟨hρC, sound_ty (P.good MC rfl) hEC dv hd.2.1 ρ hρC, Equiv.rfl⟩
      have hfD : Fits MD σ (.letBinding A value :: Γ) (vcons (den MC σ ρ value) ρ) := by
        rw [sameV]
        exact ⟨hρD, sound_ty (P.good MD rfl) hED dv hd.2.1 ρ hρD, Equiv.rfl⟩
      have hr := context_ordinary P μ fd C σ marks Γ ρ η hctx
        (.letBinding A value) (den MC σ ρ value) (den MC σ η value) ev
      have rb := of_typing P μ fd C σ K hEC hED db hd.2.2
        (ordinary marks) (vcons (den MC σ ρ value) ρ) (vcons (den MC σ η value) η)
        hfC hfD hr hfree'.2
      change Value (mkM P μ) fd C (mode (ordinary marks) body)
        (Ed MC (den MC σ ρ (instantiate0 value B)))
        (Ed MD (den MD σ ρ (instantiate0 value B)))
        (den MC σ (vcons (den MC σ ρ value) ρ) body)
        (den MC σ (vcons (den MC σ η value) η) body)
      rw [den_inst0, den_inst0, ← sameV]
      exact rb
  | _, _, _, .lit _ _ _ _, _, _, _, _, _, _, _, _ => Equiv.rfl
  | _, _, _, .conv _ e A B u d c, hd, marks, ρ, η, hρC, hρD, hctx, hfree => by
      have r := of_typing P μ fd C σ K hEC hED d hd.1
        marks ρ η hρC hρD hctx hfree
      exact conversion_case P μ fd C σ K hEC hED marks ρ η hρC hρD d c hd r

/-- The domain equality is produced by the complete actual typing
recursion followed by sort exclusion; the context relation is the only
local recursive-origin input. No term-classification callback remains. -/
theorem domain_eq (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n)
    (marks : Marks) (ρ η : Nat → PSet.{4})
    (hρC : Fits (mkM P (table P μ fd C)) σ Γ ρ)
    (hρD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρ)
    (hctx : Context P μ fd C σ marks Γ ρ η)
    {A : Expr Nat} {u : Level} (hfree : occursConst fd.fref A = false)
    (d : HasTyT E n Γ A (.sort u)) (hd : LOKt σ 4 K d) :
    Equiv (den (mkM P (table P μ fd C)) σ ρ A)
      (den (mkM P (table P μ fd C)) σ η A) :=
  typed_type P μ fd C σ K hEC marks ρ η hρC d hd
    (of_typing P μ fd C σ K hEC hED d hd marks ρ η hρC hρD hctx hfree)

end Rcic.F3.PSet.RecFieldMask

import rcic.RcicF3PiSyntaxCompile
import rcic.RcicF3PiRecBridge
/-! Exact IH-type semantics for compiled syntax telescopes.
The leaf equation is required only along actual fitting arguments; the
actual recursive child is retained. This component does not extract the
leaf equation from an admitted raw group. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet
universe u v
open Rcic.Declarative

theorem RecTel.erasedIHType_congr {I : Type v} (M : Interp.{u})
    (C : I → PSet.{u} → PSet.{u})
    (hC : ∀ i x y, Equiv x y → Equiv (C i x) (C i y))
    {m : Nat} (t : RecTel.{u,v} I m) {x y : PSet.{u}} (h : Equiv x y) :
    Equiv (t.erasedIHType M C x) (t.erasedIHType M C y) := by
  induction t generalizing x y with
  | ret i => exact tyv_congr (hC i x y h)
  | pi A B ih =>
    apply piVal_congr M Equiv.rfl
    intro a b hab
    apply tyv_congr
    exact (classFiber_congr A _ hab).trans
      (classFiber_values (fun q => ed_congr M (ih q (fapp_congr h Equiv.rfl))) b)

/-- Elementary tag recovery: the proof/data dichotomy is needed only at leaves. -/
theorem RecTel.erasedIHType_tagged {I : Type v} (M : Interp.{u})
    (C : I → PSet.{u} → PSet.{u}) (hC : ∀ i x, Dich (C i x))
    {m : Nat} (t : RecTel.{u,v} I m) (x : PSet.{u}) :
    Equiv (tyv (Ed M (t.erasedIHType M C x))) (t.erasedIHType M C x) := by
  cases t with
  | ret i => exact tyv_congr (ed_tyv M (hC i x))
  | pi A B =>
    exact tyv_congr (ed_piVal M (tyv A)
      (fun a => tyv (classFiber A
        (fun q => Ed M ((B q).erasedIHType M C (fapp x (PiCompile.classValue A q)))) a))
      (fun _ _ h => tyv_congr (classFiber_congr A _ h)))

namespace PiSyntaxIH

def EndEq {I : Type v} (M : Interp.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{u}) → I) (C : I → PSet.{u} → PSet.{u})
    (b : Expr Nat) : List (Expr Nat) → (Nat → PSet.{u}) → PSet.{u} → Prop
  | [], ρ, x => Equiv (tyv (C (R ρ) x)) (den M σ ρ b)
  | A :: ds, ρ, x => ∀ a, a ∈ Ed M (den M σ ρ A) →
      EndEq M σ R C b ds (vcons a ρ) (fapp x a)

theorem compile_spec {I : Type v} (M : Interp.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{u}) → I) (C : I → PSet.{u} → PSet.{u})
    (hC : ∀ i x, Dich (C i x))
    (b : Expr Nat) : ∀ ds ρ x, EndEq M σ R C b ds ρ x →
      Equiv ((PiSyntaxCompile.compile M σ R ds ρ).erasedIHType M C x)
        (den M σ ρ (policyPi ds b)) := by
  intro ds
  induction ds with
  | nil => intro ρ x h; exact h
  | cons A ds ih =>
    intro ρ x h
    let D := Ed M (den M σ ρ A)
    let B := fun a => tyv (classFiber D (fun q =>
      Ed M ((PiSyntaxCompile.compile M σ R ds
        (vcons (PiCompile.classValue D q) ρ)).erasedIHType M C
          (fapp x (PiCompile.classValue D q)))) a)
    have hB : ∀ a b, Equiv a b → Equiv (B a) (B b) :=
      fun _ _ hab => tyv_congr (classFiber_congr D _ hab)
    change Equiv (piVal M (tyv D) B)
      (piVal M (den M σ ρ A) (fun a => den M σ (vcons a ρ) (policyPi ds b)))
    apply Equiv.trans (PiEraseCompile.piVal_ed_domain M (den M σ ρ A) B hB)
    apply piVal_congr_on M (B' := fun a => den M σ (vcons a ρ) (policyPi ds b))
      Equiv.rfl hB (fun a b hab => den_congr M σ _ (vcons_congr hab (fun _ => Equiv.rfl)))
    intro a ha
    obtain ⟨i, hi⟩ := ha
    let q := Quotient.mk (FSetoid D) i
    have ef := (classFiber_congr D (fun q =>
      Ed M ((PiSyntaxCompile.compile M σ R ds
        (vcons (PiCompile.classValue D q) ρ)).erasedIHType M C
          (fapp x (PiCompile.classValue D q)))) hi.symm).trans (classFiber_at D _ i)
    exact (tyv_congr ef).trans
      (((PiSyntaxCompile.compile M σ R ds (vcons (PiCompile.classValue D q) ρ)).erasedIHType_tagged
        M C hC (fapp x (PiCompile.classValue D q))).trans
        ((ih _ _ (h _ (PiCompile.classValue_mem D q))).trans
          (den_congr M σ (policyPi ds b)
            (vcons_congr ((PiCompile.classValue_at D i).trans hi) (fun _ => Equiv.rfl)))))
theorem endEq_iff {I : Type v} (M : Interp.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{u}) → I) (C : I → PSet.{u} → PSet.{u}) (b : Expr Nat) :
    ∀ ds ρ x, EndEq M σ R C b ds ρ x ↔
      ∀ xs, TelFits M σ ds ρ xs →
        Equiv (tyv (C (R (push xs ρ)) (fapps x xs))) (den M σ (push xs ρ) b) := by
  intro ds
  induction ds with
  | nil =>
    intro ρ x
    constructor
    · intro h xs hx
      cases xs with
      | nil => exact h
      | cons a xs => exact False.elim hx
    · intro h
      exact h [] trivial
  | cons A ds ih =>
    intro ρ x
    constructor
    · intro h xs hx
      cases xs with
      | nil => exact False.elim hx
      | cons a xs => exact (ih (vcons a ρ) (fapp x a)).mp (h a hx.1) xs hx.2
    · intro h a ha
      exact (ih (vcons a ρ) (fapp x a)).mpr (fun xs hxs => h (a :: xs) ⟨ha, hxs⟩)
end PiSyntaxIH
end Rcic.F3.PSet

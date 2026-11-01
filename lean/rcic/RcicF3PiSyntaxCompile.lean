import rcic.RcicF3PiEraseCompile
import rcic.RcicF3Fam
import rcic.RcicF3Fund
/-!
# Actual-product semantics of structural syntax telescopes

Domains are extracted from `Ed (den A)`. Domain dichotomy and all domain
extensionality follow internally. `EndEq` records only the leaf-family
agreement along arguments fitting this telescope; `endEq_iff` states its
literal scope. Conversion transport consumes a bounded typed witness.
Producing such a witness for every successful normalized admission, and
extracting a small raw family signature, remain unpaid. `closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSyntaxCompile
open Rcic.Declarative
universe u v

def compile {I : Type v} (M : Interp.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{u}) → I) :
    (ds : List (Expr Nat)) → (Nat → PSet.{u}) → RecTel.{u, v} I ds.length
  | [], ρ => .ret (R ρ)
  | A :: ds, ρ => .pi (Ed M (den M σ ρ A)) (fun q =>
      compile M σ R ds (vcons (PiCompile.classValue (Ed M (den M σ ρ A)) q) ρ))

def EndEq {I : Type v} (M : Interp.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{u}) → I) (X : I → PSet.{u}) (b : Expr Nat) :
    List (Expr Nat) → (Nat → PSet.{u}) → Prop
  | [], ρ => Equiv (tyv (X (R ρ))) (den M σ ρ b)
  | A :: ds, ρ => ∀ a, a ∈ Ed M (den M σ ρ A) → EndEq M σ R X b ds (vcons a ρ)

theorem compile_domains {I : Type v} (M : Interp.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{u}) → I) : ∀ ds ρ, (compile M σ R ds ρ).DomainsDich := by
  intro ds
  induction ds with
  | nil => intro ρ; trivial
  | cons A ds ih => intro ρ; exact ⟨dich_ed M _, fun _ => ih _⟩

theorem compile_spec {I : Type v} (M : Interp.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{u}) → I) (X : I → PSet.{u}) (hX : ∀ i, Dich (X i))
    (b : Expr Nat) : ∀ ds ρ, EndEq M σ R X b ds ρ →
      Equiv ((compile M σ R ds ρ).erasedType M X) (den M σ ρ (policyPi ds b)) := by
  intro ds
  induction ds with
  | nil => intro ρ h; exact h
  | cons A ds ih =>
    intro ρ h
    let D := Ed M (den M σ ρ A)
    let C := fun a => tyv (classFiber D (fun q =>
      Ed M ((compile M σ R ds (vcons (PiCompile.classValue D q) ρ)).erasedType M X)) a)
    have hC : ∀ a b, Equiv a b → Equiv (C a) (C b) :=
      fun _ _ h => tyv_congr (classFiber_congr D _ h)
    change Equiv (piVal M (tyv D) C)
      (piVal M (den M σ ρ A) (fun a => den M σ (vcons a ρ) (policyPi ds b)))
    apply Equiv.trans (PiEraseCompile.piVal_ed_domain M (den M σ ρ A) C hC)
    apply piVal_congr_on M (B' := fun a => den M σ (vcons a ρ) (policyPi ds b))
      Equiv.rfl hC (fun a b h => den_congr M σ _ (vcons_congr h (fun _ => Equiv.rfl)))
    intro a ha
    obtain ⟨i, hi⟩ := ha
    let q := Quotient.mk (FSetoid D) i
    have ef := (classFiber_congr D (fun q =>
      Ed M ((compile M σ R ds (vcons (PiCompile.classValue D q) ρ)).erasedType M X))
      hi.symm).trans (classFiber_at D _ i)
    exact (tyv_congr ef).trans
      (((compile M σ R ds (vcons (PiCompile.classValue D q) ρ)).erasedType_tagged M X hX).trans
        ((ih _ (h _ (PiCompile.classValue_mem D q))).trans
          (den_congr M σ (policyPi ds b)
            (vcons_congr ((PiCompile.classValue_at D i).trans hi) (fun _ => Equiv.rfl)))))

theorem endEq_iff {I : Type v} (M : Interp.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{u}) → I) (X : I → PSet.{u}) (b : Expr Nat) :
    ∀ ds ρ, EndEq M σ R X b ds ρ ↔
      ∀ xs, TelFits M σ ds ρ xs →
        Equiv (tyv (X (R (push xs ρ)))) (den M σ (push xs ρ) b) := by
  intro ds
  induction ds with
  | nil =>
    intro ρ
    constructor
    · intro h xs hx
      cases xs with
      | nil => exact h
      | cons a xs => exact False.elim hx
    · intro h
      exact h [] trivial
  | cons A ds ih =>
    intro ρ
    constructor
    · intro h xs hx
      cases xs with
      | nil => exact False.elim hx
      | cons a xs => exact (ih (vcons a ρ)).mp (h a hx.1) xs hx.2
    · intro h a ha
      exact (ih (vcons a ρ)).mpr (fun xs hxs => h (a :: xs) ⟨ha, hxs⟩)

/-- Elementary transport along an actual bounded typed conversion. This
is not a producer of conversion witnesses from successful normalization. -/
theorem compile_spec_of_conv {I : Type v} (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hE : EnvSound (mkM P μ) σ K E n)
    (R : (Nat → PSet.{4}) → I) (X : I → PSet.{4}) (hX : ∀ i, Dich (X i))
    (ds : List (Expr Nat)) (b A T : Expr Nat)
    (d : ConvT E n Γ A (policyPi ds b) T) (hd : LOKc σ 4 K d)
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ)
    (hEnd : EndEq (mkM P μ) σ R X b ds ρ) :
    Equiv ((compile (mkM P μ) σ R ds ρ).erasedType (mkM P μ) X)
      (den (mkM P μ) σ ρ A) := by
  exact (compile_spec (mkM P μ) σ R X hX b ds ρ hEnd).trans
    (sound_conv (P.good _ rfl) hE d hd ρ hρ).1.symm
end Rcic.F3.PSet.PiSyntaxCompile

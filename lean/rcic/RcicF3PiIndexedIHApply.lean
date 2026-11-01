import rcic.RcicF3PiIndexedIH
import rcic.RcicF3PiIndex
import rcic.RcicF3PiSmallValue

/-!
# Computation of indexed IHs on actual normalized telescope arguments

The indexed IH applies along the full semantic domains and returns the
leaf map at the complete index and actual applied major. The proof covers
arbitrary dependent binder depth, including proof-erased ordinary fields.
It constructs no evaluation witnesses; a later evaluator must supply them.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PiIndexedIHApply
open Rcic.Declarative
universe u v

/-- Nested actual-domain lambdas with the full leaf selector. -/
noncomputable def value {I : Type v} (M : Interp.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{u}) → I) (g : I → PSet.{u} → PSet.{u}) :
    List (Expr Nat) → (Nat → PSet.{u}) → PSet.{u} → PSet.{u}
  | [], ρ, x => g (R ρ) x
  | A :: ds, ρ, x => lamVal M (den M σ ρ A)
      (fun a => value M σ R g ds (vcons a ρ) (fapp x a))

/-- Syntax denotation supplies all domain congruence; only leaf congruence remains. -/
theorem value_congr {I : Type v} (M : Interp.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{u}) → I)
    (hR : ∀ ρ ρ', (∀ n, Equiv (ρ n) (ρ' n)) → R ρ = R ρ')
    (g : I → PSet.{u} → PSet.{u})
    (hg : ∀ i x y, Equiv x y → Equiv (g i x) (g i y)) :
    ∀ ds {ρ ρ' : Nat → PSet.{u}} {x x' : PSet.{u}},
      (∀ n, Equiv (ρ n) (ρ' n)) → Equiv x x' →
      Equiv (value M σ R g ds ρ x) (value M σ R g ds ρ' x') := by
  intro ds
  induction ds with
  | nil =>
      intro ρ ρ' x x' hρ hx
      dsimp only [value]
      rw [hR ρ ρ' hρ]
      exact hg _ _ _ hx
  | cons A ds ih =>
      intro ρ ρ' x x' hρ hx
      exact lamVal_congr M (den_congr M σ A hρ)
        (fun a b hab => ih (vcons_congr hab hρ) (fapp_congr hx hab))

/-- The quotient-compiled operation agrees with actual-domain lambdas. -/
theorem compile_value {I : Type v} (M : Interp.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{u}) → I)
    (hR : ∀ ρ ρ', (∀ n, Equiv (ρ n) (ρ' n)) → R ρ = R ρ')
    (g : I → PSet.{u} → PSet.{u})
    (hg : ∀ i x y, Equiv x y → Equiv (g i x) (g i y)) :
    ∀ ds ρ x, Equiv
      ((PiSyntaxCompile.compile M σ R ds ρ).indexedIH M g x)
      (value M σ R g ds ρ x) := by
  intro ds
  induction ds with
  | nil => intro ρ x; exact Equiv.rfl
  | cons A ds ih =>
      intro ρ x
      let D := Ed M (den M σ ρ A)
      let b := fun a => value M σ R g ds (vcons a ρ) (fapp x a)
      have hb : ∀ a a', Equiv a a' → Equiv (b a) (b a') :=
        fun a a' ha => value_congr M σ R hR g hg ds
          (vcons_congr ha (fun _ => Equiv.rfl)) (fapp_congr Equiv.rfl ha)
      have he : Equiv
          ((PiSyntaxCompile.compile M σ R (A :: ds) ρ).indexedIH M g x)
          (lamVal M (tyv D) b) := by
        apply lamVal_congr_on M Equiv.rfl
          (fun _ _ h => classFiber_congr D _ h)
        intro a ha
        have haD : a ∈ D := mem_congr_right (ed_tyv M (dich_ed M _)) ha
        exact (classFiber_values
          (fun q => ih (vcons (PiCompile.classValue D q) ρ)
            (fapp x (PiCompile.classValue D q))) a).trans
          (PiCompile.classFiber_value D b hb a haD)
      exact he.trans (PiSmallValue.lamVal_ed_domain.{u,u} M b hb
        (ed_tyv M (dich_ed M _)))

/-- Actual fitting arguments compute the exact leaf value. -/
theorem value_apply {I : Type v} (M : Interp.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{u}) → I)
    (hR : ∀ ρ ρ', (∀ n, Equiv (ρ n) (ρ' n)) → R ρ = R ρ')
    (g : I → PSet.{u} → PSet.{u})
    (hg : ∀ i x y, Equiv x y → Equiv (g i x) (g i y)) :
    ∀ ds ρ x xs, TelFits M σ ds ρ xs →
      Equiv (fapps (value M σ R g ds ρ x) xs)
        (g (R (push xs ρ)) (fapps x xs)) := by
  intro ds
  induction ds with
  | nil =>
      intro ρ x xs hxs
      cases xs with
      | nil => exact Equiv.rfl
      | cons a xs => exact False.elim hxs
  | cons A ds ih =>
      intro ρ x xs hxs
      cases xs with
      | nil => exact False.elim hxs
      | cons a xs =>
          have hb : ∀ b b', Equiv b b' →
              Equiv (value M σ R g ds (vcons b ρ) (fapp x b))
                (value M σ R g ds (vcons b' ρ) (fapp x b')) :=
            fun b b' h => value_congr M σ R hR g hg ds
              (vcons_congr h (fun _ => Equiv.rfl)) (fapp_congr Equiv.rfl h)
          exact (fapps_congr (beta_val M hb hxs.1) xs).trans
            (ih (vcons a ρ) (fapp x a) xs hxs.2)

/-- Computation at any finite normalized telescope depth and full leaf key. -/
theorem indexed_apply (M : Interp.{u}) (σ : Nat → Nat)
    (ds args : List (Expr Nat)) (ρ : Nat → PSet.{u})
    (g : PiIndex.Index.{u} → PSet.{u} → PSet.{u})
    (hg : ∀ i x y, Equiv x y → Equiv (g i x) (g i y))
    (x : PSet.{u}) (xs : List PSet.{u}) (hxs : TelFits M σ ds ρ xs) :
    Equiv (fapps ((PiIndex.tel M σ ds args ρ).indexedIH M g x) xs)
      (g (PiIndex.key (args.map (den M σ (push xs ρ)))) (fapps x xs)) := by
  have hR := fun ρ ρ' h => PiIndex.read_congr M σ args (ρ := ρ) (ρ' := ρ') h
  exact (fapps_congr (compile_value M σ (PiIndex.read M σ args) hR g hg ds ρ x) xs).trans
    (value_apply M σ (PiIndex.read M σ args) hR g hg ds ρ x xs hxs)

end Rcic.F3.PSet.PiIndexedIHApply

import rcic.RcicF3ReaderSupport

/-!
# Exact denotations for reader capture environments

The reader's parallel substitution is interpreted by the actual captured
values, including under binders. A closure may keep the valuation of its
original typing derivation: transparent stored bodies use their original
zero valuation, and their level-closed syntax supplies agreement with the
reader's full valuation. No bound is transported from zero to that full
valuation and no masked assignment is asserted to fit.

These are the algebraic maps used by the typed reader-provenance proof.
They do not postulate a successful-reader provenance or a domain mask.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.ReaderSubstitution
open Rcic.Declarative
universe u

def capture (M : Interp.{u}) (σ : Nat → Nat) (ρ : Nat → PSet.{u})
    (s : SubstT) : Nat → PSet.{u} := fun i => den M σ ρ (s i)

theorem capture_up (M : Interp.{u}) (σ : Nat → Nat)
    (ρ : Nat → PSet.{u}) (s : SubstT) (x : PSet.{u}) :
    capture M σ (vcons x ρ) s.up = vcons x (capture M σ ρ s) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      change den M σ (vcons x ρ) (s.up (i + 1)) = den M σ ρ (s i)
      rw [SubstT.up_succ, den_lift, liftρ_zero, shiftρ_one_cons]

/-- This is an equality for the actual `substT`, with all source locals
retained. In particular, no beta-domain membership is needed here. -/
theorem den_subst (M : Interp.{u}) (σ : Nat → Nat) :
    (e : Expr Nat) → (s : SubstT) → (ρ : Nat → PSet.{u}) →
    den M σ ρ (substT s e) = den M σ (capture M σ ρ s) e
  | .bvar _, _, _ => rfl
  | .sort _, _, _ => rfl
  | .const _ _, _, _ => rfl
  | .lit _, _, _ => rfl
  | .app f a, s, ρ => by
      change fapp (den M σ ρ (substT s f)) (den M σ ρ (substT s a)) = _
      rw [den_subst M σ f s ρ, den_subst M σ a s ρ]
      rfl
  | .lam A b, s, ρ => by
      change lamVal M (den M σ ρ (substT s A))
        (fun x => den M σ (vcons x ρ) (substT s.up b)) = _
      rw [den_subst M σ A s ρ]
      have hb : (fun x => den M σ (vcons x ρ) (substT s.up b)) =
          (fun x => den M σ (vcons x (capture M σ ρ s)) b) := by
        funext x
        rw [den_subst M σ b s.up (vcons x ρ), capture_up]
      rw [hb]
      rfl
  | .pi A B, s, ρ => by
      change piVal M (den M σ ρ (substT s A))
        (fun x => den M σ (vcons x ρ) (substT s.up B)) = _
      rw [den_subst M σ A s ρ]
      have hB : (fun x => den M σ (vcons x ρ) (substT s.up B)) =
          (fun x => den M σ (vcons x (capture M σ ρ s)) B) := by
        funext x
        rw [den_subst M σ B s.up (vcons x ρ), capture_up]
      rw [hB]
      rfl
  | .letE _ v b, s, ρ => by
      change den M σ (vcons (den M σ ρ (substT s v)) ρ) (substT s.up b) = _
      rw [den_subst M σ b s.up _, capture_up, den_subst M σ v s ρ]
      rfl

/-- Only levels present in the source syntax must agree. The expected
type and conversion derivation remain at their original valuation. -/
def Levels (σ τ : Nat → Nat) : Expr Nat → Prop
  | .bvar _ => True
  | .sort l => evalTotal σ l = evalTotal τ l
  | .const _ ls => ls.map (evalTotal σ) = ls.map (evalTotal τ)
  | .lit _ => True
  | .app f a => Levels σ τ f ∧ Levels σ τ a
  | .lam A b => Levels σ τ A ∧ Levels σ τ b
  | .pi A B => Levels σ τ A ∧ Levels σ τ B
  | .letE A v b => (Levels σ τ A ∧ Levels σ τ v) ∧ Levels σ τ b

theorem Levels.refl (σ : Nat → Nat) : ∀ e, Levels σ σ e
  | .bvar _ => True.intro
  | .sort _ => rfl
  | .const _ _ => rfl
  | .lit _ => True.intro
  | .app f a => ⟨refl σ f, refl σ a⟩
  | .lam A b => ⟨refl σ A, refl σ b⟩
  | .pi A B => ⟨refl σ A, refl σ B⟩
  | .letE A v b => ⟨⟨refl σ A, refl σ v⟩, refl σ b⟩

theorem Levels.of_closed (σ τ : Nat → Nat) :
    (e : Expr Nat) → exprLevelsBounded 0 e = true → Levels σ τ e
  | .bvar _, _ => True.intro
  | .sort l, h => evalTotal_levelBounded0 σ τ l h
  | .const _ ls, h => map_evalTotal_levelsBounded0 σ τ ls h
  | .lit _, _ => True.intro
  | .app f a, h => by
      have hs := Bool.and_eq_true_iff.mp h
      exact ⟨of_closed σ τ f hs.1, of_closed σ τ a hs.2⟩
  | .lam A b, h => by
      have hs := Bool.and_eq_true_iff.mp h
      exact ⟨of_closed σ τ A hs.1, of_closed σ τ b hs.2⟩
  | .pi A B, h => by
      have hs := Bool.and_eq_true_iff.mp h
      exact ⟨of_closed σ τ A hs.1, of_closed σ τ B hs.2⟩
  | .letE A v b, h => by
      have hs := Bool.and_eq_true_iff.mp h
      have hav := Bool.and_eq_true_iff.mp hs.1
      exact ⟨⟨of_closed σ τ A hav.1, of_closed σ τ v hav.2⟩,
        of_closed σ τ b hs.2⟩

theorem den_levels (M : Interp.{u}) (σ τ : Nat → Nat) :
    (e : Expr Nat) → Levels σ τ e → (ρ : Nat → PSet.{u}) →
    den M σ ρ e = den M τ ρ e
  | .bvar _, _, _ => rfl
  | .sort _, h, _ => by change tyv (M.U _) = tyv (M.U _); rw [h]
  | .const r _, h, _ => congrArg (M.μ r) h
  | .lit _, _, _ => rfl
  | .app f a, h, ρ => by
      change fapp _ _ = fapp _ _
      rw [den_levels M σ τ f h.1 ρ, den_levels M σ τ a h.2 ρ]
  | .lam A b, h, ρ => by
      change lamVal M _ _ = lamVal M _ _
      rw [den_levels M σ τ A h.1 ρ]
      exact congrArg (lamVal M (den M τ ρ A))
        (funext fun x => den_levels M σ τ b h.2 (vcons x ρ))
  | .pi A B, h, ρ => by
      change piVal M _ _ = piVal M _ _
      rw [den_levels M σ τ A h.1 ρ]
      exact congrArg (piVal M (den M τ ρ A))
        (funext fun x => den_levels M σ τ B h.2 (vcons x ρ))
  | .letE _ v b, h, ρ => by
      change den M σ (vcons (den M σ ρ v) ρ) b = _
      rw [den_levels M σ τ v h.1.2 ρ]
      exact den_levels M σ τ b h.2 _

/-- The reader's full valuation and a source body's original valuation
meet only through the proved syntactic level agreement. -/
theorem den_closure (M : Interp.{u}) (σ τ : Nat → Nat)
    (e : Expr Nat) (h : Levels σ τ e) (s : SubstT) (ρ : Nat → PSet.{u}) :
    den M σ ρ (substT s e) = den M τ (capture M σ ρ s) e :=
  (den_subst M σ e s ρ).trans (den_levels M σ τ e h _)

end Rcic.F3.PSet.ReaderSubstitution

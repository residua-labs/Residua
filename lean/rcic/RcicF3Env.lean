import rcic.RcicF3Fund
import rcic.RcicModelEnv

/-!
# F3 S4: what the denotation of a term depends on

- `den_agree`: the denotation reads the constant interpretation only at the
  references the term mentions (`denRefs`, landed with the R1-b model);
- `den_cutoff`: a term that `lift` fixes from cutoff `c` on reads only the
  environment below `c` (closed terms read none of it);
- `den_levels_closed`: a term without level parameters does not read the
  level valuation.

These let the interpretation of an environment be built member by member
(F3 plan, S4). closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (denRefs denRefsLit)

universe T

namespace PSet

/-- The interpretation with another constant table. -/
def withμ (M : Interp.{T}) (μ : Nat → List Nat → PSet.{T}) : Interp.{T} :=
  { dec := M.dec, U := M.U, μ := μ }

theorem denLit_agree (M : Interp.{T}) {μ₁ μ₂ : Nat → List Nat → PSet.{T}} :
    (t : Nat) → (∀ r, r ∈ denRefsLit t → ∀ ls, μ₁ r ls = μ₂ r ls) →
      denLit (withμ M μ₁) t = denLit (withμ M μ₂) t
  | 0, h => h 1 (by simp [denRefsLit]) []
  | t + 1, h => by
      show fapp (μ₁ 2 []) (denLit (withμ M μ₁) t) = fapp (μ₂ 2 []) (denLit (withμ M μ₂) t)
      rw [h 2 (by simp [denRefsLit]) [], denLit_agree M t (fun r hr => h r (by simp [denRefsLit, hr]))]

/-- The denotation reads constants only at the references the term mentions. -/
theorem den_agree (M : Interp.{T}) {μ₁ μ₂ : Nat → List Nat → PSet.{T}} (σ : Nat → Nat) :
    (e : Expr Nat) → (∀ r, r ∈ denRefs e → ∀ ls, μ₁ r ls = μ₂ r ls) →
      ∀ ρ, den (withμ M μ₁) σ ρ e = den (withμ M μ₂) σ ρ e
  | .bvar _, _, _ => rfl
  | .sort _, _, _ => rfl
  | .const r ls, h, _ => h r (by simp [denRefs]) _
  | .app f a, h, ρ => by
      show fapp _ _ = fapp _ _
      rw [den_agree M σ f (fun r hr => h r (by simp [denRefs, hr])) ρ,
        den_agree M σ a (fun r hr => h r (by simp [denRefs, hr])) ρ]
  | .lam A b, h, ρ => by
      show lamVal _ _ _ = lamVal _ _ _
      have hA := den_agree M σ A (fun r hr => h r (by simp [denRefs, hr])) ρ
      have hb : (fun x => den (withμ M μ₁) σ (vcons x ρ) b) = (fun x => den (withμ M μ₂) σ (vcons x ρ) b) :=
        funext fun x => den_agree M σ b (fun r hr => h r (by simp [denRefs, hr])) (vcons x ρ)
      rw [hA, hb]
      rfl
  | .pi A B, h, ρ => by
      show piVal _ _ _ = piVal _ _ _
      have hA := den_agree M σ A (fun r hr => h r (by simp [denRefs, hr])) ρ
      have hB : (fun x => den (withμ M μ₁) σ (vcons x ρ) B) = (fun x => den (withμ M μ₂) σ (vcons x ρ) B) :=
        funext fun x => den_agree M σ B (fun r hr => h r (by simp [denRefs, hr])) (vcons x ρ)
      rw [hA, hB]
      rfl
  | .letE A v b, h, ρ => by
      show den _ σ (vcons (den _ σ ρ v) ρ) b = den _ σ (vcons (den _ σ ρ v) ρ) b
      rw [den_agree M σ v (fun r hr => h r (by simp [denRefs, hr])) ρ]
      exact den_agree M σ b (fun r hr => h r (by simp [denRefs, hr])) _
  | .lit t, h, _ => denLit_agree M t (fun r hr => h r (by simpa [denRefs] using hr))

/-- A term fixed by `lift` from cutoff `c` on reads only the environment below `c`. -/
theorem den_cutoff (M : Interp.{T}) (σ : Nat → Nat) :
    (e : Expr Nat) → ∀ (c : Nat), (∀ k, c ≤ k → Rcic.Declarative.lift k 1 e = e) →
      ∀ ρ ρ' : Nat → PSet.{T}, (∀ i, i < c → ρ i = ρ' i) → den M σ ρ e = den M σ ρ' e
  | .bvar i, c, h, ρ, ρ', hρ => by
      have hi : i < c := by
        refine Nat.lt_of_not_le fun hci => ?_
        have := h i hci
        simp only [Rcic.Declarative.lift, if_pos (Nat.le_refl i), Expr.bvar.injEq] at this
        omega
      exact hρ i hi
  | .sort _, _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _, _ => rfl
  | .lit _, _, _, _, _, _ => rfl
  | .app f a, c, h, ρ, ρ', hρ => by
      have hf : ∀ k, c ≤ k → Rcic.Declarative.lift k 1 f = f := fun k hk => by
        have := h k hk; simp only [Rcic.Declarative.lift, Expr.app.injEq] at this; exact this.1
      have ha : ∀ k, c ≤ k → Rcic.Declarative.lift k 1 a = a := fun k hk => by
        have := h k hk; simp only [Rcic.Declarative.lift, Expr.app.injEq] at this; exact this.2
      show fapp _ _ = fapp _ _
      rw [den_cutoff M σ f c hf ρ ρ' hρ, den_cutoff M σ a c ha ρ ρ' hρ]
  | .lam A b, c, h, ρ, ρ', hρ => by
      have hA : ∀ k, c ≤ k → Rcic.Declarative.lift k 1 A = A := fun k hk => by
        have := h k hk; simp only [Rcic.Declarative.lift, Expr.lam.injEq] at this; exact this.1
      have hb : ∀ k, c + 1 ≤ k → Rcic.Declarative.lift k 1 b = b := fun k hk => by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have := h k' (by omega); simp only [Rcic.Declarative.lift, Expr.lam.injEq] at this; exact this.2
      show lamVal _ _ _ = lamVal _ _ _
      rw [den_cutoff M σ A c hA ρ ρ' hρ]
      have : (fun x => den M σ (vcons x ρ) b) = (fun x => den M σ (vcons x ρ') b) := funext fun x =>
        den_cutoff M σ b (c + 1) hb _ _ (fun i hi => by
          cases i with
          | zero => rfl
          | succ i => exact hρ i (by omega))
      rw [this]
  | .pi A B, c, h, ρ, ρ', hρ => by
      have hA : ∀ k, c ≤ k → Rcic.Declarative.lift k 1 A = A := fun k hk => by
        have := h k hk; simp only [Rcic.Declarative.lift, Expr.pi.injEq] at this; exact this.1
      have hB : ∀ k, c + 1 ≤ k → Rcic.Declarative.lift k 1 B = B := fun k hk => by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have := h k' (by omega); simp only [Rcic.Declarative.lift, Expr.pi.injEq] at this; exact this.2
      show piVal _ _ _ = piVal _ _ _
      rw [den_cutoff M σ A c hA ρ ρ' hρ]
      have : (fun x => den M σ (vcons x ρ) B) = (fun x => den M σ (vcons x ρ') B) := funext fun x =>
        den_cutoff M σ B (c + 1) hB _ _ (fun i hi => by
          cases i with
          | zero => rfl
          | succ i => exact hρ i (by omega))
      rw [this]
  | .letE A v b, c, h, ρ, ρ', hρ => by
      have hv : ∀ k, c ≤ k → Rcic.Declarative.lift k 1 v = v := fun k hk => by
        have := h k hk; simp only [Rcic.Declarative.lift, Expr.letE.injEq] at this; exact this.2.1
      have hb : ∀ k, c + 1 ≤ k → Rcic.Declarative.lift k 1 b = b := fun k hk => by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have := h k' (by omega); simp only [Rcic.Declarative.lift, Expr.letE.injEq] at this; exact this.2.2
      show den M σ (vcons (den M σ ρ v) ρ) b = den M σ (vcons (den M σ ρ' v) ρ') b
      rw [den_cutoff M σ v c hv ρ ρ' hρ]
      exact den_cutoff M σ b (c + 1) hb _ _ (fun i hi => by
        cases i with
        | zero => rfl
        | succ i => exact hρ i (by omega))

theorem den_closed (M : Interp.{T}) (σ : Nat → Nat) (e : Expr Nat)
    (h : ∀ k, Rcic.Declarative.lift k 1 e = e) (ρ ρ' : Nat → PSet.{T}) :
    den M σ ρ e = den M σ ρ' e :=
  den_cutoff M σ e 0 (fun k _ => h k) ρ ρ' (fun _ hi => absurd hi (Nat.not_lt_zero _))

theorem evalTotal_levelBounded0 (σ σ' : Nat → Nat) :
    (l : Level) → levelBounded 0 l = true → evalTotal σ l = evalTotal σ' l
  | .zero, _ => rfl
  | .succ l, h => by simp only [evalTotal, evalTotal_levelBounded0 σ σ' l h]
  | .max a b, h => by
      simp only [levelBounded, Bool.and_eq_true] at h
      simp only [evalTotal, evalTotal_levelBounded0 σ σ' a h.1, evalTotal_levelBounded0 σ σ' b h.2]
  | .imax a b, h => by
      simp only [levelBounded, Bool.and_eq_true] at h
      simp only [evalTotal, evalTotal_levelBounded0 σ σ' a h.1, evalTotal_levelBounded0 σ σ' b h.2]
  | .param i, h => by simp [levelBounded] at h

theorem map_evalTotal_levelsBounded0 (σ σ' : Nat → Nat) :
    (ls : List Level) → levelsBounded 0 ls = true → ls.map (evalTotal σ) = ls.map (evalTotal σ')
  | [], _ => rfl
  | l :: ls, h => by
      simp only [levelsBounded, Bool.and_eq_true] at h
      simp only [List.map_cons, evalTotal_levelBounded0 σ σ' l h.1,
        map_evalTotal_levelsBounded0 σ σ' ls h.2]

/-- A term without level parameters does not read the level valuation. -/
theorem den_levels_closed (M : Interp.{T}) (σ σ' : Nat → Nat) :
    (e : Expr Nat) → exprLevelsBounded 0 e = true → ∀ ρ, den M σ ρ e = den M σ' ρ e
  | .bvar _, _, _ => rfl
  | .sort l, h, _ => by
      show tyv (M.U (evalTotal σ l)) = tyv (M.U (evalTotal σ' l))
      rw [evalTotal_levelBounded0 σ σ' l h]
  | .const r ls, h, _ => by
      show M.μ r (ls.map (evalTotal σ)) = M.μ r (ls.map (evalTotal σ'))
      rw [map_evalTotal_levelsBounded0 σ σ' ls h]
  | .lit _, _, _ => rfl
  | .app f a, h, ρ => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at h
      show fapp _ _ = fapp _ _
      rw [den_levels_closed M σ σ' f h.1 ρ, den_levels_closed M σ σ' a h.2 ρ]
  | .lam A b, h, ρ => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at h
      show lamVal _ _ _ = lamVal _ _ _
      rw [den_levels_closed M σ σ' A h.1 ρ]
      have : (fun x => den M σ (vcons x ρ) b) = (fun x => den M σ' (vcons x ρ) b) :=
        funext fun x => den_levels_closed M σ σ' b h.2 _
      rw [this]
  | .pi A B, h, ρ => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at h
      show piVal _ _ _ = piVal _ _ _
      rw [den_levels_closed M σ σ' A h.1 ρ]
      have : (fun x => den M σ (vcons x ρ) B) = (fun x => den M σ' (vcons x ρ) B) :=
        funext fun x => den_levels_closed M σ σ' B h.2 _
      rw [this]
  | .letE A v b, h, ρ => by
      simp only [exprLevelsBounded, Bool.and_eq_true] at h
      show den M σ (vcons (den M σ ρ v) ρ) b = den M σ' (vcons (den M σ' ρ v) ρ) b
      rw [den_levels_closed M σ σ' v h.1.2 ρ]
      exact den_levels_closed M σ σ' b h.2 _

end PSet

end Rcic.F3

import rcic.RcicF3Fam

/-!
# F3 S5a-3: reading a sound derivation of a telescope type

- `pi_body_sound` / `pi_dom_sound`: a hereditarily sound derivation of
  `Π A, B` (at any type) contains hereditarily sound derivations of `A` and
  of `B` at sorts (peeling conversions);
- `tel_end_type`: for a hereditarily sound derivation of `policyPi Ds b` at a
  sort, at every fitting environment and fitting values, `b` denotes an
  element of a sort;
- `ne_of_mem_sort`: an element of a sort of the height-4 table is not `∅`.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

variable {E : ResolvedEnv} {n : Nat} {M : Interp.{T}} {σ : Nat → Nat}

theorem pi_body_sound : {Γ : LCtx} → {A B T' : Expr Nat} → (h : HasTyT E n Γ (.pi A B) T') →
    HSoundT M σ h → ∃ (v : Level) (hB : HasTyT E n (.assumption A :: Γ) B (.sort v)), HSoundT M σ hB
  | _, _, _, _, .pi _ _ _ _ v _ hB, hs => ⟨v, hB, hs.2.2⟩
  | _, _, _, _, .conv _ _ _ _ _ h _, hs => pi_body_sound h hs.2.1

theorem pi_dom_sound : {Γ : LCtx} → {A B T' : Expr Nat} → (h : HasTyT E n Γ (.pi A B) T') →
    HSoundT M σ h → ∃ (u : Level) (hA : HasTyT E n Γ A (.sort u)), HSoundT M σ hA
  | _, _, _, _, .pi _ _ u _ _ hA _, hs => ⟨u, hA, hs.2.1⟩
  | _, _, _, _, .conv _ _ _ _ _ h _, hs => pi_dom_sound h hs.2.1

/-- The end of a soundly typed telescope type denotes an element of a sort. -/
theorem tel_end_type (b : Expr Nat) : (Ds : List (Expr Nat)) → {Γ : LCtx} → {u : Level} →
    (h : HasTyT E n Γ (policyPi Ds b) (.sort u)) → HSoundT M σ h →
    ∀ ρ xs, Fits M σ Γ ρ → TelFits M σ Ds ρ xs →
      ∃ v, den M σ (push xs ρ) b ∈ Ed M (den M σ (push xs ρ) (.sort v))
  | [], _, u, h, hs, ρ, [], hf, _ => ⟨u, hs.root ρ hf⟩
  | A :: Ds, _, _, h, hs, ρ, x :: xs, hf, ⟨hx, hfs⟩ => by
      obtain ⟨v, hB, hsB⟩ := pi_body_sound h hs
      exact tel_end_type b Ds hB hsB (vcons x ρ) xs ⟨hf, hx⟩ hfs

/-- `tel_end_type` for a derivation of a term equal to a telescope type. -/
theorem tel_end_type' (b : Expr Nat) (Ds : List (Expr Nat)) {Γ : LCtx} {u : Level} {e : Expr Nat}
    (h : HasTyT E n Γ e (.sort u)) (he : e = policyPi Ds b) (hs : HSoundT M σ h) :
    ∀ ρ xs, Fits M σ Γ ρ → TelFits M σ Ds ρ xs →
      ∃ v, den M σ (push xs ρ) b ∈ Ed M (den M σ (push xs ρ) (.sort v)) := by
  subst he
  exact tel_end_type b Ds h hs

theorem tyv_of_mem_U4 {x : PSet.{4}} : (k : Nat) → x ∈ U W4 k → ∃ S, Equiv x (tyv S)
  | 0, h => let ⟨S, _, he⟩ := mem_sImage_tyv.mp h; ⟨S, he⟩
  | _ + 1, h => let ⟨S, _, he⟩ := mem_sImage_tyv.mp h; ⟨S, he⟩

/-- An element of a sort of the height-4 table is not `∅`. -/
theorem ne_of_mem_sort {M : Interp.{4}} (hU : M.U = U W4) {σ : Nat → Nat}
    {ρ : Nat → PSet.{4}} {v : Level} {x : PSet.{4}} (hx : x ∈ Ed M (den M σ ρ (.sort v))) :
    ¬ Equiv x pempty := by
  intro h0
  have hx' : x ∈ Ed M (tyv (U W4 (evalTotal σ v))) := by
    have : den M σ ρ (.sort v) = tyv (M.U (evalTotal σ v)) := rfl
    rw [this, hU] at hx; exact hx
  obtain ⟨S, he⟩ := tyv_of_mem_U4 _ (mem_congr_right (ed_tyv M (U4_dich _)) hx')
  exact tyv_ne_pempty S (he.symm.trans h0)

end PSet

end Rcic.F3

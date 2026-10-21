/-
02 §7 fifth and sixth judgments, quoted over the landed
`HasTy` / `Step` / `Conv` (G-2: DERIVABLE, not an introduction).

  02:165  E ; n ; Γ ⊢ e ↦ e' : A     — `StepAt`
  02:166  E ; n ; Γ ⊢ a ≈ b : A      — `ConvAt`
  02:255  "The typed one-step relation"
  02:281  typed convertibility contains one-step reduction

This is the pairing G-2 exhibited. It is not `ConvReducibility`, not
a normalization theorem, and not a second `Step` inductive.

M-005: `witness_sort_refl` inhabits `ConvAt` (sort, refl).
Premises: none of the open §19.2 rows.
closure_claim stays 0.
-/
import rcic.RcicDeclarative

namespace Rcic.StepAt
open Rcic.Declarative

/-- 02 §7 :165. G-2 exhibited form. -/
inductive StepAt (E : ResolvedEnv) (n : Nat) :
    LCtx → Expr Nat → Expr Nat → Expr Nat → Type where
  | of (Γ : LCtx) (e e' A : Expr Nat)
      (hstep : Step E n Γ e e')
      (hty : HasTy E n Γ e A) :
      StepAt E n Γ e e' A

/-- 02 §7 :166 / §10. Convertibility at a type. -/
structure ConvAt (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (a b A : Expr Nat) : Type where
  conv : Conv E n Γ a b
  ha : HasTy E n Γ a A
  hb : HasTy E n Γ b A

def convAt_refl {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a A : Expr Nat} (ha : HasTy E n Γ a A) :
    ConvAt E n Γ a a A :=
  ⟨.refl Γ a, ha, ha⟩

def convAt_symm {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b A : Expr Nat} (h : ConvAt E n Γ a b A) :
    ConvAt E n Γ b a A :=
  ⟨.symm Γ a b h.conv, h.hb, h.ha⟩

/-- Typed `trans` keeps `A`. Untyped `Conv.trans` does not. -/
def convAt_trans {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b c A : Expr Nat}
    (h1 : ConvAt E n Γ a b A) (h2 : ConvAt E n Γ b c A) :
    ConvAt E n Γ a c A :=
  ⟨.trans Γ a b c h1.conv h2.conv, h1.ha, h2.hb⟩

/-- M-005: `ConvAt` is inhabited (empty env, `0 : sort 1`, refl). -/
def witness_sort_refl :
    ConvAt emptyEnv 0 [] (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  convAt_refl (.sort [] .zero)

def witness_sort_trans :
    ConvAt emptyEnv 0 [] (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  convAt_trans witness_sort_refl witness_sort_refl

theorem witness_sort_refl_is_refl :
    witness_sort_refl.conv = .refl [] (.sort .zero) := rfl

theorem witness_sort_trans_is_trans :
    witness_sort_trans.conv =
      .trans [] (.sort .zero) (.sort .zero) (.sort .zero)
        (.refl [] (.sort .zero)) (.refl [] (.sort .zero)) := rfl

/-- Packing `Conv.irr`'s own premises is definitional — both endpoints
    are already typed at `P`. This is not PiConvInj. -/
def convAt_of_irr {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {P p q : Expr Nat}
    (hP : HasTy E n Γ P (.sort .zero))
    (hp : HasTy E n Γ p P) (hq : HasTy E n Γ q P) :
    ConvAt E n Γ p q P :=
  ⟨.irr Γ P p q hP hp hq, hp, hq⟩

end Rcic.StepAt

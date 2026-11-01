import rcic.RcicF3Fund
import rcic.RcicF3EnvModel

/-!
# Bounded type-conversion chains exposed by an actual variable derivation

A derivation whose subject is a bound variable can only start at lookup
and add conversion rules. The level bound records every conversion used
by those rules. This module extracts that actual bounded TyConvT chain
and composes it with the existing height-four conversion soundness theorem.

The original local context is retained literally. In particular, this is
not context strengthening, a producer of a bounded normalized family
spine, or a proof that own-parameter and family-parameter telescopes agree.
No parameter-mirror premise is added. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.BoundedBVar
open Rcic.Declarative

variable {E : ResolvedEnv} {n : Nat}

/-- Every conversion-at-a-sort edge in this actual type-conversion chain
has the same valuation and the same explicit level and constant bounds. -/
def Bounded (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) :
    {Γ : LCtx} → {A B : Expr Nat} → TyConvT E n Γ A B → Prop
  | _, _, _, .refl _ _ => True
  | _, _, _, .of _ _ _ _ d => LOKc σ N K d
  | _, _, _, .trans _ _ _ _ c d => Bounded σ N K c ∧ Bounded σ N K d

private theorem extract_aux (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {k : Nat} :
    {e T : Expr Nat} → (d : HasTyT E n Γ e T) → LOKt σ N K d → e = .bvar k →
      ∃ A, lookupType Γ k = some A ∧
        ∃ c : TyConvT E n Γ A T, Bounded σ N K c
  | _, _, .bvar _ j A hj, _, he => by
      injection he with hjk
      subst j
      refine ⟨A, hj, .refl Γ A, ?_⟩
      simpa only [Bounded] using True.intro
  | _, _, .conv _ _ A B u d c, hd, he => by
      obtain ⟨S, hS, q, hq⟩ := extract_aux σ N K d hd.1 he
      refine ⟨S, hS, .trans Γ S A B q (.of Γ A B u c), ?_⟩
      simpa only [Bounded] using And.intro hq hd.2
  | _, _, .sort _ _, _, he => by cases he
  | _, _, .const _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .pi _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .lam _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .app _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .letE _ _ _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .lit _ _ _ _, _, he => by cases he

/-- The source type is the literal lookup result in the original context.
All conversion bounds come from d; no separately admitted mirror is used. -/
theorem extract (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {k : Nat} {T : Expr Nat}
    (d : HasTyT E n Γ (.bvar k) T) (hd : LOKt σ N K d) :
    ∃ A, lookupType Γ k = some A ∧
      ∃ c : TyConvT E n Γ A T, Bounded σ N K c :=
  extract_aux σ N K d hd rfl

/-- A known lookup result fixes the extracted chain's source exactly. -/
theorem extract_of_lookup (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {k : Nat} {A T : Expr Nat}
    (hlook : lookupType Γ k = some A)
    (d : HasTyT E n Γ (.bvar k) T) (hd : LOKt σ N K d) :
    ∃ c : TyConvT E n Γ A T, Bounded σ N K c := by
  obtain ⟨S, hS, c, hc⟩ := extract σ N K d hd
  have hSA : S = A := Option.some.inj (hS.symm.trans hlook)
  cases hSA
  exact ⟨c, hc⟩

/-- Literal composition with bounded conversion soundness. The environment
must fit the entire original Γ, including every intervening local binder. -/
theorem chain_sound (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) {Γ : LCtx}
    (hE : EnvSound (mkM P μ) σ K E n)
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ) :
    {A B : Expr Nat} → (c : TyConvT E n Γ A B) → Bounded σ 4 K c →
      Equiv (den (mkM P μ) σ ρ A) (den (mkM P μ) σ ρ B)
  | _, _, .refl _ _, _ => Equiv.rfl
  | _, _, .of _ _ _ _ d, hd => by
      have hd' : LOKc σ 4 K d := by simpa only [Bounded] using hd
      exact (sound_conv (P.good _ rfl) hE d hd' ρ hρ).1
  | _, _, .trans _ _ _ _ c d, hcd => by
      have hcd' : Bounded σ 4 K c ∧ Bounded σ 4 K d := by
        simpa only [Bounded] using hcd
      exact (chain_sound P μ σ K hE ρ hρ c hcd'.1).trans
        (chain_sound P μ σ K hE ρ hρ d hcd'.2)

/-- The extracted chain and its semantic interpretation compose without
an additional conversion or mirror hypothesis. This does not manufacture
the original-context fit needed by the soundness call. -/
theorem lookup_equiv (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) {Γ : LCtx} {k : Nat} {A T : Expr Nat}
    (hE : EnvSound (mkM P μ) σ K E n)
    (hlook : lookupType Γ k = some A)
    (d : HasTyT E n Γ (.bvar k) T) (hd : LOKt σ 4 K d)
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ) :
    Equiv (den (mkM P μ) σ ρ A) (den (mkM P μ) σ ρ T) := by
  obtain ⟨c, hc⟩ := extract_of_lookup σ 4 K hlook d hd
  exact chain_sound P μ σ K hE ρ hρ c hc

end Rcic.F3.PSet.BoundedBVar

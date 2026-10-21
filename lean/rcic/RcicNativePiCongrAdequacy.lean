import rcic.RcicNativePiModel
import rcic.RcicNativePiHeadObs

set_option autoImplicit false

/-!
# Native Pi adequacy for the existing congruence fragment

`PiModelAudit.congrFrag_pi_semInj` proves semantic component equality.
Here the original `ConvT` derivation supplies actual native component
conversions for that same fragment. The semantic model is not assumed
sound for the computational or proof-irrelevance rules.

`CongrFrag` is reused unchanged. It lives in `Prop`; the data-valued
worker recurses on the original `ConvT`, and uses the fragment proof only
to select its original children or refute excluded constructors. No
`Nonempty` witness is selected and no choice principle is used.

Transitivity first proves that the original middle term is literally a
Pi in this fragment. Its two original child conversions produce native
observations, which are composed by the existing `PiHeadObs.trans`.
The recursive calls in symmetry, transitivity and index transport are
on original conversion children. No produced conversion is recursed on.

This constructs a restricted observation producer. It does not extend
the fragment to beta, substitution, arbitrary application observations,
proof irrelevance, or unrestricted `TyConvT`. The chain worker covers exactly original
`TyConvT.of` nodes in the same existing fragment. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.NativePiCongrAdequacy

open PiModelAudit NativePiHeadObs

variable {E : ResolvedEnv} {n : Nat}

/-- The congruence/index fragment preserves literal Pi-head shape. -/
theorem congrFrag_isPi {Γ : LCtx} {a b T : Expr Nat}
    {c : ConvT E n Γ a b T} (h : CongrFrag E n c) :
    isPiTel 1 a = isPiTel 1 b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | pi => rfl
  | lam => rfl
  | app => rfl
  | tyConv _ ih => exact ih
  | sorts => rfl
  | consts => rfl

private def piData (e : Expr Nat) (h : isPiTel 1 e = true) :
    Σ' (A B : Expr Nat), e = .pi A B := by
  cases e <;> try { exact ⟨_, _, rfl⟩ } <;> cases h

/-- Actual native observations, computed from the original conversion
in the existing congruence fragment, at any literal Pi source. -/
def observation_of_congrFrag (hW : EnvWfT E) :
    {Γ : LCtx} → (hΓ : CtxWfT E n Γ) →
    {a b T : Expr Nat} → (c : ConvT E n Γ a b T) →
    CongrFrag E n c → isPiTel 1 a = true → PiHeadObs E n Γ a b
  | Γ, hΓ, _, _, _, c, hc, ha => by
      cases c with
      | refl _ a _ _ =>
          obtain ⟨A, B, he⟩ := piData _ ha
          cases he
          exact PiHeadObs.refl A B
      | symm _ a b T c =>
          have hf : CongrFrag E n c := by cases hc with | symm hf => exact hf
          have hp := (congrFrag_isPi hf).trans ha
          exact (observation_of_congrFrag hW hΓ c hf hp).symm hW hΓ
      | trans _ a b d T c₁ c₂ =>
          have hf₁ : CongrFrag E n c₁ := by cases hc with | trans h _ => exact h
          have hf₂ : CongrFrag E n c₂ := by cases hc with | trans _ h => exact h
          have hb := (congrFrag_isPi hf₁).symm.trans ha
          exact (observation_of_congrFrag hW hΓ c₁ hf₁ ha).trans hW hΓ
            (observation_of_congrFrag hW hΓ c₂ hf₂ hb)
      | beta => cases ha
      | zeta => cases ha
      | zetaLocal => exact False.elim (by cases hc)
      | delta => cases ha
      | iota => exact False.elim (by cases hc)
      | lit => exact False.elim (by cases hc)
      | app => cases ha
      | lam => cases ha
      | pi _ A A' B B' u v hA hB =>
          exact PiHeadObs.of_components (.of Γ A A' u hA)
            (.of (.assumption A :: Γ) B B' v hB)
      | letE => exact False.elim (by cases hc)
      | sorts => cases ha
      | consts => cases ha
      | eta => cases ha
      | irr => exact False.elim (by cases hc)
      | tyConv _ a b T T' u c cT =>
          have hf : CongrFrag E n c := by cases hc with | tyConv hf => exact hf
          exact observation_of_congrFrag hW hΓ c hf ha

/-- Native component conversion read-off for the existing fragment.
The returned values are in `Type`, not merely semantic equalities. -/
def components_of_congrFrag (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B A' B' T : Expr Nat} (c : ConvT E n Γ (.pi A B) (.pi A' B') T)
    (hc : CongrFrag E n c) :
    TyConvT E n Γ A A' × TyConvT E n (.assumption A :: Γ) B B' :=
  (observation_of_congrFrag hW hΓ c hc rfl).components

/-- The existing fragment predicate, checked at every original `of`
node of a `TyConvT` chain. This is a restriction, not a semantic premise
asserted for arbitrary native type conversions. -/
def ChainCongrFrag : {Γ : LCtx} → {a b : Expr Nat} → TyConvT E n Γ a b → Prop
  | _, _, _, .refl _ _ => True
  | _, _, _, .of _ _ _ _ c => CongrFrag E n c
  | _, _, _, .trans _ _ _ _ c₁ c₂ => ChainCongrFrag c₁ ∧ ChainCongrFrag c₂

/-- Literal Pi-head preservation through the original type chain. -/
theorem chainCongr_isPi {Γ : LCtx} : {a b : Expr Nat} →
    (c : TyConvT E n Γ a b) → ChainCongrFrag c → isPiTel 1 a = isPiTel 1 b
  | _, _, .refl _ _, _ => rfl
  | _, _, .of _ _ _ _ c, h => congrFrag_isPi (by simpa only [ChainCongrFrag] using h)
  | _, _, .trans _ _ _ _ c₁ c₂, h => by
      have hh : ChainCongrFrag c₁ ∧ ChainCongrFrag c₂ := by
        simpa only [ChainCongrFrag] using h
      exact (chainCongr_isPi c₁ hh.1).trans (chainCongr_isPi c₂ hh.2)

/-- The observation producer for original `TyConvT` chains whose `of`
nodes lie in the existing congruence fragment. Every recursive call is
on an original `TyConvT` child. -/
def observation_of_congrChain (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) : {a b : Expr Nat} →
    (c : TyConvT E n Γ a b) → ChainCongrFrag c → isPiTel 1 a = true →
    PiHeadObs E n Γ a b
  | a, _, .refl _ _, _, ha => by
      obtain ⟨A, B, he⟩ := piData a ha
      cases he
      exact PiHeadObs.refl A B
  | _, _, .of _ _ _ _ c, h, ha =>
      observation_of_congrFrag hW hΓ c (by simpa only [ChainCongrFrag] using h) ha
  | _, _, .trans _ _ _ _ c₁ c₂, h, ha => by
      have hh : ChainCongrFrag c₁ ∧ ChainCongrFrag c₂ := by
        simpa only [ChainCongrFrag] using h
      exact (observation_of_congrChain hW hΓ c₁ hh.1 ha).trans hW hΓ
        (observation_of_congrChain hW hΓ c₂ hh.2
          ((chainCongr_isPi c₁ hh.1).symm.trans ha))

/-- Native component read-off for the restricted original type chain. -/
def components_of_congrChain (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (c : TyConvT E n Γ (.pi A B) (.pi A' B')) (hc : ChainCongrFrag c) :
    TyConvT E n Γ A A' × TyConvT E n (.assumption A :: Γ) B B' :=
  (observation_of_congrChain hW hΓ c hc rfl).components

#print axioms ChainCongrFrag
#print axioms chainCongr_isPi
#print axioms observation_of_congrChain
#print axioms components_of_congrChain

#print axioms congrFrag_isPi
#print axioms observation_of_congrFrag
#print axioms components_of_congrFrag

end Rcic.Declarative.NativeValleys.NativePiCongrAdequacy

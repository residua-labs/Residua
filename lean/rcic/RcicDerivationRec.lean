/-
RCIC derivation recursion — the mutual-induction infrastructure for 02's
metatheory, and the RULING WITNESS for the knife-2 structural question.

The lane reported: Lean 4's `induction` tactic rejects the HasTy/Step/Conv
mutual family ("the eliminator has multiple motives"), and asked whether to
① merge the three judgments into one Derivation inductive, or ② switch to
well-founded recursion on a size measure.

RULING, carried by this compiling file rather than by prose:

  ① is REJECTED on M-001 grounds: 02 presents THREE mutually defined
    judgments; a merged Derivation type mechanizes a different presentation
    of the theory — the exact second-authority shape M-001 refuses.
  ③ (not on the lane's list) is ADOPTED: mutual `def`s over the family —
    the equation compiler supports structural recursion on mutual
    inductives; the `induction` TACTIC is what does not, and nothing
    obliges the proofs to use it. The sizes below are the compiling
    demonstration, and `sizeHasTy_pos` is the proof-idiom template:
    pattern-match on the derivation, recurse mutually, no tactic-level
    induction anywhere.
  ② is thereby unnecessary, but its prerequisite (the size measure) falls
    out of ③ for free and is kept for any future well-founded argument.
-/
import rcic.RcicDeclarative

namespace Rcic.Declarative

mutual

/-- Size of a typing derivation (counts every rule application). -/
def sizeHasTy {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {e A : Expr Nat} → HasTy E n Γ e A → Nat
  | _, _, _, .sort _ _ => 1
  | _, _, _, .bvar _ _ _ _ => 1
  | _, _, _, .const _ _ _ _ _ _ _ => 1
  | _, _, _, .pi _ _ _ _ _ hA hB => sizeHasTy hA + sizeHasTy hB + 1
  | _, _, _, .lam _ _ _ _ _ hA hb => sizeHasTy hA + sizeHasTy hb + 1
  | _, _, _, .app _ _ _ _ _ hf ha => sizeHasTy hf + sizeHasTy ha + 1
  | _, _, _, .letE _ _ _ _ _ hA hv hb =>
      sizeHasTy hA + sizeHasTy hv + sizeHasTy hb + 1
  | _, _, _, .lit _ _ _ hexp => sizeHasTy hexp + 1
  | _, _, _, .conv _ _ _ _ h hc => sizeHasTy h + sizeConv hc + 1

/-- Size of a step derivation. -/
def sizeStep {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} → Step E n Γ a b → Nat
  | _, _, _, .beta _ _ _ _ => 1
  | _, _, _, .zeta _ _ _ _ => 1
  | _, _, _, .zetaLocal _ _ _ _ => 1
  | _, _, _, .delta _ _ _ _ _ _ _ _ => 1
  | _, _, _, .iota _ _ _ _ => 1
  | _, _, _, .lit _ _ _ _ => 1

/-- Size of a convertibility derivation. -/
def sizeConv {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} → Conv E n Γ a b → Nat
  | _, _, _, .refl _ _ => 1
  | _, _, _, .symm _ _ _ h => sizeConv h + 1
  | _, _, _, .trans _ _ _ _ h1 h2 => sizeConv h1 + sizeConv h2 + 1
  | _, _, _, .step _ _ _ h => sizeStep h + 1
  | _, _, _, .app _ _ _ _ _ h1 h2 => sizeConv h1 + sizeConv h2 + 1
  | _, _, _, .lam _ _ _ _ _ hA hb => sizeConv hA + sizeConv hb + 1
  | _, _, _, .pi _ _ _ _ _ hA hb => sizeConv hA + sizeConv hb + 1
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb => sizeConv hA + sizeConv hv + sizeConv hb + 1
  | _, _, _, .sorts _ _ _ _ => 1
  | _, _, _, .consts _ _ _ _ _ => 1
  | _, _, _, .eta _ _ _ _ h => sizeHasTy h + 1
  | _, _, _, .irr _ _ _ _ hP hp hq => sizeHasTy hP + sizeHasTy hp + sizeHasTy hq + 1

end

mutual

/-- Template for every metatheory proof over the family: mutual recursion by
pattern match — no `induction` tactic anywhere. Reuse this shape for
DT-003..013. -/
theorem sizeHasTy_pos {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {e A : Expr Nat} → (h : HasTy E n Γ e A) → 1 ≤ sizeHasTy h
  | _, _, _, .sort _ _ => by simp [sizeHasTy]
  | _, _, _, .bvar _ _ _ _ => by simp [sizeHasTy]
  | _, _, _, .const _ _ _ _ _ _ _ => by simp [sizeHasTy]
  | _, _, _, .pi _ _ _ _ _ hA hB => by simp [sizeHasTy]
  | _, _, _, .lam _ _ _ _ _ hA hb => by simp [sizeHasTy]
  | _, _, _, .app _ _ _ _ _ hf ha => by simp [sizeHasTy]
  | _, _, _, .letE _ _ _ _ _ hA hv hb => by simp [sizeHasTy]
  | _, _, _, .lit _ _ _ hexp => by simp only [sizeHasTy]; omega
  | _, _, _, .conv _ _ _ _ h hc => by simp [sizeHasTy]

theorem sizeConv_pos {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} → (h : Conv E n Γ a b) → 1 ≤ sizeConv h
  | _, _, _, .refl _ _ => by simp [sizeConv]
  | _, _, _, .symm _ _ _ h => by simp [sizeConv]
  | _, _, _, .trans _ _ _ _ h1 h2 => by simp [sizeConv]
  | _, _, _, .step _ _ _ h => by simp [sizeConv]
  | _, _, _, .app _ _ _ _ _ h1 h2 => by simp [sizeConv]
  | _, _, _, .lam _ _ _ _ _ hA hb => by simp [sizeConv]
  | _, _, _, .pi _ _ _ _ _ hA hb => by simp [sizeConv]
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb => by simp [sizeConv]
  | _, _, _, .sorts _ _ _ _ => by simp [sizeConv]
  | _, _, _, .consts _ _ _ _ _ => by simp [sizeConv]
  | _, _, _, .eta _ _ _ _ h => by simp [sizeConv]
  | _, _, _, .irr _ _ _ _ hP hp hq => by simp [sizeConv]

end

end Rcic.Declarative

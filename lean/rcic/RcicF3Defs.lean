import rcic.RcicTypedGroupPins

/-!
# F3: the consistency target and its premises (definitions)

The statement layer of the F3 consistency line, with no model and no class
theorem. It is kept separate so that statements about the soundness tier can
name it before the model lands.

- `Choice.{u}`: indefinite description for `PSet.{u}`-sized types, the choice
  premise of the set model. It is a hypothesis, never an axiom.
- `Premises4`: the residual assumptions of the height-4 model, as data:
  decidability of every proposition and `Choice.{0} … Choice.{3}`.
- `LevelsOK`, `LOKt`, `LOKc`: the level bound on a derivation. Every sort
  level, every level a `pi` or conversion rule introduces, and (against `K r`)
  every instance of a constant `r` evaluates at `σ` to at most the bound.
- `LevelsBelow N K D`: `LOKt` at `σ = fun _ => 0`, for a closed derivation `D`.
- `AxiomFreeEnv'`: no member is of class axiom.
- `RcicConsistentAsStated`: the target as first stated. It is false:
  `rcicConsistentAsStated_false`, at the admitted `trueEnvU`, because
  `falseFamMember` is only "a `Prop` family with no parameter".
- `RcicConsistentEmpty`: the corrected target. The family at 0 has its
  recursor at 1, so it has no constructor. Its hypotheses are inhabited
  (`rcicConsistentEmpty_hyps`).
- `RcicConsistentEmptyBelow N K`: the same target restricted to derivations
  within the level bound. This is the form a relative-consistency model
  proves: by Gödel's second theorem a model inside Lean bounds the levels.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe u

/-- The F3 choice premise: indefinite description for `PSet.{u}`-sized types.
It is a hypothesis of every theorem that uses it, never an axiom. -/
def Choice : Type (u + 2) := ∀ {α : Type (u + 1)} (p : α → Prop), (∃ x, p x) → {x : α // p x}

namespace PSet

/-- The residual assumptions of the height-4 model, as data (so that `dec`
is never a local instance). -/
structure Premises4 : Type 5 where
  dec : ∀ p : Prop, Decidable p
  c0 : Choice.{0}
  c1 : Choice.{1}
  c2 : Choice.{2}
  c3 : Choice.{3}

section Bounds

variable {E : ResolvedEnv} {n : Nat} (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)

/-- Every level of the list evaluates to at most `b`. -/
def LevelsOK (b : Nat) (ls : List Level) : Prop := ∀ l, l ∈ ls → evalTotal σ l ≤ b

mutual
/-- The level bound, typing side. -/
def LOKt : {Γ : LCtx} → {e A : Expr Nat} → HasTyT E n Γ e A → Prop
  | _, _, _, .sort _ l => evalTotal σ l + 1 ≤ N
  | _, _, _, .bvar _ _ _ _ => True
  | _, _, _, .const _ r ls _ _ _ _ => LevelsOK σ (K r) ls
  | _, _, _, .pi _ _ u _ v hA hB => evalTotal σ u ≤ N ∧ evalTotal σ v ≤ N ∧ LOKt hA ∧ LOKt hB
  | _, _, _, .lam _ _ _ _ _ hA hbody => LOKt hA ∧ LOKt hbody
  | _, _, _, .app _ _ _ _ _ hf ha => LOKt hf ∧ LOKt ha
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb => LOKt hA ∧ LOKt hv ∧ LOKt hb
  | _, _, _, .lit _ _ _ hexp => LOKt hexp
  | _, _, _, .conv _ _ _ _ _ h hc => LOKt h ∧ LOKc hc

/-- The level bound, conversion side. -/
def LOKc : {Γ : LCtx} → {a b T : Expr Nat} → ConvT E n Γ a b T → Prop
  | _, _, _, _, .refl _ _ _ h => LOKt h
  | _, _, _, _, .symm _ _ _ _ h => LOKc h
  | _, _, _, _, .trans _ _ _ _ _ h1 h2 => LOKc h1 ∧ LOKc h2
  | _, _, _, _, .beta _ _ _ _ _ _ hA hbody harg => LOKt hA ∧ LOKt hbody ∧ LOKt harg
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb => LOKt hA ∧ LOKt hv ∧ LOKt hb
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv => LOKt hv
  | _, _, _, _, .delta _ r ls _ _ _ _ _ _ _ hb => LevelsOK σ (K r) ls ∧ LOKt hb
  | _, _, _, _, .iota _ _ _ _ _ hl hr => LOKt hl ∧ LOKt hr
  | _, _, _, _, .lit _ _ _ _ _ hexp => LOKt hexp
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2 => LOKc h1 ∧ LOKc h2
  | _, _, _, _, .lam _ _ _ _ _ _ _ hA hb => LOKc hA ∧ LOKc hb
  | _, _, _, _, .pi _ _ _ _ _ u v hA hB => evalTotal σ u ≤ N ∧ evalTotal σ v ≤ N ∧ LOKc hA ∧ LOKc hB
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb => LOKc hA ∧ LOKc hv ∧ LOKc hb
  | _, _, _, _, .sorts _ l₁ _ _ => evalTotal σ l₁ + 1 ≤ N
  | _, _, _, _, .consts _ r ls ls' _ _ _ _ _ _ => LevelsOK σ (K r) ls ∧ LevelsOK σ (K r) ls'
  | _, _, _, _, .eta _ _ _ _ h => LOKt h
  | _, _, _, _, .irr _ _ _ _ hP hp hq => LOKt hP ∧ LOKt hp ∧ LOKt hq
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA => LOKc h ∧ LOKc hA
end

end Bounds

/-- The level bound on a derivation, with every universe parameter at `0`:
sort levels and the levels `pi`/conversion rules introduce at most `N`
(a sort's own level strictly below `N`), the instance levels of each
constant `r` at most `K r`. -/
def LevelsBelow {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat} (N : Nat) (K : Nat → Nat)
    (D : HasTyT E n Γ e A) : Prop :=
  LOKt (fun _ => 0) N K D

/-- No axiom member. -/
def AxiomFreeEnv' (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m → m.mclass ≠ .axiomM

/-- The target as first stated. -/
def RcicConsistentAsStated : Prop :=
  ∀ (E : ResolvedEnv), EnvWfT E → AxiomFreeEnv' E → E.members 0 = some falseFamMember →
    ∀ (n : Nat) (e : Expr Nat), HasTyT E n [] e (.const 0 []) → False

theorem trueEnvU_axiomFree : AxiomFreeEnv' trueEnvU := by
  intro r m h
  match r, h with
  | 0, h => cases h; exact fun h => MemberClass.noConfusion h
  | 1, h => cases h; exact fun h => MemberClass.noConfusion h
  | 2, h => cases h; exact fun h => MemberClass.noConfusion h
  | r + 3, h =>
      have h' : trueEnvU.members (r + 3) = none := by
        simp only [trueEnvU, truePrefix, trueFamOnly, extendEnv, emptyEnv]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [h'] at h; exact Option.noConfusion h

/-- **The stated target is false**: `True.intro` proves the family at 0 of `trueEnvU`. -/
theorem rcicConsistentAsStated_false : ¬ RcicConsistentAsStated := fun h =>
  h trueEnvU trueEnvUWfT trueEnvU_axiomFree rfl 0 (.const 1 [])
    (HasTyT.const [] 1 [] trueIntroMember rfl rfl rfl)

/-- The corrected target: the family at 0 is `Prop`-typed and its recursor sits at 1,
so it has no constructor. -/
def RcicConsistentEmpty : Prop :=
  ∀ (E : ResolvedEnv), EnvWfT E → AxiomFreeEnv' E → E.members 0 = some falseFamMember →
    E.members 1 = some falseRecMemberU →
    ∀ (n : Nat) (e : Expr Nat), HasTyT E n [] e (.const 0 []) → False

/-- The corrected target for derivations within the level bound `N` and the
instance bound `K`. -/
def RcicConsistentEmptyBelow (N : Nat) (K : Nat → Nat) : Prop :=
  ∀ (E : ResolvedEnv), EnvWfT E → AxiomFreeEnv' E → E.members 0 = some falseFamMember →
    E.members 1 = some falseRecMemberU →
    ∀ (n : Nat) (e : Expr Nat) (D : HasTyT E n [] e (.const 0 [])), LevelsBelow N K D → False

/-- The unbounded target gives every bounded one. -/
theorem rcicConsistentEmptyBelow_of (h : RcicConsistentEmpty) (N : Nat) (K : Nat → Nat) :
    RcicConsistentEmptyBelow N K :=
  fun E hW hA h0 h1 n e D _ => h E hW hA h0 h1 n e D

theorem falseEnvU_axiomFree : AxiomFreeEnv' falseEnvU := by
  intro r m h
  match r, h with
  | 0, h => cases h; exact fun h => MemberClass.noConfusion h
  | 1, h => cases h; exact fun h => MemberClass.noConfusion h
  | r + 2, h =>
      have h' : falseEnvU.members (r + 2) = none := by
        simp only [falseEnvU, falsePrefix, extendEnv, emptyEnv]
        rw [if_neg (by omega), if_neg (by omega)]
      rw [h'] at h; exact Option.noConfusion h

/-- The corrected target's hypotheses are inhabited, at the admitted `falseEnvU`. -/
theorem rcicConsistentEmpty_hyps :
    Nonempty (EnvWfT falseEnvU) ∧ AxiomFreeEnv' falseEnvU ∧ falseEnvU.members 0 = some falseFamMember ∧
      falseEnvU.members 1 = some falseRecMemberU :=
  ⟨⟨falseEnvUWfT⟩, falseEnvU_axiomFree, rfl, rfl⟩

end PSet

end Rcic.F3

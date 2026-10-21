/- rcic: DT-025/A-6 S0-N N0 — the legacy `Normalizing` row is FALSE.
Same shape as `sortConvChar_false`: the unchecked proof-irrelevance
collapse types a growing ω = (λx:s0. x (x x)) (λx:s0. x (x x)) in the
empty context at `sort 0`, and every `ParRedStar`-reachable term keeps
a β-redex whose contraction fails `eqExprN`, so the endpoint clause
cannot hold. The collapse supplies `sort 0 : sort 0` (`propSelfTyped`)
and `Π s0 s0 : sort 0` (`refutPiIsProp`), hence `Conv s0 (Π s0 s0)` by
`Conv.irr`. Inversions reuse `parRed_app`/`parRed_lam`/`parRed_sort`/
`parRed_bvar`. No `sorry`. -/

import rcic.RcicUntypedConvCollapse
import rcic.RcicConvChar
import rcic.RcicParRedIota
import rcic.RcicParRedDiamond
import rcic.RcicParRedWeight

namespace Rcic.Declarative.NormalizingFalse

open Rcic.Declarative
open Rcic.Declarative.UntypedConvCollapse

/-- `x (x x)`, the body of the diverging λ. -/
def omBody : Expr Nat := .app (.bvar 0) (.app (.bvar 0) (.bvar 0))

/-- The ω-lam: `λ (x : sort u). x (x x)`. -/
def omLam (u : Level) : Expr Nat := .lam (.sort u) omBody

/-- Reachable-Ω invariant: binary `app`-trees whose leaves are
`omLam u` with `u =ₙ 0`. Every `ParRedStar`-reachable term from `ω`
is a nonempty such tree. -/
inductive OmTree : Expr Nat → Prop
  | leaf {u : Level} (h : eqN u .zero) : OmTree (omLam u)
  | node {F X : Expr Nat} : OmTree F → OmTree X → OmTree (.app F X)

/-- Spine head for the `iotaSpine`/recCall vacuity argument: peels
`app`s to the leftmost symbol. -/
def headSym : Expr Nat → Bool
  | .app f _ => headSym f
  | .const _ _ => true
  | _ => false

theorem headSym_foldApps (l : List (Expr Nat)) (f : Expr Nat) :
    headSym (foldApps f l) = headSym f := by
  induction l generalizing f with
  | nil => rfl
  | cons x xs ih => exact ih (.app f x)

theorem omTree_headSym {t : Expr Nat} (h : OmTree t) : headSym t = false := by
  induction h with
  | leaf _ => rfl
  | node _ _ ihF _ => exact ihF

/-- A `const`-headed `recCall` can never equal a term whose spine head
is not a `const`. Kills the `iotaSpine` arm everywhere below. -/
theorem recCall_ne_of_headSym {r : Nat} {lsR : List Level}
    {pre : List (Expr Nat)} {M t : Expr Nat} (ht : headSym t = false) :
    recCall (.const r lsR) pre M ≠ t := by
  intro heq
  have hs := congrArg headSym heq
  have hL : headSym (recCall (.const r lsR) pre M) = true :=
    (headSym_foldApps (pre ++ [M]) (.const r lsR)).trans rfl
  rw [hL, ht] at hs
  exact Bool.noConfusion hs

-- ### inversions (via the landed `parRed_*` matchers)

theorem parRed_bvar0_assump {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A t : Expr Nat}
    (h : ParRed E n (LocalDecl.assumption A :: Γ) (.bvar 0) t) :
    t = .bvar 0 := by
  rcases parRed_bvar h rfl with heq | ⟨A', v, v', hget, _, _⟩
  · exact heq
  · rw [show (LocalDecl.assumption A :: Γ).get? 0 =
        some (.assumption A) from rfl] at hget
    cases hget

theorem parRed_omBody {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat}
    {t : Expr Nat}
    (h : ParRed E n (LocalDecl.assumption A :: Γ) omBody t) :
    t = omBody := by
  rcases parRed_app h rfl with ⟨f', x', heq, hf, hx⟩ | inr
  · rcases parRed_app hx rfl with ⟨f2', a2', heq2, hf2, ha2⟩ | inr2
    · subst heq heq2
      rw [parRed_bvar0_assump hf, parRed_bvar0_assump hf2,
        parRed_bvar0_assump ha2]
      exact rfl
    · cases inr2 with
      | inl tb =>
          obtain ⟨A', body, A'', body', x2', hf_eq, _, _, _, _⟩ := tb
          exact Expr.noConfusion hf_eq
      | inr w =>
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hEqL, _⟩ := w
          exact (recCall_ne_of_headSym (t := .app (.bvar 0) (.bvar 0))
              rfl hEqL).elim
  · cases inr with
    | inl tb =>
        obtain ⟨A', body, A'', body', x', hf_eq, _, _, _, _⟩ := tb
        exact Expr.noConfusion hf_eq
    | inr w =>
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hEqL, _⟩ := w
        exact (recCall_ne_of_headSym (t := omBody) rfl hEqL).elim

theorem omTree_lam_inv {A b : Expr Nat} (h : OmTree (.lam A b)) :
    ∃ u, eqN u .zero ∧ A = .sort u ∧ b = omBody := by
  cases h with
  | leaf hu => exact ⟨_, hu, rfl, rfl⟩

theorem eqExprN_app_inv {a b c d : Expr Nat}
    (h : eqExprN (.app a b) (.app c d)) : eqExprN a c ∧ eqExprN b d := by
  cases h with
  | app hf ha => exact ⟨hf, ha⟩

theorem eqExprN_app_lam {a b c d : Expr Nat} :
    ¬ eqExprN (.app a b) (.lam c d) := by
  intro h
  cases h

-- ### step lemmas

theorem omTree_step {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {N N' : Expr Nat}
    (h : ParRed E n Γ N N') (hN : OmTree N) : OmTree N' := by
  induction hN generalizing N' with
  | leaf hu =>
      obtain ⟨A', b', heq, hA, hb⟩ := parRed_lam h rfl
      subst heq
      obtain ⟨u', hAeq, hequ⟩ := parRed_sort hA rfl
      subst hAeq
      have hb' := parRed_omBody hb
      subst hb'
      exact .leaf fun ρ => ((hequ ρ).symm).trans (hu ρ)
  | node hF hX ihF ihX =>
      rcases parRed_app h rfl with ⟨f', x', heq, hf, hx⟩ | inr
      · subst heq
        exact .node (ihF hf) (ihX hx)
      · rcases inr with ⟨A, body, A', body', x', hf_eq, hA, hb, hx, he⟩ | iota
        · obtain ⟨u, hu, hAe, hbe⟩ := omTree_lam_inv (hf_eq ▸ hF)
          subst hAe hbe he
          have hb' := parRed_omBody hb
          subst hb'
          have harg := ihX hx
          exact .node harg (.node harg harg)
        · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hEqL, _⟩ := iota
          exact (recCall_ne_of_headSym
            (omTree_headSym (.node hF hX)) hEqL).elim

/-- A reachable Ω term stays `app`-headed: `instantiate0 X omBody` is
`app`-headed, and every other reachable arm is congruence. -/
theorem omTree_step_app {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {F X N' : Expr Nat}
    (h : ParRed E n Γ (.app F X) N') (hN : OmTree (.app F X)) :
    ∃ F' X', N' = .app F' X' ∧ OmTree F' ∧ OmTree X' := by
  cases hN with
  | node hF hX =>
      rcases parRed_app h rfl with ⟨f', x', heq, hf, hx⟩ | inr
      · subst heq
        exact ⟨_, _, rfl, omTree_step hf hF, omTree_step hx hX⟩
      · rcases inr with ⟨A, body, A', body', x', hf_eq, hA, hb, hx, he⟩ | iota
        · obtain ⟨u, hu, hAe, hbe⟩ := omTree_lam_inv (hf_eq ▸ hF)
          subst hAe hbe
          have hb' := parRed_omBody hb
          subst hb'
          have harg := omTree_step hx hX
          exact ⟨_, _, he, harg, .node harg harg⟩
        · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hEqL, _⟩ := iota
          exact (recCall_ne_of_headSym
            (omTree_headSym (.node hF hX)) hEqL).elim

/-- The invariant transported forward along `ParRedStar`. -/
theorem omTree_star {E : ResolvedEnv} {n : Nat} {a b : Expr Nat}
    (h : ParRedStar E n [] a b) :
    OmTree a → (∃ F X, a = .app F X) →
    OmTree b ∧ ∃ F X, b = .app F X := by
  induction h with
  | refl => intro ha haa; exact ⟨ha, haa⟩
  | tail hstep _ ih =>
      intro ha haa
      obtain ⟨F, X, heq⟩ := haa
      subst heq
      obtain ⟨F', X', hN', hF', hX'⟩ := omTree_step_app hstep ha
      subst hN'
      exact ih (.node hF' hX') ⟨_, _, rfl⟩

/-- `λ x:s0. x (x x)`. -/
def omLamZero : Expr Nat := omLam .zero

/-- `ω = (λx:s0. x (x x)) (λx:s0. x (x x))`. -/
def omApp : Expr Nat := .app omLamZero omLamZero

theorem omTree_reach {E : ResolvedEnv} {n : Nat} {N : Expr Nat}
    (h : ParRedStar E n [] omApp N) :
    OmTree N ∧ ∃ F X, N = .app F X :=
  omTree_star h (.node (.leaf fun _ => rfl) (.leaf fun _ => rfl))
    ⟨_, _, rfl⟩

/-- The endpoint fails: every nonempty Ω-tree has a `ParRed` step whose
target is not `eqExprN`. Structural recursion on `OmTree F`: when `F`
is a node the bad step lives inside it and lifts through `.app`; when
`F` is an ω-leaf the head β-step is the witness — its reduct
`app X (app X X)` fails `eqExprN` at the argument side when `X` is a
leaf (`app` vs `lam`) or at the function side when `X` is a node
(the reduct's function is `app`-headed, the original's is `lam`). -/
theorem omTree_stepBad {E : ResolvedEnv} {n : Nat} {F X : Expr Nat}
    (hF : OmTree F) (hX : OmTree X) :
    Nonempty (Σ' (N' : Expr Nat), ParRed E n [] (.app F X) N' ×'
      (eqExprN N' (.app F X) → False)) := by
  induction hF generalizing X with
  | leaf hu =>
      refine ⟨⟨.app X (.app X X),
        .beta [] _ _ _ _ _ _ (.refl [] _) (.refl _ _) (.refl [] X),
        fun heq => ?_⟩⟩
      obtain ⟨hfun, harg⟩ := eqExprN_app_inv heq
      cases hX with
      | leaf _ => exact eqExprN_app_lam harg
      | node _ _ => exact eqExprN_app_lam hfun
  | node hF1 hF2 ih1 _ =>
      obtain ⟨w⟩ := ih1 hF2
      exact ⟨.app w.1 X, .app [] _ _ _ _ w.2.1 (.refl [] X), fun heq =>
        w.2.2 (eqExprN_app_inv heq).1⟩

/-- The collapse typing: `ω : sort 0` in the empty context. -/
def omApp_typed {E : ResolvedEnv} {n : Nat} :
    HasTy E n [] omApp (.sort .zero) :=
  have hPiSS : HasTy E n [] (.pi (.sort .zero) (.sort .zero)) (.sort .zero) :=
    refutPiIsProp [] (.sort .zero) (.succ .zero) (.sort .zero)
      (.sort [] .zero) (propSelfTyped _)
  have hconv : Conv E n [] (.sort .zero) (.pi (.sort .zero) (.sort .zero)) :=
    .irr [] (.sort .zero) (.sort .zero) (.pi (.sort .zero) (.sort .zero))
      (propSelfTyped []) (propSelfTyped []) hPiSS
  have hconv1 : Conv E n [LocalDecl.assumption (.sort .zero)] (.sort .zero)
      (.pi (.sort .zero) (.sort .zero)) :=
    .irr _ _ _ _ (propSelfTyped _) (propSelfTyped _)
      (refutPiIsProp _ _ _ _ (.sort _ .zero) (propSelfTyped _))
  have hx0 : HasTy E n [LocalDecl.assumption (.sort .zero)] (.bvar 0)
      (.sort .zero) :=
    .bvar _ 0 _ rfl
  have hxPi : HasTy E n [LocalDecl.assumption (.sort .zero)] (.bvar 0)
      (.pi (.sort .zero) (.sort .zero)) :=
    .conv _ _ _ _ hx0 hconv1
  have hxx : HasTy E n [LocalDecl.assumption (.sort .zero)]
      (.app (.bvar 0) (.bvar 0)) (.sort .zero) :=
    .app _ _ _ _ _ hxPi hx0
  have hxxx : HasTy E n _ (.app (.bvar 0) (.app (.bvar 0) (.bvar 0)))
      (.sort .zero) :=
    .app _ _ _ _ _ hxPi hxx
  have hlam : HasTy E n [] omLamZero (.pi (.sort .zero) (.sort .zero)) :=
    .lam [] (.sort .zero) (.succ .zero) omBody (.sort .zero)
      (.sort [] .zero) hxxx
  have hlamP : HasTy E n [] omLamZero (.sort .zero) :=
    .conv _ _ _ _ hlam (.symm [] _ _ hconv)
  .app [] _ _ _ _ hlam hlamP

/-- The row itself: `Normalizing` is false at every well-formed
environment — the collapse fixture works at `[]` regardless of `E`. -/
theorem normalizing_false {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) :
    Normalizing E n → False := by
  intro hN
  obtain ⟨N, hstar, hend⟩ := hN hE [] omApp (.sort .zero) .nil omApp_typed
  obtain ⟨hOm, F, X, hNX⟩ := omTree_reach hstar
  subst hNX
  cases hOm with
  | node hF hX =>
      obtain ⟨wit⟩ := omTree_stepBad hF hX
      exact wit.2.2 (hend wit.1 wit.2.1)

#print axioms normalizing_false

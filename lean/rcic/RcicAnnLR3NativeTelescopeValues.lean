import rcic.RcicAnnLR3NativeMemberValues

/-!
# Native constant telescopes with retained result codes

A closed native lambda tower ignores its raw arguments and returns the
native tagged neutral type. Its application equations hold at arbitrary
raw arguments, including empty ones. At the final result the actual
retained code and its universe membership are constructed. This does
not assert a dependent telescope CodeSystem or a source constant arm.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.NativeTelescopeValues

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements

/-- Native domain annotations do not contribute observations. The
placeholder annotation is not a claim about source member typing. -/
def term : Nat → Option Nat → Nat → Expr Nat
  | 0, k, name => NativeMemberValues.term k name
  | n + 1, k, name => .lam (.sort .zero) (term n k name)

def value (depth : Nat) (k : Option Nat) (name : Nat) : Value :=
  denI EnvI.bot (term depth k name)

theorem environment (depth : Nat) (ρ : EnvI) (k : Option Nat) (name : Nat) :
    ValueEq (denI ρ (term depth k name)) (value depth k name) := by
  induction depth generalizing ρ with
  | zero => exact NativeMemberValues.environment ρ k name
  | succ depth ih =>
      intro c
      constructor
      · intro hc
        rcases approxI_lam_inv hc with hc | ⟨g, hc, hbody⟩
        · subst c
          exact ApproxI.bot _ _
        · subst c
          apply ApproxI.lam
          intro s hs
          have h := (ih (EnvI.cons (demand s.1) ρ)).trans
            (ih (EnvI.cons (demand s.1) EnvI.bot)).symm
          exact (h s.2).mp (hbody s hs)
      · intro hc
        rcases approxI_lam_inv hc with hc | ⟨g, hc, hbody⟩
        · subst c
          exact ApproxI.bot _ _
        · subst c
          apply ApproxI.lam
          intro s hs
          have h := (ih (EnvI.cons (demand s.1) EnvI.bot)).trans
            (ih (EnvI.cons (demand s.1) ρ)).symm
          exact (h s.2).mp (hbody s hs)

theorem value_bot (depth : Nat) (k : Option Nat) (name : Nat) :
    value depth k name .bot := .bot _ _

/-- One application removes precisely one layer at every raw argument. -/
theorem application (depth : Nat) (k : Option Nat) (name : Nat) (x : Value) :
    ValueEq (NeutralPi.applyValue (value (depth + 1) k name) x)
      (value depth k name) :=
  (FunctionEval.native_lambda_application EnvI.bot (.sort .zero)
    (term depth k name) x).trans (environment depth (EnvI.cons x EnvI.bot) k name)

def applyArgs : Value → List Value → Value
  | f, [] => f
  | f, x :: xs => applyArgs (NeutralPi.applyValue f x) xs

theorem applyArgs_congr {f g : Value} (h : ValueEq f g) (xs : List Value) :
    ValueEq (applyArgs f xs) (applyArgs g xs) := by
  induction xs generalizing f g with
  | nil => exact h
  | cons x xs ih => exact ih (NeutralPi.applyValue_congr h (ValueEq.refl x))

/-- Full application returns the actual tagged native value. No code or
membership premise for the raw arguments is needed by this equation. -/
theorem applications (xs : List Value) (k : Option Nat) (name : Nat) :
    ValueEq (applyArgs (value xs.length k name) xs) (NativeMemberValues.value k name) := by
  induction xs with
  | nil => exact ValueEq.refl _
  | cons x xs ih =>
      exact (applyArgs_congr (application xs.length k name x) xs).trans ih

theorem two_applications (k : Option Nat) (name : Nat) (x y : Value) :
    ValueEq (NeutralPi.applyValue (NeutralPi.applyValue (value 2 k name) x) y)
      (NativeMemberValues.value k name) :=
  (NeutralPi.applyValue_congr (application 1 k name x) (ValueEq.refl y)).trans
    (application 0 k name y)

theorem retained_result (xs : List Value) (k name : Nat) :
    (StratifiedCandidates.universeCode k).relation
      (StratifiedCandidates.encode k (NativeMemberValues.neutralCode k name))
      (StratifiedCandidates.encode k (NativeMemberValues.neutralCode k name)) ∧
    ValueEq (applyArgs (value xs.length (some k) name) xs)
      (StratifiedCandidates.erase (k + 1)
        (StratifiedCandidates.encode k (NativeMemberValues.neutralCode k name))) := by
  refine ⟨NativeMemberValues.universe_member k name, ?_⟩
  rw [NativeMemberValues.universe_erasure]
  exact applications xs (some k) name

theorem undefined_result (xs : List Value) (name : Nat) :
    Member (NoneUniverseBoundary.TaggedChaos none)
      (applyArgs (value xs.length none name) xs) := by
  rw [NeutralCodes.valueEq_eq (applications xs none name)]
  exact NativeMemberValues.none_member name

end Rcic.Declarative.Ann.LR3.NativeTelescopeValues

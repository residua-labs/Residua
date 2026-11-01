import rcic.RcicF3EvalRoleDelta
import rcic.RcicF3EvalRawTable

/-!
# A real transparent definition exercises the all-instance delta producer

The admitted idFalse environment contains a stored transparent body. The
canonical indexed-plan installer produces its faithful table. Every level
argument list is covered, including a length-three list at values above
four, even though this definition's arity is zero. Updating the next fresh
reference arbitrarily leaves the body's equations intact.

This witnesses the delta component. It asserts neither universal recursor
soundness nor the overall checked-apex non-vacuity goal.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.EvalRoleDeltaAttack

open Rcic.Declarative

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  EvalRole.rawTable P idFalseEnvWfT

theorem faithful (P : Premises4) :
    EvalRole.Faithful RawFamily.role P (table P)
      (envCtx idFalseEnvWfT) (EvalRole.envPlan idFalseEnvWfT) idFalseEnv :=
  (EvalRole.rawTable_spec P idFalseEnvWfT).1

/-- Successful transparent lookup at an actual admitted definition. -/
theorem lookup (ls : List Level) :
    transparentBody idFalseEnv 2 ls = some idFalseBody := rfl

theorem equations (P : Premises4) (σ : Nat → Nat) :
    DeltaNormalize.BodyEquations (mkM P (table P)) idFalseEnv σ :=
  EvalRoleDelta.bodyEquations_of_faithful RawFamily.role P (table P)
    (envCtx idFalseEnvWfT) (EvalRole.envPlan idFalseEnvWfT) idFalseEnvWfT
    (fun _ _ => rfl) (faithful P) σ

/-- No bound and no arity equality is assumed in the produced equation. -/
theorem every_instance (P : Premises4) (σ : Nat → Nat) (ls : List Level)
    (ρ : Nat → PSet.{4}) :
    Equiv (table P 2 (ls.map (evalTotal σ)))
      (den (mkM P (table P)) σ ρ idFalseBody) :=
  equations P σ 2 ls idFalseBody (lookup ls) ρ

def longInstance : List Level := [.param 0, .succ (.param 1), .zero]

theorem malformed_arity : longInstance.length ≠ idFalseMember.arity := by decide

theorem high_levels : longInstance.map (evalTotal (fun i => i + 9)) = [9, 11, 0] := rfl

theorem long_high_equation (P : Premises4) (ρ : Nat → PSet.{4}) :
    Equiv (table P 2 [9, 11, 0])
      (den (mkM P (table P)) (fun i => i + 9) ρ idFalseBody) :=
  every_instance P (fun i => i + 9) longInstance ρ

/-- The interpretation installed at a fresh reference is entirely arbitrary. -/
theorem fresh_equations (P : Premises4) (X : List Nat → PSet.{4}) (σ : Nat → Nat) :
    DeltaNormalize.BodyEquations (mkM P (upd (table P) 3 X)) idFalseEnv σ :=
  EvalRoleDelta.bodyEquations_transfer P idFalseEnvWfT
    (agreeOn_upd (show idFalseEnv.members 3 = none from rfl) (table P) X)
    σ (equations P σ)

def Witness (P : Premises4) : Prop :=
  EvalRole.Faithful RawFamily.role P (table P)
    (envCtx idFalseEnvWfT) (EvalRole.envPlan idFalseEnvWfT) idFalseEnv ∧
  (∀ ls, transparentBody idFalseEnv 2 ls = some idFalseBody) ∧
  (∀ σ, DeltaNormalize.BodyEquations (mkM P (table P)) idFalseEnv σ) ∧
  longInstance.length ≠ idFalseMember.arity ∧
  longInstance.map (evalTotal (fun i => i + 9)) = [9, 11, 0] ∧
  (∀ ρ, Equiv (table P 2 [9, 11, 0])
    (den (mkM P (table P)) (fun i => i + 9) ρ idFalseBody)) ∧
  (∀ X σ, DeltaNormalize.BodyEquations (mkM P (upd (table P) 3 X)) idFalseEnv σ)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨faithful P, lookup, equations P, malformed_arity, high_levels,
    long_high_equation P, fresh_equations P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) := by
  intro h
  exact h (component_witness P) P

end Rcic.F3.PSet.EvalRoleDeltaAttack

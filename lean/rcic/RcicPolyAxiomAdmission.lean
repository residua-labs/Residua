import rcic.RcicTypedEnv
import rcic.RcicF3Defs

/-!
# Parameter-preserving bodyless axiom admission

The fixture has a genuine universe parameter in its stored type. It is an
object-language declaration, with no added proof axiom. Its constant instances
also witness that `LevelsBelow 4` does not impose an instance bound of three.
This module makes no consistency claim. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.PolyAxiomAdmission

def member : CheckedMember := ⟨.axiomM, 1, .sort (.param 0), none⟩

def env : ResolvedEnv := extendEnv emptyEnv 7 member

def admitted : EnvWfT env :=
  .axiom emptyEnv 7 (.sort (.param 0)) (.succ (.param 0)) .empty rfl
    (.sort [] (.param 0)) (fun _ => rfl) rfl

/-- The admitted declaration retains its parameter and its exact arity. -/
theorem stored_parameter : env.members 7 = some member ∧
    member.arity = 1 ∧ member.mtype = .sort (.param 0) := ⟨rfl, rfl, rfl⟩

/-- The stored parameter is genuinely outside the monomorphic scope. -/
theorem stored_type_not_monomorphic : exprLevelsBounded 0 member.mtype = false := rfl

/-- Instantiation substitutes the requested level rather than closing it to zero. -/
def use {n : Nat} (l : Level) (hl : levelBounded n l = true) :
    HasTyT env n [] (.const 7 [l]) (.sort l) :=
  .const [] 7 [l] member rfl rfl (by
    change levelBounded n l && true = true
    rw [hl]
    rfl)

def five : Level := .succ (.succ (.succ (.succ (.succ .zero))))

def highUse : HasTyT env 0 [] (.const 7 [five]) (.sort five) := use five rfl

/-- A constant leaf can instantiate the parameter above three inside the
    current height-four predicate whenever its independent `K` allows it. -/
theorem highUse_below : Rcic.F3.PSet.LevelsBelow 4 (fun _ => 5) highUse := by
  intro l hl
  have heq : l = five := List.mem_singleton.mp hl
  subst l
  exact Nat.le_refl 5

theorem highUse_above_three : ¬ Rcic.Declarative.evalTotal (fun _ => 0) five ≤ 3 := by
  decide

end Rcic.Declarative.PolyAxiomAdmission

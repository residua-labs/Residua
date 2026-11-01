import rcic.RcicF3PiRecValue
import rcic.RcicF3PendAWHiddenAttack
/-! The complete typed PendA hidden-field fixture distinguishes the repaired
admission-plan endpoint from the stored raw endpoint. The correct result is
obtained with a typed local minor. This is an operational regression, not
full group/recursor typing. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecPlanValueAttack
open Rcic.Declarative PendAWHiddenAttack

def input (M : Interp.{4}) : Nat → PSet.{4} :=
  push ([tyv pempty] ++ pempty :: ([datum, minor M] ++ ([] ++ [dataVal 1 [pempty]]))) ρ0

theorem endpoint (M : Interp.{4}) (σ : Nat → Nat) :
    Nonempty (EnvWfT PendAWHidden.eAll) ∧ PendA PendAWHidden.pNode ∧
    Equiv (RecPlanValue.endValue M σ (famDataOf PendAWHidden.pNode.a)
      (RecPlan.nodePlan PendAWHidden.pNode) (input M)) datum ∧
    Equiv (recEnd M σ (famDataOf PendAWHidden.pNode.a) (input M)) pempty ∧
    ¬ Equiv (RecPlanValue.endValue M σ (famDataOf PendAWHidden.pNode.a)
      (RecPlan.nodePlan PendAWHidden.pNode) (input M))
      (recEnd M σ (famDataOf PendAWHidden.pNode.a) (input M)) := by
  have hn : evalTotal σ (fd 4).resLevel ≠ 0 := by change 1 ≠ 0; decide
  have hmin : minorsOf (fd 4).indices.length (fd 4).ctors.length (input M) =
      [datum, minor M] := minorsOf_env [tyv pempty] pempty [datum, minor M] []
        (dataVal 1 [pempty]) ρ0 rfl rfl
  have hz : input M 0 = dataVal 1 [pempty] := by
    unfold input
    rw [push_cons_eq]
    rfl
  have ha : Equiv (RecPlanValue.endValue M σ (famDataOf PendAWHidden.pNode.a)
      (RecPlan.nodePlan PendAWHidden.pNode) (input M)) datum := by
    rw [admitted_descriptor, admitted_plan]
    unfold RecPlanValue.endValue
    rw [cond_neg hn, hmin, hz]
    exact normalized_success M 4
  have hb : Equiv (recEnd M σ (famDataOf PendAWHidden.pNode.a) (input M)) pempty := by
    rw [admitted_descriptor]
    unfold recEnd
    rw [cond_neg hn, hmin, hz]
    exact raw_failure M 4
  refine ⟨⟨PendAWHidden.envWfT⟩, PendAWHidden.pendA, ha, hb, ?_⟩
  intro h
  exact dataVal_ne_pempty 0 [] (ha.symm.trans (h.trans hb))
end Rcic.F3.PSet.RecPlanValueAttack

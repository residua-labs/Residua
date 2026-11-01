import rcic.RcicF3NormDataIotaRow
import rcic.RcicF3NormDataRecMemAttack

/-!
# A real witnessed row inside the higher-order PendA W group

The canonical installed plan's leaf row consumes the new row producer;
the other constructor remains the original higher-order W constructor.
The leaf returns the actual first minor, the height-omega value used in
the retained typed DATA recursion witness. AllSound and MemberSound are
retained from the new public member producer. This is row unfolding and
its composition witness, not the full stable typed IotaAt theorem.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDataIotaRowAttack
open Rcic.Declarative Rcic.Model.PS RawFamily PiIndex
open NormDataRecMemAttack (plan)
open RawDataRecAttack (base minors parameter)

noncomputable def leafSlot : Fin plan.node.a.constructors.length :=
  ⟨0, by
    have h := node_ctors_length
      (ctors := [(5, PendAW.leaf), (6, PendAW.node)]) plan.node rfl
    rw [h]
    exact Nat.zero_lt_succ 1⟩

theorem leaf_fields : (plan.node.a.constructorViews leafSlot).fields = [] := by
  rcases (PendAWGroup.views plan.node leafSlot).2.2 with ⟨h, _⟩ | ⟨_, h⟩
  · exact h
  · change (0 : Nat) = 1 at h
    cases h

theorem leaf_kinds : analyzeFields plan.node.a.family.ref
    (plan.node.a.constructorViews leafSlot).fields = some [] := by
  rw [leaf_fields]
  rfl

theorem cached_leaf : EvalPlanNormal.fields plan leafSlot = [] :=
  (NormDataIotaRow.row_fields plan
    (NormDPlanBridge.bodies_of_group natEnvUWfT PendAW.membersT plan.node)
    leafSlot [] leaf_kinds).trans leaf_fields

/-- The exact canonical plan and the installed W table remain in use. -/
theorem leaf_equation (P : Premises4) :
    Equiv (RecPlan.nodeCore (mkM P (base P)) plan.node (minors P) (dataVal 0 []))
      (fxZW P) := by
  have h := NormDataIotaRow.core_of_group_row P (base P)
    natEnvUWfT PendAW.membersT plan.node leafSlot [] leaf_kinds
    (minors P) [] (dataVal 0 []) (by rw [leaf_fields]; rfl) Equiv.rfl
  rw [leaf_fields] at h
  exact h

theorem leaf_result_not_empty (P : Premises4) :
    ¬ Equiv (RecPlan.nodeCore (mkM P (base P)) plan.node (minors P) (dataVal 0 []))
      pempty := by
  have h := (RawWFrame.raw_admissible P (base P) [] (key [parameter])).2
  change (if (1 : Nat) = 0 then _ else _) at h
  rw [if_neg (by decide : (1 : Nat) ≠ 0)] at h
  intro he
  exact h _ (RawDataRecAttack.omega_mem P) ((leaf_equation P).symm.trans he)

def Witness (P : Premises4) : Prop :=
  NormDataRecMemAttack.Witness P ∧ PendA PendAW.pNode ∧
  analyzeFields plan.node.a.family.ref
    (plan.node.a.constructorViews leafSlot).fields = some [] ∧
  EvalPlanNormal.fields plan leafSlot = [] ∧
  Equiv (RecPlan.nodeCore (mkM P (base P)) plan.node (minors P) (dataVal 0 []))
    (fxZW P) ∧
  ¬ Equiv (RecPlan.nodeCore (mkM P (base P)) plan.node (minors P) (dataVal 0 [])) pempty

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormDataRecMemAttack.component_witness P, PendAW.pendA, leaf_kinds,
    cached_leaf, leaf_equation P, leaf_result_not_empty P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormDataIotaRowAttack

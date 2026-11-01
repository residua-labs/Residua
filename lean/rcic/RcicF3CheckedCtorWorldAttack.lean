import rcic.RcicF3CheckedCtorWorld
import rcic.RcicF3PointwiseDataRecAttack
import rcic.RcicF3NormDataGroupAttack

/-!
# Checked common-row bounds at the actual W group

The exact selected W plan is used. A nonconstant bound gives the leaf and
node distinct bounds while the recursor covers both; the original check
passes. The actual W family has arity zero, so its constructor universe
vector is empty. This scope is retained literally. The all-row typing
producer is also invoked with the already proved BoundDG instance.

The same-P witness includes the inhabited pointwise W recursion component.
No new mask, normalized typing or universal local candidate is inferred.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.CheckedCtorWorldAttack
open Rcic.Declarative Rcic.F3.StepDGOrder
open NormPendAW (plan)

def uneven (r : Nat) : Nat := if r = 5 then 1 else if r = 6 then 2 else 3

theorem group_check : Rcic.F3.StepWDApex.groupCheck uneven natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT = none :=
  (Rcic.F3.StepWDApex.groupCheck_pass_iff uneven natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT).mpr
    ((NormPendAWChecked.w_d_side_iff uneven _).mpr ⟨by decide, by decide⟩)

theorem constructor_arity (j : Fin plan.node.a.constructors.length) :
    (plan.node.a.constructors[j.val]).arity = 0 := by
  rw [(plan.node.a.constructorViews j).arity, PendAWGroup.familyMember plan.node]

theorem produced_world (j : Fin plan.node.a.constructors.length) (σ : Nat → Nat) :
    ([].map (evalTotal σ)).length = plan.node.a.family.member.arity ∧
    ∀ v, v ∈ ([].map (evalTotal σ)) → v ≤ uneven 7 :=
  CheckedCtorWorld.constructor_world uneven natEnvUWfT rfl PendAWGroup.ctorClasses rfl
    PendAW.membersT group_check j σ [] (constructor_arity j).symm
    (fun _ h => (List.not_mem_nil _ h).elim)

theorem produced_fields (j : Fin plan.node.a.constructors.length) (σ : Nat → Nat) :
    ∀ (i : Fin plan.node.a.constructors.length)
      (k : Fin (plan.node.a.constructorViews i).fields.length),
      ∃ l : Level, ∃ d : HasTyT (extendEnv natEnvU 4 PendAW.fam)
        plan.node.a.family.member.arity
        (policyPrefixContext (plan.node.a.family.parameters ++ (plan.node.a.constructorViews i).fields)
          (plan.node.a.family.parameters.length + k.val))
        ((plan.node.a.constructorViews i).fields[k]) (.sort l),
        LOKt (σOf ([].map (evalTotal σ))) 4 (fun _ => 1) d :=
  CheckedCtorWorld.all_row_fields (fun _ => 1) natEnvUWfT rfl PendAWGroup.ctorClasses rfl
    PendAW.membersT (NormDataGroupAttack.group_check 1) (PendAWGroup.boundDG 1)
    j σ [] (constructor_arity j).symm (fun _ h => (List.not_mem_nil _ h).elim)

def Witness (P : Premises4) : Prop :=
  PointwiseDataRecAttack.Witness P ∧
  uneven 5 = 1 ∧ uneven 6 = 2 ∧ uneven 7 = 3 ∧
  Rcic.F3.StepWDApex.groupCheck uneven natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT = none ∧
  (∀ j : Fin plan.node.a.constructors.length, ∀ σ : Nat → Nat,
    ([].map (evalTotal σ)).length = plan.node.a.family.member.arity ∧
    ∀ v, v ∈ ([].map (evalTotal σ)) → v ≤ uneven 7) ∧
  (∀ (j : Fin plan.node.a.constructors.length) (σ : Nat → Nat),
    ∀ (i : Fin plan.node.a.constructors.length)
      (k : Fin (plan.node.a.constructorViews i).fields.length),
      ∃ l : Level, ∃ d : HasTyT (extendEnv natEnvU 4 PendAW.fam)
        plan.node.a.family.member.arity
        (policyPrefixContext (plan.node.a.family.parameters ++ (plan.node.a.constructorViews i).fields)
          (plan.node.a.family.parameters.length + k.val))
        ((plan.node.a.constructorViews i).fields[k]) (.sort l),
        LOKt (σOf ([].map (evalTotal σ))) 4 (fun _ => 1) d)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨PointwiseDataRecAttack.component_witness P, rfl, rfl, rfl,
    group_check, produced_world, produced_fields⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.CheckedCtorWorldAttack

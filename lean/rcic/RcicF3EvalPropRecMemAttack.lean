import rcic.RcicF3EvalPropRecMem
import rcic.RcicF3PropEvalNormalAttack

/-!
# The produced stored-type bridge at the actual installed AccR table

The public Prop/anySort member-soundness producer is applied to the actual
admitted group and its canonical new table. The full earlier component
witness is retained, including the separately proved installed iota
equation. The new conjunct is MemberSound for the complete stored recursor
type at every level vector allowed by the fixture's bound.

This fixture does not claim universal higher-order iota. Its selected
AccR application has an empty recursive child domain; the inherited
depth-three and height-omega fixtures keep their previously stated scopes.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.EvalPropRecMemAttack
open Rcic.Declarative PlanPropEndAttack
open PropEvalAdmittedInputsAttack (bound)

def Witness (P : Premises4) : Prop :=
  PropEvalNormalAttack.Witness P ∧
  MemberSound P (EvalInstalledAttack.table P) bound 2 accRecMember

/-- The canonical plan equality was already produced from the actual scan;
no second reduction of the dependent group walk is needed here. -/
theorem component_witness (P : Premises4) : Witness P := by
  have hctors : ∀ c ∈ [(1, accIntroMember)], c.2.mclass = .constructorM := by
    intro c hc
    have he : c = (1, accIntroMember) := List.mem_singleton.mp hc
    cases he
    rfl
  have hp : EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
      (fm := accFamMember) (ctors := [(1, accIntroMember)])
      (rr := 2) (rm := accRecMember) rfl hctors rfl AccEnv.accMembersT =
        EvalPlanValueAttack.plan := by
    have h := EvalInstalledAttack.canonical_plan
    change some (EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
      (fm := accFamMember) (ctors := [(1, accIntroMember)])
      (rr := 2) (rm := accRecMember) rfl hctors rfl AccEnv.accMembersT) =
        some EvalPlanValueAttack.plan at h
    exact Option.some.inj h
  have hProp : UniformProp
      (EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
        (fm := accFamMember) (ctors := [(1, accIntroMember)])
        (rr := 2) (rm := accRecMember) rfl hctors rfl AccEnv.accMembersT).node.a.family.resultLevel := by
    rw [hp]
    intro σ
    rfl
  have hpolicy :
      (EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
        (fm := accFamMember) (ctors := [(1, accIntroMember)])
        (rr := 2) (rm := accRecMember) rfl hctors rfl AccEnv.accMembersT).node.a.policy = .anySort := by
    rw [hp]
    rfl
  refine ⟨PropEvalNormalAttack.component_witness P, ?_⟩
  exact EvalPropRecMem.member_sound P (EvalInstalledAttack.table P) bound
    .empty rfl hctors rfl AccEnv.accMembersT
    (PlanPropStepAttack.boundG bound) (EvalCandidateStepAttack.empty_gInv P bound)
    (envCtx (.empty : EnvWfT emptyEnv)) (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ hm => by nomatch hm)
    (envCtx AccEnv.accEnvWfT) (EvalRole.envPlan AccEnv.accEnvWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) (EvalRole.rawTable_spec P AccEnv.accEnvWfT).1
    hProp hpolicy

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.EvalPropRecMemAttack

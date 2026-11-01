import rcic.RcicF3EvalPropRecPkg
import rcic.RcicF3EvalPropRecMemAttack

/-!
# Complete literal Prop RecPkg at the actual installed AccR table

The witness retains all earlier component conjuncts and applies the public
recursor-package producer at the actual admitted group and canonical new
table. Its IotaAt conjunct has the literal legacy-witness scope documented
by EvalPropRecIota; the actual nonempty indexed-IH computation remains in
the retained installed witness. No overall W/D check or Premises4
inhabitant is claimed. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.EvalPropRecPkgAttack
open Rcic.Declarative PlanPropEndAttack
open PropEvalAdmittedInputsAttack (bound)

def Witness (P : Premises4) : Prop :=
  EvalPropRecMemAttack.Witness P ∧
  RecPkg P (EvalInstalledAttack.table P) bound accEnv 2 accRecMember

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
  refine ⟨EvalPropRecMemAttack.component_witness P, ?_⟩
  exact EvalPropRecPkg.rec_pkg P (EvalInstalledAttack.table P) bound
    .empty rfl hctors rfl AccEnv.accMembersT
    (PlanPropStepAttack.boundG bound) (EvalCandidateStepAttack.empty_gInv P bound)
    (envCtx (.empty : EnvWfT emptyEnv)) (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ hm => by nomatch hm)
    (envCtx AccEnv.accEnvWfT) (EvalRole.envPlan AccEnv.accEnvWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) (EvalRole.rawTable_spec P AccEnv.accEnvWfT).1
    hProp hpolicy ⟨PlanPropStepAttack.pNode, PlanPropStepAttack.pendA⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.EvalPropRecPkgAttack

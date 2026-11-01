import rcic.RcicF3EvalPlanNormalCompare
import rcic.RcicF3EvalPlanNormalPropAttack
import rcic.RcicF3EvalCandidateStepAttack

/-!
# Actual AccR composition of the bounded reverse comparison

The real admitted AccR group, the new canonical faithful table, its actual
Prop BoundG and the repaired empty predecessor invariant instantiate the
public reverse producer. At the fixed parameter slice, both frames have
the same members at every complete key and universe vector. The full
recursor valuation is [1], retaining its extra motive universe even though
AccR's family arity is zero. All previously composed raw/normalized
presentations, closure, inhabitedness and hidden-field checks remain a
literal conjunct. This is a Prop-face fixture, not a universal StepAG.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.EvalPlanNormalCompareAttack
open Rcic.Declarative PiIndex RawFamily RawFamilyRec
open EvalPlanNormalAttack (plan μ parameter)
open PropEvalAdmittedInputsAttack (bound)

def Witness (P : Premises4) : Prop :=
  EvalPlanNormalPropAttack.Witness P ∧
  σOf [1] 0 = 1 ∧
  (∀ vs i z, paramKey 1 i = key [parameter] →
    (z ∈ frame P (μ P) (EvalPlanNormal.fd plan) vs i ↔
      z ∈ frame P (μ P) (famDataOf plan.node.a) vs i))

/-- The actual repaired predecessor, stored typed bound, full valuation and
canonical faithful table pay the public comparison premises. -/
theorem component_witness (P : Premises4) : Witness P := by
  have hb := EvalPlanNormalPropAttack.component_witness P
  obtain ⟨_, _, _, hforward, _⟩ := hb
  have hctors : ∀ c ∈ [(1, accIntroMember)], c.2.mclass = .constructorM := by
    intro c hc
    have he : c = (1, accIntroMember) := List.mem_singleton.mp hc
    cases he
    rfl
  have hback := EvalPlanNormalCompare.normalized_le_raw P (μ P) (σOf [1]) bound
    plan accFamMember [(1, accIntroMember)] .empty rfl hctors rfl
    AccEnv.accMembersT (PlanPropStepAttack.boundG bound)
    (EvalCandidateStepAttack.empty_gInv P bound)
    (envCtx (.empty : EnvWfT emptyEnv)) (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ hm => by nomatch hm)
    rfl rfl [1] rfl
    (fun v hv => by
      have he : v = 1 := List.mem_singleton.mp hv
      subst v
      exact Nat.le_refl 1)
    [parameter]
  refine ⟨EvalPlanNormalPropAttack.component_witness P, rfl, ?_⟩
  intro vs i z hkey
  constructor
  · intro hz
    exact hback vs i z hz (fun u hu => by
      change u < 0 at hu
      exact (Nat.not_lt_zero u hu).elim) hkey
  · exact hforward vs i z

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.EvalPlanNormalCompareAttack

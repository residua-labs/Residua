import rcic.RcicF3EvalPlanNormalProp
import rcic.RcicF3EvalPlanNormalAttack

/-!
# Actual AccR composition of normalized closure and raw inclusion

The existing new-table constructor witness is retained as a conjunct. At
that same admitted group and faithful table, the public Prop/anySort
producer gives a globally admissible closed normalized frame and the
public comparison places the raw frame inside it. The explicit empty
parameter yields a member of both frames at the same full key, at every
universe vector. AccR's family arity is zero; no higher relevant family
universe or universal data-frame result is claimed.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.EvalPlanNormalPropAttack
open Rcic.Declarative PiIndex RawFamily
open EvalPlanNormalAttack (plan μ parameter)

def Witness (P : Premises4) : Prop :=
  EvalPlanNormalAttack.Witness P ∧
  Admissible (EvalPlanNormal.fd plan) (frame P (μ P) (EvalPlanNormal.fd plan)) ∧
  Closed P (μ P) (EvalPlanNormal.fd plan) (frame P (μ P) (EvalPlanNormal.fd plan)) ∧
  FrameSub (frame P (μ P) (famDataOf plan.node.a))
    (frame P (μ P) (EvalPlanNormal.fd plan)) ∧
  (∀ vs, pempty ∈ frame P (μ P) (famDataOf plan.node.a) vs (key [parameter]) ∧
    pempty ∈ frame P (μ P) (EvalPlanNormal.fd plan) vs (key [parameter]))

/-- Actual admission, selection and new-table faithfulness pay every
premise of both public producers, and the original presentation is used to
exhibit a member in the resulting two frames. -/
theorem component_witness (P : Premises4) : Witness P := by
  have hb := EvalPlanNormalAttack.component_witness P
  obtain ⟨hfaith, _, _, _, _, hpresent, _⟩ := hb
  have hctors : ∀ c ∈ [(1, accIntroMember)], c.2.mclass = .constructorM := by
    intro c hc
    have he : c = (1, accIntroMember) := List.mem_singleton.mp hc
    cases he
    rfl
  have hn := EvalPlanNormalProp.normalized_closed P (μ P) plan accFamMember
    [(1, accIntroMember)] .empty AccEnv.accMembersT (fun _ => 0) rfl rfl
  have hsub := EvalPlanNormalProp.raw_le_normalized RawFamily.role P (μ P)
    (envCtx AccEnv.accEnvWfT) (EvalRole.envPlan AccEnv.accEnvWfT) plan
    accFamMember [(1, accIntroMember)] .empty rfl hctors rfl AccEnv.accMembersT
    (fun _ _ => rfl) hfaith (fun _ => 0) rfl rfl
  refine ⟨EvalPlanNormalAttack.component_witness P, hn.1, hn.2, hsub, ?_⟩
  intro vs
  have hraw : pempty ∈ frame P (μ P) (famDataOf plan.node.a) vs (key [parameter]) :=
    (RawFamilyPropAttack.acc_closed P (μ P)).2 vs (key [parameter]) pempty
      (hpresent vs).1
  exact ⟨hraw, hsub vs (key [parameter]) pempty hraw⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.EvalPlanNormalPropAttack

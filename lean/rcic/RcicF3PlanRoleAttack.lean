import rcic.RcicF3PlanRole
import rcic.RcicF3PiRecValueAttack
import rcic.RcicF3PendARoleW
/-! Plan-aware role regression: the exact admitted W group has the full
repaired group step; the hidden-field fixture selects its normalized depth
and separates the endpoint from the raw operation. Computation pins are
kernel readbacks. This is not universal A production. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PlanRoleAttack
open Rcic.Declarative
kernel_rfl_theorem hidden_scan :
  PlanRole.scanPlan PendAWHidden.membersT = some [[], [.recursive 1]]
kernel_rfl_theorem hidden_plan :
  PlanRole.envPlan PendAWHidden.envWfT 7 = [[], [.recursive 1]]
kernel_rfl_theorem hidden_ctx :
  envCtx PendAWHidden.envWfT 7 = .recursor (PendAWHiddenAttack.fd 4)
kernel_rfl_theorem w_scan :
  PlanRole.scanPlan PendAW.membersT = some [[], [.recursive 1]]
kernel_rfl_theorem w_plan :
  PlanRole.envPlan PendAWGroup.wft 7 = RecPlan.rawPlan PendAWBridge.fd

def natFD : FamData := (scanRec natMembersT).getD
  ⟨0, [], [], .zero, [], .propOnly⟩
kernel_rfl_theorem w_ctx : envCtx PendAWGroup.wft =
  groupRoles PendAWBridge.fd 4 7 (groupRoles natFD 0 3 (fun _ => .plain))
kernel_rfl_theorem nat_plan :
  PlanRole.envPlan PendAWGroup.wft 3 = RecPlan.rawPlan natFD

theorem w_raw (r : Nat) (fd : FamData)
    (h : envCtx PendAWGroup.wft r = .recursor fd) :
    PlanRole.envPlan PendAWGroup.wft r = RecPlan.rawPlan fd := by
  rw [w_ctx] at h
  by_cases h7 : r = 7
  · subst r
    change Role.recursor PendAWBridge.fd = .recursor fd at h
    cases h
    exact w_plan
  by_cases h3 : r = 3
  · subst r
    change Role.recursor natFD = .recursor fd at h
    cases h
    exact nat_plan
  unfold groupRoles at h
  simp only [h7, h3, if_false] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h <;> cases h
theorem w_groupStep (P : Premises4) (K : Nat → Nat) :
    PlanRole.GroupStepAt famKT P K natEnvUWfT (by rfl)
      PendAWGroup.ctorClasses (by rfl) PendAW.membersT := by
  intro hAg hB hD _
  exact PlanRole.gInv_of_raw famKT P K PendAWGroup.wft (fun r _ => w_raw r)
    (PendARoleW.groupStep P K hAg hB hD (RoleNat.gInv P K))
theorem selected_endpoint (M : Interp.{4}) (σ : Nat → Nat) :
    Nonempty (EnvWfT PendAWHidden.eAll) ∧ PendA PendAWHidden.pNode ∧
    Equiv (RecPlanValue.endValue M σ (PendAWHiddenAttack.fd 4)
      (PlanRole.envPlan PendAWHidden.envWfT 7) (RecPlanValueAttack.input M))
      PendAWHiddenAttack.datum ∧
    ¬ Equiv (RecPlanValue.endValue M σ (PendAWHiddenAttack.fd 4)
      (PlanRole.envPlan PendAWHidden.envWfT 7) (RecPlanValueAttack.input M))
      (recEnd M σ (PendAWHiddenAttack.fd 4) (RecPlanValueAttack.input M)) := by
  obtain ⟨hw, ha, he, _, hn⟩ := RecPlanValueAttack.endpoint M σ
  rw [PendAWHiddenAttack.admitted_descriptor, PendAWHiddenAttack.admitted_plan] at he hn
  rw [hidden_plan]
  exact ⟨hw, ha, he, hn⟩
end Rcic.F3.PSet.PlanRoleAttack

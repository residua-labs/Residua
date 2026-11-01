import rcic.RcicF3PlanFamilyGroup
import rcic.RcicF3RawFamilyGroupAttack
import rcic.RcicF3PlanRoleAttack
/-! Exact original typed PendA W group through planned raw-frame composition.
No frame/package premise is retained by the fixture theorem. It does not
produce the two components at an arbitrary admitted signature. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Rcic.F3.PSet.PlanFamilyGroupAttack
open Rcic.Declarative RawFamily
kernel_rfl_theorem w_raw : PlanRole.admittedPlan PendAW.pNode.a PendAW.pNode.h14 =
  RecPlan.rawPlan (famDataOf PendAW.pNode.a)
kernel_rfl_theorem w_scan : PlanRole.scanPlan PendAW.membersT =
  some (PlanRole.admittedPlan PendAW.pNode.a PendAW.pNode.h14)

/-- Elementary adapter of the already produced original-W package. -/
theorem w_package (P : Premises4) (K : Nat → Nat) (Efin : ResolvedEnv)
    (μ : Nat → List Nat → PSet.{4})
    (X : PlanFamilyGroup.RecStepCtx P K PendAW.fam PendAW.pNode μ) :
    RecPkgAt P μ K Efin PendAW.eAll 7 PendAW.recMem :=
  RawFamilyGroupAttack.w_package P K Efin μ (X.toRaw P w_raw)

theorem w_groupStep (P : Premises4) (K : Nat → Nat) :
    PlanRole.GroupStepAt role P K natEnvUWfT (by rfl)
      PendAWGroup.ctorClasses (by rfl) PendAW.membersT := by
  exact PlanFamilyGroup.stepAt_node P K natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT PendAW.pNode PendAWGroup.scanHit w_scan
    (fun _ μ _ _ _ => ⟨RawWFrame.raw_admissible P μ,
      RawFamilyGroupAttack.w_frame_closed P μ⟩) (w_package P K)
end Rcic.F3.PSet.PlanFamilyGroupAttack

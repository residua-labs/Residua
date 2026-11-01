import rcic.RcicF3RawFamilyPlanReads
import rcic.RcicF3PlanRoleAttack

/-!
# Inhabited planned-table regressions

These are complete table-installation instances at the original PendA W
environment and its typed beta-hidden variant. The hidden recursor uses
its admitted depth and still differs from the legacy raw-field operation.
No constructor-membership or universal StepAG claim is made.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.RawFamilyPlanReadsAttack
open Rcic.Declarative

theorem w_installed (P : Premises4) :
    ∃ μ, PlanRole.Faithful RawFamily.role P μ
      (envCtx PendAWGroup.wft) (PlanRole.envPlan PendAWGroup.wft) PendAW.eAll :=
  PlanRole.rawTable_exists P PendAWGroup.wft

theorem hidden_installed (P : Premises4) (σ : Nat → Nat) :
    ∃ μ, PlanRole.Faithful RawFamily.role P μ
      (envCtx PendAWHidden.envWfT) (PlanRole.envPlan PendAWHidden.envWfT) PendAWHidden.eAll ∧
      PendA PendAWHidden.pNode ∧
      Equiv (RecPlanValue.endValue (mkM P μ) σ (PendAWHiddenAttack.fd 4)
        (PlanRole.envPlan PendAWHidden.envWfT 7) (RecPlanValueAttack.input (mkM P μ)))
        PendAWHiddenAttack.datum ∧
      ¬ Equiv (RecPlanValue.endValue (mkM P μ) σ (PendAWHiddenAttack.fd 4)
        (PlanRole.envPlan PendAWHidden.envWfT 7) (RecPlanValueAttack.input (mkM P μ)))
        (recEnd (mkM P μ) σ (PendAWHiddenAttack.fd 4) (RecPlanValueAttack.input (mkM P μ))) := by
  let μ := PlanRole.rawTable P PendAWHidden.envWfT
  obtain ⟨_, ha, he, hn⟩ := PlanRoleAttack.selected_endpoint (mkM P μ) σ
  exact ⟨μ, (PlanRole.rawTable_spec P PendAWHidden.envWfT).1, ha, he, hn⟩

end Rcic.F3.PSet.RawFamilyPlanReadsAttack

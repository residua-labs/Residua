import rcic.RcicF3NormAFrameChecked
import rcic.RcicF3NormDataRecPkgAttack
import rcic.RcicF3NormPendAWChecked

/-!
# The generic DATA group producer at the exact checked W fixture

The exact normalized W frame is admissible and closed for every ambient
table, so it supplies the entire SmallFrameAt context, not only the final
installed table. The new generic DATA group theorem is called directly.
Its original walk, both bounds and the produced Nat predecessor are then
supplied at every constant bound to obtain the new invariant and actual
same-table soundness. Both unchanged whole-environment checks are retained.

The same Premises4 value is used throughout. The witness includes actual
height-omega membership and the preceding typed DATA/iota components. It
does not assert universal FramesADataChecked, unchecked StepAG, an inhabited
typed legacy-redex fixture, or the distinguished False-prefix apex witness.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDataGroupAttack
open Rcic.Declarative Rcic.Model.PS RawFamily
open RawDataRecAttack (base)
open NormDataRecMemAttack (plan)

/-- Every faithful-table instance has its small normalized candidate.
The exact W construction works for arbitrary ambient μ. -/
theorem small_frames (P : Premises4) (K : Nat → Nat) :
    NormDataGroup.SmallFrameAt P K natEnvUWfT rfl PendAWGroup.ctorClasses rfl
      PendAW.membersT := by
  intro _ _ _ _ _ _ _ _ μ _
  exact ⟨frame P μ (EvalPlanNormal.fd plan),
    NormPendAW.normalized_admissible P μ, NormPendAW.normalized_closed P μ⟩

/-- This invokes the new generic DATA producer, not the prior W-specific
GroupStepAt or any current-group invariant. -/
theorem group_step (P : Premises4) (K : Nat → Nat) :
    NormRole.GroupStepAt P K natEnvUWfT rfl PendAWGroup.ctorClasses rfl
      PendAW.membersT :=
  NormDataGroup.group_step P K natEnvUWfT rfl PendAWGroup.ctorClasses rfl
    PendAW.membersT NormDataRecMemAttack.type_family
    NormDataRecMemAttack.matching_parameters (small_frames P K)

theorem group_check (k : Nat) :
    Rcic.F3.StepWDApex.groupCheck (fun _ => k) natEnvUWfT rfl
      PendAWGroup.ctorClasses rfl PendAW.membersT = none :=
  (Rcic.F3.StepWDApex.groupCheck_pass_iff (fun _ => k) natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT).mpr
    ((NormPendAWChecked.w_d_side_iff (fun _ => k) _).mpr
      ⟨Nat.le_refl k, Nat.le_refl k⟩)

theorem checked_group_step (P : Premises4) (k : Nat) :
    NormRole.GroupStepAt P (fun _ => k) natEnvUWfT rfl PendAWGroup.ctorClasses rfl
      PendAW.membersT :=
  NormDataGroup.group_step_of_check P (fun _ => k) natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT NormDataRecMemAttack.type_family
    (group_check k) (small_frames P (fun _ => k))

theorem invariant (P : Premises4) (k : Nat) :
    NormRole.GInv P (fun _ => k) PendAWGroup.wft :=
  checked_group_step P k PendAWGroup.walkAgree (PendAWGroup.boundG _)
    (PendAWGroup.boundDG k) (NormNatInvariant.gInv P _)

theorem env_sound (P : Premises4) (k : Nat) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (base P)) σ (fun _ => k) PendAW.eAll n :=
  NormRole.envSound_of_gInv P (fun _ => k) PendAWGroup.wft (invariant P k) σ n

def Witness (P : Premises4) : Prop :=
  NormDataRecPkgAttack.Witness P ∧
  UniformType plan.node.a.family.resultLevel ∧
  (∃ node : PendAWGroup.Node, PendA node) ∧
  (∀ K, NormDataGroup.SmallFrameAt P K natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT) ∧
  (∀ K, NormRole.GroupStepAt P K natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT) ∧
  Rcic.F3.StepWApex.envCheck PendAWGroup.wft = true ∧
  (∀ k, Rcic.F3.StepWDApex.groupCheck (fun _ => k) natEnvUWfT rfl
      PendAWGroup.ctorClasses rfl PendAW.membersT = none ∧
    Rcic.F3.StepWDApex.envCheck (fun _ => k) PendAWGroup.wft = true ∧
    BoundG (fun _ => k) PendAWGroup.wft ∧ BoundDG (fun _ => k) PendAWGroup.wft ∧
    NormRole.GInv P (fun _ => k) PendAWGroup.wft ∧
    ∀ σ n, EnvSound (mkM P (base P)) σ (fun _ => k) PendAW.eAll n) ∧
  fxZW P ∈ Ed (mkM P (base P)) (fapps (base P 4 []) [tyv fxS]) ∧
  (∀ K, NormAFrameChecked.FramesADataChecked P K → NormADataChecked.StepADataChecked P K)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormDataRecPkgAttack.component_witness P, NormDataRecMemAttack.type_family,
    ⟨PendAW.pNode, PendAW.pendA⟩, small_frames P, group_step P, NormPendAWChecked.w_check,
    (fun k => ⟨group_check k, NormPendAWChecked.d_check k, PendAWGroup.boundG _,
      PendAWGroup.boundDG k, invariant P k, env_sound P k⟩),
    NormPendAW.installed_height_omega P, NormAFrameChecked.stepADataChecked_of_frames P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormDataGroupAttack

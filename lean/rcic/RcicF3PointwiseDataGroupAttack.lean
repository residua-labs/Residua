import rcic.RcicF3PointwiseDataGroup
import rcic.RcicF3PointwiseDataPrefixAttack

/-!
# Complete new-table W composition through the generic pointwise producer

The actual W local candidates are supplied for every ambient table and K.
The NEW generic group producer is called directly with the unchanged
selected D check, original walk/bounds, and produced pointwise Nat
predecessor. It gives the pointwise W invariant and SAME installed-table
soundness at every constant bound. The complete recursor package is also
called directly at this table, with no current-W invariant as an input.

The witness retains same-P installation, height-omega membership and both
unchanged whole-environment checks. Iota has its literal legacy witness
scope; the other W row remains higher-order. No universal local-candidate
producer, old/new invariant equality or final False-prefix tier witness is
asserted. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseDataGroupAttack
open Rcic.Declarative RawFamily
open NormPendAW (plan)
open PointwiseRoleAttack (table)

theorem local_candidates_at (P : Premises4) (K : Nat → Nat) :
    PointwiseDataGroup.LocalCandidatesAt P K natEnvUWfT rfl
      PendAWGroup.ctorClasses rfl PendAW.membersT := by
  intro _ _ _ _ _ _ _ _ _ _ μ _
  exact PointwiseDataPrefixAttack.local_candidates P μ K

theorem group_step (P : Premises4) (k : Nat) :
    PointwiseDataGroup.GroupStepAt P (fun _ => k) natEnvUWfT rfl
      PendAWGroup.ctorClasses rfl PendAW.membersT :=
  PointwiseDataGroup.group_step_of_check P (fun _ => k) natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT NormDataRecMemAttack.type_family
    (NormDataGroupAttack.group_check k) (local_candidates_at P _)

theorem invariant (P : Premises4) (k : Nat) :
    PointwiseRole.GInv P (fun _ => k) PendAWGroup.wft :=
  group_step P k PendAWGroup.walkAgree (PendAWGroup.boundG _)
    (PendAWGroup.boundDG k) (PointwiseNatInvariant.gInv P _)

/-- The complete public package is instantiated without the new W invariant. -/
theorem rec_pkg (P : Premises4) (k : Nat) :
    RecPkg P (table P) (fun _ => k) PendAW.eAll 7 PendAW.recMem :=
  PointwiseDataRecPkg.rec_pkg P (table P) (fun _ => k)
    natEnvUWfT rfl PendAWGroup.ctorClasses rfl PendAW.membersT
    PendAWGroup.walkAgree (PendAWGroup.boundG _) (PendAWGroup.boundDG k)
    (PointwiseNatInvariant.gInv P _)
    (PointwiseRole.arities PendAW.eAll) PointwiseRoleAttack.metadata
    (NormRole.envCtx PendAWGroup.wft) (EvalRole.envPlan PendAWGroup.wft)
    (fun _ _ => rfl) (fun _ _ => rfl) (PointwiseRoleAttack.faithful P)
    (NormDataGroupAttack.group_check k)
    (PointwiseDataPrefixAttack.local_candidates P (table P) _)
    NormDataRecMemAttack.type_family

theorem all_sound (P : Premises4) (k : Nat) :
    AllSound P (table P) (fun _ => k) PendAW.eAll :=
  (invariant P k (PointwiseRole.arities PendAW.eAll) PointwiseRoleAttack.metadata
    (NormRole.envCtx PendAWGroup.wft) (fun _ _ => rfl)
    (EvalRole.envPlan PendAWGroup.wft) (fun _ _ => rfl) _
    (PointwiseRoleAttack.faithful P)).1

theorem env_sound (P : Premises4) (k : Nat) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (table P)) σ (fun _ => k) PendAW.eAll n :=
  PointwiseRole.envSound_of_gInv P (fun _ => k) PendAWGroup.wft (invariant P k) σ n

def Witness (P : Premises4) : Prop :=
  PointwiseDataPrefixAttack.Witness P ∧
  UniformType plan.node.a.family.resultLevel ∧
  (∃ node : PendAWGroup.Node, PendA node) ∧
  (∀ K, PointwiseDataGroup.LocalCandidatesAt P K natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT) ∧
  Rcic.F3.StepWApex.envCheck PendAWGroup.wft = true ∧
  (∀ k, Rcic.F3.StepWDApex.groupCheck (fun _ => k) natEnvUWfT rfl
      PendAWGroup.ctorClasses rfl PendAW.membersT = none ∧
    Rcic.F3.StepWDApex.envCheck (fun _ => k) PendAWGroup.wft = true ∧
    BoundG (fun _ => k) PendAWGroup.wft ∧ BoundDG (fun _ => k) PendAWGroup.wft ∧
    PointwiseDataGroup.GroupStepAt P (fun _ => k) natEnvUWfT rfl
      PendAWGroup.ctorClasses rfl PendAW.membersT ∧
    PointwiseRole.GInv P (fun _ => k) PendAWGroup.wft ∧
    RecPkg P (table P) (fun _ => k) PendAW.eAll 7 PendAW.recMem ∧
    AllSound P (table P) (fun _ => k) PendAW.eAll ∧
    ∀ σ n, EnvSound (mkM P (table P)) σ (fun _ => k) PendAW.eAll n) ∧
  fxZW P ∈ Ed (mkM P (table P)) (fapps (table P 4 []) [tyv fxS])

theorem component_witness (P : Premises4) : Witness P :=
  ⟨PointwiseDataPrefixAttack.component_witness P, NormDataRecMemAttack.type_family,
    ⟨PendAW.pNode, PendAW.pendA⟩, local_candidates_at P, NormPendAWChecked.w_check,
    (fun k => ⟨NormDataGroupAttack.group_check k, NormPendAWChecked.d_check k,
      PendAWGroup.boundG _, PendAWGroup.boundDG k, group_step P k, invariant P k,
      rec_pkg P k, all_sound P k, env_sound P k⟩),
    PointwiseRoleAttack.installed_height_omega P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PointwiseDataGroupAttack

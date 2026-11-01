import rcic.RcicF3NormDFallback
import rcic.RcicF3NormFiniteFamilyAttack
import rcic.RcicF3NormPendAWChecked

/-!
# Actual checked Nat composition through the new D fallback producer

The selected-node D check passes at every constant bound. Its actual
admission, walk and bounds feed the new group-step producer, starting from
the empty normalized predecessor. At the same installed normalized table
the finite family supplies MemberSound, bounded D stages and GroupFaithB.
The resulting group invariant supplies EnvSound at every local valuation.

The complete previous finite-family and checked W-fixture witnesses are
retained, including the height-omega element and the AccR/depth-three
positive-A boundaries. This is a non-refutability witness for the composed
D fallback component, not a universal A or checked-apex certificate.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.NormDFallbackAttack
open Rcic.Declarative Rcic.Model.PS Rcic.F3.StepDGOrder
open NormNatPlan (plan)

def Witness (P : Premises4) : Prop :=
  NormFiniteFamilyAttack.Witness P ∧ NormPendAWChecked.Witness P ∧
  ∀ k : Nat,
    Rcic.F3.StepWDApex.groupCheck (fun _ => k)
      (f := 0) (fm := natFamMember) (ctors := [(1, natZeroMember), (2, natSuccMember)])
      (rr := 3) (rm := natRecMemberU)
      EnvWfT.empty rfl NormNatPlan.ctorClasses rfl natMembersT = none ∧
    NormRole.GroupStepAt P (fun _ => k)
      EnvWfT.empty rfl NormNatPlan.ctorClasses rfl natMembersT ∧
    MemberSound P (NormNatPlan.table P) (fun _ => k) 0 natFamMember ∧
    DStage P (fun _ => k) plan.node (NormNatPlan.table P) ∧
    GroupFaithB P (NormNatPlan.table P) (fun _ => k) natFamMember plan.node ∧
    ∀ σ n, EnvSound (mkM P (NormNatPlan.table P)) σ (fun _ => k) natEnvU n

theorem component_witness (P : Premises4) : Witness P := by
  refine ⟨NormFiniteFamilyAttack.component_witness P,
    NormPendAWChecked.component_witness P, ?_⟩
  intro k
  let K : Nat → Nat := fun _ => k
  have hside : StepDGSide K plan.node :=
    (NormPendAWChecked.nat_d_side_iff K plan.node).mpr
      ⟨Nat.le_refl k, Nat.le_refl k⟩
  have hp := (Rcic.F3.StepWDApex.groupCheck_pass_iff K
    (f := 0) (fm := natFamMember) (ctors := [(1, natZeroMember), (2, natSuccMember)])
    (rr := 3) (rm := natRecMemberU)
    EnvWfT.empty rfl NormNatPlan.ctorClasses rfl natMembersT).mpr hside
  have hAn : ¬ ∃ node : NatNode, PendA node := by
    intro ⟨node, ha⟩
    apply NormDPlanBridge.not_noFun_of_pendA ha
    intro j s hs
    rw [NormNatPlan.node_shapes node j] at hs
    by_cases hj : j.val = 0
    · rw [if_pos hj] at hs
      exact (List.not_mem_nil s hs).elim
    · rw [if_neg hj] at hs
      exact Or.inr (List.mem_singleton.mp hs)
  have hFallback : ¬ (UniformProp plan.node.a.family.resultLevel ∧
      plan.node.a.policy = .anySort) :=
    fun h => NormDPlanBridgeAttack.nat_data (fun _ => 0) (h.1 _)
  have hStep := NormDFallback.group_step_of_check P K
    (f := 0) (fm := natFamMember) (ctors := [(1, natZeroMember), (2, natSuccMember)])
    (rr := 3) (rm := natRecMemberU)
    EnvWfT.empty rfl NormNatPlan.ctorClasses rfl natMembersT hp hAn hFallback
  have hB := natEnvUWfT_classG.2 K
  have hD : BoundDG K natEnvUWfT := (PendAWGroup.boundDG k).1
  have hPred := NormRole.gInv_empty P K
  have hI := hStep (walkG_of_classG natEnvUWfT natEnvUWfT_classG.1).2.2 hB hD hPred
  have hfm := NormDFaith.family_member_sound P (NormNatPlan.table P)
    (f := 0) (fm := natFamMember) (ctors := [(1, natZeroMember), (2, natSuccMember)])
    (rr := 3) (rm := natRecMemberU)
    EnvWfT.empty rfl NormNatPlan.ctorClasses rfl natMembersT
    (NormRole.envCtx natEnvUWfT) (EvalRole.envPlan natEnvUWfT)
    (fun _ _ => rfl) (NormNatPlan.faithful P) NormDPlanBridgeAttack.nat_noFun K
  have D := NormDStage.stage_of_invariant
    (P := P) (K := K) (f := 0) (fm := natFamMember)
    (ctors := [(1, natZeroMember), (2, natSuccMember)]) (rr := 3) (rm := natRecMemberU)
    EnvWfT.empty rfl NormNatPlan.ctorClasses rfl natMembersT plan.node
    NormDPlanBridgeAttack.nat_noFun hside.1 hB.1 (hD.2 plan.node) hPred
    (NormRole.envCtx (.empty : EnvWfT emptyEnv)) (fun _ _ => rfl)
    (EvalRole.envPlan (.empty : EnvWfT emptyEnv)) (fun _ _ => rfl)
    (NormNatPlan.table P) (fun _ _ hm => by nomatch hm) hfm
  have hG := NormDFaith.group_faith P (NormNatPlan.table P) K
    (f := 0) (fm := natFamMember) (ctors := [(1, natZeroMember), (2, natSuccMember)])
    (rr := 3) (rm := natRecMemberU)
    EnvWfT.empty rfl NormNatPlan.ctorClasses rfl natMembersT
    (NormRole.envCtx natEnvUWfT) (EvalRole.envPlan natEnvUWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) (NormNatPlan.faithful P)
    NormDPlanBridgeAttack.nat_noFun hFallback D
  refine ⟨hp, hStep, hfm, D, hG, ?_⟩
  intro σ n
  exact NormRole.envSound_of_gInv P K natEnvUWfT hI σ n

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormDFallbackAttack

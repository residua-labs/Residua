import rcic.RcicF3NormDPlanBridge
import rcic.RcicF3NormPendAWInvariant
import rcic.RcicF3EvalPlanAttack

/-!
# Actual Nat composition and retained higher-order boundaries

The new generic operational-plan and endpoint adapters are invoked at the
actual canonical Nat plan, with body freshness and NoFunRec produced.
The complete existing Nat invariant and W height-omega invariant are kept
in the conjunction. The W and AccR nodes explicitly fail NoFunRec; the
adapter is not being used to discard those families from the A target.

The inherited beta/delta/zeta, relabelled depth-three cache component keeps
its exact reader-fixture scope and complete dependent key. Its positive
depth is not asserted to meet this A-negative compatibility hypothesis.
This component is not a universal W/D consumer or StepAG producer.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.NormDPlanBridgeAttack
open Rcic.Declarative
open NormDPlanBridge
open NormNatPlan (plan fd)

theorem nat_bodies : FamFreeBodies plan.node.E0 plan.node.a.family.ref :=
  bodies_of_group (f := 0) (rr := 3) (fm := natFamMember) (rm := natRecMemberU)
    (ctors := [(1, natZeroMember), (2, natSuccMember)]) EnvWfT.empty natMembersT plan.node

theorem nat_noFun : NoFunRec plan.node := by
  intro j s hs
  rw [NormNatPlan.node_shapes plan.node j] at hs
  by_cases hj : j.val = 0
  · rw [if_pos hj] at hs
    exact (List.not_mem_nil s hs).elim
  · rw [if_neg hj] at hs
    exact Or.inr (List.mem_singleton.mp hs)

/-- This equality is obtained from the new generic producer. -/
theorem nat_raw_plan : RecPlan.rawPlan fd = RecPlan.nodePlan plan.node :=
  node_raw_plan_of_group (f := 0) (rr := 3) (fm := natFamMember) (rm := natRecMemberU)
    (ctors := [(1, natZeroMember), (2, natSuccMember)]) EnvWfT.empty natMembersT plan.node nat_noFun

theorem nat_normalized : EvalPlanNormal.fd plan = nodeFam plan.node :=
  normalized_descriptor plan nat_bodies nat_noFun

theorem nat_data (σ : Nat → Nat) : evalTotal σ plan.node.a.family.resultLevel ≠ 0 := by
  rw [(nat_family plan.node).2.2]
  exact Nat.one_ne_zero

/-- The supplied interpretation, full universe valuation and local environment
remain arbitrary; the actual Nat result level selects the data branch. -/
theorem nat_endpoint (M : Interp.{4}) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    EvalPlanValue.endValue M σ plan ρ = recEnd M σ fd ρ :=
  endpoint_data M σ plan nat_bodies nat_noFun (nat_data σ) ρ

theorem nat_member (M : Interp.{4}) (σ : Nat → Nat) :
    EvalPlanValue.memberValue M σ plan natRecMemberU =
      piLam M σ (recEnd M σ fd) ρ0 natRecMemberU.mtype :=
  member_fallback M σ plan nat_bodies nat_noFun
    (fun h => nat_data σ h.1) natRecMemberU

/-- The new abstraction equality composes with the actual installer. -/
theorem nat_installed (P : Premises4) (vs : List Nat) :
    Equiv (NormNatPlan.table P 3 vs)
      (piLam (mkM P (NormNatPlan.table P)) (σOf vs)
        (recEnd (mkM P (NormNatPlan.table P)) (σOf vs) fd) ρ0
        natRecMemberU.mtype) := by
  have h := NormNatPlan.faithful P 3 natRecMemberU rfl vs
  rw [NormNatPlan.recursor_role, NormNatPlan.canonical_plan] at h
  change Equiv (NormNatPlan.table P 3 vs)
    (EvalPlanValue.memberValue (mkM P (NormNatPlan.table P)) (σOf vs) plan
      natRecMemberU) at h
  rw [nat_member] at h
  exact h

theorem w_not_noFun : ¬ NoFunRec PendAW.pNode :=
  not_noFun_of_pendA PendAW.pendA

theorem acc_not_noFun : ¬ NoFunRec PlanPropStepAttack.pNode :=
  not_noFun_of_pendA PlanPropStepAttack.pendA

def Witness (P : Premises4) : Prop :=
  NormNatInvariant.Witness P ∧ NormPendAWInvariant.Witness P ∧
  EvalPlanAttack.Witness ∧
  FamFreeBodies plan.node.E0 plan.node.a.family.ref ∧
  NoFunRec plan.node ∧
  RecPlan.rawPlan fd = RecPlan.nodePlan plan.node ∧
  EvalPlanNormal.fd plan = nodeFam plan.node ∧
  (∀ (M : Interp.{4}) σ ρ,
    EvalPlanValue.endValue M σ plan ρ = recEnd M σ fd ρ) ∧
  (∀ (M : Interp.{4}) σ,
    EvalPlanValue.memberValue M σ plan natRecMemberU =
      piLam M σ (recEnd M σ fd) ρ0 natRecMemberU.mtype) ∧
  (∀ vs, Equiv (NormNatPlan.table P 3 vs)
    (piLam (mkM P (NormNatPlan.table P)) (σOf vs)
      (recEnd (mkM P (NormNatPlan.table P)) (σOf vs) fd) ρ0
      natRecMemberU.mtype)) ∧
  (¬ NoFunRec PendAW.pNode) ∧
  (¬ NoFunRec PlanPropStepAttack.pNode)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormNatInvariant.component_witness P, NormPendAWInvariant.component_witness P,
    EvalPlanAttack.component_witness, nat_bodies, nat_noFun, nat_raw_plan,
    nat_normalized, nat_endpoint, nat_member, nat_installed P,
    w_not_noFun, acc_not_noFun⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormDPlanBridgeAttack

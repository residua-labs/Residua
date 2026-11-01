import rcic.RcicF3NormFiniteFamily
import rcic.RcicF3NormDPlanBridgeAttack

/-!
# The finite comparison at the actual normalized Nat table

The new generic family producer is invoked at the actual admitted Nat
plan and actual normalized installed table. The produced limit candidate
contains every finite numeral, with zero and one distinguished, and the
installed family entry is the finite limit at every full universe vector.

The retained conjunction also carries the actual W height-omega model,
AccR positive-depth boundary, and hidden/relabelled depth-three cache
fixture. Those positive-depth families are not asserted to satisfy
NoFunRec. This is a composed finite-family component, not a universal
A-axis or apex closure claim. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.NormFiniteFamilyAttack
open Rcic.Declarative PiIndex RawFamily
open NormNatPlan (plan fd)

theorem actual_package (P : Premises4) :
    NormFiniteFamily.Package P (NormNatPlan.table P) (EvalPlanNormal.fd plan) :=
  NormFiniteFamily.package_of_group P (NormNatPlan.table P) plan natFamMember
    [(1, natZeroMember), (2, natSuccMember)] EnvWfT.empty natMembersT
    NormDPlanBridgeAttack.nat_noFun

theorem numeral_in_candidate (P : Premises4) (n : Nat) (vs : List Nat) :
    RawNatFrame.numeral n ∈
      RawFiniteFrame.candidate P (NormNatPlan.table P) (EvalPlanNormal.fd plan)
        vs (key []) := by
  have h := actual_package P
  apply frame_least P (NormNatPlan.table P) (EvalPlanNormal.fd plan)
    (RawFiniteFrame.candidate P (NormNatPlan.table P) (EvalPlanNormal.fd plan))
    h.candidateAdmissible h.candidateClosed vs (key []) (RawNatFrame.numeral n)
  rw [NormNatPlan.normalized_descriptor]
  change RawNatFrame.numeral n ∈ frame P (NormNatPlan.table P)
    (famDataOf plan.node.a) vs (key [])
  rw [RawNatFrame.descriptor plan.node]
  exact RawNatFrame.numeral_mem P (NormNatPlan.table P) plan.node.a.policy n vs

theorem numeral_in_limit (P : Premises4) (n : Nat) (vs : List Nat) :
    RawNatFrame.numeral n ∈
      RawFiniteFrame.fibre P (NormNatPlan.table P) (EvalPlanNormal.fd plan)
        (σOf vs) ρ0 := by
  exact mem_congr_right
    (RawFiniteFrame.candidate_key P (NormNatPlan.table P) (EvalPlanNormal.fd plan)
      vs []) (numeral_in_candidate P n vs)

/-- This comparison is about the table installed by the new canonical
context and plans, not a table substituted from the old model. -/
theorem installed_finite (P : Premises4) (vs : List Nat) :
    Equiv (NormNatPlan.table P 0 vs)
      (famLim P (NormNatPlan.table P) (EvalPlanNormal.fd plan) vs) := by
  have h := (actual_package P).value vs
  rw [NormNatPlan.normalized_descriptor] at h ⊢
  exact (NormNatPlan.family_value P vs).trans h

def Witness (P : Premises4) : Prop :=
  NormDPlanBridgeAttack.Witness P ∧
  NormFiniteFamily.Package P (NormNatPlan.table P) (EvalPlanNormal.fd plan) ∧
  (∀ n vs, RawNatFrame.numeral n ∈
    RawFiniteFrame.candidate P (NormNatPlan.table P) (EvalPlanNormal.fd plan)
      vs (key [])) ∧
  (∀ n vs, RawNatFrame.numeral n ∈
    RawFiniteFrame.fibre P (NormNatPlan.table P) (EvalPlanNormal.fd plan)
      (σOf vs) ρ0) ∧
  (∀ vs, Equiv (NormNatPlan.table P 0 vs)
    (famLim P (NormNatPlan.table P) (EvalPlanNormal.fd plan) vs)) ∧
  ¬ Equiv (RawNatFrame.numeral 0) (RawNatFrame.numeral 1)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormDPlanBridgeAttack.component_witness P, actual_package P,
    numeral_in_candidate P, numeral_in_limit P, installed_finite P,
    RawNatFrame.zero_ne_one⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormFiniteFamilyAttack

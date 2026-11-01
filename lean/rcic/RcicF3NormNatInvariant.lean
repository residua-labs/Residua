import rcic.RcicF3RawNatFrame
import rcic.RcicF3NormNatPlan

/-!
# The produced normalized-role Nat predecessor invariant

The actual Nat plan preserves its full descriptor and recursor endpoint.
The raw Nat family has already been proved equivalent to its least fixed
point. Those component equations transport new faithfulness to the proved
Nat model and yield the new invariant for every bound function.

The transport is specific to the actual admitted Nat environment. It does
not identify the old and new invariant universally. The actual normalized
installed table is sound and contains every finite numeral, with zero and
one distinguished. Stable IotaAt keeps its literal existing witness scope.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormNatInvariant
open Rcic.Declarative Rcic.Model.PS
open NormNatPlan (plan fd)

/-- Every equation needed by the existing Nat invariant is produced from
the new faithful equations, including the actual installed recursor plan. -/
theorem faithful_to_least (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom natEnvU r → ctx r = NormRole.envCtx natEnvUWfT r)
    (hplans : ∀ r, Dom natEnvU r → plans r = EvalRole.envPlan natEnvUWfT r)
    (hFaith : EvalRole.Faithful RawFamily.role P μ ctx plans natEnvU) :
    RoleModel.Faithful famKT P μ ctx natEnvU := by
  intro r m hm vs
  have h := hFaith r m hm vs
  have hctxG : ctx r = groupRoles fd 0 3 (fun _ => .plain) r :=
    (hctx r (dom_of_members hm)).trans (congrFun NormNatPlan.normalized_context r)
  rw [hctxG] at h ⊢
  have hL : ([(1, natZeroMember), (2, natSuccMember)].map Prod.fst) =
      (List.range ([(1, natZeroMember), (2, natSuccMember)].length)).map
        (fun i => 0 + 1 + i) := rfl
  rcases group_member_cases natMembersT hL rfl plan.node hm with
    hold | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨j, rfl, rfl⟩
  · cases hold
  · rw [groupRoles_at_f] at h ⊢
    exact h.trans (RawNatFrame.role_value_at_node P μ plan.node vs)
  · change Equiv (μ 3 vs) (EvalRole.memberVal RawFamily.role P μ (plans 3)
      (groupRoles fd 0 3 (fun _ => .plain) 3) natRecMemberU vs) at h
    change Equiv (μ 3 vs) (RoleModel.memberVal famKT P μ
      (groupRoles fd 0 3 (fun _ => .plain) 3) natRecMemberU vs)
    rw [groupRoles_at_rr fd (by decide : 0 < 3)] at h ⊢
    rw [hplans 3 (dom_of_members (show natEnvU.members 3 = some natRecMemberU from rfl)),
      NormNatPlan.canonical_plan] at h
    change Equiv (μ 3 vs)
      (EvalPlanValue.memberValue (mkM P μ) (σOf vs) plan natRecMemberU) at h
    rw [NormNatPlan.member_value_eq] at h
    exact h
  · have hj : 0 + 1 + j.val < 3 := by
      have hj0 : j.val < 2 := Nat.lt_of_lt_of_eq j.isLt
        (node_ctors_length (ctors := [(1, natZeroMember), (2, natSuccMember)])
          plan.node rfl)
      omega
    rw [groupRoles_at_ctor _ _ hj] at h ⊢
    exact h

/-- The new canonical Nat invariant, with no named semantic premise. -/
theorem gInv (P : Premises4) (K : Nat → Nat) :
    NormRole.GInv P K natEnvUWfT := by
  intro ctx hctx plans hplans μ hFaith
  apply RoleNat.gInv P K ctx
    (fun r hr => (hctx r hr).trans (congrFun NormNatPlan.context_eq r)) μ
  exact faithful_to_least P μ ctx plans hctx hplans hFaith

/-- The actual new installer supplies a non-vacuous faithful table. -/
theorem actual_invariant (P : Premises4) (K : Nat → Nat) :
    AllSound P (NormNatPlan.table P) K natEnvU ∧
      ∀ Efin, (∀ r m, natEnvU.members r = some m → Efin.members r = some m) →
        ∀ r m, natEnvU.members r = some m → m.mclass = .recursorM →
          IotaAt P (NormNatPlan.table P) K Efin r :=
  gInv P K (NormRole.envCtx natEnvUWfT) (fun _ _ => rfl)
    (EvalRole.envPlan natEnvUWfT) (fun _ _ => rfl) (NormNatPlan.table P)
    (NormNatPlan.faithful P)

theorem installed_numeral (P : Premises4) (n : Nat) :
    RawNatFrame.numeral n ∈ Ed (mkM P (NormNatPlan.table P))
      (NormNatPlan.table P 0 []) := by
  have hraw : RawNatFrame.numeral n ∈
      RawFamily.frame P (NormNatPlan.table P) fd [] (PiIndex.key []) := by
    change RawNatFrame.numeral n ∈ RawFamily.frame P (NormNatPlan.table P)
      (famDataOf plan.node.a) [] (PiIndex.key [])
    rw [RawNatFrame.descriptor plan.node]
    exact RawNatFrame.numeral_mem P (NormNatPlan.table P) plan.node.a.policy n []
  have hread := RawFamily.apply_ofFrame_ed P (NormNatPlan.table P) fd
    (RawFamily.frame P (NormNatPlan.table P) fd)
    (RawNatFrame.admissible_at_node P (NormNatPlan.table P) plan.node) [] []
    (by rw [NormNatPlan.descriptor]; trivial)
  exact mem_congr_right (ed_congr (mkM P (NormNatPlan.table P))
    (NormNatPlan.family_value P [])).symm (mem_congr_right hread.symm hraw)

def Witness (P : Premises4) : Prop :=
  NormNatPlan.Witness P ∧
  RawNatFrame.Witness P (NormNatPlan.table P) plan.node ∧
  (∀ K, NormRole.GInv P K natEnvUWfT) ∧
  (∀ K, AllSound P (NormNatPlan.table P) K natEnvU ∧
    ∀ Efin, (∀ r m, natEnvU.members r = some m → Efin.members r = some m) →
      ∀ r m, natEnvU.members r = some m → m.mclass = .recursorM →
        IotaAt P (NormNatPlan.table P) K Efin r) ∧
  (∀ n, RawNatFrame.numeral n ∈ Ed (mkM P (NormNatPlan.table P))
    (NormNatPlan.table P 0 [])) ∧
  ¬ Equiv (RawNatFrame.numeral 0) (RawNatFrame.numeral 1)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormNatPlan.component_witness P,
    RawNatFrame.component_witness P (NormNatPlan.table P) plan.node,
    gInv P, actual_invariant P, installed_numeral P, RawNatFrame.zero_ne_one⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormNatInvariant

import rcic.RcicF3PointwiseDataComparison
import rcic.RcicF3NormNatInvariant

/-!
# Actual Nat predecessor for the separate interpretation

Nat already has a produced global small closed candidate. The explicitly
conditional comparison therefore identifies its family value, for every
ambient table and vector. Only this actual Nat environment is transported
to its existing invariant. No universal equality of invariants is claimed.
The new installer and same-P witness are retained. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseNatInvariant
open Rcic.Declarative Rcic.Model.PS RawFamily
open NormNatPlan (plan fd)

theorem family_value (α : PointwiseRole.Arities) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (hα : PointwiseRole.AritiesAgree α natEnvU)
    (vs : List Nat) :
    Equiv (PointwiseRole.familyValue α P μ fd vs) (RawFamily.role P μ fd vs) := by
  have hex : ∃ C, Admissible (EvalPlanNormal.fd plan) C ∧
      Closed P μ (EvalPlanNormal.fd plan) C := by
    rw [NormNatPlan.normalized_descriptor]
    exact ⟨RawFamily.frame P μ fd, RawNatFrame.admissible_at_node P μ plan.node,
      RawNatFrame.closed_at_node P μ plan.node⟩
  have h := PointwiseRole.familyValue_equiv_of_global_candidate α P μ plan natFamMember
    [(1, natZeroMember), (2, natSuccMember)] EnvWfT.empty natMembersT hα hex vs
  simpa only [NormNatPlan.normalized_descriptor] using h

theorem faithful_to_raw (α : PointwiseRole.Arities) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (hα : PointwiseRole.AritiesAgree α natEnvU)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom natEnvU r → ctx r = NormRole.envCtx natEnvUWfT r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans natEnvU) :
    EvalRole.Faithful RawFamily.role P μ ctx plans natEnvU := by
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
    exact h.trans (family_value α P μ hα vs)
  · change Equiv (μ 3 vs)
      (EvalRole.memberVal (PointwiseRole.familyValue α) P μ (plans 3)
        (groupRoles fd 0 3 (fun _ => .plain) 3) natRecMemberU vs) at h
    change Equiv (μ 3 vs) (EvalRole.memberVal RawFamily.role P μ (plans 3)
      (groupRoles fd 0 3 (fun _ => .plain) 3) natRecMemberU vs)
    rw [groupRoles_at_rr fd (by decide : 0 < 3)] at h ⊢
    cases hp : plans 3 with
    | none => simpa only [hp, EvalRole.memberVal, RoleModel.memberVal] using h
    | some p => simpa only [hp, EvalRole.memberVal] using h
  · have hj : 0 + 1 + j.val < 3 := by
      have hj0 : j.val < 2 := Nat.lt_of_lt_of_eq j.isLt
        (node_ctors_length (ctors := [(1, natZeroMember), (2, natSuccMember)]) plan.node rfl)
      omega
    rw [groupRoles_at_ctor _ _ hj] at h ⊢
    exact h

/-- The reverse transport is also confined to this actual Nat environment.
It permits a concrete larger table to supply the new Nat predecessor. -/
theorem faithful_of_raw (α : PointwiseRole.Arities) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (hα : PointwiseRole.AritiesAgree α natEnvU)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom natEnvU r → ctx r = NormRole.envCtx natEnvUWfT r)
    (hFaith : EvalRole.Faithful RawFamily.role P μ ctx plans natEnvU) :
    EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans natEnvU := by
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
    exact h.trans (family_value α P μ hα vs).symm
  · change Equiv (μ 3 vs) (EvalRole.memberVal RawFamily.role P μ (plans 3)
      (groupRoles fd 0 3 (fun _ => .plain) 3) natRecMemberU vs) at h
    change Equiv (μ 3 vs)
      (EvalRole.memberVal (PointwiseRole.familyValue α) P μ (plans 3)
        (groupRoles fd 0 3 (fun _ => .plain) 3) natRecMemberU vs)
    rw [groupRoles_at_rr fd (by decide : 0 < 3)] at h ⊢
    cases hp : plans 3 with
    | none => simpa only [hp, EvalRole.memberVal, RoleModel.memberVal] using h
    | some p => simpa only [hp, EvalRole.memberVal] using h
  · have hj : 0 + 1 + j.val < 3 := by
      have hj0 : j.val < 2 := Nat.lt_of_lt_of_eq j.isLt
        (node_ctors_length (ctors := [(1, natZeroMember), (2, natSuccMember)]) plan.node rfl)
      omega
    rw [groupRoles_at_ctor _ _ hj] at h ⊢
    exact h

theorem gInv (P : Premises4) (K : Nat → Nat) :
    PointwiseRole.GInv P K natEnvUWfT := by
  intro α hα ctx hctx plans hplans μ hFaith
  exact NormNatInvariant.gInv P K ctx hctx plans hplans μ
    (faithful_to_raw α P μ hα ctx plans hctx hFaith)

theorem actual_invariant (P : Premises4) (K : Nat → Nat) :
    AllSound P (PointwiseRole.table P natEnvUWfT) K natEnvU ∧
      ∀ Efin, (∀ r m, natEnvU.members r = some m → Efin.members r = some m) →
        ∀ r m, natEnvU.members r = some m → m.mclass = .recursorM →
          IotaAt P (PointwiseRole.table P natEnvUWfT) K Efin r :=
  gInv P K (PointwiseRole.arities natEnvU) (PointwiseRole.arities_agree natEnvU)
    (NormRole.envCtx natEnvUWfT) (fun _ _ => rfl)
    (EvalRole.envPlan natEnvUWfT) (fun _ _ => rfl) _
    (PointwiseRole.table_spec P natEnvUWfT).2.1

def Witness (P : Premises4) : Prop :=
  NormNatInvariant.Witness P ∧
  (∀ K, PointwiseRole.GInv P K natEnvUWfT) ∧
  PointwiseRole.AritiesAgree (PointwiseRole.arities natEnvU) natEnvU ∧
  EvalRole.Faithful (PointwiseRole.familyValue (PointwiseRole.arities natEnvU))
    P (PointwiseRole.table P natEnvUWfT) (NormRole.envCtx natEnvUWfT)
    (EvalRole.envPlan natEnvUWfT) natEnvU ∧
  (∀ K, AllSound P (PointwiseRole.table P natEnvUWfT) K natEnvU ∧
    ∀ Efin, (∀ r m, natEnvU.members r = some m → Efin.members r = some m) →
      ∀ r m, natEnvU.members r = some m → m.mclass = .recursorM →
        IotaAt P (PointwiseRole.table P natEnvUWfT) K Efin r)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormNatInvariant.component_witness P, gInv P, PointwiseRole.arities_agree natEnvU,
    (PointwiseRole.table_spec P natEnvUWfT).2.1, actual_invariant P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PointwiseNatInvariant

import rcic.RcicF3RoleTable
import rcic.RcicF3FamKTBridge
import rcic.RcicF3KTWNonIR

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Rcic.F3.PSet.RoleNat
open Rcic.Declarative

theorem finite_eq (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (node : NatNode) (vs : List Nat) :
    Equiv (famLim P μ (famDataOf node.a) vs) (famKT P μ (famDataOf node.a) vs) := by
  have hcls : ∀ c, c ∈ (famDataOf node.a).ctors →
      FieldsClass (famDataOf node.a).fref node.a.family.member.arity
        (famDataOf node.a).params.length (famDataOf node.a).indices.length c.1 0 := by
    intro c hc
    obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
    have hd := (natEnvUWfT_classG.1.2.1 node).1 i
    change FieldsClass node.a.family.ref node.a.family.member.arity
      node.a.family.parameters.length node.a.family.indices.length
      (node.a.constructorViews i).fields 0
    rw [node.fam]
    exact fieldsClass_of_direct _ _ hd
  have hpf : ∀ e, e ∈ (famDataOf node.a).params ++ (famDataOf node.a).indices →
      occursConst (famDataOf node.a).fref e = false := by
    intro e he
    change e ∈ node.a.family.parameters ++ node.a.family.indices at he
    rw [(nat_family node).1, (nat_family node).2.1] at he
    cases he
  have hri : ∀ c, c ∈ (famDataOf node.a).ctors → ∀ e, e ∈ c.2 →
      occursConst (famDataOf node.a).fref e = false := by
    intro c hc e he
    obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
    change e ∈ (node.a.constructorViews i).resultIndices at he
    rw [(nat_views node i).2.1] at he
    cases he
  have hn : ∀ c, c ∈ (famDataOf node.a).ctors → NonIRKinds (famDataOf node.a).fref c.1 := by
    intro c hc j k hjk hk _
    obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
    change k < (node.a.constructorViews i).fields.length at hk
    rcases (nat_views node i).2.2 with ⟨hf, _⟩ | ⟨hf, _⟩
    · rw [hf] at hk; simp only [List.length_nil] at hk; omega
    · rw [hf] at hk; simp only [List.length_singleton] at hk; omega
  have hno : ∀ c, c ∈ (famDataOf node.a).ctors → ∀ p,
      p ∈ kindsOf (famDataOf node.a).fref c.1 → p ≠ .fn := by
    intro c hc p hp
    obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
    change p ∈ kindsOf node.a.family.ref (node.a.constructorViews i).fields at hp
    rcases (nat_views node i).2.2 with ⟨hf, _⟩ | ⟨hf, _⟩
    · rw [hf] at hp; cases hp
    · rw [hf, node.fam] at hp
      change p ∈ [PKind.direct] at hp
      have he := List.mem_singleton.mp hp
      rw [he]; exact PKind.noConfusion
  exact famLim_famKT_type P μ (famDataOf node.a) node.a.family.member.arity
    ⟨by rw [show (famDataOf node.a).fref = 0 from node.fam]; decide,
     by rw [show (famDataOf node.a).fref = 0 from node.fam]; decide⟩
    (famBounded_node node (typeFacts_of_envWfT natEnvUWfT)) hpf hcls hri
    (hres_of_admitted node.a) (hN_of_kinds P μ _ hn) hno vs
    (by change evalTotal (σOf vs) node.a.family.resultLevel ≠ 0
        rw [(nat_family node).2.2]; exact Nat.succ_ne_zero _)


/-- Nat's full invariant survives the replacement family role. -/
theorem gInv (P : Premises4) (K : Nat → Nat) :
    RoleModel.GInv famKT P K natEnvUWfT := by
  intro ctx hctx μ hF
  apply TierGroup.gInv_natEnvU P K ctx hctx μ
  obtain ⟨node, hs⟩ := group_node (ctors := [(1, natZeroMember), (2, natSuccMember)]) EnvWfT.empty
    (by rfl : natFamMember.mclass = .inductiveM)
    (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl)
    (by rfl : natRecMemberU.mclass = .recursorM) natMembersT
  have hc : envCtx natEnvUWfT = groupRoles (famDataOf node.a) 0 3 (fun _ => .plain) :=
    envCtx_group_some (ctors := [(1, natZeroMember), (2, natSuccMember)])
      EnvWfT.empty rfl (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl)
      rfl natMembersT _ hs
  intro r m hr vs
  have h := hF r m hr vs
  rw [hctx r (dom_of_members hr), hc] at h ⊢
  by_cases he : r = 0
  · subst he
    rw [groupRoles_at_f] at h ⊢
    exact h.trans (finite_eq P μ node vs).symm
  · have hv : RoleModel.memberVal famKT P μ
        (groupRoles (famDataOf node.a) 0 3 (fun _ => .plain) r) m vs =
        memberValR P μ (groupRoles (famDataOf node.a) 0 3 (fun _ => .plain) r) m vs := by
      unfold groupRoles
      rw [if_neg he]
      split
      · rfl
      · split <;> rfl
    rw [hv] at h
    exact h

theorem reads (P : Premises4) (node : NatNode) :
    RoleModel.FamilyReads famKT P (famDataOf node.a) := by
  intro μ₁ μ₂ S h hpi hfam vs
  exact (finite_eq P μ₁ node vs).symm.trans
    ((famLim_agreeOn P (fun r hr ls => by rw [h r hr ls]; exact Equiv.rfl)
      _ hpi hfam vs).trans (finite_eq P μ₂ node vs))

theorem readsCtx (P : Premises4) :
    RoleModel.FamilyReadsCtx famKT P (envCtx natEnvUWfT) := by
  obtain ⟨node, hs⟩ := group_node (ctors := [(1, natZeroMember), (2, natSuccMember)]) EnvWfT.empty
    (by rfl : natFamMember.mclass = .inductiveM)
    (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl)
    (by rfl : natRecMemberU.mclass = .recursorM) natMembersT
  have hc : envCtx natEnvUWfT = groupRoles (famDataOf node.a) 0 3 (fun _ => .plain) :=
    envCtx_group_some (ctors := [(1, natZeroMember), (2, natSuccMember)])
      EnvWfT.empty rfl (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl)
      rfl natMembersT _ hs
  rw [hc]
  exact RoleModel.familyReadsCtx_groupRoles
    (RoleModel.familyReadsCtx_plain famKT P) (reads P node)

end Rcic.F3.PSet.RoleNat

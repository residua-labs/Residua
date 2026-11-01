import rcic.RcicF3NormDataRec
import rcic.RcicF3RawDataRecAttack

/-!
# The normalized DATA consumer at the actual height-omega W group

The actual cached fields of the explicit admitted W node normalize to
themselves. This exact descriptor identity supplies its small closed
normalized candidate from the already produced W frame. The new normalized
consumer is then called with the actual predecessor, existing group bounds,
stored motive/minor tuple, original reader environment and constructor codes.

The resulting value belongs to the nonempty data target at motive level 1.
Only the literal W descriptor is identified with the raw fixture; no
universal raw/normalized frame equation or universal data closure is claimed.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDataRecAttack
open Rcic.Declarative Rcic.Model.PS PiIndex RawFamily PropEval
open RawDataRecAttack (σ K base model parameter target motive minors context)

noncomputable abbrev plan : EvalPlan.Plan := EvalPlan.ofNode PendAW.pNode

theorem fields_eq (j : Fin plan.node.a.constructors.length) :
    EvalPlanNormal.fields plan j = (plan.node.a.constructorViews j).fields := by
  apply NormPendAW.fields_identity plan.node.E0
    (NormPendAWValue.node_family_body PendAW.pNode) (plan.constructors j).fields
  intro A hA
  change A ∈ (PendAW.pNode.a.constructorViews j).fields at hA
  rcases (PendAWGroup.views PendAW.pNode j).2.2 with ⟨hf, _⟩ | ⟨hf, _⟩
  · rw [hf] at hA
    exact (List.not_mem_nil _ hA).elim
  · rw [hf] at hA
    exact List.mem_singleton.mp hA

theorem constructors_eq :
    EvalPlanNormal.constructors plan = (famDataOf PendAW.pNode.a).ctors := by
  apply List.ext_getElem
  · exact (EvalPlanNormal.ctors_length plan).trans
      (famDataOf_ctors_length PendAW.pNode.a).symm
  · intro j hn hr
    let k : Fin plan.node.a.constructors.length :=
      ⟨j, by simpa only [famDataOf_ctors_length] using hr⟩
    have hN := EvalPlanNormal.ctor_get plan ⟨j, hn⟩
    have hk : EvalPlanNormal.index plan ⟨j, hn⟩ = k := Fin.ext rfl
    rw [hk, fields_eq k] at hN
    have hR := famDataOf_ctor PendAW.pNode.a k
    change (famDataOf PendAW.pNode.a).ctors[j]? =
      some ((plan.node.a.constructorViews k).fields,
        (plan.node.a.constructorViews k).resultIndices) at hR
    rw [List.getElem?_eq_getElem hr] at hR
    exact hN.trans (Option.some.inj hR).symm

theorem normalized_descriptor : EvalPlanNormal.fd plan = PendAWBridge.fd := by
  unfold EvalPlanNormal.fd
  rw [constructors_eq]
  rfl

theorem small_closed (P : Premises4) :
    ∃ A, Admissible (EvalPlanNormal.fd plan) A ∧
      Closed P (base P) (EvalPlanNormal.fd plan) A := by
  rw [normalized_descriptor]
  exact ⟨frame P (base P) PendAWBridge.fd, RawWFrame.raw_admissible P (base P),
    RawFamilyInductionAttack.w_closed P (base P)⟩

theorem matching_parameters : ∀ j : Fin PendAW.pNode.a.constructors.length,
    (PendAW.pNode.a.constructorViews j).parameters = PendAW.pNode.a.family.parameters :=
  fun j => (PendAWGroup.views PendAW.pNode j).1.trans
    (PendAWGroup.familyInfo PendAW.pNode).1.symm

theorem predecessor_context : ∀ r, Dom natEnvU r →
    NormRole.envCtx PendAWGroup.wft r = NormRole.envCtx natEnvUWfT r :=
  NormRole.envCtx_group_stable natEnvUWfT rfl PendAWGroup.ctorClasses rfl PendAW.membersT

theorem predecessor_plans : ∀ r, Dom natEnvU r →
    EvalRole.envPlan PendAWGroup.wft r = EvalRole.envPlan natEnvUWfT r :=
  EvalRole.envPlan_group_stable natEnvUWfT rfl PendAWGroup.ctorClasses rfl PendAW.membersT

theorem predecessor_faithful (P : Premises4) :
    EvalRole.Faithful role P (base P) (NormRole.envCtx PendAWGroup.wft)
      (EvalRole.envPlan PendAWGroup.wft) natEnvU :=
  fun r m hm => NormPendAW.faithful P r m (groupMembersT_preserve PendAW.membersT r m hm)

/-- Every component input is supplied to the public normalized consumer.
The source of the constructor cases is its normalized frame, not a raw
closure premise or a supplied local minor contract. -/
theorem produced (P : Premises4) :
    ∀ (i : Index.{4}) (z : PSet.{4}), RawFamilyRec.paramKey 1 i = key [parameter] →
      z ∈ frame P (base P) (EvalPlanNormal.fd plan) [] i →
      RecPlan.nodeCore (model P) PendAW.pNode (minors P) z ∈
        PiRawMotiveAny.guarded (model P) σ 1 ((model P).μ 4 [])
          (motive P) [parameter] [] (push [parameter] ρ0) i z := by
  have hM : (context P).M = mkM P (table P (base P) (famDataOf (context P).node.a)
      (frame P (base P) (EvalPlanNormal.fd (EvalPlan.ofNode (context P).node)))) := by
    change model P = mkM P (table P (base P) PendAWBridge.fd
      (frame P (base P) (EvalPlanNormal.fd plan)))
    rw [normalized_descriptor]
  exact NormDataRec.nodeCore_guarded_of_small_frame P (base P) K (context P) hM
    PendAW.fam [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT rfl PendAWGroup.ctorClasses
    rfl PendAW.membersT (PendAWGroup.boundG K) (PendAWGroup.boundDG 1)
    matching_parameters (NormNatInvariant.gInv P K)
    (NormRole.envCtx PendAWGroup.wft) (EvalRole.envPlan PendAWGroup.wft)
    predecessor_context predecessor_plans (predecessor_faithful P) (small_closed P)
    (fun _ h => (List.not_mem_nil _ h).elim) (by change 1 ≠ 0; decide)
    (RawDataRecAttack.environment P) (.param 0) rfl
    (RawFamilyIHBuilderAttack.motive_mem P (base P)) (RawDataRecAttack.minors_typed P)
    (RawDataRecAttack.constructor_data P)

theorem omega_mem (P : Premises4) :
    fxZW P ∈ frame P (base P) (EvalPlanNormal.fd plan) [] (key [parameter]) := by
  rw [normalized_descriptor]
  exact RawDataRecAttack.omega_mem P

/-- The normalized constructor-case consumer yields an actual data result. -/
theorem result_mem (P : Premises4) :
    RecPlan.nodeCore (model P) PendAW.pNode (minors P) (fxZW P) ∈ target P := by
  have h := produced P (key [parameter]) (fxZW P) rfl (omega_mem P)
  have hz := RawDataRecAttack.family_mem P (fxZW P) (RawDataRecAttack.omega_mem P)
  have hm := RawDataRecAttack.motive_apply P (fxZW P) hz
  have hT : fapps (motive P) [fxZW P] ∈ (model P).U 1 :=
    mem_congr_left hm.symm (RawFamilyIHBuilderAttack.target_type P (base P))
  have hg := PiRawMotiveAny.guarded_key (model P) σ 1 ((model P).μ 4 [])
    (motive P) [parameter] [] (push [parameter] ρ0) [] (fxZW P) True.intro hz hT
  exact mem_congr_right (hg.trans ((ed_congr (model P) hm).trans
    (ed_tyv (model P) (admissible_dich (RawWFrame.raw_admissible P (base P)) [] _)))) h

theorem result_not_empty (P : Premises4) :
    ¬ Equiv (RecPlan.nodeCore (model P) PendAW.pNode (minors P) (fxZW P)) pempty := by
  have h := (RawWFrame.raw_admissible P (base P) [] (key [parameter])).2
  change (if (1 : Nat) = 0 then _ else _) at h
  rw [if_neg (by decide : (1 : Nat) ≠ 0)] at h
  exact h _ (result_mem P)

def Witness (P : Premises4) : Prop :=
  RawDataRecAttack.Witness P ∧
  EvalPlanNormal.fd plan = PendAWBridge.fd ∧
  (∃ A, Admissible (EvalPlanNormal.fd plan) A ∧
    Closed P (base P) (EvalPlanNormal.fd plan) A) ∧
  (∀ (i : Index.{4}) (z : PSet.{4}), RawFamilyRec.paramKey 1 i = key [parameter] →
    z ∈ frame P (base P) (EvalPlanNormal.fd plan) [] i →
    RecPlan.nodeCore (model P) PendAW.pNode (minors P) z ∈
      PiRawMotiveAny.guarded (model P) σ 1 ((model P).μ 4 [])
        (motive P) [parameter] [] (push [parameter] ρ0) i z) ∧
  fxZW P ∈ frame P (base P) (EvalPlanNormal.fd plan) [] (key [parameter]) ∧
  RecPlan.nodeCore (model P) PendAW.pNode (minors P) (fxZW P) ∈ target P ∧
  ¬ Equiv (RecPlan.nodeCore (model P) PendAW.pNode (minors P) (fxZW P)) pempty

theorem component_witness (P : Premises4) : Witness P :=
  ⟨RawDataRecAttack.component_witness P, normalized_descriptor, small_closed P,
    produced P, omega_mem P, result_mem P, result_not_empty P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormDataRecAttack

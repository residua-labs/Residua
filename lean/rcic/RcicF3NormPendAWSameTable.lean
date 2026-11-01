import rcic.RcicF3NormPendAWChecked

/-!
# Finite numerals at the same sound, checked PendA W table

The W extension preserves the canonical Nat family role. Restricting the
actual normalized table's faithful equations therefore identifies its Nat
entry with the raw Nat family value at that same table. Every finite numeral,
including distinct zero and one, belongs to this installed entry.

The composed witness retains the whole-environment W/D certificate and
height-omega element. It is a fixture certificate; universal StepAG and
the checked apex remain separate obligations. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPendAWSameTable
open Rcic.Declarative Rcic.Model.PS
open NormNatPlan (plan fd)

theorem nat_family_role : NormRole.envCtx PendAWGroup.wft 0 = .fam fd := by
  have hdom : Dom natEnvU 0 :=
    dom_of_members (show natEnvU.members 0 = some natFamMember from rfl)
  exact (NormRole.envCtx_group_stable natEnvUWfT rfl PendAWGroup.ctorClasses rfl
    PendAW.membersT 0 hdom).trans NormNatPlan.family_role

/-- The family equation uses the full W table on both sides. -/
theorem nat_family_value (P : Premises4) (vs : List Nat) :
    Equiv (NormPendAW.table P 0 vs)
      (RawFamily.role P (NormPendAW.table P) fd vs) := by
  have hm : PendAW.eAll.members 0 = some natFamMember :=
    groupMembersT_preserve PendAW.membersT 0 natFamMember rfl
  have h := NormPendAW.faithful P 0 natFamMember hm vs
  rw [nat_family_role] at h
  exact h

theorem installed_numeral (P : Premises4) (n : Nat) :
    RawNatFrame.numeral n ∈ Ed (mkM P (NormPendAW.table P))
      (NormPendAW.table P 0 []) := by
  have hraw : RawNatFrame.numeral n ∈
      RawFamily.frame P (NormPendAW.table P) fd [] (PiIndex.key []) := by
    change RawNatFrame.numeral n ∈ RawFamily.frame P (NormPendAW.table P)
      (famDataOf plan.node.a) [] (PiIndex.key [])
    rw [RawNatFrame.descriptor plan.node]
    exact RawNatFrame.numeral_mem P (NormPendAW.table P) plan.node.a.policy n []
  have hread := RawFamily.apply_ofFrame_ed P (NormPendAW.table P) fd
    (RawFamily.frame P (NormPendAW.table P) fd)
    (RawNatFrame.admissible_at_node P (NormPendAW.table P) plan.node) [] []
    (by rw [NormNatPlan.descriptor]; trivial)
  exact mem_congr_right (ed_congr (mkM P (NormPendAW.table P))
    (nat_family_value P [])).symm (mem_congr_right hread.symm hraw)

theorem zero_one (P : Premises4) :
    RawNatFrame.numeral 0 ∈ Ed (mkM P (NormPendAW.table P))
      (NormPendAW.table P 0 []) ∧
    RawNatFrame.numeral 1 ∈ Ed (mkM P (NormPendAW.table P))
      (NormPendAW.table P 0 []) ∧
    ¬ Equiv (RawNatFrame.numeral 0) (RawNatFrame.numeral 1) :=
  ⟨installed_numeral P 0, installed_numeral P 1, RawNatFrame.zero_ne_one⟩

def Witness (P : Premises4) : Prop :=
  NormPendAWChecked.Witness P ∧
  (∀ n, RawNatFrame.numeral n ∈ Ed (mkM P (NormPendAW.table P))
    (NormPendAW.table P 0 [])) ∧
  RawNatFrame.numeral 0 ∈ Ed (mkM P (NormPendAW.table P))
    (NormPendAW.table P 0 []) ∧
  RawNatFrame.numeral 1 ∈ Ed (mkM P (NormPendAW.table P))
    (NormPendAW.table P 0 []) ∧
  ¬ Equiv (RawNatFrame.numeral 0) (RawNatFrame.numeral 1)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormPendAWChecked.component_witness P, installed_numeral P, zero_one P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormPendAWSameTable

import rcic.RcicF3PointwiseDataFinite
import rcic.RcicF3PointwiseNatInvariant
import rcic.RcicF3NormFiniteFamilyAttack
import rcic.RcicF3NormPendAWChecked

/-!
# The generic finite DATA producer at the actual pointwise Nat table

The finite local-candidate adapter is called at every ambient table and
bound. The NEW generic checked group producer, actual walk and bounds then
produce the new Nat invariant directly at constant bounds. The existing
Nat invariant is not used in this derivation.

Every numeral inhabits this SAME installed table. Only the already-proved
Nat-specific family comparison is used to decode numerals; no old table or
universal invariant equality is substituted. Zero and one are distinct.
This is a finite-face component, not universal DATA closure. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseDataFiniteAttack
open Rcic.Declarative Rcic.Model.PS RawFamily
open Rcic.F3.StepWCheck
open NormNatPlan (plan fd ctorClasses)

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  PointwiseRole.table P natEnvUWfT

theorem faithful (P : Premises4) :
    EvalRole.Faithful (PointwiseRole.familyValue (PointwiseRole.arities natEnvU))
      P (table P) (NormRole.envCtx natEnvUWfT)
      (EvalRole.envPlan natEnvUWfT) natEnvU :=
  (PointwiseRole.table_spec P natEnvUWfT).2.1

theorem local_candidates (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) : PointwiseDataLocal.LocalCandidates P μ plan K :=
  PointwiseDataFinite.local_candidates P μ plan natFamMember
    [(1, natZeroMember), (2, natSuccMember)] .empty natMembersT
    NormDPlanBridgeAttack.nat_noFun K

theorem uniform_type : UniformType plan.node.a.family.resultLevel := by
  rw [(nat_family plan.node).2.2]
  intro σ
  exact Nat.zero_lt_succ 0

theorem group_check (k : Nat) :
    Rcic.F3.StepWDApex.groupCheck (fun _ => k) .empty
      (f := 0) (fm := natFamMember) (ctors := [(1, natZeroMember), (2, natSuccMember)])
      (rr := 3) (rm := natRecMemberU) rfl ctorClasses rfl natMembersT = none :=
  (Rcic.F3.StepWDApex.groupCheck_pass_iff _ _ _ _ _ _).mpr
    ((NormPendAWChecked.nat_d_side_iff (fun _ => k) plan.node).mpr
      ⟨Nat.le_refl k, Nat.le_refl k⟩)

theorem group_step (P : Premises4) (k : Nat) :
    PointwiseDataGroup.GroupStepAt P (fun _ => k) .empty
      (f := 0) (fm := natFamMember) (ctors := [(1, natZeroMember), (2, natSuccMember)])
      (rr := 3) (rm := natRecMemberU) rfl ctorClasses rfl natMembersT :=
  PointwiseDataFinite.group_step_of_check P (fun _ => k) .empty
    (f := 0) (fm := natFamMember) (ctors := [(1, natZeroMember), (2, natSuccMember)])
    (rr := 3) (rm := natRecMemberU) rfl ctorClasses rfl natMembersT
    uniform_type NormDPlanBridgeAttack.nat_noFun (group_check k)

theorem invariant (P : Premises4) (k : Nat) :
    PointwiseRole.GInv P (fun _ => k) natEnvUWfT :=
  group_step P k
    (walkAgree_of_groupWChecked P .empty rfl ctorClasses rfl natMembersT
      NormPendAWChecked.nat_w_checked.2)
    (PendAWGroup.boundG (fun _ => k)).1 (PendAWGroup.boundDG k).1
    (PointwiseRole.gInv_empty P (fun _ => k))

theorem env_sound (P : Premises4) (k : Nat) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (table P)) σ (fun _ => k) natEnvU n :=
  PointwiseRole.envSound_of_gInv P (fun _ => k) natEnvUWfT (invariant P k) σ n

theorem family_value (P : Premises4) (vs : List Nat) :
    Equiv (table P 0 vs) (RawFamily.role P (table P) fd vs) := by
  have h := faithful P 0 natFamMember rfl vs
  rw [NormNatPlan.normalized_context, groupRoles_at_f] at h
  exact h.trans (PointwiseNatInvariant.family_value (PointwiseRole.arities natEnvU)
    P (table P) (PointwiseRole.arities_agree natEnvU) vs)

theorem installed_numeral (P : Premises4) (n : Nat) :
    RawNatFrame.numeral n ∈ Ed (mkM P (table P)) (table P 0 []) := by
  have hraw : RawNatFrame.numeral n ∈
      RawFamily.frame P (table P) fd [] (PiIndex.key []) := by
    change RawNatFrame.numeral n ∈ RawFamily.frame P (table P)
      (famDataOf plan.node.a) [] (PiIndex.key [])
    rw [RawNatFrame.descriptor plan.node]
    exact RawNatFrame.numeral_mem P (table P) plan.node.a.policy n []
  have hread := RawFamily.apply_ofFrame_ed P (table P) fd
    (RawFamily.frame P (table P) fd)
    (RawNatFrame.admissible_at_node P (table P) plan.node) [] []
    (by rw [NormNatPlan.descriptor]; trivial)
  exact mem_congr_right (ed_congr (mkM P (table P)) (family_value P [])).symm
    (mem_congr_right hread.symm hraw)

def Witness (P : Premises4) : Prop :=
  (∀ μ K, PointwiseDataLocal.LocalCandidates P μ plan K) ∧
  (∀ k, PointwiseDataGroup.GroupStepAt P (fun _ => k) .empty
    (f := 0) (fm := natFamMember) (ctors := [(1, natZeroMember), (2, natSuccMember)])
    (rr := 3) (rm := natRecMemberU) rfl ctorClasses rfl natMembersT) ∧
  (∀ k, PointwiseRole.GInv P (fun _ => k) natEnvUWfT) ∧
  (∀ k σ n, EnvSound (mkM P (table P)) σ (fun _ => k) natEnvU n) ∧
  (∀ n, RawNatFrame.numeral n ∈ Ed (mkM P (table P)) (table P 0 [])) ∧
  ¬ Equiv (RawNatFrame.numeral 0) (RawNatFrame.numeral 1)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨local_candidates P, group_step P, invariant P, env_sound P,
    installed_numeral P, RawNatFrame.zero_ne_one⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PointwiseDataFiniteAttack

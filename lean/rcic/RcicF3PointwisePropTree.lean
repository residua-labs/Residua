import rcic.RcicF3PointwisePropParamGroup
import rcic.RcicF3PointwiseRoleConsumer
import rcic.RcicF3NormPropTree

/-!
# Inhabited higher-order PropOnly at the same pointwise table

The original admitted two-constructor Prop tree and its typing, bounds and
checks are reused as syntax. Its new group and complete recursor producers
are called directly. All semantic memberships and the typed beta equation
below are rebuilt at the new pointwise installer; no old table or invariant
is substituted. The recursive domain Prop has an actual inhabitant and its
constant-leaf branch is applied to that inhabitant.

This composes the PropOnly migration with a nonempty recursive domain,
while the separate AccR witness records its empty child domain literally.
No universal DATA local-candidate or apex claim is made. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwisePropTree
open Rcic.Declarative Rcic.Model.PS RawFamily
open Rcic.F3.StepDGOrder
open Rcic.Declarative.PropTree
open PropTreeBounds (wft ctorClasses)
open NormPropTree (plan uniform_prop matching_parameters branch_bound node_bound beta_bound d_side d_check)

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  PointwiseRole.table P wft

theorem faithful (P : Premises4) :
    EvalRole.Faithful (PointwiseRole.familyValue (PointwiseRole.arities eAll))
      P (table P) (NormRole.envCtx wft) (EvalRole.envPlan wft) eAll :=
  (PointwiseRole.table_spec P wft).2.1

/-- The complete producer has actual bounded inputs at every K. -/
theorem package (P : Premises4) (K : Nat → Nat) :
    RecPkg P (table P) K eAll 7 recMem :=
  PointwisePropOnlyIota.rec_pkg P (table P) K
    (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
    (rr := 7) (rm := recMem) EnvWfT.empty rfl ctorClasses rfl membersT
    (PropTreeBounds.boundG K) (PropTreeBounds.boundDG K) matching_parameters
    (PointwiseRole.gInv_empty P K)
    (PointwiseRole.arities eAll) (fun _ _ h => nomatch h)
    (NormRole.envCtx EnvWfT.empty) (EvalRole.envPlan EnvWfT.empty)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ h => nomatch h)
    (NormRole.envCtx wft) (EvalRole.envPlan wft)
    (fun _ _ => rfl) (fun _ _ => rfl) (faithful P)
    uniform_prop (PropTreeBounds.policyPropOnly plan.node)

theorem group_step (P : Premises4) (K : Nat → Nat) :
    PointwiseDataGroup.GroupStepAt P K EnvWfT.empty
      (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
      (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT :=
  PointwisePropParamGroup.group_step_no_parameters P K EnvWfT.empty
    (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
    (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT
    uniform_prop (PropTreeBounds.policyPropOnly plan.node)
    (PropTreeBounds.familyInfo plan.node).1

theorem invariant (P : Premises4) (K : Nat → Nat) : PointwiseRole.GInv P K wft :=
  group_step P K PropTreeBounds.walkAgree (PropTreeBounds.boundG K)
    (PropTreeBounds.boundDG K) (PointwiseRole.gInv_empty P K)

theorem env_sound (P : Premises4) (K σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (table P)) σ K eAll n :=
  PointwiseRole.envSound_of_gInv P K wft (invariant P K) σ n

/-- The semantic values below all use this same produced installed table. -/
theorem member_sound (P : Premises4) (K : Nat → Nat) (r : Nat) (m : CheckedMember)
    (hr : eAll.members r = some m) : MemberSound P (table P) K r m :=
  (invariant P K (PointwiseRole.arities eAll) (PointwiseRole.arities_agree eAll)
    (NormRole.envCtx wft) (fun _ _ => rfl)
    (EvalRole.envPlan wft) (fun _ _ => rfl) (table P) (faithful P)).1 r m hr

theorem leaf_mem (P : Premises4) :
    table P 5 [] ∈ Ed (mkM P (table P)) (table P 4 []) :=
  (member_sound P (fun _ => 1) 5 leaf rfl (fun _ => 0) [] ρ0 rfl
    (fun l hl => (List.not_mem_nil l hl).elim)).1

theorem family_mem (P : Premises4) : table P 4 [] ∈ U W4 0 := by
  have h := (member_sound P (fun _ => 1) 4 fam rfl (fun _ => 0) [] ρ0 rfl
    (fun l hl => (List.not_mem_nil l hl).elim)).1
  exact mem_congr_right (ed_tyv (mkM P (table P)) (U4_dich 0)) h

theorem branch_mem (P : Premises4) (σ : Nat → Nat) :
    den (mkM P (table P)) σ ρ0 branch ∈
      Ed (mkM P (table P)) (den (mkM P (table P)) σ ρ0 field) :=
  sound_ty (P.good _ rfl) (env_sound P (fun _ => 1) σ 0)
    branch_typed (branch_bound σ (fun _ => 1)) ρ0 True.intro

theorem node_mem (P : Premises4) (σ : Nat → Nat) :
    den (mkM P (table P)) σ ρ0 nodeTerm ∈
      Ed (mkM P (table P)) (table P 4 []) :=
  sound_ty (P.good _ rfl) (env_sound P (fun _ => 1) σ 0)
    node_typed (node_bound σ (fun _ => 1)) ρ0 True.intro

/-- The actual branch is exercised at the installed family proposition,
an inhabitant of its Prop domain, and returns the installed leaf. -/
theorem branch_application (P : Premises4) (σ : Nat → Nat) :
    Equiv (fapp (den (mkM P (table P)) σ ρ0 branch) (table P 4 []))
      (table P 5 []) :=
  (sound_conv (P.good _ rfl) (env_sound P (fun _ => 1) σ 0)
    branch_beta (beta_bound σ (fun _ => 1)) ρ0 True.intro).1

theorem checked_group_step (P : Premises4) (k : Nat) :
    PointwiseDataGroup.GroupStepAt P (fun _ => k) EnvWfT.empty
      (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
      (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT :=
  PointwisePropParamGroup.group_step_of_check P (fun _ => k) EnvWfT.empty
    (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
    (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT
    uniform_prop (PropTreeBounds.policyPropOnly plan.node) (d_check k)

def Witness (P : Premises4) : Prop :=
  PropTreeBounds.Witness ∧
  (∀ K : Nat → Nat, PointwiseRole.GInv P K wft ∧ RecPkg P (table P) K eAll 7 recMem) ∧
  (∀ k : Nat, Rcic.F3.StepWDApex.groupCheck (fun _ => k) EnvWfT.empty
    (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
    (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT = none ∧
    PointwiseDataGroup.GroupStepAt P (fun _ => k) EnvWfT.empty
      (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
      (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT) ∧
  table P 4 [] ∈ U W4 0 ∧
  table P 5 [] ∈ Ed (mkM P (table P)) (table P 4 []) ∧
  (∀ σ : Nat → Nat,
    den (mkM P (table P)) σ ρ0 branch ∈
      Ed (mkM P (table P)) (den (mkM P (table P)) σ ρ0 field) ∧
    den (mkM P (table P)) σ ρ0 nodeTerm ∈
      Ed (mkM P (table P)) (table P 4 []) ∧
    Equiv (fapp (den (mkM P (table P)) σ ρ0 branch) (table P 4 []))
      (table P 5 []))

theorem component_witness (P : Premises4) : Witness P :=
  ⟨PropTreeBounds.component_witness, fun K => ⟨invariant P K, package P K⟩,
    (fun k => ⟨d_check k, checked_group_step P k⟩), family_mem P, leaf_mem P,
    fun σ => ⟨branch_mem P σ, node_mem P σ, branch_application P σ⟩⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PointwisePropTree

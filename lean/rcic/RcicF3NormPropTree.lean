import rcic.RcicF3NormPropParamGroup
import rcic.RcicF3PropTreeBounds
import rcic.RcicF3NormRoleConsumer

/-!
# The produced higher-order PropOnly group at its actual installed table

The admitted two-constructor Prop tree has a recursive field Prop → F.
Its actual branch domain is inhabited, and the constant-leaf branch and
its node application are typed in this same environment. All bounds and
walks are supplied by the concrete admission, at arbitrary K.

The new parameter-telescope producer supplies the complete literal RecPkg
and group invariant. Their same-table soundness then supplies membership
of the actual leaf, branch argument, branch and node, together with the
typed beta equation on the inhabited branch. No StepAG input or old
invariant appears. The universal data and unchecked-mirror cases remain
open. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPropTree
open Rcic.Declarative Rcic.Model.PS RawFamily
open Rcic.F3.StepDGOrder
open Rcic.Declarative.PropTree
open PropTreeBounds (wft ctorClasses)

noncomputable def plan : EvalPlan.Plan :=
  EvalPlan.ofGroup EnvWfT.empty (f := 4) (fm := fam)
    (ctors := [(5, leaf), (6, node)]) (rr := 7) (rm := recMem)
    rfl ctorClasses rfl membersT

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  NormRole.table P wft

theorem faithful (P : Premises4) :
    EvalRole.Faithful role P (table P) (NormRole.envCtx wft)
      (EvalRole.envPlan wft) eAll :=
  (NormRole.table_spec P wft).1

theorem uniform_prop : UniformProp plan.node.a.family.resultLevel := by
  intro σ
  rw [(PropTreeBounds.familyInfo plan.node).2.2]
  rfl

theorem matching_parameters : ∀ j : Fin plan.node.a.constructors.length,
    (plan.node.a.constructorViews j).parameters = plan.node.a.family.parameters :=
  NormPropParamFields.matching_parameters_of_empty plan.node
    (PropTreeBounds.familyInfo plan.node).1

/-- All literal inputs of the new complete recursor producer are paid
by this actual group and table, independently at each bound K. -/
theorem package (P : Premises4) (K : Nat → Nat) :
    RecPkg P (table P) K eAll 7 recMem :=
  NormPropOnlyIota.rec_pkg P (table P) K
    (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
    (rr := 7) (rm := recMem) EnvWfT.empty rfl ctorClasses rfl membersT
    (PropTreeBounds.boundG K) (PropTreeBounds.boundDG K) matching_parameters
    (NormRole.gInv_empty P K)
    (NormRole.envCtx EnvWfT.empty) (EvalRole.envPlan EnvWfT.empty)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ h => nomatch h)
    (NormRole.envCtx wft) (EvalRole.envPlan wft)
    (fun _ _ => rfl) (fun _ _ => rfl) (faithful P)
    uniform_prop (PropTreeBounds.policyPropOnly plan.node)

theorem group_step (P : Premises4) (K : Nat → Nat) :
    NormRole.GroupStepAt P K EnvWfT.empty
      (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
      (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT :=
  NormPropParamGroup.group_step_no_parameters P K EnvWfT.empty
    (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
    (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT
    uniform_prop (PropTreeBounds.policyPropOnly plan.node)
    (PropTreeBounds.familyInfo plan.node).1

theorem invariant (P : Premises4) (K : Nat → Nat) : NormRole.GInv P K wft :=
  group_step P K PropTreeBounds.walkAgree (PropTreeBounds.boundG K)
    (PropTreeBounds.boundDG K) (NormRole.gInv_empty P K)

theorem env_sound (P : Premises4) (K σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (table P)) σ K eAll n :=
  NormRole.envSound_of_gInv P K wft (invariant P K) σ n

/-- The semantic values below all use this same produced installed table. -/
theorem member_sound (P : Premises4) (K : Nat → Nat) (r : Nat) (m : CheckedMember)
    (hr : eAll.members r = some m) : MemberSound P (table P) K r m :=
  (invariant P K (NormRole.envCtx wft) (fun _ _ => rfl)
    (EvalRole.envPlan wft) (fun _ _ => rfl) (table P) (faithful P)).1 r m hr

theorem leaf_mem (P : Premises4) :
    table P 5 [] ∈ Ed (mkM P (table P)) (table P 4 []) :=
  (member_sound P (fun _ => 1) 5 leaf rfl (fun _ => 0) [] ρ0 rfl
    (fun l hl => (List.not_mem_nil l hl).elim)).1

theorem family_mem (P : Premises4) : table P 4 [] ∈ U W4 0 := by
  have h := (member_sound P (fun _ => 1) 4 fam rfl (fun _ => 0) [] ρ0 rfl
    (fun l hl => (List.not_mem_nil l hl).elim)).1
  exact mem_congr_right (ed_tyv (mkM P (table P)) (U4_dich 0)) h

theorem branch_bound (σ K : Nat → Nat) : LOKt σ 4 K branch_typed := by
  change 1 ≤ 4 ∧ LevelsOK σ (K 5) []
  exact ⟨by decide, fun l hl => (List.not_mem_nil l hl).elim⟩

theorem node_bound (σ K : Nat → Nat) : LOKt σ 4 K node_typed :=
  ⟨fun l hl => (List.not_mem_nil l hl).elim, branch_bound σ K⟩

theorem beta_bound (σ K : Nat → Nat) : LOKc σ 4 K branch_beta := by
  change 1 ≤ 4 ∧ LevelsOK σ (K 5) [] ∧ LevelsOK σ (K 4) []
  exact ⟨by decide, fun l hl => (List.not_mem_nil l hl).elim,
    fun l hl => (List.not_mem_nil l hl).elim⟩

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

/-- The executable selected-node check accepts this same positive-depth
PropOnly group at any constant bound. Its parameter and policy checks are
paid structurally, rather than by treating PendA as a skipped case. -/
theorem d_side (k : Nat) (n : PropTreeBounds.Node) :
    StepDGSide (fun _ => k) n := by
  refine ⟨NormPropParamFields.matching_parameters_of_empty n
    (PropTreeBounds.familyInfo n).1, ?_, ?_⟩
  · intro _ hp
    rw [PropTreeBounds.policyPropOnly n] at hp
    cases hp
  · intro _
    exact Nat.le_refl k

theorem d_check (k : Nat) :
    Rcic.F3.StepWDApex.groupCheck (fun _ => k) EnvWfT.empty
      (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
      (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT = none :=
  (Rcic.F3.StepWDApex.groupCheck_pass_iff _ _ _ _ _ _).mpr (d_side k plan.node)

theorem checked_group_step (P : Premises4) (k : Nat) :
    NormRole.GroupStepAt P (fun _ => k) EnvWfT.empty
      (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
      (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT :=
  NormPropParamGroup.group_step_of_check P (fun _ => k) EnvWfT.empty
    (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
    (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT
    uniform_prop (PropTreeBounds.policyPropOnly plan.node) (d_check k)

def Witness (P : Premises4) : Prop :=
  PropTreeBounds.Witness ∧
  (∀ K : Nat → Nat, NormRole.GInv P K wft ∧ RecPkg P (table P) K eAll 7 recMem) ∧
  (∀ k : Nat, Rcic.F3.StepWDApex.groupCheck (fun _ => k) EnvWfT.empty
    (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
    (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT = none) ∧
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
    d_check, family_mem P, leaf_mem P,
    fun σ => ⟨branch_mem P σ, node_mem P σ, branch_application P σ⟩⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormPropTree

import rcic.RcicF3CheckedCtorWorld
import rcic.RcicF3NormSmallFrameLocalAttack
import rcic.RcicTypedGroupPinsList
import rcic.RcicF3DBoundBridge

/-!
# A nonempty checked constructor world at the admitted polymorphic List group

This is the existing `listEnvUWfT` admission, with `PosList.raisedFam`:
family arity one, result `succ (param 0)`, and recursor arity two. The
family is not the unraised `listUFamMember` from the syntax-only fixture.

The nil bound is 2, the cons bound is 1, and the recursor/family bounds
are 3. Invoking nil at the nonempty vector [2] directly calls the checked
world producer. Its all-row companion produces the two actual cons
field typings at that SAME vector, even though 2 exceeds cons's own
bound. Their original parameter and field-prefix contexts are retained.

The same-P conjunction retains the local W assembler and its independent
hidden/dependent/height-omega witnesses. No new List invariant, local
candidate producer, reader-domain mask, or recursor equation is claimed.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.CheckedCtorWorldListAttack
open Rcic.Declarative PosList Rcic.F3.StepDGOrder

abbrev Node := RecNode natEnvU listEnvUT 8 11 listURecMember

def uneven (r : Nat) : Nat := if r = 9 then 2 else if r = 10 then 1 else 3
def σ (i : Nat) : Nat := if i = 0 then 2 else 3

theorem ctorClasses :
    ∀ c ∈ [(9, listUNilMember), (10, listUConsMember)],
      c.2.mclass = .constructorM := by
  intro c hc
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> rfl

noncomputable def plan : EvalPlan.Plan :=
  EvalPlan.ofGroup natEnvUWfT (f := 8) (fm := raisedFam)
    (ctors := [(9, listUNilMember), (10, listUConsMember)])
    (rr := 11) (rm := listURecMember) rfl ctorClasses rfl listMembersU

theorem family_member (node : Node) : node.a.family.member = raisedFam :=
  Option.some.inj ((node_fam_member node).symm.trans rfl)

theorem count (node : Node) : node.a.constructors.length = 2 :=
  node_ctors_length (ctors := [(9, listUNilMember), (10, listUConsMember)]) node rfl

theorem constructor_member (node : Node) (i : Fin node.a.constructors.length) :
    (node.a.constructors[i.val] = listUNilMember ∧ i.val = 0) ∨
      (node.a.constructors[i.val] = listUConsMember ∧ i.val = 1) := by
  obtain ⟨k, hk⟩ := i
  have h := node_ctor_member node ⟨k, hk⟩
  have hi : k < 2 := count node ▸ hk
  match k, hk, hi, h with
  | 0, _, _, h => exact Or.inl ⟨Option.some.inj (h.symm.trans rfl), rfl⟩
  | 1, _, _, h => exact Or.inr ⟨Option.some.inj (h.symm.trans rfl), rfl⟩

/-- The actual selected scan determines the family data, without a
Type-valued equality between recursor nodes or their typing proofs. -/
theorem selected_data : famDataOf plan.node.a = famDataOf listGroupU := by
  have h := (groupNode natEnvUWfT (f := 8) (fm := raisedFam)
    (ctors := [(9, listUNilMember), (10, listUConsMember)])
    (rr := 11) (rm := listURecMember) rfl ctorClasses rfl listMembersU).property
  change some (famDataOf listGroupU) = some (famDataOf plan.node.a) at h
  exact (Option.some.inj h).symm

theorem family_parameters : plan.node.a.family.parameters = [paramSort] :=
  congrArg FamData.params selected_data

theorem family_level : plan.node.a.family.resultLevel = .succ (.param 0) :=
  congrArg FamData.resLevel selected_data

theorem own_telescope (node : Node) (i : Fin node.a.constructors.length) :
    (((node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields =
        [paramSort]) ∧ i.val = 0) ∨
    (((node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields =
        [paramSort, hdField, tlField]) ∧ i.val = 1) := by
  have hs := (node.a.constructorViews i).storedType
  have hn := foldApps_ne_pi
    (.const node.a.family.ref (policyFamilyLevels node.a.family))
    (fun _ _ h => Expr.noConfusion h)
    (policyParameterLocals (node.a.constructorViews i).parameters.length
      (node.a.constructorViews i).fields.length ++
      (node.a.constructorViews i).resultIndices)
  rcases constructor_member node i with ⟨hm, hi⟩ | ⟨hm, hi⟩
  · have ht : (node.a.constructors[i.val]).mtype =
        policyPi [paramSort] (.app (.const 8 [.param 0]) (.bvar 0)) := by
      rw [hm]
      rfl
    exact Or.inl ⟨((policyPi_split_eq [paramSort] _ _ _
      (fun _ _ h => Expr.noConfusion h) hn (ht.symm.trans hs)).1).symm, hi⟩
  · have ht : (node.a.constructors[i.val]).mtype =
        policyPi [paramSort, hdField, tlField]
          (.app (.const 8 [.param 0]) (.bvar 2)) := by
      rw [hm]
      rfl
    exact Or.inr ⟨((policyPi_split_eq [paramSort, hdField, tlField] _ _ _
      (fun _ _ h => Expr.noConfusion h) hn (ht.symm.trans hs)).1).symm, hi⟩

theorem matching_parameters (i : Fin plan.node.a.constructors.length) :
    (plan.node.a.constructorViews i).parameters = plan.node.a.family.parameters := by
  have hl : (plan.node.a.constructorViews i).parameters.length = 1 := by
    rw [(plan.node.a.constructorViews i).parameterCount, family_parameters]
    rfl
  have ht := List.take_left (plan.node.a.constructorViews i).parameters
    (plan.node.a.constructorViews i).fields
  rw [hl] at ht
  rcases own_telescope plan.node i with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he] at ht
    rw [family_parameters]
    exact ht.symm
  · rw [he] at ht
    rw [family_parameters]
    exact ht.symm

theorem group_check : Rcic.F3.StepWDApex.groupCheck uneven natEnvUWfT rfl
    ctorClasses rfl listMembersU = none := by
  apply (Rcic.F3.StepWDApex.groupCheck_pass_iff uneven natEnvUWfT rfl
    ctorClasses rfl listMembersU).mpr
  change StepDGSide uneven plan.node
  refine ⟨matching_parameters, ?_, ?_⟩
  · intro hu
    have h := hu (fun _ => 0)
    rw [family_level] at h
    exact False.elim (Nat.noConfusion h)
  · intro i
    rcases constructor_member plan.node i with ⟨_, hi⟩ | ⟨_, hi⟩
    · change uneven (8 + 1 + i.val) ≤ uneven 11
      rw [hi]
      decide
    · change uneven (8 + 1 + i.val) ≤ uneven 11
      rw [hi]
      decide

/-- These are actual stored typings at the recursor's instances. The
constructor's own numeric bound is deliberately not used here. -/
theorem stored_at_rec_bound (node : Node) (i : Fin node.a.constructors.length)
    (vs : List Nat) (hv : ∀ v, v ∈ vs → v ≤ uneven 11) :
    ∃ u : Level, ∃ d : HasTyT listFamOnlyU node.a.family.member.arity []
      (node.a.constructors[i.val]).mtype (.sort u), LOKt (σOf vs) 4 uneven d := by
  have h0 : σOf vs 0 ≤ 3 := by
    cases vs with
    | nil => exact Nat.zero_le 3
    | cons v vs => exact hv v (List.mem_cons_self _ _)
  have hu : evalTotal (σOf vs) (.param 0) ≤ 4 :=
    Nat.le_trans h0 (by decide)
  have hs : evalTotal (σOf vs) (.succ (.param 0)) ≤ 4 :=
    Nat.succ_le_succ h0
  have hc : LevelsOK (σOf vs) (uneven 8) [.param 0] := by
    intro l hl
    rw [List.mem_singleton.mp hl]
    exact h0
  rw [family_member node]
  rcases constructor_member node i with ⟨hm, _⟩ | ⟨hm, _⟩
  · rw [hm]
    exact ⟨_, listNilTyT (E := listFamOnlyU) rfl,
      hs, hs, hs, hc, True.intro⟩
  · rw [hm]
    exact ⟨_, listConsTyT (E := listFamOnlyU) rfl,
      hs, imax_le hu (imax_le hs hs), hs,
      hu, imax_le hs hs, True.intro,
      hs, hs, ⟨hc, True.intro⟩, ⟨hc, True.intro⟩⟩

theorem boundDG : BoundDG uneven listEnvUWfT := by
  have hn : BoundDG uneven natEnvUWfT := by
    apply boundDG_of_boundG uneven natEnvUWfT
    · refine ⟨True.intro, ?_⟩
      intro r _ hr
      have h9 : r ≠ 9 := by omega
      have h10 : r ≠ 10 := by omega
      change 3 ≤ (if r = 9 then 2 else if r = 10 then 1 else 3)
      rw [if_neg h9, if_neg h10]
      exact Nat.le_refl 3
    · exact natEnvUWfT_classG.2 uneven
  refine ⟨hn, ?_⟩
  intro node i vs _ hvs k
  obtain ⟨u, d, hd⟩ := stored_at_rec_bound node i vs hvs
  obtain ⟨d', hd'⟩ := lokt_cast (σOf vs) 4 uneven
    (node.a.constructorViews i).storedType d hd
  have hk : (node.a.constructorViews i).parameters.length + k.val <
      ((node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields).length := by
    rw [List.length_append]
    have := k.isLt
    omega
  obtain ⟨l, df, hf⟩ := policyPi_inv_lokt_nil (σOf vs) 4 uneven _ _ d' hd' _ hk
  have hg : ((node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields)[
      (node.a.constructorViews i).parameters.length + k.val]'hk =
        (node.a.constructorViews i).fields[k] := by
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    simp only [Nat.add_sub_cancel_left, Fin.getElem_fin]
  exact ⟨l, lokt_cast (σOf vs) 4 uneven hg df hf⟩

noncomputable def nilIndex : Fin plan.node.a.constructors.length :=
  ⟨0, by rw [count plan.node]; decide⟩
noncomputable def consIndex : Fin plan.node.a.constructors.length :=
  ⟨1, by rw [count plan.node]; decide⟩

theorem cons_fields : (plan.node.a.constructorViews consIndex).fields = [hdField, tlField] := by
  rcases own_telescope plan.node consIndex with ⟨_, hi⟩ | ⟨ht, _⟩
  · exact False.elim (Nat.noConfusion hi)
  · rw [matching_parameters consIndex, family_parameters] at ht
    exact (List.cons.inj ht).2

theorem invocation_arity : ([.param 0] : List Level).length =
    (plan.node.a.constructors[nilIndex.val]).arity := by
  rw [(plan.node.a.constructorViews nilIndex).arity, family_member plan.node]
  rfl

theorem invocation_levels : ∀ l, l ∈ [.param 0] → evalTotal σ l ≤ uneven 9 := by
  intro l hl
  rw [List.mem_singleton.mp hl]
  exact Nat.le_refl 2

theorem produced_world :
    ([2] : List Nat).length = plan.node.a.family.member.arity ∧
    ∀ v, v ∈ ([2] : List Nat) → v ≤ uneven 11 :=
  CheckedCtorWorld.constructor_world uneven natEnvUWfT rfl ctorClasses rfl
    listMembersU group_check nilIndex σ [.param 0] invocation_arity invocation_levels

theorem produced_fields :
    ∀ (i : Fin plan.node.a.constructors.length)
      (k : Fin (plan.node.a.constructorViews i).fields.length),
      ∃ l : Level, ∃ d : HasTyT listFamOnlyU plan.node.a.family.member.arity
        (policyPrefixContext (plan.node.a.family.parameters ++ (plan.node.a.constructorViews i).fields)
          (plan.node.a.family.parameters.length + k.val))
        ((plan.node.a.constructorViews i).fields[k]) (.sort l),
        LOKt (σOf [2]) 4 uneven d :=
  CheckedCtorWorld.all_row_fields uneven natEnvUWfT rfl ctorClasses rfl listMembersU
    group_check boundDG nilIndex σ [.param 0] invocation_arity invocation_levels

def Witness (P : Premises4) : Prop :=
  NormSmallFrameLocalAttack.Witness P ∧ Nonempty (EnvWfT listEnvUT) ∧
  plan.node.a.family.member.arity = 1 ∧ listURecMember.arity = 2 ∧
  plan.node.a.family.parameters = [paramSort] ∧
  plan.node.a.family.resultLevel = .succ (.param 0) ∧
  (plan.node.a.constructorViews consIndex).fields = [hdField, tlField] ∧
  uneven 9 = 2 ∧ uneven 10 = 1 ∧ uneven 11 = 3 ∧
  σ 0 = 2 ∧ σ 1 = 3 ∧ ([.param 0].map (evalTotal σ)) = [2] ∧
  2 > uneven 10 ∧
  Rcic.F3.StepWDApex.groupCheck uneven natEnvUWfT rfl ctorClasses rfl listMembersU = none ∧
  BoundDG uneven listEnvUWfT ∧
  (∀ v, v ∈ ([2] : List Nat) → v ≤ uneven 11) ∧
  (∀ (i : Fin plan.node.a.constructors.length)
      (k : Fin (plan.node.a.constructorViews i).fields.length),
      ∃ l : Level, ∃ d : HasTyT listFamOnlyU plan.node.a.family.member.arity
        (policyPrefixContext (plan.node.a.family.parameters ++ (plan.node.a.constructorViews i).fields)
          (plan.node.a.family.parameters.length + k.val))
        ((plan.node.a.constructorViews i).fields[k]) (.sort l),
        LOKt (σOf [2]) 4 uneven d)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormSmallFrameLocalAttack.component_witness P, pin_envWfT_listU,
    by rw [family_member plan.node]; rfl,
    rfl, family_parameters, family_level, cons_fields,
    rfl, rfl, rfl, rfl, rfl, rfl, by decide,
    group_check, boundDG, produced_world.2, produced_fields⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.CheckedCtorWorldListAttack

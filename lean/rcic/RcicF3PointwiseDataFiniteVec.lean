import rcic.RcicF3PointwiseDataFiniteList
import rcic.RcicF3PointwiseRemainingDataRigid
import rcic.RcicTypedGroupPinsVec

/-!
# The actual indexed Vec group through the syntax-produced finite DATA step

This file uses the existing Nat-then-Vec admission. The selected family
has one literal term parameter and one Nat index; the result indices are
zero and successor n. Their syntax rules out an extended own parameter
cut. The actual successful cache has only plain and depth-zero recursive
fields. Both original bounds are produced, and the complete invariant is
applied to the actual pointwise table.

No InScope premise, W check, alternative group, or replacement recursor
is used. This is an indexed instance of the new produced coverage, not a
claim about every indexed DATA family. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Rcic.F3.PSet.PointwiseDataFiniteVec
open Rcic.Declarative Rcic.Model.PS RawFamily

abbrev Node := RecNode natEnvU vecEnvUT 4 7 vecRecMemberU

def bound : Nat → Nat := fun _ => 1

abbrev parameter : Expr Nat := .sort (.succ .zero)

def fields : List (Expr Nat) :=
  [.const 0 [], .bvar 1, .app (.app (.const 4 []) (.bvar 2)) (.bvar 1)]

theorem ctorClasses :
    ∀ c ∈ [(5, vecNilMember), (6, vecConsMember)], c.2.mclass = .constructorM := by
  intro c hc
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> rfl

noncomputable def plan : EvalPlan.Plan :=
  EvalPlan.ofGroup natEnvUWfT (f := 4) (fm := vecFamMember)
    (ctors := [(5, vecNilMember), (6, vecConsMember)])
    (rr := 7) (rm := vecRecMemberU) rfl ctorClasses rfl vecMembersU

theorem family_member (node : Node) : node.a.family.member = vecFamMember :=
  Option.some.inj ((node_fam_member node).symm.trans rfl)

theorem count (node : Node) : node.a.constructors.length = 2 :=
  node_ctors_length (ctors := [(5, vecNilMember), (6, vecConsMember)]) node rfl

theorem constructor_member (node : Node) (i : Fin node.a.constructors.length) :
    (node.a.constructors[i.val] = vecNilMember ∧ i.val = 0) ∨
      (node.a.constructors[i.val] = vecConsMember ∧ i.val = 1) := by
  obtain ⟨k, hk⟩ := i
  have h := node_ctor_member node ⟨k, hk⟩
  have hi : k < 2 := count node ▸ hk
  match k, hk, hi, h with
  | 0, _, _, h => exact Or.inl ⟨Option.some.inj (h.symm.trans rfl), rfl⟩
  | 1, _, _, h => exact Or.inr ⟨Option.some.inj (h.symm.trans rfl), rfl⟩

/-- The descriptor is the actual scan result; no equality between
Type-valued nodes or typing derivations is used. -/
theorem selected_data : famDataOf plan.node.a = famDataOf vecGroupU := by
  have h := (groupNode natEnvUWfT (f := 4) (fm := vecFamMember)
    (ctors := [(5, vecNilMember), (6, vecConsMember)])
    (rr := 7) (rm := vecRecMemberU) rfl ctorClasses rfl vecMembersU).property
  change some (famDataOf vecGroupU) = some (famDataOf plan.node.a) at h
  exact (Option.some.inj h).symm

theorem family_parameters : plan.node.a.family.parameters = [parameter] :=
  congrArg FamData.params selected_data

theorem family_indices : plan.node.a.family.indices = [.const 0 []] :=
  congrArg FamData.indices selected_data

theorem family_level : plan.node.a.family.resultLevel = .succ .zero :=
  congrArg FamData.resLevel selected_data

theorem family_level_at (node : Node) : node.a.family.resultLevel = .succ .zero :=
  (Rcic.F3.StepWGroup.nodeResult_unique node plan.node).trans family_level

theorem own_telescope (node : Node) (i : Fin node.a.constructors.length) :
    ((node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields =
      [parameter]) ∨
    ((node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields =
      parameter :: fields) := by
  have hs := (node.a.constructorViews i).storedType
  have hn := foldApps_ne_pi
    (.const node.a.family.ref (policyFamilyLevels node.a.family))
    (fun _ _ h => Expr.noConfusion h)
    (policyParameterLocals (node.a.constructorViews i).parameters.length
      (node.a.constructorViews i).fields.length ++
      (node.a.constructorViews i).resultIndices)
  rcases constructor_member node i with ⟨hm, _⟩ | ⟨hm, _⟩
  · have ht : (node.a.constructors[i.val]).mtype =
        policyPi [parameter] (.app (.app (.const 4 []) (.bvar 0)) (.const 1 [])) := by
      rw [hm]
      rfl
    exact Or.inl ((policyPi_split_eq [parameter] _ _ _
      (fun _ _ h => Expr.noConfusion h) hn (ht.symm.trans hs)).1).symm
  · have ht : (node.a.constructors[i.val]).mtype =
        policyPi (parameter :: fields)
          (.app (.app (.const 4 []) (.bvar 3)) (.app (.const 2 []) (.bvar 2))) := by
      rw [hm]
      rfl
    exact Or.inr ((policyPi_split_eq (parameter :: fields) _ _ _
      (fun _ _ h => Expr.noConfusion h) hn (ht.symm.trans hs)).1).symm

theorem matching_parameters (j : Fin plan.node.a.constructors.length) :
    (plan.node.a.constructorViews j).parameters = plan.node.a.family.parameters := by
  have hl : (plan.node.a.constructorViews j).parameters.length = 1 := by
    rw [(plan.node.a.constructorViews j).parameterCount, family_parameters]
    rfl
  have ht := List.take_left (plan.node.a.constructorViews j).parameters
    (plan.node.a.constructorViews j).fields
  rw [hl] at ht
  rcases own_telescope plan.node j with he | he
  · rw [he] at ht
    rw [family_parameters]
    exact ht.symm
  · rw [he] at ht
    rw [family_parameters]
    exact ht.symm

/-- Fields and terminal indices are read from the same actual scan. -/
theorem constructor_data (j : Fin plan.node.a.constructors.length) :
    ((plan.node.a.constructorViews j).fields = [] ∧
      (plan.node.a.constructorViews j).resultIndices = [.const 1 []]) ∨
    ((plan.node.a.constructorViews j).fields = fields ∧
      (plan.node.a.constructorViews j).resultIndices = [.app (.const 2 []) (.bvar 2)]) := by
  have hc := famDataOf_ctor plan.node.a j
  rw [selected_data] at hc
  by_cases h0 : j.val = 0
  · have hlookup : (famDataOf vecGroupU).ctors[j.val]? =
        some (([] : List (Expr Nat)), [.const 1 []]) := by
      rw [h0]
      rfl
    have he := Option.some.inj (hlookup.symm.trans hc)
    exact Or.inl ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
  · have hj : j.val < 2 := count plan.node ▸ j.isLt
    have h1 : j.val = 1 := by omega
    have hlookup : (famDataOf vecGroupU).ctors[j.val]? =
        some (fields, [.app (.const 2 []) (.bvar 2)]) := by
      rw [h1]
      rfl
    have he := Option.some.inj (hlookup.symm.trans hc)
    exact Or.inr ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

theorem first_index_rigid : PointwiseDataFiniteRigid.FirstIndexRigid plan.node := by
  intro j k h
  rcases constructor_data j with ⟨_, hi⟩ | ⟨_, hi⟩
  · rw [hi] at h
    cases h
  · rw [hi] at h
    cases h

theorem no_fun : NoFunRec plan.node := by
  intro j s hs
  have hbF := transparentBody_family plan.node.a.family []
  rw [plan.node.fam] at hbF
  have hmN : plan.node.E0.members 0 = some natFamMember :=
    plan.node.base 0 natFamMember rfl
  have hbN : transparentBody plan.node.E0 0 [] = none := by
    unfold transparentBody
    rw [hmN]
    rfl
  have hread : ∀ A ∈ (plan.node.a.constructorViews j).fields,
      ∃ readFuel, piTelescopeFuel plan.node.E0 readFuel A = some ([], A) := by
    intro A hA
    rcases constructor_data j with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at hA
      exact (List.not_mem_nil _ hA).elim
    · rw [he] at hA
      change A ∈ [.const 0 [], .bvar 1,
        .app (.app (.const 4 []) (.bvar 2)) (.bvar 1)] at hA
      rcases List.mem_cons.mp hA with rfl | hA
      · exact ⟨2, piTelescopeFuel_famApp [] hbN (Nat.le_refl 2)⟩
      · rcases List.mem_cons.mp hA with rfl | hA
        · exact ⟨2, rfl⟩
        · have he := List.mem_singleton.mp hA
          subst A
          exact ⟨2, piTelescopeFuel_famApp [.bvar 2, .bvar 1] hbF (Nat.le_refl 2)⟩
  have h := PointwiseDataFiniteList.fields_no_fun_of_readers
    (plan.constructors j).fields hread
  rw [(plan.constructors j).shapes_admitted] at h
  exact h s hs

theorem uniform_type : UniformType plan.node.a.family.resultLevel := by
  rw [family_level]
  intro σ
  exact Nat.zero_lt_succ 0

/-- Constructor typings contain only closed levels and empty constant
instances, so they satisfy the original bound at every valuation and K. -/
theorem stored_typed (K σ : Nat → Nat) (node : Node)
    (i : Fin node.a.constructors.length) :
    ∃ u : Level, ∃ d : HasTyT vecFamOnlyU node.a.family.member.arity []
      (node.a.constructors[i.val]).mtype (.sort u), LOKt σ 4 K d := by
  rw [family_member node]
  rcases constructor_member node i with ⟨hm, _⟩ | ⟨hm, _⟩
  · rw [hm]
    refine ⟨vecNilSortU, vecNilTyT rfl rfl, ?_⟩
    simp [vecNilTyT, vecOfTyT, vecConstTyT, LOKt, LevelsOK, evalTotal]
  · rw [hm]
    refine ⟨vecConsSortU, vecConsTyT rfl rfl rfl, ?_⟩
    simp [vecConsTyT, vecOfTyT, vecConstTyT, natConstTyT, LOKt, LevelsOK, evalTotal]

theorem boundG (K : Nat → Nat) : BoundG K vecEnvUWfT := by
  refine ⟨natEnvUWfT_classG.2 K, ?_, ?_, ?_⟩
  · intro node i vs _ _
    exact stored_typed K (σOf vs) node i
  · refine ⟨trivial, ?_, ?_, trivial, trivial⟩
    · intro vs _ _ k
      obtain ⟨k, hk⟩ := k
      match k, hk with
      | 0, _ => exact ⟨HasTyT.sort [] (.succ .zero), by change 2 ≤ 4; decide⟩
    · intro vs _ _ k
      obtain ⟨k, hk⟩ := k
      match k, hk with
      | 0, _ => exact ⟨HasTyT.sort [] (.succ .zero), by change 2 ≤ 4; decide⟩
      | 1, _ => exact ⟨natConstTyT rfl, fun l hl => (List.not_mem_nil l hl).elim⟩
      | 2, _ => exact ⟨HasTyT.bvar _ 1 _ rfl, True.intro⟩
      | 3, _ =>
          refine ⟨vecOfTyT (E := vecFamNilU) (n := 0) rfl
            (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl), ?_⟩
          simp [vecOfTyT, vecConstTyT, LOKt, LevelsOK]
  · intro node hProp _ _ _ _ _
    have hz := hProp (fun _ => 0)
    rw [family_level_at node] at hz
    exact False.elim (Nat.noConfusion hz)

/-- At this concrete constant bound, the existing bridge produces the
unchanged BoundDG. No comparison is a premise of the group invariant. -/
theorem boundDG : BoundDG bound vecEnvUWfT := by
  apply boundDG_of_boundG bound vecEnvUWfT ?_ (boundG bound)
  exact ⟨⟨trivial, fun _ _ _ => Nat.le_refl 1⟩,
    fun _ _ _ => Nat.le_refl 1⟩

theorem invariant (P : Premises4) : PointwiseRole.GInv P bound vecEnvUWfT :=
  PointwiseDataFiniteRigid.invariant_step P bound natEnvUWfT rfl
    ctorClasses rfl vecMembersU uniform_type no_fun matching_parameters
    first_index_rigid (boundG bound) boundDG (PointwiseNatInvariant.gInv P bound)

theorem actual_table (P : Premises4) :
    AllSound P (PointwiseRole.table P vecEnvUWfT) bound vecEnvUT ∧
      ∀ Efin, (∀ r m, vecEnvUT.members r = some m → Efin.members r = some m) →
        ∀ r m, vecEnvUT.members r = some m → m.mclass = .recursorM →
          IotaAt P (PointwiseRole.table P vecEnvUWfT) bound Efin r :=
  invariant P (PointwiseRole.arities vecEnvUT) (PointwiseRole.arities_agree vecEnvUT)
    (NormRole.envCtx vecEnvUWfT) (fun _ _ => rfl)
    (EvalRole.envPlan vecEnvUWfT) (fun _ _ => rfl) _
    (PointwiseRole.table_spec P vecEnvUWfT).2.1

theorem newly_covered :
    PointwiseRemainingDataRigid.DataCovered natEnvUWfT (fm := vecFamMember)
      (ctors := [(5, vecNilMember), (6, vecConsMember)])
      (rr := 7) (rm := vecRecMemberU) rfl ctorClasses rfl vecMembersU ∧
    ¬ PointwiseRemainingRefined.DataCovered natEnvUWfT (fm := vecFamMember)
      (ctors := [(5, vecNilMember), (6, vecConsMember)])
      (rr := 7) (rm := vecRecMemberU) rfl ctorClasses rfl vecMembersU := by
  refine ⟨Or.inr ⟨matching_parameters, no_fun, first_index_rigid⟩, ?_⟩
  intro h
  rcases h with he | ⟨u, he, _⟩
  · cases he
  · cases he

def Witness (P : Premises4) : Prop :=
  Nonempty (EnvWfT vecEnvUT) ∧
  BoundG bound vecEnvUWfT ∧ BoundDG bound vecEnvUWfT ∧
  plan.node.a.family.parameters = [parameter] ∧
  plan.node.a.family.indices = [.const 0 []] ∧
  NoFunRec plan.node ∧ PointwiseDataFiniteRigid.FirstIndexRigid plan.node ∧
  (PointwiseRemainingDataRigid.DataCovered natEnvUWfT (fm := vecFamMember)
    (ctors := [(5, vecNilMember), (6, vecConsMember)])
    (rr := 7) (rm := vecRecMemberU) rfl ctorClasses rfl vecMembersU) ∧
  (¬ PointwiseRemainingRefined.DataCovered natEnvUWfT (fm := vecFamMember)
    (ctors := [(5, vecNilMember), (6, vecConsMember)])
    (rr := 7) (rm := vecRecMemberU) rfl ctorClasses rfl vecMembersU) ∧
  PointwiseRole.GInv P bound vecEnvUWfT ∧
  AllSound P (PointwiseRole.table P vecEnvUWfT) bound vecEnvUT

theorem witness (P : Premises4) : Witness P :=
  ⟨⟨vecEnvUWfT⟩, boundG bound, boundDG, family_parameters, family_indices,
    no_fun, first_index_rigid, newly_covered.1, newly_covered.2,
    invariant P, (actual_table P).1⟩

end Rcic.F3.PSet.PointwiseDataFiniteVec

#print axioms Rcic.F3.PSet.PointwiseDataFiniteVec.no_fun
#print axioms Rcic.F3.PSet.PointwiseDataFiniteVec.boundG
#print axioms Rcic.F3.PSet.PointwiseDataFiniteVec.boundDG
#print axioms Rcic.F3.PSet.PointwiseDataFiniteVec.invariant
#print axioms Rcic.F3.PSet.PointwiseDataFiniteVec.witness

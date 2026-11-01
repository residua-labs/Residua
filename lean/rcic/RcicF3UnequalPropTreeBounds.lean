import rcic.RcicF3UnequalPropTreeFixture
import rcic.RcicF3PendAWGroup
import rcic.RcicF3AndFixture

/-!
# Original bounds and exact views for the unequal-mirror PropOnly tree

The stored recursor's leading Prop binder forces one family parameter,
even for an arbitrary RecNode witnessing this same actual group. The
constructor views therefore have their literal beta-expanded parameter
and the original empty/recursive field rows. A concrete K = 2 suffices
for the original BoundG and BoundDG, with no recursor/constructor rebound.
Source-only draft; root owns native validation. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Rcic.F3.PSet.UnequalPropTreeBounds
open Rcic.Declarative Rcic.Declarative.UnequalPropTree

abbrev Node := RecNode emptyEnv eAll 4 7 recMem
def bound : Nat → Nat := fun _ => 2

theorem familyMember (n : Node) : n.a.family.member = fam :=
  Option.some.inj ((node_fam_member n).symm.trans rfl)

theorem recursorHead : ∃ B : Expr Nat, recMem.mtype = .pi (.sort .zero) B := by
  rw [recA.recursorType]
  unfold policyRecursorType
  rw [family_parameters]
  exact ⟨_, rfl⟩

theorem familyInfo (n : Node) :
    n.a.family.parameters = [.sort .zero] ∧ n.a.family.indices = [] ∧
      n.a.family.resultLevel = .zero := by
  have hst := n.a.family.storedType
  rw [familyMember n] at hst
  obtain ⟨hds, hbody⟩ := policyPi_split_eq [.sort .zero] _ _ _
    (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) hst
  injection hbody with hl
  cases hp : n.a.family.parameters with
  | nil =>
      obtain ⟨B, hB⟩ := recursorHead
      have hr := n.a.recursorType
      unfold policyRecursorType at hr
      rw [hp] at hr
      change recMem.mtype = .pi (policyMotiveType n.a.family n.a.policy) _ at hr
      have hh := hB.symm.trans hr
      injection hh with hdom _
      obtain ⟨A, C, hAC⟩ := policyMotiveType_pi n.a.family n.a.policy
      rw [hAC] at hdom
      cases hdom
  | cons A As =>
      rw [hp, List.cons_append] at hds
      obtain ⟨hA, htail⟩ := List.cons.inj hds
      obtain ⟨hAs, hIs⟩ := List.append_eq_nil.mp htail.symm
      refine ⟨?_, hIs, hl.symm⟩
      simp only [hp, hAs, ← hA]

theorem familyArity (n : Node) : n.a.family.member.arity = 0 :=
  congrArg (fun m : CheckedMember => m.arity) (familyMember n)

theorem ctorCount (n : Node) : n.a.constructors.length = 2 :=
  node_ctors_length (ctors := [(5, leaf), (6, node)]) n rfl

theorem policyPropOnly (n : Node) : n.a.policy = .propOnly :=
  (n.a.uniformProp_many (fun σ => by rw [(familyInfo n).2.2]; rfl)
    (by rw [ctorCount n]; decide)).1

theorem ctorInfo (n : Node) (i : Fin n.a.constructors.length) :
    (n.a.constructors[i.val] = leaf ∧ i.val = 0) ∨
      (n.a.constructors[i.val] = node ∧ i.val = 1) := by
  obtain ⟨k, hk⟩ := i
  have hm := node_ctor_member n ⟨k, hk⟩
  have hi : k < 2 := (ctorCount n) ▸ hk
  match k, hk, hi, hm with
  | 0, _, _, h => exact Or.inl ⟨Option.some.inj (h.symm.trans rfl), rfl⟩
  | 1, _, _, h => exact Or.inr ⟨Option.some.inj (h.symm.trans rfl), rfl⟩

theorem views (n : Node) (i : Fin n.a.constructors.length) :
    (n.a.constructorViews i).parameters = [ownParam] ∧
    (n.a.constructorViews i).resultIndices = [] ∧
    (((n.a.constructorViews i).fields = [] ∧ i.val = 0) ∨
      ((n.a.constructorViews i).fields = [field] ∧ i.val = 1)) := by
  obtain ⟨hP, hI, _⟩ := familyInfo n
  have hpl : (n.a.constructorViews i).parameters.length = 1 := by
    rw [(n.a.constructorViews i).parameterCount, hP]
    rfl
  have hri : (n.a.constructorViews i).resultIndices = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [(n.a.constructorViews i).indexCount, hI]
    rfl
  have hst := (n.a.constructorViews i).storedType
  have hne := foldApps_ne_pi (.const n.a.family.ref (policyFamilyLevels n.a.family))
    (fun _ _ h => Expr.noConfusion h)
    (policyParameterLocals (n.a.constructorViews i).parameters.length
      (n.a.constructorViews i).fields.length ++ (n.a.constructorViews i).resultIndices)
  rcases ctorInfo n i with ⟨e, h0⟩ | ⟨e, h1⟩
  · have hm : (n.a.constructors[i.val]).mtype =
        policyPi [ownParam] (famApp (.bvar 0)) := by rw [e]; rfl
    have hsp := (policyPi_split_eq _ _ _ _
      (fun _ _ h => Expr.noConfusion h) hne (hm.symm.trans hst)).1
    obtain ⟨hp, hf⟩ := List.append_inj
      (show ([ownParam] : List (Expr Nat)) ++ [] = _ from hsp)
      (by rw [hpl]; rfl)
    exact ⟨hp.symm, hri, Or.inl ⟨hf.symm, h0⟩⟩
  · have hm : (n.a.constructors[i.val]).mtype =
        policyPi [ownParam, field] (famApp (.bvar 1)) := by rw [e]; rfl
    have hsp := (policyPi_split_eq _ _ _ _
      (fun _ _ h => Expr.noConfusion h) hne (hm.symm.trans hst)).1
    obtain ⟨hp, hf⟩ := List.append_inj
      (show ([ownParam] : List (Expr Nat)) ++ [field] = _ from hsp)
      (by rw [hpl]; rfl)
    exact ⟨hp.symm, hri, Or.inr ⟨hf.symm, h1⟩⟩

theorem walkClass (n : Node) : WalkClass n.a.family.parameters.length membersT := by
  rw [(familyInfo n).1]
  unfold membersT
  repeat rw [walkClass_andRec]
  refine ⟨True.intro, ?_⟩
  repeat rw [walkClass_andRec]
  refine ⟨rfl, ?_⟩
  repeat rw [walkClass_andRec]
  refine ⟨rfl, ?_⟩
  repeat rw [walkClass_andRec]
  exact ⟨rfl, True.intro⟩

theorem walkAgree (n : Node) :
    WalkAgree (AgreeAt n.a.family.parameters.length) membersT :=
  walkAgree_of_walkClass n membersT (walkClass n)

theorem ctorClasses : ∀ c ∈ [(5, leaf), (6, node)], c.2.mclass = .constructorM := by
  intro c hc
  rcases List.mem_cons.mp hc with h | h
  · cases h; rfl
  · cases List.mem_singleton.mp h; rfl

noncomputable def wft : EnvWfT eAll :=
  .group emptyEnv 4 fam [(5, leaf), (6, node)] 7 recMem eAll
    .empty rfl ctorClasses rfl membersT

theorem walkG : WalkG wft :=
  ⟨True.intro, walkRec_of_walkClass _ membersT (walkClass pNode), walkAgree⟩

theorem ctorBound (n : Node) (σ : Nat → Nat) (i : Fin n.a.constructors.length) :
    ∃ (u : Level) (d : HasTyT eFam n.a.family.member.arity []
      (n.a.constructors[i.val]).mtype (.sort u)), LOKt σ 4 bound d := by
  rw [familyMember n]
  rcases ctorInfo n i with ⟨e, _⟩ | ⟨e, _⟩
  · rw [e]
    refine ⟨_, leaf_type_typed rfl, ?_⟩
    simp [leaf_type_typed, ownParam_typed, famApp_typed, parameter_typed,
      ownParam_beta, LOKt, LOKc, LevelsOK, evalTotal]
  · rw [e]
    refine ⟨_, node_type_typed rfl, ?_⟩
    simp [node_type_typed, field_typed, ownParam_typed, famApp_typed, parameter_typed,
      ownParam_beta, LOKt, LOKc, LevelsOK, evalTotal]

kernel_rfl_theorem leafLength : PendAWGroup.ownLength leafAdm = 1
kernel_rfl_theorem nodeLength : PendAWGroup.ownLength nodeAdm = 2
kernel_rfl_theorem leafAt0Eq :
  (fun K σ : Nat → Nat => PendAWGroup.ownAt K σ leafAdm 0) =
    (fun K σ => ∃ d : HasTyT eFam 0 [] ownParam
      (.sort (.succ .zero)), LOKt σ 4 K d)
kernel_rfl_theorem nodeAt0Eq :
  (fun K σ : Nat → Nat => PendAWGroup.ownAt K σ nodeAdm 0) =
    (fun K σ => ∃ d : HasTyT eLeaf 0 [] ownParam
      (.sort (.succ .zero)), LOKt σ 4 K d)
kernel_rfl_theorem nodeAt1Eq :
  (fun K σ : Nat → Nat => PendAWGroup.ownAt K σ nodeAdm 1) =
    (fun K σ => ∃ d : HasTyT eLeaf 0 [.assumption ownParam] field
      (.sort (.imax (.succ .zero) .zero)), LOKt σ 4 K d)

theorem leafBound : PendAWGroup.ownBound bound leafAdm := by
  apply PendAWGroup.ownBound_of_at
  intro vs k
  cases k with
  | zero =>
      rw [congrFun (congrFun leafAt0Eq bound) (σOf vs)]
      refine ⟨ownParam_typed eFam [], ?_⟩
      simp [ownParam_typed, LOKt, evalTotal]
  | succ k =>
      exact PendAWGroup.ownAt_ge _ _ _ _
        (leafLength ▸ Nat.succ_le_succ (Nat.zero_le k))

theorem nodeBound : PendAWGroup.ownBound bound nodeAdm := by
  apply PendAWGroup.ownBound_of_at
  intro vs k
  cases k with
  | zero =>
      rw [congrFun (congrFun nodeAt0Eq bound) (σOf vs)]
      refine ⟨ownParam_typed eLeaf [], ?_⟩
      simp [ownParam_typed, LOKt, evalTotal]
  | succ k =>
      cases k with
      | zero =>
          rw [congrFun (congrFun nodeAt1Eq bound) (σOf vs)]
          refine ⟨field_typed rfl, ?_⟩
          simp [field_typed, famApp_typed, parameter_typed, ownParam_beta,
            LOKt, LOKc, LevelsOK, evalTotal]
      | succ k =>
          exact PendAWGroup.ownAt_ge _ _ _ _
            (nodeLength ▸ Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k)))

theorem walkBound : WalkB2 bound membersT := by
  unfold membersT
  repeat rw [walkB2_andRec]
  refine ⟨True.intro, ?_⟩
  repeat rw [walkB2_andRec]
  refine ⟨leafBound, ?_⟩
  repeat rw [walkB2_andRec]
  refine ⟨nodeBound, ?_⟩
  repeat rw [walkB2_andRec]
  exact ⟨True.intro, True.intro⟩

theorem boundG : BoundG bound wft := by
  refine ⟨True.intro, fun n i vs _ _ => ctorBound n (σOf vs) i,
    walkBound, fun n _ ha => ?_⟩
  rw [policyPropOnly n] at ha
  cases ha

theorem fieldBound (n : Node) (σ : Nat → Nat)
    (i : Fin n.a.constructors.length) (k : Fin (n.a.constructorViews i).fields.length) :
    ∃ l : Level,
      ∃ d : HasTyT eFam n.a.family.member.arity
        (policyPrefixContext ((n.a.constructorViews i).parameters ++
          (n.a.constructorViews i).fields)
          ((n.a.constructorViews i).parameters.length + k.val))
        ((n.a.constructorViews i).fields[k]) (.sort l), LOKt σ 4 bound d := by
  obtain ⟨hp, _, hfields⟩ := views n i
  rcases hfields with ⟨hf, _⟩ | ⟨hf, _⟩
  · have hlen : (n.a.constructorViews i).fields.length = 0 := congrArg List.length hf
    exact (Nat.not_lt_zero k.val (Nat.lt_of_lt_of_eq k.isLt hlen)).elim
  · obtain ⟨k, hk⟩ := k
    have hk0 : k = 0 := by
      rw [hf] at hk
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
    subst k
    have hΓ : policyPrefixContext ((n.a.constructorViews i).parameters ++
        (n.a.constructorViews i).fields)
        ((n.a.constructorViews i).parameters.length + 0) = [.assumption ownParam] := by
      rw [hp, hf]
      rfl
    have hfield : (n.a.constructorViews i).fields[0]'hk = field := by
      simp only [hf, List.getElem_cons_zero]
    change ∃ l : Level,
      ∃ d : HasTyT eFam n.a.family.member.arity
        (policyPrefixContext ((n.a.constructorViews i).parameters ++
          (n.a.constructorViews i).fields)
          ((n.a.constructorViews i).parameters.length + 0))
        ((n.a.constructorViews i).fields[0]'hk) (.sort l), LOKt σ 4 bound d
    rw [familyArity n, hΓ, hfield]
    refine ⟨.imax (.succ .zero) .zero, field_typed rfl, ?_⟩
    simp [field_typed, famApp_typed, parameter_typed, ownParam_beta,
      LOKt, LOKc, LevelsOK, evalTotal]

theorem boundDG : BoundDG bound wft :=
  ⟨True.intro, fun n i vs _ _ k => fieldBound n (σOf vs) i k⟩

def Witness : Prop :=
  UnequalPropTree.Witness ∧ WalkG wft ∧ BoundG bound wft ∧ BoundDG bound wft

theorem component_witness : Witness :=
  ⟨UnequalPropTree.component_witness, walkG, boundG, boundDG⟩

end Rcic.F3.PSet.UnequalPropTreeBounds

#print axioms Rcic.F3.PSet.UnequalPropTreeBounds.boundG
#print axioms Rcic.F3.PSet.UnequalPropTreeBounds.boundDG
#print axioms Rcic.F3.PSet.UnequalPropTreeBounds.component_witness

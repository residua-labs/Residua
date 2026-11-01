import rcic.RcicF3FamilyBetaPropTreeFixture
import rcic.RcicF3PendAWGroup

/-!
# Original bounds for the admitted head-beta PropOnly tree

Every recursor node of the admitted four-member group has the literal
parameter-free, index-free, two-constructor Prop-only signature. The
stored constructor types and their original field typings satisfy the
bound at every K, directly: all constant instances have arity zero.
No comparison between the recursor and constructor bounds is assumed.

The component retains the fixture's actual typed inhabited branch and
supplies WalkG, WalkAgree, BoundG and BoundDG for the same explicit group
derivation. It does not itself produce a semantic group invariant. Source-only draft;
root owns native validation.
closure_claim = 0.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Rcic.F3.PSet.FamilyBetaPropTreeBounds
open Rcic.Declarative
open Rcic.Declarative.FamilyBetaPropTree

abbrev Node := RecNode emptyEnv eAll 4 7 recMem

theorem familyMember (n : Node) : n.a.family.member = fam :=
  Option.some.inj ((node_fam_member n).symm.trans rfl)

theorem familyInfo (n : Node) :
    n.a.family.parameters = [] ∧ n.a.family.indices = [] ∧
      n.a.family.resultLevel = .zero := by
  have hst := n.a.family.storedType
  rw [familyMember n] at hst
  obtain ⟨hds, hbody⟩ := policyPi_split_eq [] _ _ _
    (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) hst
  obtain ⟨hp, hi⟩ := List.append_eq_nil.mp hds.symm
  injection hbody with hl
  exact ⟨hp, hi, hl.symm⟩

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
    (n.a.constructorViews i).parameters = [] ∧
    (n.a.constructorViews i).resultIndices = [] ∧
    (((n.a.constructorViews i).fields = [] ∧ i.val = 0) ∨
      ((n.a.constructorViews i).fields = [field] ∧ i.val = 1)) := by
  obtain ⟨hP, hI, _⟩ := familyInfo n
  have hp : (n.a.constructorViews i).parameters = [] := by
    apply List.eq_nil_of_length_eq_zero
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
  · have hm : (n.a.constructors[i.val]).mtype = policyPi [] (.const 4 []) := by
      rw [e]
      rfl
    have hsp := (policyPi_split_eq _ _ _ _
      (fun _ _ h => Expr.noConfusion h) hne (hm.symm.trans hst)).1
    rw [hp, List.nil_append] at hsp
    exact ⟨hp, hri, Or.inl ⟨hsp.symm, h0⟩⟩
  · have hm : (n.a.constructors[i.val]).mtype = policyPi [field] (.const 4 []) := by
      rw [e]
      rfl
    have hsp := (policyPi_split_eq _ _ _ _
      (fun _ _ h => Expr.noConfusion h) hne (hm.symm.trans hst)).1
    rw [hp, List.nil_append] at hsp
    exact ⟨hp, hri, Or.inr ⟨hsp.symm, h1⟩⟩

theorem walkClass (n : Node) : WalkClass n.a.family.parameters.length membersT := by
  rw [(familyInfo n).1]
  unfold membersT checkedCons recMembersT
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
  · cases h
    rfl
  · cases List.mem_singleton.mp h
    rfl

-- Retain the admission derivation as kernel data without a generated executable.
noncomputable def wft : EnvWfT eAll :=
  .group emptyEnv 4 fam [(5, leaf), (6, node)] 7 recMem eAll
    .empty rfl ctorClasses rfl membersT

theorem walkG : WalkG wft :=
  ⟨True.intro, walkRec_of_walkClass _ membersT (walkClass pNode), walkAgree⟩

theorem ctorBound (n : Node) (K σ : Nat → Nat)
    (i : Fin n.a.constructors.length) :
    ∃ (u : Level) (d : HasTyT eFam n.a.family.member.arity []
      (n.a.constructors[i.val]).mtype (.sort u)), LOKt σ 4 K d := by
  rw [familyMember n]
  rcases ctorInfo n i with ⟨e, _⟩ | ⟨e, _⟩
  · rw [e]
    refine ⟨.zero, .const [] 4 [] fam rfl rfl rfl, ?_⟩
    simp [LOKt, LevelsOK]
  · rw [e]
    refine ⟨_, .pi [] field (.imax (.succ .zero) .zero) (.const 4 []) .zero
      (field_typed rfl [])
      (.const [.assumption field] 4 [] fam rfl rfl rfl), ?_⟩
    simp [field_typed, normalField_typed, LOKt, LevelsOK, evalTotal]

kernel_rfl_theorem leafLength : PendAWGroup.ownLength leafAdm = 0
kernel_rfl_theorem nodeLength : PendAWGroup.ownLength nodeAdm = 1
kernel_rfl_theorem nodeAt0Eq :
  (fun K σ : Nat → Nat => PendAWGroup.ownAt K σ nodeAdm 0) =
    (fun K σ => ∃ d : HasTyT eLeaf 0 [] field
      (.sort (.imax (.succ .zero) .zero)), LOKt σ 4 K d)

theorem leafBound (K : Nat → Nat) : PendAWGroup.ownBound K leafAdm := by
  apply PendAWGroup.ownBound_of_at
  intro vs k
  apply PendAWGroup.ownAt_ge
  rw [leafLength]
  exact Nat.zero_le k

theorem nodeBound (K : Nat → Nat) : PendAWGroup.ownBound K nodeAdm := by
  apply PendAWGroup.ownBound_of_at
  intro vs k
  cases k with
  | zero =>
    rw [congrFun (congrFun nodeAt0Eq K) (σOf vs)]
    refine ⟨field_typed rfl [], ?_⟩
    simp [field_typed, normalField_typed, LOKt, LevelsOK, evalTotal]
  | succ k =>
    apply PendAWGroup.ownAt_ge
    rw [nodeLength]
    exact Nat.succ_le_succ (Nat.zero_le k)

theorem walkBound (K : Nat → Nat) : WalkB2 K membersT := by
  unfold membersT checkedCons recMembersT
  repeat rw [walkB2_andRec]
  refine ⟨True.intro, ?_⟩
  repeat rw [walkB2_andRec]
  refine ⟨leafBound K, ?_⟩
  repeat rw [walkB2_andRec]
  refine ⟨nodeBound K, ?_⟩
  repeat rw [walkB2_andRec]
  exact ⟨True.intro, True.intro⟩

theorem boundG (K : Nat → Nat) : BoundG K wft := by
  refine ⟨True.intro, fun n i vs _ _ => ctorBound n K (σOf vs) i,
    walkBound K, fun n _ ha => ?_⟩
  rw [policyPropOnly n] at ha
  cases ha

theorem fieldBound (n : Node) (K σ : Nat → Nat)
    (i : Fin n.a.constructors.length)
    (k : Fin (n.a.constructorViews i).fields.length) :
    ∃ l : Level,
      ∃ d : HasTyT eFam n.a.family.member.arity
        (policyPrefixContext ((n.a.constructorViews i).parameters ++
          (n.a.constructorViews i).fields)
          ((n.a.constructorViews i).parameters.length + k.val))
        ((n.a.constructorViews i).fields[k]) (.sort l), LOKt σ 4 K d := by
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
        ((n.a.constructorViews i).parameters.length + 0) = [] := by
      rw [hp, hf]
      rfl
    have hfield : (n.a.constructorViews i).fields[0]'hk = field := by
      simp only [hf, List.getElem_cons_zero]
    change ∃ l : Level,
      ∃ d : HasTyT eFam n.a.family.member.arity
        (policyPrefixContext ((n.a.constructorViews i).parameters ++
          (n.a.constructorViews i).fields)
          ((n.a.constructorViews i).parameters.length + 0))
        ((n.a.constructorViews i).fields[0]'hk) (.sort l), LOKt σ 4 K d
    rw [familyArity n, hΓ, hfield]
    refine ⟨.imax (.succ .zero) .zero, field_typed rfl [], ?_⟩
    simp [field_typed, normalField_typed, LOKt, LevelsOK, evalTotal]

theorem boundDG (K : Nat → Nat) : BoundDG K wft :=
  ⟨True.intro, fun n i vs _ _ k => fieldBound n K (σOf vs) i k⟩

def Witness : Prop :=
  FamilyBetaPropTree.Witness ∧ WalkG wft ∧
    (∀ n : Node, WalkAgree (AgreeAt n.a.family.parameters.length) membersT) ∧
    (∀ K : Nat → Nat, BoundG K wft ∧ BoundDG K wft)

theorem component_witness : Witness :=
  ⟨FamilyBetaPropTree.component_witness, walkG, walkAgree, fun K => ⟨boundG K, boundDG K⟩⟩

theorem component_nonrefutable : ¬ (Witness → False) :=
  fun h => h component_witness

end Rcic.F3.PSet.FamilyBetaPropTreeBounds

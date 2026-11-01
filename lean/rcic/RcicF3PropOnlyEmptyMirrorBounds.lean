import rcic.RcicF3PropOnlyEmptyMirrorFixture
import rcic.RcicF3PendAWGroup
import rcic.RcicF3DBoundDefs
import rcic.RcicF3AndFixture

/-!
# Original bounds for the empty-field mirror fixture

The two constructor instance bounds are zero. The recursor's instance
bound is three. The argument is checked at every original RecNode, not
only at the explicit witness from the fixture. Every selected constructor
has no fields, so BoundDG's original field obligation is empty.

This auxiliary example concerns a proposed universal parameter-fit lemma;
the original PropOnly invariant is not being refuted. The fixture lies in
the already covered AllPlain case. Source-only draft; root owns native
validation. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Rcic.F3.PSet.PropOnlyEmptyMirrorBounds
open Rcic.Declarative Rcic.Declarative.PropOnlyEmptyMirror

abbrev Node := RecNode emptyEnv eAll 4 7 recMem
def bound (r : Nat) : Nat := if r = 5 ∨ r = 6 then 0 else 3

theorem familyMember (n : Node) : n.a.family.member = fam :=
  Option.some.inj ((node_fam_member n).symm.trans rfl)

theorem recursorHead : ∃ B : Expr Nat, recMem.mtype = .pi (.sort .zero) B :=
  ⟨_, rfl⟩

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

theorem familyArity (n : Node) : n.a.family.member.arity = 1 :=
  congrArg (fun m : CheckedMember => m.arity) (familyMember n)

theorem ctorCount (n : Node) : n.a.constructors.length = 2 :=
  node_ctors_length (ctors := [(5, leaf), (6, leaf)]) n rfl

theorem policyPropOnly (n : Node) : n.a.policy = .propOnly :=
  (n.a.uniformProp_many (fun σ => by rw [(familyInfo n).2.2]; rfl)
    (by rw [ctorCount n]; decide)).1

theorem ctorMember (n : Node) (i : Fin n.a.constructors.length) :
    n.a.constructors[i.val] = leaf := by
  obtain ⟨k, hk⟩ := i
  have hm := node_ctor_member n ⟨k, hk⟩
  have hi : k < 2 := (ctorCount n) ▸ hk
  match k, hk, hi, hm with
  | 0, _, _, h => exact Option.some.inj (h.symm.trans rfl)
  | 1, _, _, h => exact Option.some.inj (h.symm.trans rfl)

theorem views (n : Node) (i : Fin n.a.constructors.length) :
    (n.a.constructorViews i).parameters = [ownParam] ∧
    (n.a.constructorViews i).fields = [] ∧
    (n.a.constructorViews i).resultIndices = [] := by
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
  have hm : (n.a.constructors[i.val]).mtype =
      policyPi [ownParam] (famApp (.bvar 0)) := by rw [ctorMember n i]; rfl
  have hsp := (policyPi_split_eq _ _ _ _
    (fun _ _ h => Expr.noConfusion h) hne (hm.symm.trans hst)).1
  obtain ⟨hp, hf⟩ := List.append_inj
    (show ([ownParam] : List (Expr Nat)) ++ [] = _ from hsp)
    (by rw [hpl]; rfl)
  exact ⟨hp.symm, hf.symm, hri⟩

theorem sigma_zero (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ 0) :
    σOf vs 0 = 0 := by
  cases vs with
  | nil => rfl
  | cons v vs =>
      change v = 0
      exact Nat.eq_zero_of_le_zero (hvs v (List.mem_cons_self _ _))

theorem ownParam_bound (E : ResolvedEnv) (Γ : LCtx) (σ : Nat → Nat)
    (hσ : σ 0 = 0) : LOKt σ 4 bound (ownParam_typed E Γ) := by
  simp [ownParam_typed, domLevel, argLevel, ul, LOKt, evalTotal, hσ]

theorem leaf_bound {E : ResolvedEnv} (hF : E.members 4 = some fam)
    (σ : Nat → Nat) (hσ : σ 0 = 0) :
    LOKt σ 4 bound (leaf_type_typed hF) := by
  simp [leaf_type_typed, ownParam_typed, famApp_typed, parameter_typed,
    ownParam_beta, domLevel, argLevel, ul, LOKt, LOKc, LevelsOK, evalTotal, hσ,
    bound]

theorem ctorBound (n : Node) (i : Fin n.a.constructors.length)
    (vs : List Nat) (_hlen : vs.length = n.a.family.member.arity)
    (hvs : ∀ v, v ∈ vs → v ≤ bound (4 + 1 + i.val)) :
    ∃ (u : Level) (d : HasTyT eFam n.a.family.member.arity []
      (n.a.constructors[i.val]).mtype (.sort u)), LOKt (σOf vs) 4 bound d := by
  have hi : i.val < 2 := (ctorCount n) ▸ i.isLt
  have hc : 4 + 1 + i.val = 5 ∨ 4 + 1 + i.val = 6 := by omega
  have hz : ∀ v, v ∈ vs → v ≤ 0 := by
    intro v hv
    simpa only [bound, if_pos hc] using hvs v hv
  rw [familyMember n, ctorMember n i]
  exact ⟨_, leaf_type_typed rfl, leaf_bound rfl (σOf vs) (sigma_zero vs hz)⟩

theorem leafBound : PendAWGroup.ownBound bound leafAdm := by
  intro vs _hlen hvs ⟨k, hk⟩
  have hk0 : k = 0 := by change k < 1 at hk; omega
  subst k
  refine ⟨ownParam_typed eFam [], ownParam_bound eFam [] (σOf vs) ?_⟩
  apply sigma_zero
  intro v hv
  simpa only [bound, if_pos (show 5 = 5 ∨ 5 = 6 from Or.inl rfl)] using hvs v hv

theorem leaf2Bound : PendAWGroup.ownBound bound leaf2Adm := by
  intro vs _hlen hvs ⟨k, hk⟩
  have hk0 : k = 0 := by change k < 1 at hk; omega
  subst k
  refine ⟨ownParam_typed eLeaf [], ownParam_bound eLeaf [] (σOf vs) ?_⟩
  apply sigma_zero
  intro v hv
  simpa only [bound, if_pos (show 6 = 5 ∨ 6 = 6 from Or.inr rfl)] using hvs v hv

theorem walkBound : WalkB2 bound membersT := by
  unfold membersT
  repeat rw [walkB2_andRec]
  refine ⟨True.intro, ?_⟩
  repeat rw [walkB2_andRec]
  refine ⟨leafBound, ?_⟩
  repeat rw [walkB2_andRec]
  refine ⟨leaf2Bound, ?_⟩
  repeat rw [walkB2_andRec]
  exact ⟨True.intro, True.intro⟩

theorem boundG : BoundG bound envWfT := by
  refine ⟨True.intro, ctorBound, walkBound, fun n _ ha => ?_⟩
  rw [policyPropOnly n] at ha
  cases ha

theorem boundDG : BoundDG bound envWfT := by
  refine ⟨True.intro, fun n i _vs _hlen _hvs k => ?_⟩
  have hz : (n.a.constructorViews i).fields.length = 0 :=
    congrArg List.length (views n i).2.1
  have hk : k.val < 0 := Eq.mp (congrArg (fun z => k.val < z) hz) k.isLt
  exact (Nat.not_lt_zero k.val hk).elim

theorem high_instance : [3].length = pNode.a.family.member.arity ∧
    (∀ v, v ∈ ([3] : List Nat) → v ≤ bound 7) := by
  refine ⟨rfl, ?_⟩
  intro v hv
  cases List.mem_singleton.mp hv
  decide

def Witness : Prop :=
  Nonempty (EnvWfT eAll) ∧ BoundG bound envWfT ∧ BoundDG bound envWfT ∧
  pNode.a.policy = .propOnly ∧
  (∀ i, (pNode.a.constructorViews i).fields = []) ∧
  [3].length = pNode.a.family.member.arity ∧
  (∀ v, v ∈ ([3] : List Nat) → v ≤ bound 7)

theorem original_bounds_witness : Witness :=
  ⟨⟨envWfT⟩, boundG, boundDG, rfl, (fun i => (views pNode i).2.1),
    high_instance.1, high_instance.2⟩

end Rcic.F3.PSet.PropOnlyEmptyMirrorBounds

#print axioms Rcic.F3.PSet.PropOnlyEmptyMirrorBounds.boundG
#print axioms Rcic.F3.PSet.PropOnlyEmptyMirrorBounds.boundDG
#print axioms Rcic.F3.PSet.PropOnlyEmptyMirrorBounds.original_bounds_witness

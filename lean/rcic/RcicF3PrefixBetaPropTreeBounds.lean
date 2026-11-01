import rcic.RcicF3PrefixBetaPropTreeFixture
import rcic.RcicF3UnequalPropTreeBounds
import rcic.RcicF3UnequalPropTreeShape

/-!
# Original bounds for the local-parameter beta tree

The all-RecNode literal views are obtained from the shared shape extractor,
also used by the old unequal tree. The unchanged leaf bound is reused.
The new field's source typing is bounded at K=2 in its actual own context.
No constructor/recursor rebound or narrowed node quantifier is introduced.
Source draft; root owns native validation. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Rcic.F3.PSet.PrefixBetaPropTreeBounds
open Rcic.Declarative Rcic.Declarative.PrefixBetaPropTree
open Rcic.Declarative.UnequalPropTree (ownParam fam famApp leaf eFam eLeaf
  leafAdm ownParam_typed ownParam_beta parameter_typed famApp_typed leaf_type_typed)

abbrev Node := RecNode emptyEnv eAll 4 7 recMem
abbrev bound : Nat → Nat := UnequalPropTreeBounds.bound
noncomputable abbrev wft := envWfT

theorem recursorHead : ∃ B : Expr Nat, recMem.mtype = .pi (.sort .zero) B := ⟨_, rfl⟩
theorem familyMember (n : Node) : n.a.family.member = fam :=
  UnequalPropTreeShape.familyMember n
theorem familyInfo (n : Node) :
    n.a.family.parameters = [.sort .zero] ∧ n.a.family.indices = [] ∧
      n.a.family.resultLevel = .zero :=
  UnequalPropTreeShape.familyInfo recursorHead n
theorem familyArity (n : Node) : n.a.family.member.arity = 0 :=
  UnequalPropTreeShape.familyArity n
theorem ctorCount (n : Node) : n.a.constructors.length = 2 :=
  UnequalPropTreeShape.ctorCount n
theorem policyPropOnly (n : Node) : n.a.policy = .propOnly :=
  UnequalPropTreeShape.policyPropOnly recursorHead n
theorem views (n : Node) (i : Fin n.a.constructors.length) :
    (n.a.constructorViews i).parameters = [ownParam] ∧
    (n.a.constructorViews i).resultIndices = [] ∧
    (((n.a.constructorViews i).fields = [] ∧ i.val = 0) ∨
      ((n.a.constructorViews i).fields = [field] ∧ i.val = 1)) :=
  UnequalPropTreeShape.views recursorHead n i

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
theorem walkG : WalkG wft :=
  ⟨True.intro, walkRec_of_walkClass _ membersT (walkClass pNode), walkAgree⟩

theorem ctorBound (n : Node) (σ : Nat → Nat) (i : Fin n.a.constructors.length) :
    ∃ u : Level, ∃ d : HasTyT eFam n.a.family.member.arity []
      (n.a.constructors[i.val]).mtype (.sort u), LOKt σ 4 bound d := by
  apply UnequalPropTreeShape.ctorBound n bound σ ?_ ?_ i
  · refine ⟨_, leaf_type_typed rfl, ?_⟩
    simp [leaf_type_typed, ownParam_typed, famApp_typed, parameter_typed,
      ownParam_beta, LOKt, LOKc, LevelsOK, evalTotal]
  · refine ⟨_, node_type_typed rfl, ?_⟩
    simp [node_type_typed, field_typed, ownParam_typed, famApp_typed,
      parameter_typed, ownParam_beta, LOKt, LOKc, LevelsOK, evalTotal]

kernel_rfl_theorem nodeLength : PendAWGroup.ownLength nodeAdm = 2
kernel_rfl_theorem nodeAt0Eq :
  (fun K σ : Nat → Nat => PendAWGroup.ownAt K σ nodeAdm 0) =
    (fun K σ => ∃ d : HasTyT eLeaf 0 [] ownParam
      (.sort (.succ .zero)), LOKt σ 4 K d)
kernel_rfl_theorem nodeAt1Eq :
  (fun K σ : Nat → Nat => PendAWGroup.ownAt K σ nodeAdm 1) =
    (fun K σ => ∃ d : HasTyT eLeaf 0 [.assumption ownParam] field
      (.sort (.imax (.succ .zero) .zero)), LOKt σ 4 K d)

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
  refine ⟨UnequalPropTreeBounds.leafBound, ?_⟩
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
  apply UnequalPropTreeShape.fieldBound recursorHead n bound σ ?_ i k
  refine ⟨.imax (.succ .zero) .zero, field_typed rfl, ?_⟩
  simp [field_typed, famApp_typed, parameter_typed, ownParam_beta,
    LOKt, LOKc, LevelsOK, evalTotal]

theorem boundDG : BoundDG bound wft :=
  ⟨True.intro, fun n i vs _ _ k => fieldBound n (σOf vs) i k⟩

end Rcic.F3.PSet.PrefixBetaPropTreeBounds

#print axioms Rcic.F3.PSet.PrefixBetaPropTreeBounds.boundG
#print axioms Rcic.F3.PSet.PrefixBetaPropTreeBounds.boundDG

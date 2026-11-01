import rcic.RcicF3UnequalPropTreeBounds
import rcic.RcicF3PointwiseRemainingPropOnly

/-!
# A separating admitted SourceNormalized group with unequal mirrors

The actual family parameter telescope is [Prop]. Both constructors store
the nonliteral beta-expanded own parameter telescope [ownParam], with an
explicit typed beta equality. The leaf has no fields, and the node has the
literal recursive-1 field Prop → F p. The actual source/cache equality
therefore holds at every successful admitted fuel without any parameter
mirror premise.

The original BoundG/BoundDG are paid at the concrete bound K = 2. The
SourceNormalized producer gives original GInv directly, while AllPlain,
DirectCycle and MatchingParameters are all refuted on this same group.
Source-only draft; root owns native validation. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwiseUnequalPropTree
open Rcic.Declarative Rcic.Declarative.UnequalPropTree
open UnequalPropTreeBounds (Node wft bound ctorClasses)

noncomputable def plan : EvalPlan.Plan :=
  EvalPlan.ofGroup EnvWfT.empty (f := 4) (fm := fam)
    (ctors := [(5, leaf), (6, node)]) (rr := 7) (rm := recMem)
    rfl ctorClasses rfl membersT

theorem uniform_prop : UniformProp plan.node.a.family.resultLevel := by
  intro σ
  rw [(UnequalPropTreeBounds.familyInfo plan.node).2.2]
  rfl

theorem leaf_fields (n : Node) :
    (n.a.constructorViews ⟨0, by rw [UnequalPropTreeBounds.ctorCount n]; decide⟩).fields =
      [] := by
  rcases (UnequalPropTreeBounds.views n
    ⟨0, by rw [UnequalPropTreeBounds.ctorCount n]; decide⟩).2.2 with ⟨h, _⟩ | ⟨_, h⟩
  · exact h
  · cases h

theorem recursive_fields (n : Node) :
    (n.a.constructorViews ⟨1, by rw [UnequalPropTreeBounds.ctorCount n]; decide⟩).fields =
      [field] := by
  rcases (UnequalPropTreeBounds.views n
    ⟨1, by rw [UnequalPropTreeBounds.ctorCount n]; decide⟩).2.2 with ⟨_, h⟩ | ⟨h, _⟩
  · cases h
  · exact h

theorem source_normalized (n : Node) :
    PointwisePropOnlyNormalizedFields.SourceNormalized n := by
  intro j
  apply PointwisePropOnlyNormalizedFields.canonical_fields
    ((EvalPlan.ofNode n).constructors j).fields
    (transparentBody_family n.a.family (canonL n.a.family.member.arity))
  intro A hA
  change A ∈ (n.a.constructorViews j).fields at hA
  change ∃ ds args : List (Expr Nat),
    A = policyPi ds (foldApps (.const n.a.family.ref
      (canonL n.a.family.member.arity)) args)
  rcases (UnequalPropTreeBounds.views n j).2.2 with ⟨hfields, _⟩ | ⟨hfields, _⟩
  · rw [hfields] at hA
    exact (List.not_mem_nil A hA).elim
  · rw [hfields] at hA
    have he : A = field := List.mem_singleton.mp hA
    rw [he]
    refine ⟨[.sort .zero], [.bvar 1], ?_⟩
    rw [n.fam, UnequalPropTreeBounds.familyArity n]
    rfl

theorem family_parameters_nonempty (n : Node) : n.a.family.parameters ≠ [] := by
  rw [(UnequalPropTreeBounds.familyInfo n).1]
  exact List.cons_ne_nil _ _

theorem unequal_parameters (n : Node) (j : Fin n.a.constructors.length) :
    (n.a.constructorViews j).parameters ≠ n.a.family.parameters := by
  intro he
  rw [(UnequalPropTreeBounds.views n j).1,
    (UnequalPropTreeBounds.familyInfo n).1] at he
  exact Expr.noConfusion (List.cons.inj he).1

theorem not_matching_parameters (n : Node) :
    ¬ PointwiseRemainingPropOnly.MatchingParameters n := by
  intro h
  let j : Fin n.a.constructors.length :=
    ⟨0, by rw [UnequalPropTreeBounds.ctorCount n]; decide⟩
  exact unequal_parameters n j (h j)

theorem not_all_plain (n : Node) : ¬ PropShapeCoverage.AllPlain n := by
  intro hplain
  have hf := PropShapeCoverage.all_plain_fields_free hplain
    ⟨1, by rw [UnequalPropTreeBounds.ctorCount n]; decide⟩ field
    (by rw [recursive_fields n]; exact List.mem_singleton_self _)
  rw [n.fam] at hf
  change true = false at hf
  cases hf

theorem not_direct_cycle (n : Node) : ¬ PropShapeCoverage.DirectCycle n := by
  intro hcycle
  let j : Fin n.a.constructors.length :=
    ⟨0, by rw [UnequalPropTreeBounds.ctorCount n]; decide⟩
  have hf : (n.a.constructorViews j).fields = [] := leaf_fields n
  have hl := Rcic.F3.PSet.fieldShapesFuel_length n.E0 (n.h14.fuelAt j)
    n.a.family.ref n.a.family.member.arity n.a.family.parameters.length
    n.a.family.indices.length (n.a.constructorViews j).fields
    n.a.family.parameters.length (n.h14.shapesAt j) (n.h14.analyzed j)
  rw [hf] at hl
  have hs : n.h14.shapesAt j = [] := List.eq_nil_of_length_eq_zero hl
  have hc := hcycle j
  rw [hs] at hc
  exact List.not_mem_nil _ hc

/-- This same admitted group is outside all three previously produced
routes named in the separation target. -/
theorem outside_previous_routes :
    ¬ (PointwiseRemainingRefined.PropOnlyCovered EnvWfT.empty
        (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
        (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT ∨
      PointwiseRemainingPropOnly.MatchingParameters plan.node) := by
  intro h
  rcases h with hshape | hmatch
  · rcases hshape with hplain | hcycle
    · exact not_all_plain plan.node hplain
    · exact not_direct_cycle plan.node hcycle
  · exact not_matching_parameters plan.node hmatch

theorem covered :
    PointwiseRemainingPropOnly.Covered EnvWfT.empty
      (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
      (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT :=
  Or.inr (Or.inl (source_normalized plan.node))

/-- Original source-normalized producer, actual original bounds, actual
empty predecessor; no matching-parameter/check fallback is called. -/
theorem invariant (P : Premises4) : PointwiseRole.GInv P bound wft :=
  PointwisePropOnlyNormalizedGroup.invariant_step P bound EnvWfT.empty
    (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
    (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT
    uniform_prop (UnequalPropTreeBounds.policyPropOnly plan.node)
    (source_normalized plan.node) UnequalPropTreeBounds.boundG
    UnequalPropTreeBounds.boundDG (PointwiseRole.gInv_empty P bound)

theorem env_sound (P : Premises4) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (PointwiseRole.table P wft)) σ bound eAll n :=
  PointwiseRole.envSound_of_gInv P bound wft (invariant P) σ n

def Witness (P : Premises4) : Prop :=
  UnequalPropTreeBounds.Witness ∧
  (∀ n : Node, PointwisePropOnlyNormalizedFields.SourceNormalized n ∧
    n.a.family.parameters ≠ [] ∧
    ¬ PointwiseRemainingPropOnly.MatchingParameters n ∧
    ¬ PropShapeCoverage.AllPlain n ∧ ¬ PropShapeCoverage.DirectCycle n) ∧
  PointwiseRole.GInv P bound wft

theorem component_witness (P : Premises4) : Witness P :=
  ⟨UnequalPropTreeBounds.component_witness,
    fun n => ⟨source_normalized n, family_parameters_nonempty n,
      not_matching_parameters n, not_all_plain n, not_direct_cycle n⟩,
    invariant P⟩

end Rcic.F3.PSet.PointwiseUnequalPropTree

#print axioms Rcic.F3.PSet.PointwiseUnequalPropTree.source_normalized
#print axioms Rcic.F3.PSet.PointwiseUnequalPropTree.outside_previous_routes
#print axioms Rcic.F3.PSet.PointwiseUnequalPropTree.invariant
#print axioms Rcic.F3.PSet.PointwiseUnequalPropTree.component_witness

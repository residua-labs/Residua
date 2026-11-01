import rcic.RcicF3PointwiseRemainingPropOnly
import rcic.RcicF3PointwisePropTree

/-!
# Strict admitted extension beyond AllPlain and DirectCycle

The existing PropTree group contains an actual leaf and an actual
positive-depth recursive constructor, node : (Prop → F) → F. Its original
admission, inhabited branch, BoundG and BoundDG are retained. The syntax
guard is proved by comparing every successful cached reader with the
literal source telescope; the admission-produced cache is not reduced.

The new source-normalized producer is called directly to produce the
original PointwiseRole.GInv for this group at every K. The empty leaf row
refutes DirectCycle, and the actual recursive source field refutes
AllPlain. This witnesses strict enlargement of the previous covered
subset, without claiming general PropOnly closure. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwisePropOnlyNormalizedTree
open Rcic.Declarative
open Rcic.Declarative.PropTree
open PropTreeBounds (Node wft ctorClasses)
open NormPropTree (plan uniform_prop)

theorem leaf_fields (n : Node) :
    (n.a.constructorViews ⟨0, by rw [PropTreeBounds.ctorCount n]; decide⟩).fields = [] := by
  rcases (PropTreeBounds.views n
    ⟨0, by rw [PropTreeBounds.ctorCount n]; decide⟩).2.2 with ⟨h, _⟩ | ⟨_, h⟩
  · exact h
  · cases h

theorem recursive_fields (n : Node) :
    (n.a.constructorViews ⟨1, by rw [PropTreeBounds.ctorCount n]; decide⟩).fields =
      [field] := by
  rcases (PropTreeBounds.views n
    ⟨1, by rw [PropTreeBounds.ctorCount n]; decide⟩).2.2 with ⟨_, h⟩ | ⟨h, _⟩
  · cases h
  · exact h

/-- The actual source is a literal family-headed Pi telescope, so every
cache for this admitted node reconstructs it exactly at its own fuel. -/
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
  rcases (PropTreeBounds.views n j).2.2 with ⟨hfields, _⟩ | ⟨hfields, _⟩
  · rw [hfields] at hA
    exact (List.not_mem_nil A hA).elim
  · rw [hfields] at hA
    have he : A = field := List.mem_singleton.mp hA
    rw [he]
    refine ⟨[.sort .zero], [], ?_⟩
    rw [n.fam, PropTreeBounds.familyArity n]
    rfl

/-- Family occurrence in the actual recursive source refutes AllPlain. -/
theorem not_all_plain (n : Node) : ¬ PropShapeCoverage.AllPlain n := by
  intro hplain
  have hf := PropShapeCoverage.all_plain_fields_free hplain
    ⟨1, by rw [PropTreeBounds.ctorCount n]; decide⟩ field
    (by rw [recursive_fields n]; exact List.mem_singleton_self _)
  rw [n.fam] at hf
  change true = false at hf
  cases hf

/-- The actual leaf row has no fields and therefore no recursive shape. -/
theorem not_direct_cycle (n : Node) : ¬ PropShapeCoverage.DirectCycle n := by
  intro hcycle
  let j : Fin n.a.constructors.length :=
    ⟨0, by rw [PropTreeBounds.ctorCount n]; decide⟩
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

theorem outside_old_coverage :
    ¬ PointwiseRemainingRefined.PropOnlyCovered EnvWfT.empty
      (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
      (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT := by
  intro h
  rcases h with hplain | hcycle
  · exact not_all_plain plan.node hplain
  · exact not_direct_cycle plan.node hcycle

theorem covered :
    PointwiseRemainingPropOnly.Covered EnvWfT.empty
      (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
      (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT :=
  Or.inr (Or.inl (source_normalized plan.node))

/-- Both original bound packages and the actual empty predecessor are
paid. This application uses the new source-normalized producer directly. -/
theorem invariant (P : Premises4) (K : Nat → Nat) :
    PointwiseRole.GInv P K wft :=
  PointwisePropOnlyNormalizedGroup.invariant_step P K EnvWfT.empty
    (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
    (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT
    uniform_prop (PropTreeBounds.policyPropOnly plan.node)
    (source_normalized plan.node) (PropTreeBounds.boundG K)
    (PropTreeBounds.boundDG K) (PointwiseRole.gInv_empty P K)

theorem env_sound (P : Premises4) (K σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (PointwiseRole.table P wft)) σ K eAll n :=
  PointwiseRole.envSound_of_gInv P K wft (invariant P K) σ n

/-- Same actual admission and inhabited branch, a proved syntax guard,
strict exclusion from the previous subset, and the produced original GInv. -/
def Witness (P : Premises4) : Prop :=
  PropTreeBounds.Witness ∧
  PointwisePropOnlyNormalizedFields.SourceNormalized plan.node ∧
  ¬ PropShapeCoverage.AllPlain plan.node ∧
  ¬ PropShapeCoverage.DirectCycle plan.node ∧
  (∀ K : Nat → Nat, PointwiseRole.GInv P K wft)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨PropTreeBounds.component_witness, source_normalized plan.node,
    not_all_plain plan.node, not_direct_cycle plan.node, invariant P⟩

end Rcic.F3.PSet.PointwisePropOnlyNormalizedTree

#print axioms Rcic.F3.PSet.PointwisePropOnlyNormalizedTree.source_normalized
#print axioms Rcic.F3.PSet.PointwisePropOnlyNormalizedTree.outside_old_coverage
#print axioms Rcic.F3.PSet.PointwisePropOnlyNormalizedTree.invariant
#print axioms Rcic.F3.PSet.PointwisePropOnlyNormalizedTree.component_witness

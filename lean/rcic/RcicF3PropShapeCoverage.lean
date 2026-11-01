import rcic.RcicF3PointwisePropPlainGroup
import rcic.RcicF3StepDGRec

/-!
# Exhaustive shape classification on the admitted Prop/anySort face

The original policy selection admits at most one constructor. Its stored
descriptor therefore has a positive-depth recursive field, has only plain
fields, or contains a direct recursive field in every constructor row.

The plain alternative produces the original syntactic family-freedom
premise directly from admission. No new equality of semantic invariants,
checker-completeness premise, normalization assumption or altered bound is
introduced. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PropShapeCoverage
open Rcic.Declarative Rcic.Model.PS

def AllPlain {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Prop :=
  ∀ j s, s ∈ node.h14.shapesAt j → s = .nonrecursive

def DirectCycle {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Prop :=
  ∀ j, FieldShape.recursive 0 ∈ node.h14.shapesAt j

theorem all_plain_noFun {E E' : ResolvedEnv} {f rr : Nat}
    {rm : CheckedMember} {node : RecNode E E' f rr rm}
    (hplain : AllPlain node) : NoFunRec node :=
  fun j s hs => Or.inl (hplain j s hs)

/-- The admission analysis inspects the original field syntax in its
nonrecursive branch. In particular, beta-erased family occurrences cannot
create an admitted plain row while falsifying this conclusion. -/
theorem all_plain_fields_free {E E' : ResolvedEnv} {f rr : Nat}
    {rm : CheckedMember} {node : RecNode E E' f rr rm}
    (hplain : AllPlain node) :
    ∀ (j : Fin node.a.constructors.length) A,
      A ∈ (node.a.constructorViews j).fields →
      occursConst node.a.family.ref A = false := by
  intro j A hA
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hA
  have hlen := fieldShapesFuel_length _ _ _ _ _ _ _ _ _
    (node.h14.analyzed j)
  have hkF : k < (node.a.constructorViews j).fields.length :=
    (List.getElem?_eq_some_iff.mp hk).1
  have hkS : k < (node.h14.shapesAt j).length := by omega
  have hs : (node.h14.shapesAt j)[k]? =
      some ((node.h14.shapesAt j)[k]'hkS) :=
    List.getElem?_eq_getElem hkS
  have hp : (node.h14.shapesAt j)[k]'hkS = .nonrecursive :=
    hplain j _ (List.getElem?_mem hs)
  rw [hp] at hs
  exact shapes_nonrec_free _ _ _ _ _ _ _ _ _
    (node.h14.analyzed j) k A hs hk

/-- At most one constructor turns the presence of a direct recursive
field in any row into its presence in every row. The empty constructor
case is already covered by AllPlain. -/
theorem classify (P : Premises4) {E E' : ResolvedEnv} {f rr : Nat}
    {rm : CheckedMember} (node : RecNode E E' f rr rm)
    (hsmall : node.a.constructors.length ≤ 1) :
    PendA node ∨ AllPlain node ∨ DirectCycle node := by
  cases P.dec (PendA node) with
  | isTrue hA => exact Or.inl hA
  | isFalse hA =>
      have hN := Rcic.F3.StepDGOrder.noFunRec_of_not_pendA hA
      right
      cases P.dec (AllPlain node) with
      | isTrue hplain => exact Or.inl hplain
      | isFalse hplain =>
          right
          intro j
          cases P.dec (FieldShape.recursive 0 ∈ node.h14.shapesAt j) with
          | isTrue hrec => exact hrec
          | isFalse hrec =>
              apply False.elim (hplain ?_)
              intro i s hs
              have hij : i = j := Fin.ext (by
                have hi := i.isLt
                have hj := j.isLt
                omega)
              rw [hij] at hs
              rcases hN j s hs with h | h
              · exact h
              · rw [h] at hs
                exact False.elim (hrec hs)

/-- The original admission policy supplies the singleton premise; the
classification requires neither a successful D check nor a rebound. -/
theorem classify_anySortProp (P : Premises4)
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm)
    (hProp : UniformProp node.a.family.resultLevel)
    (hpolicy : node.a.policy = .anySort) :
    PendA node ∨ AllPlain node ∨ DirectCycle node :=
  classify P node (selection_prop node.a (fun _ => 0) (hProp _) hpolicy).2

/-- The recorded plain shape face consumes the existing checked plain
group proof with its original semantic and syntactic statements intact. -/
theorem plain_group_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hProp : UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy :
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .anySort)
    (hplain : AllPlain (EvalPlan.ofGroup hE hfam hctors hrec hmem).node) :
    PointwiseDataGroup.GroupStepAt P K hE hfam hctors hrec hmem :=
  PointwisePropPlainGroup.group_step P K hE hfam hctors hrec hmem
    hProp hpolicy (all_plain_noFun hplain) (all_plain_fields_free hplain)

#print axioms all_plain_fields_free
#print axioms classify_anySortProp
#print axioms plain_group_step

end Rcic.F3.PSet.PropShapeCoverage

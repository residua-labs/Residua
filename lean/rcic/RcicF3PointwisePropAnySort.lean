import rcic.RcicF3PointwisePropCycleGroup
import rcic.RcicF3PropShapeCoverage
import rcic.RcicF3PointwisePropGroup

/-!
# Every admitted original-bound Prop/anySort group is produced

Admission supplies the complete shape classification: a functional
recursive field uses the existing PendA producer, plain fields use the
existing original-bound plain producer, and direct cycles use the new
finite-evaluation contradiction. These alternatives cover every admitted
uniformly Prop/anySort group at its actual pointwise table.

Both original bounds and the predecessor invariant retain their literal
types. The invariant_step theorem also produces walk agreement from the
uniform Prop family at every admission node, so it needs no W or D check.
No scope restriction, checked-coverage conjecture, revised invariant, or
extra semantic callback is present. The original whole-tier root still
requires its other group classes. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwisePropAnySort
open Rcic.Declarative Rcic.Model.PS Rcic.F3.StepWMin Rcic.Syn.FamApp.StepW

theorem group_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hProp : UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .anySort) :
    PointwiseDataGroup.GroupStepAt P K hE hfam hctors hrec hmem := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  rcases PropShapeCoverage.classify_anySortProp P p.node hProp hpolicy with
    hA | hplain | hcycles
  · exact PointwisePropGroup.group_step P K hE hfam hctors hrec hmem
      hProp hpolicy ⟨p.node, hA⟩
  · exact PropShapeCoverage.plain_group_step P K hE hfam hctors hrec hmem
      hProp hpolicy hplain
  · exact PointwisePropCycleGroup.group_step P K hE hfam hctors hrec hmem
      hProp hpolicy hcycles

theorem invariant_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hProp : UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .anySort)
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  apply group_step P K hE hfam hctors hrec hmem hProp hpolicy ?_ hB hD hPred
  intro node
  have hp : UniformProp node.a.family.resultLevel := by
    rw [Rcic.F3.StepWGroup.nodeResult_unique node p.node]
    exact hProp
  exact stepW_of_uniformProp hE hfam hctors hrec hmem node (walkRec_of_group hmem) hp

end Rcic.F3.PSet.PointwisePropAnySort

#print axioms Rcic.F3.PSet.PointwisePropAnySort.group_step
#print axioms Rcic.F3.PSet.PointwisePropAnySort.invariant_step

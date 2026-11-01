import rcic.RcicF3PointwiseRemainingTier
import rcic.RcicF3PointwiseDataFiniteSimple
import rcic.RcicF3PointwisePropOnlyPlain
import rcic.RcicF3PointwisePropOnlyCycle

/-!
# Exact original-root reduction after the produced DATA and PropOnly cases

The DATA residual excludes empty constructor lists and finite families
whose stored header is a sort. The PropOnly residual excludes actual
all-plain descriptors and descriptors with a direct recursive field in
every constructor. Each excluded case calls its complete original-domain
invariant producer below; there is no coverage-completeness assumption.

Premises4.dec makes the exhaustive splits. Both original bound packages,
the original pointwise predecessor, and the literal final kernel root are
unchanged. Only the two explicitly named residual local producers remain
conditional. They are not asserted or hidden behind a checker predicate.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwiseRemainingRefined
open Rcic.Declarative

/-- Concrete DATA shapes with an actual invariant producer. The finite
condition concerns the actual selected admitted descriptor. -/
def DataCovered
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') : Prop :=
  ctors = [] ∨ ∃ u : Level, fm.mtype = .sort u ∧
    NoFunRec (EvalPlan.ofGroup hE hfam hctors hrec hmem).node

/-- These are predicates on the actual admitted descriptor, not supplied
semantic packages or successful W/D checks. -/
def PropOnlyCovered
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') : Prop :=
  PropShapeCoverage.AllPlain (EvalPlan.ofGroup hE hfam hctors hrec hmem).node ∨
    PropShapeCoverage.DirectCycle (EvalPlan.ofGroup hE hfam hctors hrec hmem).node

/-- The genuine DATA residual: the original local step is asked only
outside the concrete produced subset. No checker guard is added. -/
def StepData (P : Premises4) (K : Nat → Nat) : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E'),
    UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel →
    ¬ DataCovered hE hfam hctors hrec hmem →
    BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
    BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
    PointwiseRole.GInv P K hE →
      PointwiseRole.GInv P K
        (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem)

/-- The genuine PropOnly residual outside the two produced descriptor
classes. All original group and semantic premises are retained. -/
def StepPropOnly (P : Premises4) (K : Nat → Nat) : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E'),
    UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel →
    (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly →
    ¬ PropOnlyCovered hE hfam hctors hrec hmem →
    BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
    BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
    PointwiseRole.GInv P K hE →
      PointwiseRole.GInv P K
        (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem)

/-- Every excluded DATA shape has an actual producer under the literal
original bounds and predecessor; in particular its W walk is produced. -/
theorem data_covered_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hCovered : DataCovered hE hfam hctors hrec hmem)
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  rcases hCovered with hempty | ⟨u, hsort, hFinite⟩
  · subst ctors
    exact PointwiseDataFiniteOriginal.invariant_step_empty P K hE hfam hctors hrec hmem
      hType hB hD hPred
  · exact PointwiseDataFiniteSimple.invariant_step P K hE hfam hctors hrec hmem
      hType hFinite u hsort hB hD hPred

/-- Both excluded PropOnly shapes have complete group producers; no
constructor parameter equality or checker acceptance is supplied. -/
theorem propOnly_covered_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hProp : UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly)
    (hCovered : PropOnlyCovered hE hfam hctors hrec hmem)
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  rcases hCovered with hplain | hcycles
  · exact PointwisePropOnlyPlainGroup.invariant_step P K hE hfam hctors hrec hmem
      hProp hpolicy hplain hB hD hPred
  · exact PointwisePropOnlyCycleGroup.invariant_step P K hE hfam hctors hrec hmem
      hProp hpolicy hcycles hB hD hPred

/-- The smaller DATA obligation recovers the complete earlier DATA step
by a split whose positive branch is implemented above. -/
theorem stepData_of_remaining (P : Premises4) (K : Nat → Nat)
    (hData : StepData P K) : PointwiseRemainingTier.StepData P K := by
  intro E E' f rr fm rm ctors hE hfam hctors hrec hmem hType hB hD hPred
  cases P.dec (DataCovered hE hfam hctors hrec hmem) with
  | isTrue hCovered =>
      exact data_covered_step P K hE hfam hctors hrec hmem hType hCovered hB hD hPred
  | isFalse hRemaining =>
      exact hData hE hfam hctors hrec hmem hType hRemaining hB hD hPred

/-- The smaller PropOnly obligation similarly recovers the complete
earlier PropOnly step from the actual two producers. -/
theorem stepPropOnly_of_remaining (P : Premises4) (K : Nat → Nat)
    (hPropOnly : StepPropOnly P K) : PointwiseRemainingTier.StepPropOnly P K := by
  intro E E' f rr fm rm ctors hE hfam hctors hrec hmem hProp hpolicy hB hD hPred
  cases P.dec (PropOnlyCovered hE hfam hctors hrec hmem) with
  | isTrue hCovered =>
      exact propOnly_covered_step P K hE hfam hctors hrec hmem
        hProp hpolicy hCovered hB hD hPred
  | isFalse hRemaining =>
      exact hPropOnly hE hfam hctors hrec hmem hProp hpolicy hRemaining hB hD hPred

theorem invariant_of_remaining (P : Premises4) (K : Nat → Nat)
    (hData : StepData P K) (hPropOnly : StepPropOnly P K)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E) :
    PointwiseRole.GInv P K hW :=
  PointwiseRemainingTier.invariant_of_remaining P K
    (stepData_of_remaining P K hData) (stepPropOnly_of_remaining P K hPropOnly)
    hW hB hD hAx

theorem envSound_of_remaining (P : Premises4) (K : Nat → Nat)
    (hData : StepData P K) (hPropOnly : StepPropOnly P K)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E)
    (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (PointwiseRole.table P hW)) σ K E n :=
  PointwiseRole.envSound_of_gInv P K hW
    (invariant_of_remaining P K hData hPropOnly hW hB hD hAx) σ n

theorem tierF3Uncond_of_remaining
    (hData : ∀ (P : Premises4) (K : Nat → Nat), StepData P K)
    (hPropOnly : ∀ (P : Premises4) (K : Nat → Nat), StepPropOnly P K) :
    Rcic.Apex.TierF3Uncond :=
  PointwiseRemainingTier.tierF3Uncond_of_remaining
    (fun P K => stepData_of_remaining P K (hData P K))
    (fun P K => stepPropOnly_of_remaining P K (hPropOnly P K))

/-- The unchanged original root, conditional only on the two explicitly
remaining producers. This is a refined residual reduction, not closure. -/
theorem kernelSoundnessTierUncond_of_remaining
    (hData : ∀ (P : Premises4) (K : Nat → Nat), StepData P K)
    (hPropOnly : ∀ (P : Premises4) (K : Nat → Nat), StepPropOnly P K) :
    Rcic.Apex.KernelSoundnessTierUncond :=
  PointwiseRemainingTier.kernelSoundnessTierUncond_of_remaining
    (fun P K => stepData_of_remaining P K (hData P K))
    (fun P K => stepPropOnly_of_remaining P K (hPropOnly P K))

end Rcic.F3.PSet.PointwiseRemainingRefined

#print axioms Rcic.F3.PSet.PointwiseRemainingRefined.data_covered_step
#print axioms Rcic.F3.PSet.PointwiseRemainingRefined.propOnly_covered_step
#print axioms Rcic.F3.PSet.PointwiseRemainingRefined.stepData_of_remaining
#print axioms Rcic.F3.PSet.PointwiseRemainingRefined.stepPropOnly_of_remaining
#print axioms Rcic.F3.PSet.PointwiseRemainingRefined.kernelSoundnessTierUncond_of_remaining

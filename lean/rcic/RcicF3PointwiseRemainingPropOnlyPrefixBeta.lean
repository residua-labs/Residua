import rcic.RcicF3PointwisePropOnlyPrefixBeta
import rcic.RcicF3PointwiseRemainingDataSeparated

/-!
# Original-root residue after available-prefix beta reconstruction

The old covered union is retained and the proved SourcePrefixBeta face is
added. The residual requests the same original group invariant only outside
that union. Both original bounds and the predecessor invariant remain.
The unchanged DATA residual is reused. Neither universal residual is
proved here; closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwiseRemainingPropOnlyPrefixBeta
open Rcic.Declarative

def Covered
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') : Prop :=
  PointwiseRemainingPropOnlyFamilyBeta.Covered hE hfam hctors hrec hmem ∨
    ReaderPrefixBeta.SourcePrefixBeta (EvalPlan.ofGroup hE hfam hctors hrec hmem).node

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
    ¬ Covered hE hfam hctors hrec hmem →
    BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
    BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
    PointwiseRole.GInv P K hE →
      PointwiseRole.GInv P K
        (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem)

theorem covered_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hProp : UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly)
    (hCovered : Covered hE hfam hctors hrec hmem)
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  rcases hCovered with hold | hprefix
  · exact PointwiseRemainingPropOnlyFamilyBeta.covered_step P K
      hE hfam hctors hrec hmem hProp hpolicy hold hB hD hPred
  · exact PointwisePropOnlyPrefixBeta.invariant_step P K
      hE hfam hctors hrec hmem hProp hpolicy hprefix hB hD hPred

/-- Exhaustive recovery of the previous residual, using the supplied
decision data. A covered branch is paid by its actual complete producer. -/
theorem stepPropOnly_of_remaining (P : Premises4) (K : Nat → Nat)
    (hPropOnly : StepPropOnly P K) :
    PointwiseRemainingPropOnlyFamilyBeta.StepPropOnly P K := by
  intro E E' f rr fm rm ctors hE hfam hctors hrec hmem hProp hpolicy _hOld hB hD hPred
  cases P.dec (Covered hE hfam hctors hrec hmem) with
  | isTrue hCovered =>
      exact covered_step P K hE hfam hctors hrec hmem
        hProp hpolicy hCovered hB hD hPred
  | isFalse hRemaining =>
      exact hPropOnly hE hfam hctors hrec hmem
        hProp hpolicy hRemaining hB hD hPred

theorem invariant_of_remaining (P : Premises4) (K : Nat → Nat)
    (hData : PointwiseRemainingDataSeparated.StepData P K)
    (hPropOnly : StepPropOnly P K)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E) :
    PointwiseRole.GInv P K hW :=
  PointwiseRemainingDataSeparated.invariant_of_remaining P K hData
    (stepPropOnly_of_remaining P K hPropOnly) hW hB hD hAx

/-- Literal original root; the two universal inputs remain unpaid. -/
theorem kernelSoundnessTierUncond_of_remaining
    (hData : ∀ (P : Premises4) (K : Nat → Nat),
      PointwiseRemainingDataSeparated.StepData P K)
    (hPropOnly : ∀ (P : Premises4) (K : Nat → Nat), StepPropOnly P K) :
    Rcic.Apex.KernelSoundnessTierUncond :=
  PointwiseRemainingDataSeparated.kernelSoundnessTierUncond_of_remaining hData
    (fun P K => stepPropOnly_of_remaining P K (hPropOnly P K))

end Rcic.F3.PSet.PointwiseRemainingPropOnlyPrefixBeta

#print axioms Rcic.F3.PSet.PointwiseRemainingPropOnlyPrefixBeta.covered_step
#print axioms Rcic.F3.PSet.PointwiseRemainingPropOnlyPrefixBeta.stepPropOnly_of_remaining
#print axioms Rcic.F3.PSet.PointwiseRemainingPropOnlyPrefixBeta.kernelSoundnessTierUncond_of_remaining

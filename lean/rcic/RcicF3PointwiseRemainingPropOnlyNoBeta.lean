import rcic.RcicF3PointwiseRemainingPropOnly
import rcic.RcicF3PointwisePropOnlyNoBeta

/-!
# PropOnly residue after the actual beta-free reader face

The new covered branch is the literal ReaderNoBeta.SourceNoBeta syntax
certificate, consumed by its complete original-bound invariant producer.
The earlier AllPlain, DirectCycle, source-equality and matching-parameter
branches remain present. P.dec makes the exhaustive split.

The original DATA residue, bound packages, predecessor invariant and
KernelSoundnessTierUncond conclusion are unchanged. The remaining
PropOnly local producer remains an explicit conditional premise.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwiseRemainingPropOnlyNoBeta
open Rcic.Declarative

/-- This union contains actual syntax cases with complete producers. -/
def Covered
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') : Prop :=
  PointwiseRemainingPropOnly.Covered hE hfam hctors hrec hmem ∨
    ReaderNoBeta.SourceNoBeta (EvalPlan.ofGroup hE hfam hctors hrec hmem).node

/-- The exact original group step is still requested outside the union. -/
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

/-- Each covered case returns the original GInv. -/
theorem covered_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hProp : UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly)
    (hCovered : Covered hE hfam hctors hrec hmem)
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  rcases hCovered with hold | hreadSource
  · exact PointwiseRemainingPropOnly.covered_step P K hE hfam hctors hrec hmem
      hProp hpolicy hold hB hD hPred
  · exact PointwisePropOnlyNoBetaGroup.invariant_step P K hE hfam hctors hrec hmem
      hProp hpolicy hreadSource hB hD hPred

/-- The smaller obligation recovers the previous exact residual. -/
theorem stepPropOnly_of_remaining (P : Premises4) (K : Nat → Nat)
    (hPropOnly : StepPropOnly P K) : PointwiseRemainingPropOnly.StepPropOnly P K := by
  intro E E' f rr fm rm ctors hE hfam hctors hrec hmem hProp hpolicy _hOld hB hD hPred
  cases P.dec (Covered hE hfam hctors hrec hmem) with
  | isTrue hCovered =>
      exact covered_step P K hE hfam hctors hrec hmem
        hProp hpolicy hCovered hB hD hPred
  | isFalse hRemaining =>
      exact hPropOnly hE hfam hctors hrec hmem
        hProp hpolicy hRemaining hB hD hPred

theorem invariant_of_remaining (P : Premises4) (K : Nat → Nat)
    (hData : PointwiseRemainingRefined.StepData P K)
    (hPropOnly : StepPropOnly P K)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E) :
    PointwiseRole.GInv P K hW :=
  PointwiseRemainingPropOnly.invariant_of_remaining P K hData
    (stepPropOnly_of_remaining P K hPropOnly) hW hB hD hAx

theorem envSound_of_remaining (P : Premises4) (K : Nat → Nat)
    (hData : PointwiseRemainingRefined.StepData P K)
    (hPropOnly : StepPropOnly P K)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E)
    (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (PointwiseRole.table P hW)) σ K E n :=
  PointwiseRole.envSound_of_gInv P K hW
    (invariant_of_remaining P K hData hPropOnly hW hB hD hAx) σ n

theorem tierF3Uncond_of_remaining
    (hData : ∀ (P : Premises4) (K : Nat → Nat), PointwiseRemainingRefined.StepData P K)
    (hPropOnly : ∀ (P : Premises4) (K : Nat → Nat), StepPropOnly P K) :
    Rcic.Apex.TierF3Uncond :=
  PointwiseRemainingPropOnly.tierF3Uncond_of_remaining hData
    (fun P K => stepPropOnly_of_remaining P K (hPropOnly P K))

/-- Same original root and DATA residue; only the explicit PropOnly
residue is narrowed by the actual reader-certified invariant producer above. -/
theorem kernelSoundnessTierUncond_of_remaining
    (hData : ∀ (P : Premises4) (K : Nat → Nat), PointwiseRemainingRefined.StepData P K)
    (hPropOnly : ∀ (P : Premises4) (K : Nat → Nat), StepPropOnly P K) :
    Rcic.Apex.KernelSoundnessTierUncond :=
  PointwiseRemainingPropOnly.kernelSoundnessTierUncond_of_remaining hData
    (fun P K => stepPropOnly_of_remaining P K (hPropOnly P K))

end Rcic.F3.PSet.PointwiseRemainingPropOnlyNoBeta

#print axioms Rcic.F3.PSet.PointwiseRemainingPropOnlyNoBeta.covered_step
#print axioms Rcic.F3.PSet.PointwiseRemainingPropOnlyNoBeta.stepPropOnly_of_remaining
#print axioms Rcic.F3.PSet.PointwiseRemainingPropOnlyNoBeta.kernelSoundnessTierUncond_of_remaining

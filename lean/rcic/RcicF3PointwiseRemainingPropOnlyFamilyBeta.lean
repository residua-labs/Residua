import rcic.RcicF3PointwiseRemainingPropOnlyNoBeta
import rcic.RcicF3PointwisePropOnlyFamilyBeta

/-!
# PropOnly residue after the concrete fresh-family beta wrapper face

The new covered branch is the literal per-field SourceFamilyBeta syntax
certificate, consumed by its complete original-bound invariant producer.
All previously covered branches, including SourceNoBeta, remain present.
P.dec makes the exhaustive split.

The original DATA residue, bounds, predecessor GInv and unchanged
KernelSoundnessTierUncond conclusion are retained. The remaining PropOnly
producer is still an explicit conditional premise. The new syntax face
is not claimed to contain every successful beta reader trace.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwiseRemainingPropOnlyFamilyBeta
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
  PointwiseRemainingPropOnlyNoBeta.Covered hE hfam hctors hrec hmem ∨
    PointwisePropOnlyFamilyBetaFields.SourceFamilyBeta (EvalPlan.ofGroup hE hfam hctors hrec hmem).node

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
  · exact PointwiseRemainingPropOnlyNoBeta.covered_step P K hE hfam hctors hrec hmem
      hProp hpolicy hold hB hD hPred
  · exact PointwisePropOnlyFamilyBetaGroup.invariant_step P K hE hfam hctors hrec hmem
      hProp hpolicy hreadSource hB hD hPred

/-- The smaller obligation recovers the previous exact residual. -/
theorem stepPropOnly_of_remaining (P : Premises4) (K : Nat → Nat)
    (hPropOnly : StepPropOnly P K) : PointwiseRemainingPropOnlyNoBeta.StepPropOnly P K := by
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
  PointwiseRemainingPropOnlyNoBeta.invariant_of_remaining P K hData
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
  PointwiseRemainingPropOnlyNoBeta.tierF3Uncond_of_remaining hData
    (fun P K => stepPropOnly_of_remaining P K (hPropOnly P K))

/-- Same original root and DATA residue; only the explicit PropOnly
residue is narrowed by the actual reader-certified invariant producer above. -/
theorem kernelSoundnessTierUncond_of_remaining
    (hData : ∀ (P : Premises4) (K : Nat → Nat), PointwiseRemainingRefined.StepData P K)
    (hPropOnly : ∀ (P : Premises4) (K : Nat → Nat), StepPropOnly P K) :
    Rcic.Apex.KernelSoundnessTierUncond :=
  PointwiseRemainingPropOnlyNoBeta.kernelSoundnessTierUncond_of_remaining hData
    (fun P K => stepPropOnly_of_remaining P K (hPropOnly P K))

end Rcic.F3.PSet.PointwiseRemainingPropOnlyFamilyBeta

#print axioms Rcic.F3.PSet.PointwiseRemainingPropOnlyFamilyBeta.covered_step
#print axioms Rcic.F3.PSet.PointwiseRemainingPropOnlyFamilyBeta.stepPropOnly_of_remaining
#print axioms Rcic.F3.PSet.PointwiseRemainingPropOnlyFamilyBeta.kernelSoundnessTierUncond_of_remaining

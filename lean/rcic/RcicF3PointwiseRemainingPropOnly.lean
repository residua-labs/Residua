import rcic.RcicF3PointwiseRemainingRefined
import rcic.RcicF3PointwisePropOnlyNormalized

/-!
# A smaller original-bound PropOnly residue from two additional syntax cases

The source-normalized producer permits arbitrary constructor parameter
mirrors. The existing matching-parameter producer is also exposed directly
at the original invariant boundary; uniform Prop admission pays its walk,
so it needs no successful W or D check. Empty family parameters imply this
second predicate directly from admission.

The old AllPlain/DirectCycle coverage is retained. This additive reduction
only splits on concrete syntax predicates using Premises4.dec. The DATA
residual is passed through literally unchanged, and the kernel conclusion
is the same original KernelSoundnessTierUncond. The new PropOnly residual
is explicitly conditional and is not asserted. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwiseRemainingPropOnly
open Rcic.Declarative

/-- Literal syntax equality, already consumed by the existing complete
parameter producer. It is not a checker-acceptance predicate. -/
def MatchingParameters {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Prop :=
  ∀ j : Fin node.a.constructors.length,
    (node.a.constructorViews j).parameters = node.a.family.parameters

/-- The actual parameter-free face satisfies MatchingParameters without
asking for any D check or semantic mirror equivalence. -/
theorem matching_parameters_of_empty
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (h : node.a.family.parameters = []) :
    MatchingParameters node :=
  NormPropParamFields.matching_parameters_of_empty node h

/-- Every matched-parameter PropOnly group already has a complete producer
under the original bounds. Uniform Prop admission supplies its walk. -/
theorem matching_parameters_step (P : Premises4) (K : Nat → Nat)
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
    (hpar : MatchingParameters (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  apply PointwisePropParamGroup.group_step P K hE hfam hctors hrec hmem hProp hpolicy hpar ?_ hB hD hPred
  intro node
  have hp : UniformProp node.a.family.resultLevel := by
    rw [Rcic.F3.StepWGroup.nodeResult_unique node p.node]
    exact hProp
  exact Rcic.Syn.FamApp.StepW.stepW_of_uniformProp hE hfam hctors hrec hmem node
    (walkRec_of_group hmem) hp


/-- All three alternatives inspect the actual selected admitted node. -/
def Covered
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') : Prop :=
  PointwiseRemainingRefined.PropOnlyCovered hE hfam hctors hrec hmem ∨
    PointwisePropOnlyNormalizedFields.SourceNormalized
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node ∨
    MatchingParameters (EvalPlan.ofGroup hE hfam hctors hrec hmem).node

/-- Only the remaining syntax cases are still requested as local
producers. Original bounds, predecessor and resulting GInv are literal. -/
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

/-- Every covered face returns the original group invariant. -/
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
  rcases hCovered with hold | hsource | hpar
  · exact PointwiseRemainingRefined.propOnly_covered_step P K hE hfam hctors hrec hmem
      hProp hpolicy hold hB hD hPred
  · exact PointwisePropOnlyNormalizedGroup.invariant_step P K hE hfam hctors hrec hmem
      hProp hpolicy hsource hB hD hPred
  · exact matching_parameters_step P K hE hfam hctors hrec hmem
      hProp hpolicy hpar hB hD hPred

/-- The smaller obligation recovers the previous exact residual. -/
theorem stepPropOnly_of_remaining (P : Premises4) (K : Nat → Nat)
    (hPropOnly : StepPropOnly P K) : PointwiseRemainingRefined.StepPropOnly P K := by
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
  PointwiseRemainingRefined.invariant_of_remaining P K hData
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
  PointwiseRemainingRefined.tierF3Uncond_of_remaining hData
    (fun P K => stepPropOnly_of_remaining P K (hPropOnly P K))

/-- Same original root and DATA residue; only the explicit PropOnly
residue is narrowed by the two actual invariant producers above. -/
theorem kernelSoundnessTierUncond_of_remaining
    (hData : ∀ (P : Premises4) (K : Nat → Nat), PointwiseRemainingRefined.StepData P K)
    (hPropOnly : ∀ (P : Premises4) (K : Nat → Nat), StepPropOnly P K) :
    Rcic.Apex.KernelSoundnessTierUncond :=
  PointwiseRemainingRefined.kernelSoundnessTierUncond_of_remaining hData
    (fun P K => stepPropOnly_of_remaining P K (hPropOnly P K))

end Rcic.F3.PSet.PointwiseRemainingPropOnly

#print axioms Rcic.F3.PSet.PointwiseRemainingPropOnly.matching_parameters_step
#print axioms Rcic.F3.PSet.PointwiseRemainingPropOnly.covered_step
#print axioms Rcic.F3.PSet.PointwiseRemainingPropOnly.stepPropOnly_of_remaining
#print axioms Rcic.F3.PSet.PointwiseRemainingPropOnly.kernelSoundnessTierUncond_of_remaining

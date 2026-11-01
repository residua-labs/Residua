import rcic.RcicF3PointwiseRemainingPropOnlyFamilyBeta
import rcic.RcicF3PointwiseDataFiniteRigid

/-!
# Original root after the produced finite DATA result-cut cases

The DATA covered set retains every previous case and adds literal matching
selected parameters, actual NoFunRec, and FirstIndexRigid. Its new branch
has a complete original-bound GInv producer whose W agreement follows
from the stored result spines. No W/D check or semantic callback appears
in public coverage.

The latest PropOnly residual is retained literally. Both remaining local
producers stay explicit hypotheses; the conclusion is the unchanged
KernelSoundnessTierUncond. This is a strict DATA residual reduction when
combined with the admitted List witness, not universal DATA closure.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwiseRemainingDataRigid
open Rcic.Declarative

/-- Union of actual syntax/cache cases with complete original producers. -/
def DataCovered
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') : Prop :=
  PointwiseRemainingRefined.DataCovered hE hfam hctors hrec hmem ∨
    ((∀ j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length,
      ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructorViews j).parameters =
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.parameters) ∧
      NoFunRec (EvalPlan.ofGroup hE hfam hctors hrec hmem).node ∧
      PointwiseDataFiniteRigid.FirstIndexRigid (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)

/-- The unchanged local DATA step is requested only outside that union. -/
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

/-- Every excluded DATA case returns the original group invariant. -/
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
  rcases hCovered with hold | ⟨hpar, hFinite, hRigid⟩
  · exact PointwiseRemainingRefined.data_covered_step P K hE hfam hctors hrec hmem
      hType hold hB hD hPred
  · exact PointwiseDataFiniteRigid.invariant_step P K hE hfam hctors hrec hmem
      hType hFinite hpar hRigid hB hD hPred

/-- The new residual recovers the preceding exact DATA residual. -/
theorem stepData_of_remaining (P : Premises4) (K : Nat → Nat)
    (hData : StepData P K) : PointwiseRemainingRefined.StepData P K := by
  intro E E' f rr fm rm ctors hE hfam hctors hrec hmem hType _hOld hB hD hPred
  cases P.dec (DataCovered hE hfam hctors hrec hmem) with
  | isTrue hCovered =>
      exact data_covered_step P K hE hfam hctors hrec hmem
        hType hCovered hB hD hPred
  | isFalse hRemaining =>
      exact hData hE hfam hctors hrec hmem hType hRemaining hB hD hPred

theorem invariant_of_remaining (P : Premises4) (K : Nat → Nat)
    (hData : StepData P K)
    (hPropOnly : PointwiseRemainingPropOnlyFamilyBeta.StepPropOnly P K)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E) :
    PointwiseRole.GInv P K hW :=
  PointwiseRemainingPropOnlyFamilyBeta.invariant_of_remaining P K
    (stepData_of_remaining P K hData) hPropOnly hW hB hD hAx

theorem envSound_of_remaining (P : Premises4) (K : Nat → Nat)
    (hData : StepData P K)
    (hPropOnly : PointwiseRemainingPropOnlyFamilyBeta.StepPropOnly P K)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E)
    (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (PointwiseRole.table P hW)) σ K E n :=
  PointwiseRole.envSound_of_gInv P K hW
    (invariant_of_remaining P K hData hPropOnly hW hB hD hAx) σ n

theorem tierF3Uncond_of_remaining
    (hData : ∀ (P : Premises4) (K : Nat → Nat), StepData P K)
    (hPropOnly : ∀ (P : Premises4) (K : Nat → Nat),
      PointwiseRemainingPropOnlyFamilyBeta.StepPropOnly P K) :
    Rcic.Apex.TierF3Uncond :=
  PointwiseRemainingPropOnlyFamilyBeta.tierF3Uncond_of_remaining
    (fun P K => stepData_of_remaining P K (hData P K)) hPropOnly

/-- The literal original root, with the exact two remaining local steps
still visible. All previously produced PropOnly cases are retained. -/
theorem kernelSoundnessTierUncond_of_remaining
    (hData : ∀ (P : Premises4) (K : Nat → Nat), StepData P K)
    (hPropOnly : ∀ (P : Premises4) (K : Nat → Nat),
      PointwiseRemainingPropOnlyFamilyBeta.StepPropOnly P K) :
    Rcic.Apex.KernelSoundnessTierUncond :=
  PointwiseRemainingPropOnlyFamilyBeta.kernelSoundnessTierUncond_of_remaining
    (fun P K => stepData_of_remaining P K (hData P K)) hPropOnly

end Rcic.F3.PSet.PointwiseRemainingDataRigid

#print axioms Rcic.F3.PSet.PointwiseRemainingDataRigid.data_covered_step
#print axioms Rcic.F3.PSet.PointwiseRemainingDataRigid.stepData_of_remaining
#print axioms Rcic.F3.PSet.PointwiseRemainingDataRigid.kernelSoundnessTierUncond_of_remaining

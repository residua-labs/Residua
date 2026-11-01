import rcic.RcicF3PointwiseRemainingDataRigid
import rcic.RcicF3PointwiseDataFiniteSeparated

/-!
# Original DATA residual after exact first-field/index separation

Every previous DATA coverage case is retained. The additional branch is
paid by the complete original-bound producer in PointwiseDataFiniteSeparated.
Its public guard is literal syntax/cache data, not a soundness premise.

The resulting root still names both universal residuals explicitly and
concludes the unchanged KernelSoundnessTierUncond. No whole-tier closure
or historical-frontier reduction is asserted. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwiseRemainingDataSeparated
open Rcic.Declarative

def DataCovered
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E') : Prop :=
  PointwiseRemainingDataRigid.DataCovered hE hfam hctors hrec hmem ∨
    ((∀ j : Fin (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructors.length,
      ((EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.constructorViews j).parameters =
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.parameters) ∧
      NoFunRec (EvalPlan.ofGroup hE hfam hctors hrec hmem).node ∧
      PointwiseDataFiniteSeparated.FirstFieldSeparated
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)

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

theorem data_covered_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hType : UniformType
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hCovered : DataCovered hE hfam hctors hrec hmem)
    (hB : BoundG K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hD : BoundDG K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  rcases hCovered with hold | ⟨hpar, hFinite, hSeparated⟩
  · exact PointwiseRemainingDataRigid.data_covered_step P K hE hfam hctors hrec hmem
      hType hold hB hD hPred
  · exact PointwiseDataFiniteSeparated.invariant_step P K hE hfam hctors hrec hmem
      hType hFinite hpar hSeparated hB hD hPred

/-- This new residual supplies the complete predecessor DATA residual;
covered and uncovered cases retain exactly the same original conclusion. -/
theorem stepData_of_remaining (P : Premises4) (K : Nat → Nat)
    (hData : StepData P K) : PointwiseRemainingDataRigid.StepData P K := by
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
  PointwiseRemainingDataRigid.invariant_of_remaining P K
    (stepData_of_remaining P K hData) hPropOnly hW hB hD hAx

/-- The original root, with the two remaining universal producer families
still explicit. Neither universal residual is asserted proved. -/
theorem kernelSoundnessTierUncond_of_remaining
    (hData : ∀ (P : Premises4) (K : Nat → Nat), StepData P K)
    (hPropOnly : ∀ (P : Premises4) (K : Nat → Nat),
      PointwiseRemainingPropOnlyFamilyBeta.StepPropOnly P K) :
    Rcic.Apex.KernelSoundnessTierUncond :=
  PointwiseRemainingDataRigid.kernelSoundnessTierUncond_of_remaining
    (fun P K => stepData_of_remaining P K (hData P K)) hPropOnly

end Rcic.F3.PSet.PointwiseRemainingDataSeparated

#print axioms Rcic.F3.PSet.PointwiseRemainingDataSeparated.data_covered_step
#print axioms Rcic.F3.PSet.PointwiseRemainingDataSeparated.stepData_of_remaining
#print axioms Rcic.F3.PSet.PointwiseRemainingDataSeparated.kernelSoundnessTierUncond_of_remaining

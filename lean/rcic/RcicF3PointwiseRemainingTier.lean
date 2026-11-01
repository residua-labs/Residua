import rcic.RcicF3PointwisePropAnySort
import rcic.RcicF3PointwiseRoleConsumer
import rcic.RcicRiskTier

/-!
# The original kernel tier reduced to DATA and PropOnly

The uniformly Prop/anySort group branch is produced by
`PointwisePropAnySort.invariant_step`. The two remaining producers below
are local admission steps for uniformly Type families and uniformly Prop
families with propOnly elimination. They retain the original group,
BoundG, BoundDG, and pointwise predecessor invariant. They carry no
checker-completeness condition or replacement root premise.

The complete admission fold yields the literal
`Rcic.Apex.KernelSoundnessTierUncond` conditional on exactly these two
universal producers. Neither remaining producer is asserted here.

A separate declarative property identifies derivations all of whose
groups are Prop/anySort. Their invariant, environment soundness, and final
consistency consumer are produced with no remaining semantic step input.
The original bounds and axiom-free condition remain explicit.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.PointwiseRemainingTier
open Rcic.Declarative

/-- The remaining DATA producer on the actual selected admitted plan.
This is an explicitly unproved local obligation on the original domain. -/
def StepData (P : Premises4) (K : Nat → Nat) : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E'),
    UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel →
    BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
    BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
    PointwiseRole.GInv P K hE →
      PointwiseRole.GInv P K
        (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem)

/-- The remaining PropOnly producer on the actual selected admitted plan.
No parameter-equality, W-check, or D-check assumption is added. -/
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
    BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
    BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
    PointwiseRole.GInv P K hE →
      PointwiseRole.GInv P K
        (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem)

/-- Admission itself gives the exhaustive Prop/Type split; the original
policy gives the two Prop cases. The anySort case is produced. -/
theorem invariant_step (P : Premises4) (K : Nat → Nat)
    (hData : StepData P K) (hPropOnly : StepPropOnly P K)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  rcases selection_uniform p.node.a with hProp | hType
  · cases hpolicy : p.node.a.policy with
    | anySort =>
        exact PointwisePropAnySort.invariant_step P K hE hfam hctors hrec hmem
          hProp hpolicy hB hD hPred
    | propOnly =>
        exact hPropOnly hE hfam hctors hrec hmem hProp hpolicy hB hD hPred
  · exact hData hE hfam hctors hrec hmem hType hB hD hPred

/-- The original coverage predicate and both original bound predicates
are enough for the admission fold once the two residuals are supplied. -/
theorem steps_covered (P : Premises4) (K : Nat → Nat)
    (hData : StepData P K) (hPropOnly : StepPropOnly P K) :
    PointwiseRole.GInvSteps P K
      (fun {E : ResolvedEnv} (h : EnvWfT E) => Covered h)
      (fun {E : ResolvedEnv} (h : EnvWfT E) => BoundG K h ∧ BoundDG K h) where
  stepDef := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH =>
      PointwiseRole.gInv_singleW P K (Or.inl rfl)
        hfresh hclA hclv hlvlA hlvlv hv hB.1.2 IH⟩
  stepThm := fun _ _ _ _ hE hfresh _ hp hclA hclp hlvlA hlvlp hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH =>
      PointwiseRole.gInv_singleW P K (Or.inr (Or.inl rfl))
        hfresh hclA hclp hlvlA hlvlp hp hB.1.2 IH⟩
  stepOpq := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH =>
      PointwiseRole.gInv_singleW P K (Or.inr (Or.inr rfl))
        hfresh hclA hclv hlvlA hlvlv hv hB.1.2 IH⟩
  stepGrp := fun _ _ _ _ _ _ _ hE hfam hctors hrec hmem hC hB =>
    ⟨hC.1, ⟨hB.1.1, hB.2.1⟩, fun IH =>
      invariant_step P K hData hPropOnly hE hfam hctors hrec hmem hB.1 hB.2 IH⟩

theorem invariant_of_remaining (P : Premises4) (K : Nat → Nat)
    (hData : StepData P K) (hPropOnly : StepPropOnly P K)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E) :
    PointwiseRole.GInv P K hW :=
  PointwiseRole.gInv_of_steps P K _ _ (steps_covered P K hData hPropOnly)
    (fun {_} _ _ _ _ _ _ _ _ _ hCx => hCx)
    hW (EnvWfT_axiomFree_covered P hW hAx) ⟨hB, hD⟩

theorem envSound_of_remaining (P : Premises4) (K : Nat → Nat)
    (hData : StepData P K) (hPropOnly : StepPropOnly P K)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E)
    (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (PointwiseRole.table P hW)) σ K E n :=
  PointwiseRole.envSound_of_gInv P K hW
    (invariant_of_remaining P K hData hPropOnly hW hB hD hAx) σ n

/-- The literal original F3 proposition, conditional only on the two
named remaining producers. The two original False lookup premises,
original bounds, and original final derivation are retained by the root. -/
theorem tierF3Uncond_of_remaining
    (hData : ∀ (P : Premises4) (K : Nat → Nat), StepData P K)
    (hPropOnly : ∀ (P : Premises4) (K : Nat → Nat), StepPropOnly P K) :
    Rcic.Apex.TierF3Uncond := by
  intro P K E hW hB hD hAx _h0 h1 n e D hLOK
  exact PointwiseRole.false_of_gInv P K hW
    (invariant_of_remaining P K (hData P K) (hPropOnly P K) hW hB hD hAx)
    h1 n e D hLOK

/-- F1 is already produced. This proves an exact residual reduction of
the original root, not closure of the two displayed producer obligations. -/
theorem kernelSoundnessTierUncond_of_remaining
    (hData : ∀ (P : Premises4) (K : Nat → Nat), StepData P K)
    (hPropOnly : ∀ (P : Premises4) (K : Nat → Nat), StepPropOnly P K) :
    Rcic.Apex.KernelSoundnessTierUncond :=
  ⟨Rcic.Apex.tierF1, tierF3Uncond_of_remaining hData hPropOnly⟩

/-- A declarative property of the actual group occurrences in an
admission derivation. Ordinary declarations are unrestricted here; axiom
freedom is retained separately as the original environment premise. -/
def AllPropAnySort : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ hE _ _ _ _ => AllPropAnySort hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => AllPropAnySort hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => AllPropAnySort hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => AllPropAnySort hE
  | _, .group _ _ _ _ _ _ _ hE hfam hctors hrec hmem =>
      AllPropAnySort hE ∧
        UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel ∧
        (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .anySort

/-- Every group branch in this derivation has a produced invariant step;
there is no DATA or PropOnly producer premise in this fold. -/
theorem steps_allPropAnySort (P : Premises4) (K : Nat → Nat) :
    PointwiseRole.GInvSteps P K
      (fun {E : ResolvedEnv} (h : EnvWfT E) => Covered h ∧ AllPropAnySort h)
      (fun {E : ResolvedEnv} (h : EnvWfT E) => BoundG K h ∧ BoundDG K h) where
  stepDef := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH =>
      PointwiseRole.gInv_singleW P K (Or.inl rfl)
        hfresh hclA hclv hlvlA hlvlv hv hB.1.2 IH⟩
  stepThm := fun _ _ _ _ hE hfresh _ hp hclA hclp hlvlA hlvlp hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH =>
      PointwiseRole.gInv_singleW P K (Or.inr (Or.inl rfl))
        hfresh hclA hclp hlvlA hlvlp hp hB.1.2 IH⟩
  stepOpq := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH =>
      PointwiseRole.gInv_singleW P K (Or.inr (Or.inr rfl))
        hfresh hclA hclv hlvlA hlvlv hv hB.1.2 IH⟩
  stepGrp := fun _ _ _ _ _ _ _ hE hfam hctors hrec hmem hC hB =>
    ⟨⟨hC.1.1, hC.2.1⟩, ⟨hB.1.1, hB.2.1⟩, fun IH =>
      PointwisePropAnySort.invariant_step P K hE hfam hctors hrec hmem
        hC.2.2.1 hC.2.2.2 hB.1 hB.2 IH⟩

theorem invariant_of_allPropAnySort (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E) (hProp : AllPropAnySort hW)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E) :
    PointwiseRole.GInv P K hW :=
  PointwiseRole.gInv_of_steps P K _ _ (steps_allPropAnySort P K)
    (fun {_} _ _ _ _ _ _ _ _ _ hCx => hCx.1)
    hW ⟨EnvWfT_axiomFree_covered P hW hAx, hProp⟩ ⟨hB, hD⟩

theorem envSound_of_allPropAnySort (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E) (hProp : AllPropAnySort hW)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E)
    (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (PointwiseRole.table P hW)) σ K E n :=
  PointwiseRole.envSound_of_gInv P K hW
    (invariant_of_allPropAnySort P K hW hProp hB hD hAx) σ n

/-- The original consistency conclusion on the produced all-Prop/anySort
environment class, at the same stored False recursor and final bound. -/
theorem false_of_allPropAnySort (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E) (hProp : AllPropAnySort hW)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E)
    (h1 : E.members 1 = some falseRecMemberU) (n : Nat)
    (e : Expr Nat) (D : HasTyT E n [] e (.const 0 []))
    (hl : LevelsBelow 4 K D) : False :=
  PointwiseRole.false_of_gInv P K hW
    (invariant_of_allPropAnySort P K hW hProp hB hD hAx) h1 n e D hl

end Rcic.F3.PSet.PointwiseRemainingTier

#print axioms Rcic.F3.PSet.PointwiseRemainingTier.invariant_step
#print axioms Rcic.F3.PSet.PointwiseRemainingTier.invariant_of_remaining
#print axioms Rcic.F3.PSet.PointwiseRemainingTier.kernelSoundnessTierUncond_of_remaining
#print axioms Rcic.F3.PSet.PointwiseRemainingTier.invariant_of_allPropAnySort
#print axioms Rcic.F3.PSet.PointwiseRemainingTier.false_of_allPropAnySort

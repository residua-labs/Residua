import rcic.RcicF3PointwiseDataFinite
import rcic.RcicF3PointwisePropGroup
import rcic.RcicF3PointwisePropParamGroup
import rcic.RcicF3PointwisePropPlainGroup
import rcic.RcicF3PointwiseRoleConsumer
import rcic.RcicF3NormADataChecked

/-!
# The unchanged checked kernel tier through the separate pointwise table

This module composes actual finite DATA and both Prop policy producers,
then folds the new invariant over the original admission derivation.
The executable W and D checks, original bounds, axiom-free condition and
distinguished False prefix in the final kernel tier are unchanged.

Only the checked positive-depth DATA face retains a named semantic input.
LocalCandidatesChecked states its exact bounded-world candidate-existence
obligation; the constructor, stored recursor, reader and stable legacy
IotaAt consumers are already produced. The reader/mask construction has
not yet supplied this input universally. No new check is introduced.

This is an explicit new interpretation. It neither changes NormRole nor
asserts equality of old and new invariants, universal old StepAG, or
universal non-refutability of the remaining input. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseADataChecked
open Rcic.Declarative Rcic.Model.PS Rcic.F3.StepDGOrder Rcic.F3.StepWCheck

/-- The remaining data step on groups admitted by the original rules and
accepted by the existing selected-node D check. PendA is the original
existential group predicate, not a restriction on the chosen cache. -/
def StepADataChecked (P : Premises4) (K : Nat → Nat) : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E'),
    UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel →
    (∃ node : RecNode E E' f rr rm, PendA node) →
    Rcic.F3.StepWDApex.groupCheck K hE hfam hctors hrec hmem = none →
      PointwiseDataGroup.GroupStepAt P K hE hfam hctors hrec hmem

/-- The exact local existence obligation over the SAME original selected
check and original existential PendA domain. It has no mask/read callback
and is not an additional executable acceptance condition. -/
def LocalCandidatesChecked (P : Premises4) (K : Nat → Nat) : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E'),
    UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel →
    (∃ node : RecNode E E' f rr rm, PendA node) →
    Rcic.F3.StepWDApex.groupCheck K hE hfam hctors hrec hmem = none →
      PointwiseDataGroup.LocalCandidatesAt P K hE hfam hctors hrec hmem

/-- Real checked DATA consumers compose each local candidate with the
original stored constructors and complete recursor package. -/
theorem stepADataChecked_of_localCandidates (P : Premises4) (K : Nat → Nat)
    (hLocal : LocalCandidatesChecked P K) : StepADataChecked P K := by
  intro E E' f rr fm rm ctors hE hfam hctors hrec hmem hType hPend hcheck
  exact PointwiseDataGroup.group_step_of_check P K hE hfam hctors hrec hmem
    hType hcheck (hLocal hE hfam hctors hrec hmem hType hPend hcheck)

/-- Original checked group composition at the new table. Every Prop face
and every finite DATA face is produced; only positive-depth DATA uses the
explicit remaining producer. -/
theorem group_step_of_check (P : Premises4) (K : Nat → Nat)
    (hData : StepADataChecked P K)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hp : Rcic.F3.StepWDApex.groupCheck K hE hfam hctors hrec hmem = none) :
    PointwiseDataGroup.GroupStepAt P K hE hfam hctors hrec hmem := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  rcases selection_uniform p.node.a with hProp | hType
  · cases hpolicy : p.node.a.policy with
    | anySort =>
      cases P.dec (∃ node : RecNode E E' f rr rm, PendA node) with
      | isTrue hPend =>
        exact PointwisePropGroup.group_step P K hE hfam hctors hrec hmem
          hProp hpolicy hPend
      | isFalse hPend =>
        have hN : NoFunRec p.node :=
          noFunRec_of_not_pendA (fun h => hPend ⟨p.node, h⟩)
        have hs : StepDGSide K p.node :=
          (Rcic.F3.StepWDApex.groupCheck_pass_iff K hE hfam hctors hrec hmem).mp hp
        exact PointwisePropPlainGroup.group_step P K hE hfam hctors hrec hmem
          hProp hpolicy hN
          (fun j A hfield => (hs.2.1 hProp hpolicy j).1 A hfield)
    | propOnly =>
      exact PointwisePropParamGroup.group_step_of_check P K hE hfam hctors hrec hmem
        hProp hpolicy hp
  · cases P.dec (∃ node : RecNode E E' f rr rm, PendA node) with
    | isTrue hPend =>
      exact hData hE hfam hctors hrec hmem hType hPend hp
    | isFalse hPend =>
      have hN : NoFunRec p.node :=
        noFunRec_of_not_pendA (fun h => hPend ⟨p.node, h⟩)
      exact PointwiseDataFinite.group_step_of_check P K hE hfam hctors hrec hmem
        hType hN hp

/-- Admission folding retains the original coverage, exact checks and
both bounded-derivation predicates. Canonical read laws are produced by
the actual pointwise-role consumer. -/
theorem steps_coveredWDChecked (P : Premises4) (K : Nat → Nat)
    (hData : StepADataChecked P K) :
    PointwiseRole.GInvSteps P K
      (fun {E : ResolvedEnv} (h : EnvWfT E) =>
        Covered h ∧ EnvWChecked h ∧ Rcic.F3.StepWDApex.EnvDChecked K h)
      (fun {E : ResolvedEnv} (h : EnvWfT E) => BoundG K h ∧ BoundDG K h) where
  stepDef := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH =>
      PointwiseRole.gInv_singleW P K (Or.inl rfl) hfresh hclA hclv hlvlA hlvlv hv hB.1.2 IH⟩
  stepThm := fun _ _ _ _ hE hfresh _ hp hclA hclp hlvlA hlvlp hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH =>
      PointwiseRole.gInv_singleW P K (Or.inr (Or.inl rfl)) hfresh hclA hclp hlvlA hlvlp hp hB.1.2 IH⟩
  stepOpq := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH =>
      PointwiseRole.gInv_singleW P K (Or.inr (Or.inr rfl)) hfresh hclA hclv hlvlA hlvlv hv hB.1.2 IH⟩
  stepGrp := fun _ _ _ _ _ _ _ hE hfam hctors hrec hmem hC hB =>
    ⟨⟨hC.1.1, hC.2.1.1, hC.2.2.1⟩, ⟨hB.1.1, hB.2.1⟩, fun IH =>
      group_step_of_check P K hData hE hfam hctors hrec hmem
        ((Rcic.F3.StepWDApex.groupCheck_pass_iff K hE hfam hctors hrec hmem).mpr hC.2.2.2)
        (walkAgree_of_groupWChecked P hE hfam hctors hrec hmem hC.2.1.2) hB.1 hB.2 IH⟩

theorem invariant_of_checks (P : Premises4) (K : Nat → Nat)
    (hData : StepADataChecked P K) {E : ResolvedEnv} (hW : EnvWfT E)
    (pw : Rcic.F3.StepWApex.envCheck hW = true)
    (pd : Rcic.F3.StepWDApex.envCheck K hW = true)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E) :
    PointwiseRole.GInv P K hW := by
  have hC : Covered hW ∧ EnvWChecked hW ∧ Rcic.F3.StepWDApex.EnvDChecked K hW :=
    ⟨EnvWfT_axiomFree_covered P hW hAx,
      Rcic.F3.StepWApex.envCheck_sound hW pw,
      Rcic.F3.StepWDApex.envCheck_sound K hW pd⟩
  exact PointwiseRole.gInv_of_steps P K _ _ (steps_coveredWDChecked P K hData)
    (fun {_} _ _ _ _ _ _ _ _ _ hCx => hCx.1) hW hC ⟨hB, hD⟩

theorem envSound_of_checks (P : Premises4) (K : Nat → Nat)
    (hData : StepADataChecked P K) {E : ResolvedEnv} (hW : EnvWfT E)
    (pw : Rcic.F3.StepWApex.envCheck hW = true)
    (pd : Rcic.F3.StepWDApex.envCheck K hW = true)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E)
    (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (PointwiseRole.table P hW)) σ K E n :=
  PointwiseRole.envSound_of_gInv P K hW
    (invariant_of_checks P K hData hW pw pd hB hD hAx) σ n

/-- The existing F3 statement is unchanged, including both checks, both
bounds, axiom freedom and the distinguished False prefix. -/
theorem tierF3WDChecked_of_AData
    (hData : ∀ (P : Premises4) (K : Nat → Nat), StepADataChecked P K) :
    Rcic.F3.StepWDApex.TierF3WDChecked := by
  intro P K E hW pw pd hB hD hAx _h0 h1 n e D hLOK
  exact PointwiseRole.false_of_gInv P K hW
    (invariant_of_checks P K (hData P K) hW pw pd hB hD hAx) h1 n e D hLOK

/-- F1 and the literal checked F3 tier. The sole extra universal semantic
input here is the explicitly stated checked positive-depth data step.
The original unchecked NormRole.StepAG remains a separate target. -/
theorem kernelSoundnessTierWDChecked_of_AData
    (hData : ∀ (P : Premises4) (K : Nat → Nat), StepADataChecked P K) :
    Rcic.F3.StepWDApex.KernelSoundnessTierWDChecked :=
  ⟨Rcic.Apex.tierF1, tierF3WDChecked_of_AData hData⟩

/-- The same literal checked tier, with the remaining bounded local-frame
existence requirement exposed directly. This theorem is conditional until
the universal producer is supplied. -/
theorem kernelSoundnessTierWDChecked_of_localCandidates
    (hLocal : ∀ (P : Premises4) (K : Nat → Nat), LocalCandidatesChecked P K) :
    Rcic.F3.StepWDApex.KernelSoundnessTierWDChecked :=
  kernelSoundnessTierWDChecked_of_AData
    (fun P K => stepADataChecked_of_localCandidates P K (hLocal P K))

end Rcic.F3.PSet.PointwiseADataChecked

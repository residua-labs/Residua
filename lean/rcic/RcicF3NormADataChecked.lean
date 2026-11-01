import rcic.RcicF3NormWDChecked
import rcic.RcicF3NormPropGroup
import rcic.RcicF3NormPropParamGroup

/-!
# The unchanged checked apex with only the positive-depth data producer open

The Prop/anySort positive-depth group producer and the Prop-only producer
are composed with the existing finite/plain consumers. The literal W/D
checks are unchanged. In particular the Prop-only parameter equality is
read from the D condition already checked at every selected group node.

The remaining input is stated explicitly below: an original admitted
PendA group whose selected node has a uniformly Type-valued family and
whose existing D group check passes must produce the new GroupStepAt.
It retains the original existential PendA condition and the original walk,
BoundG, BoundDG and predecessor-invariant arguments of GroupStepAt.

This is a reduction of the checked apex's frontier, not a production or
replacement of universal unchecked NormRole.StepAG. Its implication into
the checked data premise is recorded separately. No universal data
producer or its non-refutability is asserted here. closure_claim = 0.
-/

set_option autoImplicit false
namespace Rcic.F3.PSet.NormADataChecked
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
      NormRole.GroupStepAt P K hE hfam hctors hrec hmem

/-- Universal unchecked A remains a distinct stronger premise. This
implication does not assert either premise or a converse. -/
theorem stepADataChecked_of_stepAG (P : Premises4) (K : Nat → Nat)
    (hA : NormRole.StepAG P K) : StepADataChecked P K := by
  intro E E' f rr fm rm ctors hE hfam hctors hrec hmem _hType hPend _hcheck
  exact hA hE hfam hctors hrec hmem hPend

/-- Original checked group composition. Both Prop faces and every
A-negative face are produced; only the explicit positive data face uses
the remaining input. -/
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
    NormRole.GroupStepAt P K hE hfam hctors hrec hmem := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  cases P.dec (∃ node : RecNode E E' f rr rm, PendA node) with
  | isTrue hPend =>
    rcases selection_uniform p.node.a with hProp | hType
    · cases hpolicy : p.node.a.policy with
      | anySort =>
        exact NormPropGroup.group_step P K hE hfam hctors hrec hmem
          hProp hpolicy hPend
      | propOnly =>
        exact NormPropParamGroup.group_step_of_check P K hE hfam hctors hrec hmem
          hProp hpolicy hp
    · exact hData hE hfam hctors hrec hmem hType hPend hp
  | isFalse hPend =>
    have hN : NoFunRec p.node := noFunRec_of_not_pendA (fun h => hPend ⟨p.node, h⟩)
    have hs : StepDGSide K p.node :=
      (Rcic.F3.StepWDApex.groupCheck_pass_iff K hE hfam hctors hrec hmem).mp hp
    cases P.dec (UniformProp p.node.a.family.resultLevel ∧ p.node.a.policy = .anySort) with
    | isTrue hprop =>
      exact NormPropPlainGroup.group_step P K hE hfam hctors hrec hmem
        hprop.1 hprop.2 hN (fun j A hfield => (hs.2.1 hprop.1 hprop.2 j).1 A hfield)
    | isFalse hprop =>
      exact NormDFallback.group_step P K hE hfam hctors hrec hmem hN hs hprop

/-- Admission folding retains the original coverage, exact checks and
both bounded-derivation predicates. Canonical read laws are produced by
the existing normalized-role consumer. -/
theorem steps_coveredWDChecked (P : Premises4) (K : Nat → Nat)
    (hData : StepADataChecked P K) :
    NormRole.GInvSteps P K
      (fun {E : ResolvedEnv} (h : EnvWfT E) =>
        Covered h ∧ EnvWChecked h ∧ Rcic.F3.StepWDApex.EnvDChecked K h)
      (fun {E : ResolvedEnv} (h : EnvWfT E) => BoundG K h ∧ BoundDG K h) where
  stepDef := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH =>
      NormRole.gInv_singleW P K (Or.inl rfl) hfresh hclA hclv hlvlA hlvlv hv hB.1.2 IH⟩
  stepThm := fun _ _ _ _ hE hfresh _ hp hclA hclp hlvlA hlvlp hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH =>
      NormRole.gInv_singleW P K (Or.inr (Or.inl rfl)) hfresh hclA hclp hlvlA hlvlp hp hB.1.2 IH⟩
  stepOpq := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH =>
      NormRole.gInv_singleW P K (Or.inr (Or.inr rfl)) hfresh hclA hclv hlvlA hlvlv hv hB.1.2 IH⟩
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
    NormRole.GInv P K hW := by
  have hC : Covered hW ∧ EnvWChecked hW ∧ Rcic.F3.StepWDApex.EnvDChecked K hW :=
    ⟨EnvWfT_axiomFree_covered P hW hAx,
      Rcic.F3.StepWApex.envCheck_sound hW pw,
      Rcic.F3.StepWDApex.envCheck_sound K hW pd⟩
  exact NormRole.gInv_of_steps P K _ _ (steps_coveredWDChecked P K hData)
    (fun {_} _ _ _ _ _ _ _ _ _ hCx => hCx.1) hW hC ⟨hB, hD⟩

theorem envSound_of_checks (P : Premises4) (K : Nat → Nat)
    (hData : StepADataChecked P K) {E : ResolvedEnv} (hW : EnvWfT E)
    (pw : Rcic.F3.StepWApex.envCheck hW = true)
    (pd : Rcic.F3.StepWDApex.envCheck K hW = true)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E)
    (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (NormRole.table P hW)) σ K E n :=
  NormRole.envSound_of_gInv P K hW
    (invariant_of_checks P K hData hW pw pd hB hD hAx) σ n

/-- The existing F3 statement is unchanged, including both checks, both
bounds, axiom freedom and the distinguished False prefix. -/
theorem tierF3WDChecked_of_AData
    (hData : ∀ (P : Premises4) (K : Nat → Nat), StepADataChecked P K) :
    Rcic.F3.StepWDApex.TierF3WDChecked := by
  intro P K E hW pw pd hB hD hAx _h0 h1 n e D hLOK
  exact NormRole.false_of_gInv P K hW
    (invariant_of_checks P K (hData P K) hW pw pd hB hD hAx) h1 n e D hLOK

/-- F1 and the literal checked F3 tier. The sole extra universal semantic
input here is the explicitly stated checked positive-depth data step.
Universal unchecked NormRole.StepAG remains a separate target. -/
theorem kernelSoundnessTierWDChecked_of_AData
    (hData : ∀ (P : Premises4) (K : Nat → Nat), StepADataChecked P K) :
    Rcic.F3.StepWDApex.KernelSoundnessTierWDChecked :=
  ⟨Rcic.Apex.tierF1, tierF3WDChecked_of_AData hData⟩

end Rcic.F3.PSet.NormADataChecked

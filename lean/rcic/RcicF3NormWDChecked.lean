import rcic.RcicF3NormDFallback
import rcic.RcicF3NormPropPlainGroup
import rcic.RcicF3NormRoleConsumer

/-!
# The original checked W/D apex at the repaired normalized interpretation

The A-negative group producer is composed from the produced finite-frame
fallback and the typed Prop/anySort package. The original W/D executable
checks and all original environment, bound and False-prefix conjuncts are
unchanged. Canonical normalized role and indexed-plan reads are produced
by the admitted environment; no family comparison or read law is assumed.

The remaining argument is the universal normalized StepAG producer on the
full positive-depth PendA domain. This module consumes that argument and
does not produce or assert its non-refutability. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormWDChecked
open Rcic.Declarative Rcic.Model.PS Rcic.F3.StepDGOrder Rcic.F3.StepWCheck

/-- Every selected-node D check is consumed literally. The two A-negative
semantic faces are produced; the positive-depth case consumes hA. -/
theorem group_step_of_check (P : Premises4) (K : Nat → Nat)
    (hA : NormRole.StepAG P K)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hp : Rcic.F3.StepWDApex.groupCheck K hE hfam hctors hrec hmem = none) :
    NormRole.GroupStepAt P K hE hfam hctors hrec hmem := by
  cases P.dec (∃ node : RecNode E E' f rr rm, PendA node) with
  | isTrue ha => exact hA hE hfam hctors hrec hmem ha
  | isFalse ha =>
      let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
      have hN : NoFunRec p.node := noFunRec_of_not_pendA (fun h => ha ⟨p.node, h⟩)
      have hs : StepDGSide K p.node :=
        (Rcic.F3.StepWDApex.groupCheck_pass_iff K hE hfam hctors hrec hmem).mp hp
      cases P.dec (UniformProp p.node.a.family.resultLevel ∧ p.node.a.policy = .anySort) with
      | isTrue hprop =>
          exact NormPropPlainGroup.group_step P K hE hfam hctors hrec hmem
            hprop.1 hprop.2 hN (fun j A hfield => (hs.2.1 hprop.1 hprop.2 j).1 A hfield)
      | isFalse hprop =>
          exact NormDFallback.group_step P K hE hfam hctors hrec hmem hN hs hprop

theorem steps_coveredWDChecked (P : Premises4) (K : Nat → Nat) (hA : NormRole.StepAG P K) :
    NormRole.GInvSteps P K
      (fun {E : ResolvedEnv} (h : EnvWfT E) => Covered h ∧ EnvWChecked h ∧ Rcic.F3.StepWDApex.EnvDChecked K h)
      (fun {E : ResolvedEnv} (h : EnvWfT E) => BoundG K h ∧ BoundDG K h) where
  stepDef := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH => NormRole.gInv_singleW P K (Or.inl rfl) hfresh hclA hclv hlvlA hlvlv hv hB.1.2
      IH⟩
  stepThm := fun _ _ _ _ hE hfresh _ hp hclA hclp hlvlA hlvlp hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH => NormRole.gInv_singleW P K (Or.inr (Or.inl rfl)) hfresh hclA hclp hlvlA hlvlp hp
      hB.1.2 IH⟩
  stepOpq := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH => NormRole.gInv_singleW P K (Or.inr (Or.inr rfl)) hfresh hclA hclv hlvlA hlvlv hv
      hB.1.2 IH⟩
  stepGrp := fun _ _ _ _ _ _ _ hE hfam hctors hrec hmem hC hB =>
    ⟨⟨hC.1.1, hC.2.1.1, hC.2.2.1⟩, ⟨hB.1.1, hB.2.1⟩, fun IH =>
      group_step_of_check P K hA hE hfam hctors hrec hmem
        ((Rcic.F3.StepWDApex.groupCheck_pass_iff K hE hfam hctors hrec hmem).mpr hC.2.2.2)
        (walkAgree_of_groupWChecked P hE hfam hctors hrec hmem hC.2.1.2) hB.1 hB.2 IH⟩

/-- The new invariant for every admitted axiom-free environment passing
its exact W/D checks, conditional only on the universal A producer. -/
theorem invariant_of_checks (P : Premises4) (K : Nat → Nat)
    (hA : NormRole.StepAG P K) {E : ResolvedEnv} (hW : EnvWfT E)
    (pw : Rcic.F3.StepWApex.envCheck hW = true)
    (pd : Rcic.F3.StepWDApex.envCheck K hW = true)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E) :
    NormRole.GInv P K hW := by
  have hC : Covered hW ∧ EnvWChecked hW ∧ Rcic.F3.StepWDApex.EnvDChecked K hW :=
    ⟨EnvWfT_axiomFree_covered P hW hAx,
      Rcic.F3.StepWApex.envCheck_sound hW pw,
      Rcic.F3.StepWDApex.envCheck_sound K hW pd⟩
  exact NormRole.gInv_of_steps P K _ _ (steps_coveredWDChecked P K hA)
    (fun {_} _ _ _ _ _ _ _ _ _ hCx => hCx.1) hW hC ⟨hB, hD⟩

theorem envSound_of_checks (P : Premises4) (K : Nat → Nat)
    (hA : NormRole.StepAG P K) {E : ResolvedEnv} (hW : EnvWfT E)
    (pw : Rcic.F3.StepWApex.envCheck hW = true)
    (pd : Rcic.F3.StepWDApex.envCheck K hW = true)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E)
    (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (NormRole.table P hW)) σ K E n :=
  NormRole.envSound_of_gInv P K hW
    (invariant_of_checks P K hA hW pw pd hB hD hAx) σ n

/-- The literal existing checked F3 statement, at the repaired model. -/
theorem tierF3WDChecked_of_A
    (hA : ∀ (P : Premises4) (K : Nat → Nat), NormRole.StepAG P K) :
    Rcic.F3.StepWDApex.TierF3WDChecked := by
  intro P K E hW pw pd hB hD hAx _h0 h1 n e D hLOK
  exact NormRole.false_of_gInv P K hW
    (invariant_of_checks P K (hA P K) hW pw pd hB hD hAx) h1 n e D hLOK

/-- F1 and the unchanged checked F3 tier. The sole remaining universal
semantic argument is the explicitly normalized A producer. -/
theorem kernelSoundnessTierWDChecked_of_A
    (hA : ∀ (P : Premises4) (K : Nat → Nat), NormRole.StepAG P K) :
    Rcic.F3.StepWDApex.KernelSoundnessTierWDChecked :=
  ⟨Rcic.Apex.tierF1, tierF3WDChecked_of_A hA⟩

end Rcic.F3.PSet.NormWDChecked

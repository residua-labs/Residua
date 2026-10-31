import rcic.RcicF3StepWApex
import rcic.RcicF3StepDGCheck

/-!
# W/D-checked apex: computed local acceptance, conditional completeness

The D check uses the recursor node returned by the existing admission walk.
It is the exact `StepDGSide` check at that selected node, not a decision of
`∀ node, StepDGSide` or a claim that every admitted group accepts. The raw-D
producer has been factored to consume precisely this node. The old all-node
interfaces remain available. This conservative checker runs at every group;
its refusal does not assert that the group's semantic step is false.

Only the A axis remains a soundness input. Axiom freedom, Premises4 and the
original bounds remain in the tier; axiom coverage is separate RCIC4 work.
`closure_claim = 0`: the literal A input is refuted and is being repaired.
-/

set_option autoImplicit false

namespace Rcic.F3.StepWDApex

open Rcic.Declarative Rcic.Model.PS Rcic.F3 Rcic.F3.PSet Rcic.F3.TierGroup
open Rcic.F3.StepDGOrder Rcic.F3.StepDGCheck Rcic.F3.StepWCheck

/-- Reuse the exact D diagnostic at the node actually selected by admission. -/
def groupCheck (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    Option StepDGRefusal :=
  stepDGRefusalOf K (groupNode hE hfam hctors hrec hmem).val

/-- Exactness is at the selected node; no universal-node equivalence is claimed. -/
theorem groupCheck_pass_iff (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    groupCheck K hE hfam hctors hrec hmem = none ↔
      StepDGSide K (groupNode hE hfam hctors hrec hmem).val :=
  stepDGRefusalOf_none_iff K _

/-- Local self-attack boundary: after the check passes there is no D-cell input.
A-negative groups use raw D directly; A-positive groups retain the A debt. -/
theorem groupStepAt_of_check (P : Premises4) (K : Nat → Nat) (hA : StepAG P K)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hp : groupCheck K hE hfam hctors hrec hmem = none) :
    GroupStepAt P K hE hfam hctors hrec hmem := by
  cases P.dec (∃ node : RecNode E E' f rr rm, PendA node) with
  | isTrue ha => exact hA hE hfam hctors hrec hmem ha
  | isFalse ha =>
      let selected := groupNode hE hfam hctors hrec hmem
      have hs := (groupCheck_pass_iff K hE hfam hctors hrec hmem).mp hp
      intro hAg hB hD IH
      exact gInv_groupRawD_atNode P K hE hfam hctors hrec hmem selected.val selected.property
        (noFunRec_of_not_pendA (fun h => ha ⟨selected.val, h⟩))
        hs.1 hs.2.1 hs.2.2 hAg hB hD IH

/-- The D conditions at this environment and its admitted prefixes. -/
def EnvDChecked (K : Nat → Nat) : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ hE _ _ _ _ => EnvDChecked K hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => EnvDChecked K hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => EnvDChecked K hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => EnvDChecked K hE
  | _, .group _ _ _ _ _ _ _ hE hfam hctors hrec hmem =>
      EnvDChecked K hE ∧ StepDGSide K (groupNode hE hfam hctors hrec hmem).val

/-- Finite D check, at the supplied environment and K. -/
def envCheck (K : Nat → Nat) : {E : ResolvedEnv} → EnvWfT E → Bool
  | _, .empty => true
  | _, .axiom _ _ _ _ hE _ _ _ _ => envCheck K hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => envCheck K hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => envCheck K hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => envCheck K hE
  | _, .group _ _ _ _ _ _ _ hE hfam hctors hrec hmem =>
      envCheck K hE && (groupCheck K hE hfam hctors hrec hmem).isNone

/-- The environment Bool exactly folds the selected-node D conditions. -/
theorem envCheck_pass_iff (K : Nat → Nat) : {E : ResolvedEnv} → (h : EnvWfT E) →
    (envCheck K h = true ↔ EnvDChecked K h)
  | _, .empty => by simp [envCheck, EnvDChecked]
  | _, .axiom _ _ _ _ hE _ _ _ _ => envCheck_pass_iff K hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => envCheck_pass_iff K hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => envCheck_pass_iff K hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => envCheck_pass_iff K hE
  | _, .group _ _ _ _ _ _ _ hE hfam hctors hrec hmem => by
      simp only [envCheck, Bool.and_eq_true, Option.isNone_iff_eq_none, EnvDChecked]
      exact and_congr (envCheck_pass_iff K hE) (groupCheck_pass_iff K hE hfam hctors hrec hmem)

/-- Local check soundness, distinct from universal acceptance. -/
def DCheckSound : Prop :=
  ∀ (K : Nat → Nat) {E : ResolvedEnv} (h : EnvWfT E), envCheck K h = true → EnvDChecked K h

/-- Closed declared-edge producer for D. -/
theorem envCheck_sound : DCheckSound :=
  fun K {_} h hp => (envCheck_pass_iff K h).mp hp

/-- A refusal carries the original D reason at an actual admitted cause node.
It refutes this sufficient check, not the group's semantic soundness. -/
structure EnvRefusal (K : Nat → Nat) {E : ResolvedEnv} (h : EnvWfT E) where
  causeEnv : ResolvedEnv
  admitted : EnvWfT causeEnv
  baseEnv : ResolvedEnv
  f : Nat
  rr : Nat
  rm : CheckedMember
  node : RecNode baseEnv causeEnv f rr rm
  reason : StepDGRefusal
  diagnosed : stepDGRefusalOf K node = some reason
  failed : ¬ EnvDChecked K h

/-- Produce the actual first failing prefix and its computed D reason. -/
def refusalCertificate (K : Nat → Nat) : {E : ResolvedEnv} → (h : EnvWfT E) →
    envCheck K h ≠ true → EnvRefusal K h
  | _, .empty, hn => (hn rfl).elim
  | _, .axiom _ _ _ _ hE _ _ _ _, hn =>
      let c := refusalCertificate K hE hn
      ⟨c.causeEnv, c.admitted, c.baseEnv, c.f, c.rr, c.rm, c.node, c.reason, c.diagnosed, c.failed⟩
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, hn =>
      let c := refusalCertificate K hE hn
      ⟨c.causeEnv, c.admitted, c.baseEnv, c.f, c.rr, c.rm, c.node, c.reason, c.diagnosed, c.failed⟩
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, hn =>
      let c := refusalCertificate K hE hn
      ⟨c.causeEnv, c.admitted, c.baseEnv, c.f, c.rr, c.rm, c.node, c.reason, c.diagnosed, c.failed⟩
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, hn =>
      let c := refusalCertificate K hE hn
      ⟨c.causeEnv, c.admitted, c.baseEnv, c.f, c.rr, c.rm, c.node, c.reason, c.diagnosed, c.failed⟩
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, hn => by
      let h := EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem
      by_cases hb : envCheck K hE = true
      · cases hr : groupCheck K hE hfam hctors hrec hmem with
        | none => exact (hn (by simp [envCheck, hb, hr])).elim
        | some reason =>
            exact ⟨E', h, E, f, rr, rm, (groupNode hE hfam hctors hrec hmem).val,
              reason, hr, fun hc => hn ((envCheck_pass_iff K h).mpr hc)⟩
      · let c := refusalCertificate K hE hb
        exact ⟨c.causeEnv, c.admitted, c.baseEnv, c.f, c.rr, c.rm, c.node, c.reason,
          c.diagnosed, fun hc => c.failed hc.1⟩

/-- The recorded reason is certified to fail StepDGSide at its cause node. -/
theorem EnvRefusal.side_fails (K : Nat → Nat) {E : ResolvedEnv} {h : EnvWfT E}
    (c : EnvRefusal K h) : ¬ StepDGSide K c.node := by
  apply (stepDGRefusalOf_some_iff K c.node).mp
  rw [c.diagnosed]
  exact Option.noConfusion

/-- Every failed Bool produces an admitted cause, exact reason, and failed side. -/
theorem envCheck_refusal_certified (K : Nat → Nat) {E : ResolvedEnv} (h : EnvWfT E)
    (hn : envCheck K h ≠ true) :
    ∃ c : EnvRefusal K h, ¬ StepDGSide K c.node := by
  let c := refusalCertificate K h hn
  exact ⟨c, c.side_fails K⟩

/-- Computed D success or a certified named D refusal. -/
inductive Outcome (K : Nat → Nat) {E : ResolvedEnv} (h : EnvWfT E) where
  | accepted (passed : envCheck K h = true)
  | refused (certificate : EnvRefusal K h)

/-- Total finite D diagnostic for this admitted environment and K. -/
def checkEnv (K : Nat → Nat) {E : ResolvedEnv} (h : EnvWfT E) : Outcome K h :=
  if hp : envCheck K h = true then .accepted hp else .refused (refusalCertificate K h hp)

/-- The generic fold's steps consume local W/D conditions, plus A only. -/
theorem steps_coveredWDChecked (P : Premises4) (K : Nat → Nat) (hA : StepAG P K) :
    GInvSteps P K
      (fun {E : ResolvedEnv} (h : EnvWfT E) => Covered h ∧ EnvWChecked h ∧ EnvDChecked K h)
      (fun {E : ResolvedEnv} (h : EnvWfT E) => BoundG K h ∧ BoundDG K h) where
  stepDef := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH => gInv_singleW P K (Or.inl rfl) hfresh hclA hclv hlvlA hlvlv hv hB.1.2
      (walkG_of_envWChecked P hE hC.1 hC.2.1) IH⟩
  stepThm := fun _ _ _ _ hE hfresh _ hp hclA hclp hlvlA hlvlp hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH => gInv_singleW P K (Or.inr (Or.inl rfl)) hfresh hclA hclp hlvlA hlvlp hp
      hB.1.2 (walkG_of_envWChecked P hE hC.1 hC.2.1) IH⟩
  stepOpq := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH => gInv_singleW P K (Or.inr (Or.inr rfl)) hfresh hclA hclv hlvlA hlvlv hv
      hB.1.2 (walkG_of_envWChecked P hE hC.1 hC.2.1) IH⟩
  stepGrp := fun _ _ _ _ _ _ _ hE hfam hctors hrec hmem hC hB =>
    ⟨⟨hC.1.1, hC.2.1.1, hC.2.2.1⟩, ⟨hB.1.1, hB.2.1⟩, fun IH =>
      groupStepAt_of_check P K hA hE hfam hctors hrec hmem
        ((groupCheck_pass_iff K hE hfam hctors hrec hmem).mpr hC.2.2.2)
        (walkAgree_of_groupWChecked P hE hfam hctors hrec hmem hC.2.1.2) hB.1 hB.2 IH⟩

/-- Original F3 body with both computed checks INSIDE the environment quantifier. -/
def TierF3WDChecked : Prop :=
  Premises4 → ∀ (K : Nat → Nat) (E : ResolvedEnv) (h : EnvWfT E),
    StepWApex.envCheck h = true → envCheck K h = true →
    BoundG K h → BoundDG K h → AxiomFreeEnv' E →
    E.members 0 = some falseFamMember → E.members 1 = some falseRecMemberU →
    ∀ (n : Nat) (e : Expr Nat) (D : HasTyT E n [] e (.const 0 [])),
      LevelsBelow 4 K D → False

/-- F1 plus soundness for environments passing their local W/D checks. -/
def KernelSoundnessTierWDChecked : Prop := Rcic.Apex.TierF1 ∧ TierF3WDChecked

/-- D and W check soundness suffice; no global W hypothesis or D cell occurs. -/
theorem tierF3WDChecked_of_checked
    (hW : StepWApex.EnvCheckSound) (hD : DCheckSound)
    (hA : ∀ (P : Premises4) (K : Nat → Nat), StepAG P K) : TierF3WDChecked := by
  intro P K E h pw pd hB hBDG hAx _h0 h1 n e D hLOK
  have hC : Covered h ∧ EnvWChecked h ∧ EnvDChecked K h :=
    ⟨EnvWfT_axiomFree_covered P h hAx, hW h pw, hD K h pd⟩
  have hI : GInv P K h := gInv_of_steps P K _ _ (steps_coveredWDChecked P K (hA P K))
    (fun _ _ _ _ _ _ _ _ _ hCx => hCx.1) h hC ⟨hB, hBDG⟩
  have hRA := readsOKAlong_envCtxW h (walkG_of_envWChecked P h hC.1 hC.2.1)
    (envCtx h) (fun _ _ => rfl)
  have hF := (faithfulR_envμR P (envCtx h) h hRA).1
  have hIv := hI (envCtx h) (fun _ _ => rfl) _ hF
  have hES := envSound_of P (Efin := E) (fun _ _ hx => hx) hIv.1
    (fun r m hm hk => hIv.2 E (fun _ _ hx => hx) r m hm hk) (fun _ => 0) n
  exact empty_of_falseRec P (hIv.1 1 _ h1) (sound_ty (P.good _ rfl) hES D hLOK ρ0 trivial)

/-- Declared-edge apex: both check bridges are closed; A remains explicit. -/
theorem kernelSoundnessTierWDChecked_of_checked
    (hW : StepWApex.EnvCheckSound) (hD : DCheckSound)
    (hA : ∀ (P : Premises4) (K : Nat → Nat), StepAG P K) : KernelSoundnessTierWDChecked :=
  ⟨Rcic.Apex.tierF1, tierF3WDChecked_of_checked hW hD hA⟩

/-- The W/D-checked apex consumes no StepWHyp, StepDG or StepDGChecked premise. -/
theorem kernelSoundnessTierWDChecked_of_A
    (hA : ∀ (P : Premises4) (K : Nat → Nat), StepAG P K) : KernelSoundnessTierWDChecked :=
  kernelSoundnessTierWDChecked_of_checked StepWApex.envCheck_sound envCheck_sound hA

/-- Completeness/coverage upgrade only: D acceptance upgrades this face to #8420.
This hypothesis is not used by checked soundness and is not asserted globally. -/
theorem wCheckedTier_of_D_complete
    (hD : ∀ (K : Nat → Nat) {E : ResolvedEnv} (h : EnvWfT E), envCheck K h = true)
    (tier : TierF3WDChecked) : StepWApex.TierF3WChecked :=
  fun P K E h pw => tier P K E h pw (hD K h)

/-- The positive D instance: any bound satisfying the measured δ comparison. -/
theorem dr_groupCheck_passes (K : Nat → Nat) (hk : K 2 ≤ K 3) :
    groupCheck K drBaseWfT (fm := drFamMember) (rm := drRecMember) (ctors := [(2, drMkMember)])
      rfl (fun c hc => by simp at hc; subst hc; rfl) rfl drMembersT = none := by
  apply (groupCheck_pass_iff K _ _ _ _ _).mpr
  exact (drSide_iff K _).mpr hk

/-- Actual admitted refusal: global no-refusal is already false for this checker. -/
theorem drKBad_envCheck_refuses : envCheck drKBad drEnvWfT = false := by
  apply Bool.of_not_eq_true
  intro hp
  exact drKBad_side_fails _ ((envCheck_pass_iff drKBad drEnvWfT).mp hp).2

/-- Universal acceptance is completeness work, and its literal form is refuted. -/
theorem not_all_envChecks :
    ¬ (∀ (K : Nat → Nat) {E : ResolvedEnv} (h : EnvWfT E), envCheck K h = true) := by
  intro hall
  have h := hall drKBad drEnvWfT
  rw [drKBad_envCheck_refuses] at h
  exact Bool.noConfusion h

end Rcic.F3.StepWDApex

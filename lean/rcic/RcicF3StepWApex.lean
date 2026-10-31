import rcic.RcicF3StepWGroup

/-!
# W-checked apex: soundness for environments whose exact W check passes

W is checked inside the environment quantifier, rather than assumed globally.
The original admission judgment is unchanged. A refusal identifies an admitted
prefix with a BadSortPair certificate. StepWHyp is used only for completeness.
The separate A/D premises are retained; closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.StepWApex

open Rcic.Declarative Rcic.F3.PSet Rcic.F3.StepWCheck Rcic.F3.StepWGroup
open Rcic.F3.StepWMin Rcic.F3.StepWRefusal

/-- Run the exact group decider at every group of this admitted environment. -/
def envCheck : {E : ResolvedEnv} → EnvWfT E → Bool
  | _, .empty => true
  | _, .axiom _ _ _ _ hE _ _ _ _ => envCheck hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => envCheck hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => envCheck hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => envCheck hE
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem =>
      envCheck hE && (groupRefusal hmem).isNone

/-- Exactness against the original per-environment checked proposition. -/
theorem envCheck_pass_iff : {E : ResolvedEnv} → (h : EnvWfT E) →
    (envCheck h = true ↔ EnvWChecked h)
  | _, .empty => by simp [envCheck, EnvWChecked]
  | _, .axiom _ _ _ _ hE _ _ _ _ => envCheck_pass_iff hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => envCheck_pass_iff hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => envCheck_pass_iff hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => envCheck_pass_iff hE
  | _, .group _ _ _ _ _ _ _ hE hfam hctors hrec hmem => by
      simp only [envCheck, Bool.and_eq_true, Option.isNone_iff_eq_none, EnvWChecked]
      exact and_congr (envCheck_pass_iff hE)
        (groupRefusal_none_iff hE hfam hctors hrec hmem)

/-- Soundness of this check, as distinct from universal acceptance. -/
def EnvCheckSound : Prop :=
  ∀ {E : ResolvedEnv} (h : EnvWfT E), envCheck h = true → EnvWChecked h

/-- Closed bridge from the executable check to the original checked invariant. -/
theorem envCheck_sound : EnvCheckSound :=
  fun h hp => (envCheck_pass_iff h).mp hp

/-- Named refusal, with an actual admitted cause environment and bad-sort evidence.
The cause may be an earlier prefix; no typing transport to the final environment
is asserted. The failed checked proposition belongs to the supplied environment. -/
structure EnvRefusal {E : ResolvedEnv} (h : EnvWfT E) where
  causeEnv : ResolvedEnv
  admitted : EnvWfT causeEnv
  badSortPair : BadSortPair causeEnv
  failed : ¬ EnvWChecked h

/-- Every failed executable check carries the original named W residue. -/
def EnvRefusal.reason {E : ResolvedEnv} {h : EnvWfT E} (_r : EnvRefusal h) : Refusal :=
  .gapSortBound

/-- Extract the certificate from the actual failing group, without choice. -/
def refusalCertificate : {E : ResolvedEnv} → (h : EnvWfT E) →
    envCheck h ≠ true → EnvRefusal h
  | _, .empty, hn => (hn rfl).elim
  | _, .axiom _ _ _ _ hE _ _ _ _, hn =>
      let c := refusalCertificate hE hn
      ⟨c.causeEnv, c.admitted, c.badSortPair, c.failed⟩
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, hn =>
      let c := refusalCertificate hE hn
      ⟨c.causeEnv, c.admitted, c.badSortPair, c.failed⟩
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, hn =>
      let c := refusalCertificate hE hn
      ⟨c.causeEnv, c.admitted, c.badSortPair, c.failed⟩
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, hn =>
      let c := refusalCertificate hE hn
      ⟨c.causeEnv, c.admitted, c.badSortPair, c.failed⟩
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, hn => by
      let h := EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem
      by_cases hb : envCheck hE = true
      · have hr : groupRefusal hmem = some .gapSortBound := by
          rcases groupRefusal_cases hmem with hp | hr
          · exact (hn (by simp [envCheck, hb, hp])).elim
          · exact hr
        exact ⟨E', h, refusal_has_badSortPair hE hfam hctors hrec hmem hr,
          fun hc => hn ((envCheck_pass_iff h).mpr hc)⟩
      · let c := refusalCertificate hE hb
        exact ⟨c.causeEnv, c.admitted, c.badSortPair, fun hc => c.failed hc.1⟩

/-- Every failed check entails a bad-sort certificate in an admitted environment. -/
theorem envCheck_refusal_certified {E : ResolvedEnv} (h : EnvWfT E)
    (hn : envCheck h ≠ true) :
    ∃ Ebad, Nonempty (EnvWfT Ebad) ∧ BadSortPair Ebad := by
  let c := refusalCertificate h hn
  exact ⟨c.causeEnv, ⟨c.admitted⟩, c.badSortPair⟩

/-- Admission-time outcome: a checked success or a named, certified refusal. -/
inductive Outcome {E : ResolvedEnv} (h : EnvWfT E) where
  | accepted (passed : envCheck h = true)
  | refused (certificate : EnvRefusal h)

/-- Total environment diagnostic using the exact finite group checks. -/
def checkEnv {E : ResolvedEnv} (h : EnvWfT E) : Outcome h :=
  if hp : envCheck h = true then .accepted hp else .refused (refusalCertificate h hp)

/-- Completeness only: if StepWHyp holds, no admitted environment is refused. -/
theorem envCheck_complete (hW : StepWHyp) :
    {E : ResolvedEnv} → (h : EnvWfT E) → envCheck h = true
  | _, .empty => rfl
  | _, .axiom _ _ _ _ hE _ _ _ _ => envCheck_complete hW hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => envCheck_complete hW hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => envCheck_complete hW hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => envCheck_complete hW hE
  | _, .group _ _ _ _ _ _ _ hE hfam hctors hrec hmem => by
      have hg := all_groupChecks_iff_hyp.mpr hW hE hfam hctors hrec hmem
      simp only [envCheck, envCheck_complete hW hE, hg, Option.isNone_none, Bool.and_self]

/-- Universal acceptance is exactly the original completeness conjecture. -/
theorem all_envChecks_iff_hyp :
    (∀ {E : ResolvedEnv} (h : EnvWfT E), envCheck h = true) ↔ StepWHyp := by
  constructor
  · intro hp
    apply all_groupChecks_iff_hyp.mp
    intro E E' f rr fm rm ctors hE hfam hctors hrec hmem
    exact (groupRefusal_none_iff hE hfam hctors hrec hmem).mpr
      ((envCheck_pass_iff _).mp (hp (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem))).2
  · exact envCheck_complete

/-- A certified refusal contradicts completeness, rather than soundness. -/
theorem EnvRefusal.refutes_hyp {E : ResolvedEnv} {h : EnvWfT E}
    (r : EnvRefusal h) : ¬ StepWHyp :=
  fun hW => r.failed (envCheck_sound h (envCheck_complete hW h))

/-- The original F3 tier body, restricted only by this environment's computed W
check. All bounds, axiom-freedom and Premises4 are retained verbatim. -/
def TierF3WChecked : Prop :=
  Premises4 → ∀ (K : Nat → Nat) (E : ResolvedEnv) (h : EnvWfT E),
    envCheck h = true → BoundG K h → BoundDG K h → AxiomFreeEnv' E →
    E.members 0 = some falseFamMember → E.members 1 = some falseRecMemberU →
    ∀ (n : Nat) (e : Expr Nat) (D : HasTyT E n [] e (.const 0 [])),
      LevelsBelow 4 K D → False

/-- F1 plus soundness for every environment whose W check passes. -/
def KernelSoundnessTierWChecked : Prop := Rcic.Apex.TierF1 ∧ TierF3WChecked

/-- Consume checked W inside the environment quantifier. No global W premise. -/
theorem tierF3WChecked_of_AD
    (hA : ∀ (P : Premises4) (K : Nat → Nat), TierGroup.StepAG P K)
    (hD : ∀ (P : Premises4) (K : Nat → Nat), TierGroup.StepDG P K) :
    TierF3WChecked := by
  intro P K E h hp
  exact StepWCheck.tierF3WChecked_of_ADG hA hD P K E h ((envCheck_pass_iff h).mp hp)

/-- Declared-edge apex face: its W bridge is supplied by the closed
`envCheck_sound` theorem. The bridge is about each computed check, not universal
acceptance. A/D remain independent inputs. -/
theorem kernelSoundnessTierWChecked_of_checked
    (hW : EnvCheckSound)
    (hA : ∀ (P : Premises4) (K : Nat → Nat), TierGroup.StepAG P K)
    (hD : ∀ (P : Premises4) (K : Nat → Nat), TierGroup.StepDG P K) :
    KernelSoundnessTierWChecked := by
  refine ⟨Rcic.Apex.tierF1, ?_⟩
  intro P K E h hp
  exact StepWCheck.tierF3WChecked_of_ADG hA hD P K E h (hW h hp)

/-- W-checked apex. Soundness has no StepWHyp or AllGroupChecks input.
A/D remain separate debts, including the known refutation of literal A. -/
theorem kernelSoundnessTierWChecked_of_AD
    (hA : ∀ (P : Premises4) (K : Nat → Nat), TierGroup.StepAG P K)
    (hD : ∀ (P : Premises4) (K : Nat → Nat), TierGroup.StepDG P K) :
    KernelSoundnessTierWChecked :=
  kernelSoundnessTierWChecked_of_checked envCheck_sound hA hD

/-- Only the completeness upgrade to the unchecked tier needs StepWHyp. -/
theorem uncheckedTier_of_complete (hW : StepWHyp) (h : TierF3WChecked) :
    Rcic.Apex.TierF3Uncond :=
  fun P K E hE => h P K E hE (envCheck_complete hW hE)

end Rcic.F3.StepWApex

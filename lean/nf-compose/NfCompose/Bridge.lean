import NfCompose.Basic
import algorithms.ResiduaRCCStepExecModel

/-!
Bridge between `Residua.RCC.StepExecModel` and the pinned `ExecModel`.

`StepExecModel.Model.active` is a `Bool` field. The pinned `activeClass` is
`∃ r, q r = c`. `ActiveAgrees` is that these two predicates are the same.
`profile_to_pinned` and `profile_of_pinned` are the two directions.
`badStep` is a `Profile` whose `active` flag is false on the one class in the
image of `q`, so the pinned residue law fails. No `Classical.choice`: the
`Bool` decider is an argument of `ofPinned`.
-/

namespace NfCompose

open MSTNecessityExecModelMWE
open Residua.RCC.StepExecModel

abbrev Step0 := Model.{0, 0, 0, 0, 0}

def toPinned (M : Step0) : ExecModel where
  Raw := M.Raw
  Class := M.Class
  Rep := M.Rep
  Residue := M.Residue
  Outcome := M.Outcome
  q := M.q
  evalRaw := M.evalRaw
  evalClass := M.evalClass
  admissible := M.admissible
  rho := M.rho
  sigma := M.sigma

def ActiveAgrees (M : Step0) : Prop :=
  ∀ c : M.Class, M.active c = true ↔ activeClass (toPinned M) c

def ofPinned (M : ExecModel) (active : M.Class → Bool)
    (_agree : ∀ c, active c = true ↔ activeClass M c) : Step0 where
  Raw := M.Raw
  Class := M.Class
  Rep := M.Rep
  Residue := M.Residue
  Outcome := M.Outcome
  q := M.q
  evalRaw := M.evalRaw
  evalClass := M.evalClass
  active := active
  admissible := M.admissible
  rho := M.rho
  sigma := M.sigma

theorem profile_to_pinned {M : Step0} (p : Profile M) (h : ActiveAgrees M) :
    hasMSTNFProfile (toPinned M) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r
    exact p.quotient_factorization r
  · intro c rep hs
    exact p.representative_implies_admissible c rep hs
  · intro c hc hadm
    have ha : M.active c = true := (h c).mpr hc
    rcases p.residue_totality c ha hadm with ⟨_, hres⟩
    intro hnone
    cases hres.symm.trans hnone
  · intro c hc hadm
    have ha : M.active c = true := (h c).mpr hc
    rcases p.representative_precision c ha hadm with ⟨_, hrep⟩
    intro hnone
    cases hrep.symm.trans hnone

theorem profile_of_pinned (M : ExecModel) (active : M.Class → Bool)
    (agree : ∀ c, active c = true ↔ activeClass M c) (h : hasMSTNFProfile M) :
    Profile (ofPinned M active agree) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r
    exact h.1 r
  · intro c rep hs
    exact h.2.1 c rep hs
  · intro c ha hadm
    have hc : activeClass M c := (agree c).mp ha
    have hrho := h.2.2.1 c hc hadm
    cases hr : M.rho c with
    | none => exact absurd hr hrho
    | some res => exact ⟨res, hr⟩
  · intro c ha hadm
    have hc : activeClass M c := (agree c).mp ha
    have hsig := h.2.2.2 c hc hadm
    cases hs : M.sigma c with
    | none => exact absurd hs hsig
    | some rep => exact ⟨rep, hs⟩

/-! `badStep`: Tier-1 `Profile` with `active` constantly false. The only class
is in the image of `q`, not admissible, and has no residue. -/

inductive BadRaw | only
  deriving DecidableEq

inductive BadClass | c
  deriving DecidableEq

inductive BadRep | r
  deriving DecidableEq

inductive BadResidue | e
  deriving DecidableEq

inductive BadOutcome | o
  deriving DecidableEq

def badStep : Step0 where
  Raw := BadRaw
  Class := BadClass
  Rep := BadRep
  Residue := BadResidue
  Outcome := BadOutcome
  q := fun _ => .c
  evalRaw := fun _ => .o
  evalClass := fun _ => .o
  active := fun _ => false
  admissible := fun _ => false
  rho := fun _ => none
  sigma := fun _ => none

theorem badStep_profile : Profile badStep where
  quotient_factorization := fun _ => rfl
  representative_implies_admissible := by
    intro _ _ h
    simp [badStep] at h
  residue_totality := by
    intro _ ha _
    simp [badStep] at ha
  representative_precision := by
    intro _ ha _
    simp [badStep] at ha

theorem badStep_active_class : activeClass (toPinned badStep) .c :=
  ⟨.only, rfl⟩

theorem badStep_not_pinned : ¬ hasMSTNFProfile (toPinned badStep) := by
  intro h
  exact h.2.2.1 .c badStep_active_class rfl rfl

def badStepRho : Option BadResidue := badStep.rho .c

def badStepClass : BadClass := badStep.q .only

#guard decide (badStep.active .c = false)
#guard decide (badStep.admissible .c = false)
#guard decide (badStepRho = none)
#guard decide (badStepClass = .c)

end NfCompose

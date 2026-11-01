import rcic.RcicF3NormDataGroup
import rcic.RcicF3NormADataChecked

/-!
# Checked apex reduced to the explicit normalized DATA small-frame producer

The domain is exactly the existing checked DATA step: the selected node
has a uniformly Type-valued family, the original group has an existential
PendA witness, and the unchanged selected-node D group check accepts.
SmallFrameAt retains every original GroupStepAt context and asks only for
one admissible closed candidate of that actual normalized descriptor.

The DATA consumers produce the group step from this candidate. The already
proved checked dispatcher then supplies the unchanged W/D-checked F3 and
machine-plus-F3 kernel tier. The universal frame predicate below is still
an explicit unpaid input. It is not produced or proved non-refutable here;
unchecked NormRole.StepAG and its full domain are unchanged. No additional
executable check is introduced. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormAFrameChecked
open Rcic.Declarative Rcic.Model.PS

/-- The remaining universal size-production premise on precisely the
previous checked DATA domain. This definition contains no new check. -/
def FramesADataChecked (P : Premises4) (K : Nat → Nat) : Prop :=
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
      NormDataGroup.SmallFrameAt P K hE hfam hctors hrec hmem

/-- Actual DATA constructor and recursor producers discharge the semantic
group-step consumer. The unchanged D check pays the parameter equality. -/
theorem stepADataChecked_of_frames (P : Premises4) (K : Nat → Nat)
    (hFrames : FramesADataChecked P K) : NormADataChecked.StepADataChecked P K := by
  intro E E' f rr fm rm ctors hE hfam hctors hrec hmem hType hPend hp
  exact NormDataGroup.group_step_of_check P K hE hfam hctors hrec hmem hType hp
    (hFrames hE hfam hctors hrec hmem hType hPend hp)

theorem group_step_of_check (P : Premises4) (K : Nat → Nat)
    (hFrames : FramesADataChecked P K)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hp : Rcic.F3.StepWDApex.groupCheck K hE hfam hctors hrec hmem = none) :
    NormRole.GroupStepAt P K hE hfam hctors hrec hmem :=
  NormADataChecked.group_step_of_check P K (stepADataChecked_of_frames P K hFrames)
    hE hfam hctors hrec hmem hp

theorem invariant_of_checks (P : Premises4) (K : Nat → Nat)
    (hFrames : FramesADataChecked P K) {E : ResolvedEnv} (hW : EnvWfT E)
    (pw : Rcic.F3.StepWApex.envCheck hW = true)
    (pd : Rcic.F3.StepWDApex.envCheck K hW = true)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E) :
    NormRole.GInv P K hW :=
  NormADataChecked.invariant_of_checks P K (stepADataChecked_of_frames P K hFrames)
    hW pw pd hB hD hAx

theorem envSound_of_checks (P : Premises4) (K : Nat → Nat)
    (hFrames : FramesADataChecked P K) {E : ResolvedEnv} (hW : EnvWfT E)
    (pw : Rcic.F3.StepWApex.envCheck hW = true)
    (pd : Rcic.F3.StepWDApex.envCheck K hW = true)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E)
    (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (NormRole.table P hW)) σ K E n :=
  NormADataChecked.envSound_of_checks P K (stepADataChecked_of_frames P K hFrames)
    hW pw pd hB hD hAx σ n

/-- The F3 statement itself, including both checks, both bounds, axiom
freedom and the distinguished False prefix, remains literally unchanged. -/
theorem tierF3WDChecked_of_frames
    (hFrames : ∀ (P : Premises4) (K : Nat → Nat), FramesADataChecked P K) :
    Rcic.F3.StepWDApex.TierF3WDChecked :=
  NormADataChecked.tierF3WDChecked_of_AData
    (fun P K => stepADataChecked_of_frames P K (hFrames P K))

/-- Conditional machine/F3 composition. The universal normalized DATA
frame producer is the named remaining semantic input of this theorem. -/
theorem kernelSoundnessTierWDChecked_of_frames
    (hFrames : ∀ (P : Premises4) (K : Nat → Nat), FramesADataChecked P K) :
    Rcic.F3.StepWDApex.KernelSoundnessTierWDChecked :=
  NormADataChecked.kernelSoundnessTierWDChecked_of_AData
    (fun P K => stepADataChecked_of_frames P K (hFrames P K))

end Rcic.F3.PSet.NormAFrameChecked

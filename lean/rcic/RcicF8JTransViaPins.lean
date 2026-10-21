import rcic.RcicF8JTransVia
import rcic.RcicF8JTransPins

/-!
J5aVia runs the landed non-reflexive trans fixture through a genuine inserted
target context.  The two controls distinguish an available target context proof
from a source context proof, and a certificate with the same step header from
the certificate for the actual emitted step.  closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.J5aVia.Pins
open PEqTProofFront PEqLeafTPropPins F8Occurrences

/-- The source is empty, while the correspondence target is nonempty. -/
def via : CtxWfVia emptyEnv 0 [] :=
  .wk (.assumption (.sort .zero)) 0 (.ofWf pinCtxWf)

theorem via_target : via.target = pinCtx := rfl
theorem via_target_ne_source : via.target ≠ [] := by
  intro h
  cases h

/-- This witness really uses `CtxWfVia.wk`; it is not any `ofWf` witness. -/
theorem via_ne_ofWf (hΓ : CtxWfT emptyEnv 0 []) :
    via ≠ CtxWfVia.ofWf hΓ := by
  intro h
  exact via_target_ne_source (congrArg CtxWfVia.target h)

/-- The D request is made at the image of the original middle `p`. -/
def targetD (su : F8A2Support.SortUnique emptyEnv 0) :=
  dProcWf EnvWfT.empty su via.wf
    (via.ρ.star J5a.Pins.first.valley.right)
    (via.ρ.star J5a.Pins.second.valley.left)

theorem target_D_center (su : F8A2Support.SortUnique emptyEnv 0) :
    (targetD su).1 = via.ρ.map J5a.Pins.third := rfl

/-- The retained local wrapper calls the canonical source D object. -/
def sourceD (su : F8A2Support.SortUnique emptyEnv 0) :=
  DProofVia.dProc EnvWfT.empty su via
    J5a.Pins.first.valley.right J5a.Pins.second.valley.left
    (by exact ⟨True.intro, True.intro⟩) (by exact ⟨True.intro, True.intro⟩)

theorem actual_source_D (su : F8A2Support.SortUnique emptyEnv 0) :
    (sourceD su).out = J5a.Pins.groundD := rfl

theorem actual_center_corresponds (su : F8A2Support.SortUnique emptyEnv 0) :
    via.ρ.map (sourceD su).out.1 = (targetD su).1 :=
  (sourceD su).center

/-- Alignment covers the complete actual closing spines and the payload read
at every emitted step, including the terminal source typing fields. -/
def actual_D_reads (su : F8A2Support.SortUnique emptyEnv 0) :
    DProofVia.Reads via.ρ (sourceD su).out.2.1.spine (targetD su).2.1.spine ×
      DProofVia.Reads via.ρ (sourceD su).out.2.2.spine (targetD su).2.2.spine :=
  (sourceD su).reads

/-- In this run the only target closing step is precisely the forward image
of the source `proofIndexJoin` producer, with its complete payload. -/
theorem target_D_left_spine (su : F8A2Support.SortUnique emptyEnv 0) :
    (targetD su).2.1.spine =
      DSpine.tail (.base (via.ρ.par J5a.Pins.closingStep))
        (.refl (via.ρ.evTy J5a.Pins.secondRead.rightTy)) := rfl

theorem target_D_right_spine (su : F8A2Support.SortUnique emptyEnv 0) :
    (targetD su).2.2.spine =
      DSpine.refl (via.ρ.evTy J5a.Pins.secondRead.rightTy) := rfl

/-- The source-side result is produced by the actual Via recursion. -/
def result (su : F8A2Support.SortUnique emptyEnv 0) :
    J3.Result EnvWfT.empty J5a.Pins.roots J5a.Pins.input :=
  buildFragment EnvWfT.empty su J5a.Pins.roots via J5a.Pins.input
    J5a.Pins.admissible_input J5a.Pins.cert

theorem input_nonreflexive : q ≠ J5a.Pins.third := J5a.Pins.q_ne_third

set_option maxHeartbeats 800000 in
theorem actual_source_valley (su : F8A2Support.SortUnique emptyEnv 0) :
    (result su).valley = J5a.Pins.groundValley := by
  let first : FragmentResult EnvWfT.empty J5a.Pins.roots J5a.Pins.h₁ :=
    ⟨J5a.Pins.first, True.intro, True.intro, True.intro⟩
  let second : FragmentResult EnvWfT.empty J5a.Pins.roots J5a.Pins.h₂ :=
    ⟨J5a.Pins.second, ⟨True.intro, True.intro⟩, True.intro⟩
  unfold result buildFragment
  simp only [J5a.Pins.input, J5a.Pins.h₁, J5a.Pins.h₂, J5a.Pins.pqAt,
    J5a.Pins.psAt, J5a.Pins.pq, J5a.Pins.ps, build]
  change transValley EnvWfT.empty su via first second = J5a.Pins.groundValley
  have hd : (callD EnvWfT.empty su via first second).out = J5a.Pins.groundD :=
    actual_source_D su
  simp only [transValley, hd]
  rfl

/-- Transport the actual certificate family along equality of the complete
source valley, retaining the exact emitted star as its index. -/
def transportLeftTiles
    (r : J3.Result EnvWfT.empty J5a.Pins.roots J5a.Pins.input)
    (v : Valley J5a.Pins.roots [] q J5a.Pins.third aliasP)
    (hv : r.valley = v) :
    J3.Certified J5a.Pins.roots [Jd.cv J5a.Pins.input]
      (v.left.val J5a.Pins.cl J5a.Pins.ss) :=
  Eq.mp (congrArg (fun w : Valley J5a.Pins.roots [] q J5a.Pins.third aliasP =>
    J3.Certified J5a.Pins.roots [Jd.cv J5a.Pins.input]
      (w.left.val J5a.Pins.cl J5a.Pins.ss)) hv) r.leftTiles

/-- Project the actual certificate only after its whole source valley has
been identified with the known fixture. -/
def leftCertificate (su : F8A2Support.SortUnique emptyEnv 0) :
    J3.StepCertificate J5a.Pins.roots [Jd.cv J5a.Pins.input] J5a.Pins.tile.step :=
  (transportLeftTiles (result su) J5a.Pins.groundValley (actual_source_valley su)).1

theorem actual_source_center (su : F8A2Support.SortUnique emptyEnv 0) :
    (result su).valley.N = J5a.Pins.third := by
  rw [actual_source_valley]
  rfl

theorem actual_source_step (su : F8A2Support.SortUnique emptyEnv 0) :
    (leftCertificate su).tile.step = J5a.Pins.tile.step := rfl

theorem actual_source_caller (su : F8A2Support.SortUnique emptyEnv 0) :
    (leftCertificate su).tile.X = [Jd.cv J5a.Pins.input] :=
  J3.StepCertificate.tile_removed (leftCertificate su)

theorem actual_occurrence_live (su : F8A2Support.SortUnique emptyEnv 0) :
    (occurrences (leftCertificate su).tile.step).length = 1 := by
  rw [actual_source_step]
  exact J5a.Pins.closing_occurrence_live

theorem actual_source_inventory (su : F8A2Support.SortUnique emptyEnv 0) :
    (result su).valley.leaves.length = 18 := by
  rw [actual_source_valley]
  exact J5a.Pins.ground_eighteen

theorem actual_dispatch (su : F8A2Support.SortUnique emptyEnv 0) :
    (dispatchVia EnvWfT.empty su J5a.Pins.roots via J5a.Pins.input
      J5a.Pins.cert).isSome = true :=
  dispatchVia_coverage EnvWfT.empty su J5a.Pins.roots via J5a.Pins.input J5a.Pins.cert

/-! The context mutant carries a real proof, but labels its context as the
source solely because that proof is available through `via`. -/

structure WfCandidate where
  context : LCtx
  wf : CtxWfT emptyEnv 0 context

def borrowedTarget : WfCandidate := ⟨via.target, via.wf⟩
def actualSource : WfCandidate := ⟨[], CtxWfT.nil⟩

def WeakSourceWf (c : WfCandidate) : Prop := Nonempty (CtxWfT emptyEnv 0 c.context)
def ExactSourceWf (c : WfCandidate) : Prop := c.context = []

theorem actual_source_wf_accepts : ExactSourceWf actualSource := rfl
theorem mutant_source_wf_accepts : WeakSourceWf borrowedTarget := ⟨borrowedTarget.wf⟩
theorem exact_source_wf_refuses : ¬ ExactSourceWf borrowedTarget := via_target_ne_source

/-! The certificate mutant adds an identity type-conversion wrapper.  It is
valid typed data with the same context/endpoints/index, but its raw step is not
the proof-index step that the Via worker actually emits. -/

def reusedCertificate : J3.StepCertificate J5a.Pins.roots [Jd.cv J5a.Pins.input]
    (.conv [] q J5a.Pins.third aliasP aliasP J5a.Pins.tile.step (.refl [] aliasP)) :=
  J3.StepCertificate.reindex
    (J5a.baseCertificate J5a.Pins.cl J5a.Pins.ss [Jd.cv J5a.Pins.input]
      J5a.Pins.closingStep) (.refl [] aliasP)

def reusedTile : DTile J5a.Pins.roots := reusedCertificate.tile
def SameHeader (t₁ t₂ : DTile J5a.Pins.roots) : Prop := J5a.Pins.SameHeader t₁ t₂
def ExactEmittedStep (t : DTile J5a.Pins.roots) : Prop := HEq t.step J5a.Pins.tile.step

theorem mutant_certificate_accepts : SameHeader reusedTile J5a.Pins.tile :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem exact_certificate_refuses : ¬ ExactEmittedStep reusedTile := by
  intro h
  have he := eq_of_heq h
  cases he

theorem live_mutants :
    (WeakSourceWf borrowedTarget ∧ ¬ ExactSourceWf borrowedTarget) ∧
      (SameHeader reusedTile J5a.Pins.tile ∧ ¬ ExactEmittedStep reusedTile) :=
  ⟨⟨mutant_source_wf_accepts, exact_source_wf_refuses⟩,
    ⟨mutant_certificate_accepts, exact_certificate_refuses⟩⟩

end Rcic.Declarative.F8Measure.J5aVia.Pins

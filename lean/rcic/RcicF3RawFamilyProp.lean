import rcic.RcicF3RawFamilyInduction
/-! Correctly sized proof-family intersections. A uniform Prop result gets
an explicit small closed candidate. Literal positive constructor transport
remains a production input; no universal StepAG theorem is asserted here.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamilyProp
open Rcic.Declarative PiIndex RawFamily
abbrev proofTop : Frame := fun _ _ => tv True

theorem candidate (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (h0 : ∀ vs, evalTotal (σOf vs) fd.resLevel = 0) :
    Admissible fd proofTop ∧ Closed P μ fd proofTop := by
  constructor
  · intro vs i
    rw [h0 vs, if_pos rfl]
    exact ⟨(stageW4 P 0).prop_mem (fun _ hz => (mem_tv.mp hz).2),
      fun _ hz => (mem_tv.mp hz).2⟩
  · intro vs i z hz
    obtain ⟨j, ps, xs, hp, hx, hs, hi, hz⟩ := hz
    rw [h0 vs, if_pos rfl] at hz
    exact mem_tv.mpr ⟨True.intro, hz⟩
/-- At literal Prop signatures the raw role is unconditionally correctly sized. -/
theorem admissible (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (h0 : ∀ vs, evalTotal (σOf vs) fd.resLevel = 0) :
    Admissible fd (frame P μ fd) := by
  exact frame_admissible P μ fd ⟨proofTop, candidate P μ fd h0⟩

/-- Positive constructor transport suffices for proof-family closure;
no small-domain, choice or closed-candidate input is supplied by the caller. -/
theorem closed (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (h0 : ∀ vs, evalTotal (σOf vs) fd.resLevel = 0)
    (hmono : ConstructorMono P μ fd) : Closed P μ fd (frame P μ fd) := by
  exact frame_closed_of_mono P μ fd ⟨proofTop, candidate P μ fd h0⟩ hmono
end Rcic.F3.PSet.RawFamilyProp


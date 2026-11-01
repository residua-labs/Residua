import rcic.RcicF3RawFamilyGlobalSize
import rcic.RcicF3NormSmallFrameAttack

/-!
# Global-size necessity composed with the new admitted W candidate

The general assembler's produced W candidate witnesses the global class.
It bounds the original normalized-role intersection, whose one-fibre
smallness also reproduces global existence through the necessity theorem.
The same-P composition retains the new leaf/height-omega and DATA group
producer witness. No empty-class or universal-failure claim is made.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamilyGlobalSizeAttack
open Rcic.Declarative PiIndex RawFamily
open NormPendAW (plan)

theorem one_fibre_small (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    frame P μ (EvalPlanNormal.fd plan) [] (key [tyv fxS]) ∈ W4 1 := by
  have h := frame_admissible P μ (EvalPlanNormal.fd plan)
    ⟨NormSmallFrame.candidate P μ plan, NormSmallFrameAttack.component P μ⟩
      [] (key [tyv fxS])
  have hr : (EvalPlanNormal.fd plan).resLevel = .succ .zero :=
    congrArg FamData.resLevel NormPendAW.normalized_descriptor
  rw [hr] at h
  exact h.1

/-- Invoke necessity on the small fibre bounded by the new candidate. -/
theorem global_from_one_fibre (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    ∃ C : Frame, Admissible (EvalPlanNormal.fd plan) C ∧
      Closed P μ (EvalPlanNormal.fd plan) C := by
  have hr : (EvalPlanNormal.fd plan).resLevel = .succ .zero :=
    congrArg FamData.resLevel NormPendAW.normalized_descriptor
  apply RawFamilyGlobalSize.global_candidate_of_small_fibre P μ
    (EvalPlanNormal.fd plan) [] (key [tyv fxS])
  · rw [hr]
    decide
  · rw [hr]
    exact one_fibre_small P μ

def Witness (P : Premises4) : Prop :=
  NormSmallFrameAttack.Witness P ∧
  (∀ μ, frame P μ (EvalPlanNormal.fd plan) [] (key [tyv fxS]) ∈ W4 1) ∧
  (∀ μ, ∃ C : Frame, Admissible (EvalPlanNormal.fd plan) C ∧
    Closed P μ (EvalPlanNormal.fd plan) C)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormSmallFrameAttack.component_witness P, one_fibre_small P, global_from_one_fibre P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.RawFamilyGlobalSizeAttack

import rcic.RcicF3RawFamilyMinor
import rcic.RcicF3RawFamilyIHBuilderAttack
import rcic.RcicF3PiRawMinorAttack

/-!
# Original PendA W input-spine non-vacuity

All premises of the admitted-spine producer are supplied at the original
W field, the genuine height-omega constructor, and an extra universe-1
motive. The accumulated constructor expression is the stored node reference.
This is a produced minor-input spine, not complete recursor MemberSound.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.RawFamilyMinorAttack
open Rcic.Declarative PiIndex RawFamily RawFamilyIHBuilderAttack
open PendAWBridge (fd)

def ending : Expr Nat := .app (.const 4 []) (.bvar 1)
def accumulator : Expr Nat := .app (.const 6 []) (.bvar 1)

theorem raw_field_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    x P ∈ Ed (model P μ) (den (model P μ) σ (push [tyv fxS] ρ0) PendAW.field) := by
  have h := field_mem P μ
  change x P ∈ Ed (model P μ) (den (model P μ) σ
    (vcons (x P) (vcons (motive P μ) (push [tyv fxS] ρ0)))
    (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 0 1 PendAW.field))) at h
  rw [den_lift01, den_lift01] at h
  exact h

theorem field_instances : InstOK env σ (fun _ => 0) PendAW.field := by
  simpa only [InstOK, constInsts_lift] using checks.2.1

theorem w_inputs (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    ∃ out, PiRawMinor.Inputs (model P μ) σ env 16 1 (.bvar 0) accumulator
      [.recursive 1] (Rcic.Declarative.lift 0 1 (policyPi [PendAW.field] ending))
      (push [motive P μ] (push [tyv fxS] ρ0))
      [x P] [x P, ihAtN (fun y => y) 1 (x P)] out := by
  apply RawFamilyMinor.inputs_of_admitted P μ fd (frame P μ fd)
    (RawWFrame.raw_admissible P μ) σ (fun _ => 0) 0 PendAWLim.Typed.bounded
    RawFamilyViewAttack.w_family_free (by decide)
    (.param 0) [tyv fxS] [motive P μ] rfl (motive P μ) (fun y => y)
    (fun _ _ h => h) (motive_mem P μ) env 0 type_facts (sound P μ) checks.2.2
    16 1 [.recursive 1] [PendAW.field] ending (.bvar 0) accumulator [x P]
  · change fieldShapesFuel env 16 4 0 1 0 1 [PendAW.field] = some [.recursive 1]
    simp only [fieldShapesFuel, checks.1, Option.map_some']
  · intro A hA
    cases List.mem_singleton.mp hA
    exact field_instances
  · exact ⟨raw_field_mem P μ, True.intro⟩
  · rfl
  · intro i y hp _ hy
    exact map_mem P μ i y hp hy

/-- The actual full input spine is inhabited while the original finite-stage
family still rejects its constructor. The premise is only Premises4 data. -/
theorem w_component_witness (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) :
    (∃ out, PiRawMinor.Inputs (model P μ) σ env 16 1 (.bvar 0) accumulator
      [.recursive 1] (Rcic.Declarative.lift 0 1 (policyPi [PendAW.field] ending))
      (push [motive P μ] (push [tyv fxS] ρ0))
      [x P] [x P, ihAtN (fun y => y) 1 (x P)] out) ∧
      fxZW P ∉ El (fapps (famLim P μ fd []) [tyv fxS]) ∧
      σ 0 ≠ σOf [] 0 := by
  exact ⟨w_inputs P μ, (RawWFrame.heightOmega_gap P μ).2, extra_level.2.2⟩

/-- Literal non-refutability of this inhabited input-spine component. -/
theorem w_component_nonrefutable (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) :
    ¬ ((∃ out, PiRawMinor.Inputs (model P μ) σ env 16 1 (.bvar 0) accumulator
      [.recursive 1] (Rcic.Declarative.lift 0 1 (policyPi [PendAW.field] ending))
      (push [motive P μ] (push [tyv fxS] ρ0))
      [x P] [x P, ihAtN (fun y => y) 1 (x P)] out) → (Premises4 → False)) := by
  intro h
  exact h (w_inputs P μ) P

end Rcic.F3.PSet.RawFamilyMinorAttack

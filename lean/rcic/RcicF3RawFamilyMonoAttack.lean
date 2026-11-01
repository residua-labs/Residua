import rcic.RcicF3RawFamilyMono
import rcic.RcicF3RawFamilyInductionAttack
/-! The generic normalized constructor theorem at the exact typed PendA W
signature, retaining its height-omega inhabitant. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamilyMonoAttack
open Rcic.Declarative PiValueRule RawFamily PiIndex
open PendAWBridge (fd)
def wFields (j : Fin fd.ctors.length) : List FieldSpec :=
  if j.val = 0 then [] else [.recursive [.bvar 0] [.bvar 1]]
theorem generic_W (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    ConstructorMono P μ fd ∧
      CtorAt P μ fd (frame P μ fd) [] (key [tyv fxS]) (fxZW P) ∧
      fxZW P ∉ El (fapps (famLim P μ fd []) [tyv fxS]) := by
  have hm : ConstructorMono P μ fd := by
    apply constructorMono_normalized P μ fd [] wFields
    · intro A hA
      cases List.mem_singleton.mp hA
      rfl
    · intro ⟨j, hj⟩
      cases j with
      | zero => rfl
      | succ j => cases j with
        | zero => rfl
        | succ j => exact False.elim (by change j + 2 < 2 at hj; omega)
    · intro j
      unfold wFields
      split
      · trivial
      · exact ⟨by intro A hA; cases List.mem_singleton.mp hA; rfl,
          by intro A hA; cases List.mem_singleton.mp hA; rfl, rfl, trivial⟩
    · intro ⟨j, hj⟩ A hA
      cases j with
      | zero => exact False.elim (List.not_mem_nil A hA)
      | succ j => cases j with
        | zero => exact False.elim (List.not_mem_nil A hA)
        | succ j => exact False.elim (by change j + 2 < 2 at hj; omega)
    · intro vs; rfl
  have hc := frame_closed_of_mono P μ fd
    ⟨RawWFrame.candidate P μ, RawWFrame.candidate_admissible P μ,
      RawWFrame.candidate_closed P μ⟩ hm
  refine ⟨hm, ?_, (RawWFrame.heightOmega_gap P μ).2⟩
  apply frame_dense P μ fd (RawWFrame.raw_admissible P μ) hc hm [] (key [tyv fxS]) _
  exact mem_congr_right
    (apply_ofFrame_ed P μ fd (frame P μ fd) (RawWFrame.raw_admissible P μ)
      [] [tyv fxS] (PendAWBridge.argsFit P μ pempty)) (RawWFrame.heightOmega_gap P μ).1
end Rcic.F3.PSet.RawFamilyMonoAttack

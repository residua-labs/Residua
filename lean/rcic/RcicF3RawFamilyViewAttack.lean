import rcic.RcicF3RawFamilyIH
import rcic.RcicF3RawFamilyInductionAttack
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamilyViewAttack
open Rcic.Declarative PiIndex RawFamily
open PendAWBridge (fd)
theorem w_family_free :
    ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false := by
  intro e he
  change e ∈ [Expr.sort (.succ .zero)] at he
  rcases List.mem_singleton.mp he with rfl
  rfl

theorem heightOmega_actual (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    let M := mkM P (table P μ fd (frame P μ fd))
    fxZW P ∈ Ed M (fapps (M.μ fd.fref []) [tyv fxS]) ∧
    fxZW P ∉ El (fapps (famLim P μ fd []) [tyv fxS]) := by
  dsimp only
  have h := apply_updated_mem_iff P μ fd (frame P μ fd)
    (RawWFrame.raw_admissible P μ) w_family_free [] [tyv fxS] rfl (fxZW P)
  dsimp only at h
  refine ⟨h.mpr ⟨PendAWBridge.argsFit P (table P μ fd (frame P μ fd)) pempty, ?_⟩,
    (RawWFrame.heightOmega_gap P μ).2⟩
  exact mem_congr_right
    (apply_ofFrame_ed P μ fd (frame P μ fd) (RawWFrame.raw_admissible P μ)
      [] [tyv fxS] (PendAWBridge.argsFit P μ pempty))
    (RawWFrame.heightOmega_gap P μ).1
theorem invalid_key_refused (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    let M := mkM P (table P μ fd (frame P μ fd))
    ∀ z, z ∉ Ed M (fapps (M.μ fd.fref []) [pempty]) := by
  dsimp only
  intro z hz
  have h := apply_updated_mem_iff P μ fd (frame P μ fd)
    (RawWFrame.raw_admissible P μ) w_family_free [] [pempty] rfl z
  dsimp only at h
  have hh := (h.mp hz).1.1
  change pempty ∈ Ed (mkM P (table P μ fd (frame P μ fd))) (tyv (U W4 1)) at hh
  exact pempty_not_mem_U4 P 1
    (mem_congr_right (ed_tyv _ (U4_dich 1)) hh)
theorem omega_field (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    graphOf (fxDomBig P) (fxhW P) ∈
      Ed (mkM P (table P μ fd (frame P μ fd)))
        (den (mkM P (table P μ fd (frame P μ fd))) fxσ PendAWBridge.rp PendAW.field) := by
  apply mem_congr_right
    (RawWFrame.field_read P μ (frame P μ fd) (RawWFrame.raw_admissible P μ)).symm
  refine graph_mem_piSet (B := fun _ => frame P μ fd [] (key [tyv fxS]))
    (fun _ _ _ => Equiv.rfl) _ ?_
  intro i
  rw [fx_hW_beta P i]
  apply mem_congr_right (RawWFrame.raw_fibre P μ).symm
  apply PendAFamily.finite_sub P μ
  exact mem_congr_right (PendAWBridge.unionEq P μ).symm (fxT_mem_iUnionN P _)
theorem omega_prefix (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    let M := mkM P (table P μ fd (frame P μ fd))
    ∀ p, RawFamilyRec.paramKey 1
      ((tel M (σOf []) [.bvar 0] [.bvar 1] PendAWBridge.rp).result p) = key [tyv fxS] := by
  dsimp only
  apply PiLeafParams.result_parameters _ _ [.bvar 0] [.bvar 1] PendAWBridge.rp [tyv fxS]
  intro xs hx
  cases xs with
  | nil => exact False.elim hx
  | cons a xs =>
    cases xs with
    | nil => rfl
    | cons b xs => exact False.elim hx.2
theorem wrong_parameter_refused :
    RawFamilyRec.paramKey 1 (key [tyv fxS]) ≠ key [pempty] := by
  intro h
  have he := (key_eq_iff [tyv fxS] [pempty]).mp h
  exact tyv_ne_pempty fxS he.1
theorem omega_ih (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    let M := mkM P (table P μ fd (frame P μ fd))
    ihAtN (fun x => x) 1 (graphOf (fxDomBig P) (fxhW P)) ∈
      Ed M ((tel M (σOf []) [.bvar 0] [.bvar 1] PendAWBridge.rp).erasedIHType M
        (fun i _ => frame P μ fd [] i) (graphOf (fxDomBig P) (fxhW P))) := by
  dsimp only
  exact RawFamilyIH.ih_mem_at_parameters P μ fd (frame P μ fd)
    (RawWFrame.raw_admissible P μ) w_family_free [] (by decide)
    [] rfl [.bvar 0] [.bvar 1] rfl PendAWBridge.rp [tyv fxS] (omega_prefix P μ)
    (fun i _ => frame P μ fd [] i)
    (fun i _ => admissible_dich (RawWFrame.raw_admissible P μ) [] i)
    (fun x => x) (fun _ _ h => h) (fxZW P) (graphOf (fxDomBig P) (fxhW P))
    (fun _ _ _ _ hy => hy) (omega_field P μ) (memT_dataVal (by simp [fxZW]))
end Rcic.F3.PSet.RawFamilyViewAttack

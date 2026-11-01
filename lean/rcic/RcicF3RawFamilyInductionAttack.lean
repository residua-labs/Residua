import rcic.RcicF3RawFamilyInduction
import rcic.RcicF3RawFamilyGroupAttack
/-! Generic indexed closure, induction and constructor inversion at the exact PendA W descriptor, including its height-omega member. The generic production inputs are paid here; arbitrary admitted signatures remain open. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Rcic.F3.PSet.RawFamilyInductionAttack
open Rcic.Declarative PiIndex RawFamily
open PendAWBridge (fd)
theorem w_mono (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    ConstructorMono P μ fd := by
  intro C D hC hD hsub vs i z hz
  obtain ⟨j, ps, xs, hp, hx, hs, hi, hz⟩ := hz
  cases ps with
  | nil => exact False.elim hp
  | cons a ps =>
    cases ps with
    | cons b bs => exact False.elim hp.2
    | nil =>
      have ha : a ∈ U W4 1 := mem_congr_right
        (ed_tyv (mkM P (table P μ fd C)) (U4_dich 1)) hp.1
      have hpD : TelFits (mkM P (table P μ fd D)) (σOf vs) fd.params ρ0 [a] := by
        refine ⟨?_, trivial⟩
        exact mem_congr_right (ed_tyv (mkM P (table P μ fd D)) (U4_dich 1)).symm ha
      cases j with
      | mk j hj =>
        cases j with
        | zero =>
          cases xs with
          | cons x xs => exact False.elim hx
          | nil => exact ⟨⟨0, by decide⟩, [a], [], hpD, trivial, trivial, hi, hz⟩
        | succ j =>
          cases j with
          | succ j => exact False.elim (by change j + 2 < 2 at hj; omega)
          | zero =>
            cases xs with
            | nil => exact False.elim hx
            | cons x xs =>
              cases xs with
              | cons y ys => exact False.elim hx.2
              | nil =>
                have hxC : x ∈ piSet (Ed (mkM P μ) a) (fun _ => C [] (key [a])) :=
                  mem_congr_right (RawWGeneral.field_read P μ C hC a ha) hx.1
                have hxD : x ∈ Ed (mkM P (table P μ fd D))
                    (den (mkM P (table P μ fd D)) fxσ (push [a] ρ0) PendAW.field) :=
                  mem_congr_right (RawWGeneral.field_read P μ D hD a ha).symm
                    (piSet_sub (B₁ := fun _ => C [] (key [a]))
                      (B₂ := fun _ => D [] (key [a]))
                      (fun _ _ _ => Equiv.rfl) (fun _ _ _ => Equiv.rfl)
                      (fun _ => hsub [] (key [a])) x hxC)
                have hsD : SmallAlong (mkM P (table P μ fd D)) (σOf vs)
                    (W4 1) [PendAW.field] (push [a] ρ0) [x] := by
                  refine ⟨?_, trivial⟩
                  exact mem_congr_left (RawWGeneral.field_read P μ D hD a ha).symm
                    ((stageW4 P 1).pi (fun _ _ _ => Equiv.rfl)
                      (ed_mem_W4_of_mem_U P (mkM P μ) (by decide) (by decide) ha)
                      (fun _ _ => (hD [] (key [a])).1))
                exact ⟨⟨1, by decide⟩, [a], [x], hpD, ⟨hxD, trivial⟩, hsD, hi, hz⟩
/-- Elementary replay of generic closure with both production inputs paid. -/
theorem w_closed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Closed P μ fd (frame P μ fd) := by
  exact frame_closed_of_mono P μ fd
    ⟨RawWFrame.candidate P μ, RawWFrame.candidate_admissible P μ,
      RawWFrame.candidate_closed P μ⟩ (w_mono P μ)

/-- Elementary replay of generic inversion, uniform in all parameters. -/
theorem w_dense (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    ∀ vs i z, z ∈ frame P μ fd vs i → CtorAt P μ fd (frame P μ fd) vs i z := by
  exact frame_dense P μ fd (RawWFrame.raw_admissible P μ) (w_closed P μ) (w_mono P μ)

/-- The generic induction rule is available at the actual W descriptor. -/
theorem w_induction (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (Q : List Nat → Index.{4} → PSet.{4} → Prop)
    (hQ : ∀ vs i z z', Equiv z z' → Q vs i z → Q vs i z')
    (hstep : ∀ vs i z, CtorAt P μ fd (restrict (frame P μ fd) Q) vs i z → Q vs i z) :
    ∀ vs i z, z ∈ frame P μ fd vs i → Q vs i z := by
  exact frame_induction P μ fd (RawWFrame.raw_admissible P μ)
    (w_closed P μ) (w_mono P μ) Q hQ hstep

/-- The new inversion applies to the height-omega value rejected by famLim. -/
theorem heightOmega_constructor (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    CtorAt P μ fd (frame P μ fd) [] (key [tyv fxS]) (fxZW P) ∧
      fxZW P ∉ El (fapps (famLim P μ fd []) [tyv fxS]) := by
  refine ⟨w_dense P μ [] (key [tyv fxS]) _ ?_, (RawWFrame.heightOmega_gap P μ).2⟩
  exact mem_congr_right
    (apply_ofFrame_ed P μ fd (frame P μ fd) (RawWFrame.raw_admissible P μ)
      [] [tyv fxS] (PendAWBridge.argsFit P μ pempty))
    (RawWFrame.heightOmega_gap P μ).1

end Rcic.F3.PSet.RawFamilyInductionAttack

import rcic.RcicF3PiTupleStage
import rcic.RcicF3RawFamilyInduction
/-! Literal constructor monotonicity for normalized independent signatures.
Dependent tuples keep their actual values; erased higher-order fields
supply both membership transport and stage transport. This module does
not identify raw hidden syntax with normalized fields or produce a small
closed frame for every signature. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamily
open Rcic.Declarative PiValueRule
 theorem ctorAt_mono_normalized (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ls : List Level)
    (spec : Fin fd.ctors.length → List FieldSpec)
    (hP : ∀ A ∈ fd.params, occursConst fd.fref A = false)
    (hF : ∀ j, (fd.ctors.get j).1 = (spec j).map (fieldExpr fd.fref ls))
    (hCLEAN : ∀ j, Clean fd.fref (fd.params ++ fd.indices).length (spec j))
    (hR : ∀ j, ∀ A ∈ (fd.ctors.get j).2, occursConst fd.fref A = false)
    (C D : Frame) (hC : Admissible fd C) (hD : Admissible fd D) (hsub : FrameSub C D)
    (vs : List Nat)
    (hL : evalTotal (σOf (ls.map (evalTotal (σOf vs)))) fd.resLevel =
      evalTotal (σOf vs) fd.resLevel) (i : PiIndex.Index.{4}) (z : PSet.{4}) :
    CtorAt P μ fd C vs i z → CtorAt P μ fd D vs i z := by
  intro hz
  obtain ⟨j, ps, xs, hp, hx, hs, hi, hz⟩ := hz
  let X := ofFrame P μ fd C
  let Y := ofFrame P μ fd D
  have hpD : TelFits (mkM P (upd μ fd.fref Y)) (σOf vs) fd.params ρ0 ps := by
    apply TelFits_mono fd.params (M₁ := mkM P (upd μ fd.fref X)) _ ρ0 ps hp
    intro A hA ρ x hx
    change x ∈ Ed (mkM P μ) (den (mkM P (upd μ fd.fref X)) (σOf vs) ρ A) at hx
    change x ∈ Ed (mkM P μ) (den (mkM P (upd μ fd.fref Y)) (σOf vs) ρ A)
    rw [← PiIndependent.den_free P μ fd.fref X Y (σOf vs) A (hP A hA) ρ]
    exact hx
  have hxD : TelFits (mkM P (upd μ fd.fref Y)) (σOf vs) (fd.ctors.get j).1
      (push ps ρ0) xs := by
    rw [hF j] at hx ⊢
    exact PiTupleMono.fits_mono P μ fd.fref (fd.params ++ fd.indices).length
      X Y (σOf vs) ls
      (fun ys hy => apply_ofFrame_sub P μ fd C D hC hD hsub _ ys hy)
      (spec j) (hCLEAN j) _ xs hx
  have hsD : if evalTotal (σOf vs) fd.resLevel = 0 then True else
      SmallAlong (mkM P (upd μ fd.fref Y)) (σOf vs)
        (W4 (evalTotal (σOf vs) fd.resLevel)) (fd.ctors.get j).1 (push ps ρ0) xs := by
    split
    · trivial
    · rename_i h0
      rw [if_neg h0] at hs
      rw [hF j] at hx hs ⊢
      have h0' : evalTotal (σOf (ls.map (evalTotal (σOf vs)))) fd.resLevel ≠ 0 :=
        fun h => h0 (hL.symm.trans h)
      exact PiTupleMono.smallAlong P μ fd.fref (fd.params ++ fd.indices).length
        X Y (σOf vs) ls _ (stageW4 P _)
        (fun ys hy hm => (apply_ofFrame_data P μ fd C hC _ h0' ys hy).2 pempty hm Equiv.rfl)
        (fun ys hy => by
          have h := (apply_ofFrame_data P μ fd D hD _ h0' ys hy).1
          rw [hL] at h
          exact h) (spec j) (hCLEAN j) _ xs hx hs
  have he : (fd.ctors.get j).2.map (den (mkM P (upd μ fd.fref X)) (σOf vs)
      (push xs (push ps ρ0))) =
      (fd.ctors.get j).2.map (den (mkM P (upd μ fd.fref Y)) (σOf vs)
        (push xs (push ps ρ0))) := by
    apply List.map_congr_left
    intro A hA
    exact PiIndependent.den_free P μ fd.fref X Y (σOf vs) A (hR j A hA) _
  change i = PiIndex.key (ps ++ (fd.ctors.get j).2.map
    (den (mkM P (upd μ fd.fref X)) (σOf vs) (push xs (push ps ρ0)))) at hi
  rw [he] at hi
  exact ⟨j, ps, xs, hpD, hxD, hsD, hi, hz⟩
/-- Composition over all universe instances; these are syntax and level
compatibility conditions on the normalized signature, not an apex premise. -/
 theorem constructorMono_normalized (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ls : List Level)
    (spec : Fin fd.ctors.length → List FieldSpec)
    (hP : ∀ A ∈ fd.params, occursConst fd.fref A = false)
    (hF : ∀ j, (fd.ctors.get j).1 = (spec j).map (fieldExpr fd.fref ls))
    (hCLEAN : ∀ j, Clean fd.fref (fd.params ++ fd.indices).length (spec j))
    (hR : ∀ j, ∀ A ∈ (fd.ctors.get j).2, occursConst fd.fref A = false)
    (hL : ∀ vs, evalTotal (σOf (ls.map (evalTotal (σOf vs)))) fd.resLevel =
      evalTotal (σOf vs) fd.resLevel) : ConstructorMono P μ fd := by
  intro C D hC hD hsub vs i z hz
  exact ctorAt_mono_normalized P μ fd ls spec hP hF hCLEAN hR
    C D hC hD hsub vs (hL vs) i z hz
end Rcic.F3.PSet.RawFamily

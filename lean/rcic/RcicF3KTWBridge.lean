import rcic.RcicF3KTWG

/-!
# F3 S7 KT-2c (abstract): a W-shaped operator on the big universe has a small least fixed point

`Φ` acts on `PSet.{max u v}`; `S : GSig.{u}` is a guarded W-signature one universe down.
`WShaped Φ S` says `Φ` computed at a lifted small set is the lift of the signature's operator:
`Φ (lift X) ≈ lift (gphi S X)` for `X : PSet.{u}`.

Given `Φ` respects `≈`... (only `mono` is used below) and `WShaped Φ S`:

- `lift_gSet_fixed`: `Φ (lift (gSet S)) ≈ lift (gSet S)`;
- `lift_gSet_least`: `lift (gSet S)` is below every `Y` closed under `Φ` (`Y` need not be small);
  the induction picks, at each tree, the small subset `lift (mk (br s) (decG ∘ g))` of `Y`, so no
  choice is used;
- `small_lift_gSet`: it is small.

So the fibre of an operator of this shape is the least fixed point *and* lies in the universe one
down.  Theory-agnostic (ADR #8005 §7b): only `WShaped` mentions the model.  closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u v

namespace PSet

/-- `Φ` at lifted small sets is the lift of the signature's operator. -/
structure WShaped (Φ : PSet.{max u v} → PSet.{max u v}) (S : GSig.{u}) : Prop where
  at_lift : ∀ X : PSet.{u}, Equiv (Φ (lift.{u, v} X)) (lift.{u, v} (gphi S X))

theorem lift_gSet_fixed {Φ : PSet.{max u v} → PSet.{max u v}} {S : GSig.{u}} (hW : WShaped Φ S) :
    Equiv (Φ (lift.{u, v} (gSet S))) (lift.{u, v} (gSet S)) :=
  (hW.at_lift (gSet S)).trans (lift_equiv.{u, v} (gphi_gSet_equiv S))

theorem lift_gSet_least {Φ : PSet.{max u v} → PSet.{max u v}} {S : GSig.{u}} (hW : WShaped Φ S)
    (hmono : ∀ X Y : PSet.{max u v}, Sub X Y → Sub (Φ X) (Φ Y))
    {Y : PSet.{max u v}} (hY : Sub (Φ Y) Y) : Sub (lift.{u, v} (gSet S)) Y := by
  have key : ∀ w : GT S, ValidW S w → lift.{u, v} (decG S w) ∈ Y := by
    intro w hw
    induction hw with
    | sup s g hg hok ih =>
      let X₀ : PSet.{u} := mk (S.br s) (fun b => decG S (g b))
      have hsub : Sub (lift.{u, v} X₀) Y := by
        intro z hz
        obtain ⟨y, ⟨b, hb⟩, hzy⟩ := mem_lift.{u, v}.mp hz
        exact mem_congr_left ((lift_equiv.{u, v} hb).trans hzy.symm) (ih b)
      have hmem : S.code s (fun b => X₀.Func b) ∈ gphi S X₀ :=
        ⟨⟨s, fun b => b, hok⟩, Equiv.refl _⟩
      have hl : lift.{u, v} (decG S (.sup s g)) ∈ Φ (lift.{u, v} X₀) :=
        mem_congr_right (hW.at_lift X₀).symm ((lift_mem_lift.{u, v}).mpr hmem)
      exact hY _ (hmono _ _ hsub _ hl)
  intro z hz
  obtain ⟨y, ⟨⟨w, hw⟩, hy⟩, hzy⟩ := mem_lift.{u, v}.mp hz
  exact mem_congr_left ((lift_equiv.{u, v} hy).trans hzy.symm) (key w hw)

theorem small_lift_gSet (S : GSig.{u}) : Small.{u, v} (lift.{u, v} (gSet S)) :=
  small_lift.{u, v} (gSet S)

end PSet

end Rcic.F3

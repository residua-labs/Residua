import rcic.RcicAnnLR3CandidateSubstitution

/-!
# Boundary: no uniform generic element for a type variable of `Type 0`

The open-realizer design asks every candidate to contain the reflected
neutrals (CR3). In a term model this is one class: the neutral terms. In the
raw-value model with level-tagged type images it cannot be one class. Both
`Prop` and `Prop → Prop` are codes at level 1, i.e. instantiations of a type
variable `X : Type 0`, and no value belongs to both of their relations
(`no_uniform_generic`). A member of the first is a level-zero type image,
whose observations are two-argument tag spines. Applying it gives a
three-argument spine, which is not a type image, so it is not a member of the
second.

So CR3 cannot be a fixed class of values. The reflected element of a type
variable must depend on the type it is instantiated with: the reflection is
type-directed, and to be continuous it may test only positive observations of
the type image. All premises are constructed. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.GenericReflectionBoundary

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER
open CandidateTowerProbe CandidateCodeSystem CandidateSubstitution

/-- `Prop → Prop`, a code at level 1. -/
def propToProp : GCode 1 := .pi (.univ 0) (.univ 0)

theorem propToProp_kinded : Kinded [] propToProp := ⟨trivial, trivial⟩

theorem no_uniform_generic :
    Kinded [] (GCode.univ 0) ∧ Kinded [] propToProp ∧
    ¬ ∃ g : Value, El σ0 ρ0 (GCode.univ 0) g g ∧ El σ0 ρ0 propToProp g g := by
  refine ⟨trivial, propToProp_kinded, ?_⟩
  rintro ⟨g, ⟨c, hc, hg, _⟩, hpi⟩
  obtain ⟨i, p, hobs⟩ := (closed_level c (kinded_closed c [] hc)).2
  have hgobs := (hg _).mpr hobs
  let x : Value := image σ0 (GCode.neutral 0 0)
  have hx : El σ0 ρ0 (GCode.univ 0) x x := ⟨GCode.neutral 0 0, (by decide : (0 : Nat) ≠ 11),
    ValueEq.refl _, ValueEq.refl _⟩
  have happ := (el_raw (GCode.univ 0) _ σ0 _ _ _).mp (hpi.2.2 x x hx botRel (botRel_satFor x x)).1
  obtain ⟨d, hd, h1, _⟩ := happ
  have hsm : SortMember (some 0) (NeutralPi.applyValue g x) :=
    sortMember_congr h1.symm (closed_level d (kinded_closed d [] hd)).1
  have hxb : x .bot := NativeMemberValues.value_bot _ _
  have hbad : NeutralPi.applyValue g x (.spine 10 [.spine (levelRef i) [], p, .bot]) :=
    Or.inr (Or.inr ⟨10, [.spine (levelRef i) [], p], .bot, rfl, hgobs, hxb⟩)
  have ht := hsm _ hbad
  cases ht

end Rcic.Declarative.Ann.LR3.GenericReflectionBoundary

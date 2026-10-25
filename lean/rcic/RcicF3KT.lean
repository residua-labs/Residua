import rcic.RcicF3Small

/-!
# F3 S7 KT-1: the least fixed point of a monotone operator on a set's subsets

For a set `U` and an operator `Φ` that respects `≈`, maps subsets of `U` into
`U` and is monotone on them, `lfp U Φ` is the intersection of the subsets of
`U` closed under `Φ` (`sep` over `U` of membership in every such subset).

- `lfp_least`: below every closed subset;
- `lfp_closed` / `lfp_dense` / `lfp_fixed`: `Φ (lfp U Φ) ≈ lfp U Φ`
  (Knaster–Tarski);
- `lfp_induction`: a property closed under `Φ` on the fixed point holds on
  it.

No ordinals: the intersection ranges over `𝒫 U`, a set.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u

namespace PSet

/-- `X ⊆ Y`, elementwise. -/
def Sub (X Y : PSet.{u}) : Prop := ∀ z, z ∈ X → z ∈ Y

/-- The conditions on the operator. -/
structure KTOp (U : PSet.{u}) (Φ : PSet.{u} → PSet.{u}) : Prop where
  resp : ∀ X Y, Equiv X Y → Equiv (Φ X) (Φ Y)
  into : ∀ X, Sub X U → Sub (Φ X) U
  mono : ∀ X Y, Sub X Y → Sub Y U → Sub (Φ X) (Φ Y)

/-- Membership in every subset of `U` closed under `Φ`. -/
def InAllClosed (U : PSet.{u}) (Φ : PSet.{u} → PSet.{u}) (z : PSet.{u}) : Prop :=
  ∀ X, X ∈ powerset U → Sub (Φ X) X → z ∈ X

/-- The least fixed point. -/
def lfp (U : PSet.{u}) (Φ : PSet.{u} → PSet.{u}) : PSet.{u} := sep (InAllClosed U Φ) U

theorem mem_lfp {U : PSet.{u}} {Φ : PSet.{u} → PSet.{u}} {z : PSet.{u}} :
    z ∈ lfp U Φ ↔ z ∈ U ∧ InAllClosed U Φ z := by
  constructor
  · intro h
    obtain ⟨i, hp, he⟩ := mem_sep.mp h
    exact ⟨mem_sep_subset h, fun X hX hc => mem_congr_left he (hp X hX hc)⟩
  · rintro ⟨hU, hp⟩
    obtain ⟨i, hi⟩ := hU
    exact mem_sep.mpr ⟨i, fun X hX hc => mem_congr_left hi.symm (hp X hX hc), hi⟩

theorem lfp_sub (U : PSet.{u}) (Φ : PSet.{u} → PSet.{u}) : Sub (lfp U Φ) U := fun _ h => (mem_lfp.mp h).1

theorem lfp_least {U : PSet.{u}} {Φ : PSet.{u} → PSet.{u}} {X : PSet.{u}} (hX : Sub X U) (hc : Sub (Φ X) X) :
    Sub (lfp U Φ) X := fun _ h => (mem_lfp.mp h).2 X (mem_powerset.mpr hX) hc

theorem lfp_closed {U : PSet.{u}} {Φ : PSet.{u} → PSet.{u}} (hΦ : KTOp U Φ) : Sub (Φ (lfp U Φ)) (lfp U Φ) := by
  intro z hz
  refine mem_lfp.mpr ⟨hΦ.into _ (lfp_sub U Φ) z hz, fun X hX hc => ?_⟩
  have hXU : Sub X U := mem_powerset.mp hX
  exact hc z (hΦ.mono _ _ (lfp_least hXU hc) hXU z hz)

theorem lfp_dense {U : PSet.{u}} {Φ : PSet.{u} → PSet.{u}} (hΦ : KTOp U Φ) : Sub (lfp U Φ) (Φ (lfp U Φ)) :=
  lfp_least (hΦ.into _ (lfp_sub U Φ))
    (hΦ.mono _ _ (lfp_closed hΦ) (lfp_sub U Φ))

/-- **Knaster–Tarski**: the least fixed point is a fixed point. -/
theorem lfp_fixed {U : PSet.{u}} {Φ : PSet.{u} → PSet.{u}} (hΦ : KTOp U Φ) : Equiv (Φ (lfp U Φ)) (lfp U Φ) :=
  ext fun z => ⟨lfp_closed hΦ z, lfp_dense hΦ z⟩

/-- **Induction on the least fixed point**: a property, respecting `≈`, that
holds at every element `Φ` gives from the fixed point's elements with the
property, holds on the whole fixed point. -/
theorem lfp_induction {U : PSet.{u}} {Φ : PSet.{u} → PSet.{u}} (hΦ : KTOp U Φ) (Q : PSet.{u} → Prop)
    (hQ : ∀ z z', Equiv z z' → Q z → Q z')
    (hstep : ∀ z, z ∈ Φ (sep Q (lfp U Φ)) → Q z) : ∀ z, z ∈ lfp U Φ → Q z := by
  have hsub : Sub (sep Q (lfp U Φ)) (lfp U Φ) := fun _ h => mem_sep_subset h
  have hsubU : Sub (sep Q (lfp U Φ)) U := fun z h => lfp_sub U Φ z (hsub z h)
  have hc : Sub (Φ (sep Q (lfp U Φ))) (sep Q (lfp U Φ)) := by
    intro z hz
    have hzl : z ∈ lfp U Φ := lfp_closed hΦ z (hΦ.mono _ _ hsub (lfp_sub U Φ) z hz)
    obtain ⟨i, hi⟩ := hzl
    exact mem_sep.mpr ⟨i, hQ _ _ hi.symm (hstep z hz), hi⟩
  intro z hz
  obtain ⟨i, hq, he⟩ := mem_sep.mp (lfp_least hsubU hc z hz)
  exact hQ _ _ he hq

end PSet

end Rcic.F3

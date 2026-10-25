import rcic.RcicF3PSet

/-!
# F3 carrier: lifting and universe stages

- `lift : PSet.{u} → PSet.{max u v}` re-indexes by `ULift`; it preserves and
  reflects `≈` (`lift_equiv_iff`) and membership (`mem_lift`).
- `univ.{u} : PSet.{u+1}` collects every `PSet.{u}` set (lifted): its members
  are exactly the sets `≈` to a lifted `PSet.{u}` set (`mem_univ`), the
  *small* sets. This is the universe stage `U (u+1)` of the F3 model
  (`research/rcic/routec-f3/F3_PLAN.md`, D2); Lean's universe `u+1` plays
  the inaccessible. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u v w

namespace PSet

/-- Re-index a set by `ULift`, landing in a larger universe. -/
def lift : PSet.{u} → PSet.{max u v}
  | mk α f => mk (ULift.{v} α) (fun a => lift (f a.down))

theorem lift_equiv : {x y : PSet.{u}} → Equiv x y → Equiv (lift.{u, v} x) (lift.{u, v} y)
  | mk α f, mk β g, ⟨h1, h2⟩ =>
      ⟨fun a => let ⟨b, hb⟩ := h1 a.down; ⟨⟨b⟩, lift_equiv hb⟩,
       fun b => let ⟨a, ha⟩ := h2 b.down; ⟨⟨a⟩, lift_equiv ha⟩⟩

theorem equiv_of_lift : {x y : PSet.{u}} → Equiv (lift.{u, v} x) (lift.{u, v} y) → Equiv x y
  | mk α f, mk β g, ⟨h1, h2⟩ =>
      ⟨fun a => let ⟨b, hb⟩ := h1 ⟨a⟩; ⟨b.down, equiv_of_lift hb⟩,
       fun b => let ⟨a, ha⟩ := h2 ⟨b⟩; ⟨a.down, equiv_of_lift ha⟩⟩

theorem lift_equiv_iff {x y : PSet.{u}} : Equiv (lift.{u, v} x) (lift.{u, v} y) ↔ Equiv x y :=
  ⟨equiv_of_lift, lift_equiv⟩

theorem lift_func (x : PSet.{u}) (i : (lift.{u, v} x).Idx) :
    ∃ j : x.Idx, (lift.{u, v} x).Func i = lift.{u, v} (x.Func j) := by
  cases x with
  | mk α f => exact ⟨i.down, rfl⟩

/-- Membership in a lifted set. -/
theorem mem_lift {x : PSet.{u}} {z : PSet.{max u v}} :
    z ∈ lift.{u, v} x ↔ ∃ y, y ∈ x ∧ Equiv z (lift.{u, v} y) := by
  cases x with
  | mk α f =>
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨f a.down, ⟨a.down, Equiv.refl _⟩, ha.symm⟩
    · rintro ⟨y, ⟨a, ha⟩, hz⟩
      exact ⟨⟨a⟩, (lift_equiv ha).trans hz.symm⟩

theorem lift_mem_lift {x y : PSet.{u}} : lift.{u, v} y ∈ lift.{u, v} x ↔ y ∈ x := by
  constructor
  · intro h
    obtain ⟨y', hy', he⟩ := mem_lift.mp h
    exact mem_congr_left (equiv_of_lift he).symm hy'
  · intro h
    exact mem_lift.mpr ⟨y, h, Equiv.refl _⟩

/-- The universe stage: every `PSet.{u}` set, lifted. -/
def univ : PSet.{u + 1} := mk PSet.{u} (fun x => lift.{u, u + 1} x)

/-- The members of `univ.{u}` are exactly the small sets. -/
theorem mem_univ {z : PSet.{u + 1}} : z ∈ univ.{u} ↔ ∃ x : PSet.{u}, Equiv z (lift.{u, u + 1} x) :=
  ⟨fun ⟨x, h⟩ => ⟨x, h.symm⟩, fun ⟨x, h⟩ => ⟨x, h.symm⟩⟩

/-- A small set's members are small: `univ` is transitive. -/
theorem univ_transitive {z w : PSet.{u + 1}} (hz : z ∈ univ.{u}) (hw : w ∈ z) : w ∈ univ.{u} := by
  obtain ⟨x, hx⟩ := mem_univ.mp hz
  obtain ⟨y, _, hy⟩ := mem_lift.mp (mem_congr_right hx hw)
  exact mem_univ.mpr ⟨y, hy⟩

/-- The previous stage is a member: `univ.{u}` lifted is small at `u+1`. -/
theorem univ_mem_univ : lift.{u + 1, u + 2} univ.{u} ∈ univ.{u + 1} :=
  mem_univ.mpr ⟨univ.{u}, Equiv.refl _⟩

end PSet

end Rcic.F3

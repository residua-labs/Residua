import rcic.RcicF3Table

/-!
# F3 S5b-1: countable unions in the stages

The bound of a recursive family's fibre is a union over the natural numbers.
`iUnionN f` is that union, `small_iUnionN` its smallness from small pieces
(by the choice premise, one representative per piece), and `stageN_W4` the
closure of every stage of the height-4 table.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

namespace PSet

universe u v T

/-- The union of a sequence of sets. -/
def iUnionN (f : Nat → PSet.{T}) : PSet.{T} := mk (Σ n, (f n).Idx) (fun p => (f p.1).Func p.2)

theorem mem_iUnionN {f : Nat → PSet.{T}} {z : PSet.{T}} : z ∈ iUnionN f ↔ ∃ n, z ∈ f n := by
  constructor
  · rintro ⟨⟨n, i⟩, h⟩
    exact ⟨n, i, h⟩
  · rintro ⟨n, i, h⟩
    exact ⟨⟨n, i⟩, h⟩

theorem iUnionN_congr {f g : Nat → PSet.{T}} (h : ∀ n, Equiv (f n) (g n)) : Equiv (iUnionN f) (iUnionN g) :=
  ext fun _ => ⟨fun hz => by
      obtain ⟨n, hn⟩ := mem_iUnionN.mp hz
      exact mem_iUnionN.mpr ⟨n, mem_congr_right (h n) hn⟩,
    fun hz => by
      obtain ⟨n, hn⟩ := mem_iUnionN.mp hz
      exact mem_iUnionN.mpr ⟨n, mem_congr_right (h n).symm hn⟩⟩

theorem lift_iUnionN (f : Nat → PSet.{u}) : Equiv (lift.{u, v} (iUnionN f)) (iUnionN fun n => lift.{u, v} (f n)) :=
  ext fun z => ⟨fun hz => by
      obtain ⟨y, hy, hzy⟩ := (mem_lift.{u, v}).mp hz
      obtain ⟨n, hn⟩ := mem_iUnionN.mp hy
      exact mem_iUnionN.mpr ⟨n, mem_congr_left hzy.symm ((lift_mem_lift.{u, v}).mpr hn)⟩,
    fun hz => by
      obtain ⟨n, hn⟩ := mem_iUnionN.mp hz
      obtain ⟨y, hy, hzy⟩ := (mem_lift.{u, v}).mp hn
      exact mem_congr_left hzy.symm ((lift_mem_lift.{u, v}).mpr (mem_iUnionN.mpr ⟨n, hy⟩))⟩

/-- A union of a sequence of small sets is small. -/
theorem small_iUnionN (ch : Choice.{u}) {f : Nat → PSet.{max u v}} (hf : ∀ n, Small.{u, v} (f n)) :
    Small.{u, v} (iUnionN f) := by
  let y : Nat → PSet.{u} := fun n => (ch (fun y => Equiv (f n) (lift.{u, v} y)) (hf n)).1
  have hy : ∀ n, Equiv (f n) (lift.{u, v} (y n)) := fun n => (ch (fun y => Equiv (f n) (lift.{u, v} y)) (hf n)).2
  exact ⟨iUnionN y, (iUnionN_congr hy).trans (lift_iUnionN.{u, v} y).symm⟩

/-- A stage closed under unions of sequences. -/
def StageN (W : PSet.{T}) : Prop := ∀ f : Nat → PSet.{T}, (∀ n, f n ∈ W) → iUnionN f ∈ W

theorem stageN_univIn (ch : Choice.{u}) : StageN (univIn.{u, v}) := fun _ hf =>
  mem_univIn.mpr (small_iUnionN ch fun n => mem_univIn.mp (hf n))

theorem stageN_W4 (c0 : Choice.{0}) (c1 : Choice.{1}) (c2 : Choice.{2}) (c3 : Choice.{3}) :
    ∀ k, StageN (W4 k)
  | 0 => stageN_univIn.{3, 4} c3
  | 1 => stageN_univIn.{0, 4} c0
  | 2 => stageN_univIn.{1, 4} c1
  | 3 => stageN_univIn.{2, 4} c2
  | _ + 4 => stageN_univIn.{3, 4} c3

end PSet

end Rcic.F3

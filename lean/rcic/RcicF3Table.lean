import rcic.RcicF3Stage
import rcic.RcicF3Small

/-!
# F3 S6b: the universe table from Lean's universes

- `stage_univIn`: given the choice premise at `u`, the set of all (lifted)
  `PSet.{u}` sets is a `Stage`;
- `univIn_mem_univIn`: each such stage is an element of the next one;
- `chain4` / `good4`: the table of height 4, inside `PSet.{4}`
  (`W k = univIn.{k-1, 4}` for `k = 1 … 4`), satisfies `Good` up to 4.

The level count is the relative-consistency price: R-CIC derivations whose
universe levels stay below `N` are interpreted with `N` nested Lean
universes above the carrier's base (one inaccessible per stage). Larger
literal heights are the same construction with more rows.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u v w

namespace PSet

theorem lift_pempty : Equiv (lift.{u, v} (pempty : PSet.{u})) pempty :=
  ext fun z => ⟨fun hz => by
      obtain ⟨y, hy, _⟩ := (mem_lift.{u, v}).mp hz
      exact (not_mem_pempty hy).elim,
    fun hz => (not_mem_pempty hz).elim⟩

theorem lift_lift : (x : PSet.{u}) →
    Equiv (lift.{max u v, w} (lift.{u, v} x)) (lift.{u, max v w} x)
  | mk α f => ⟨fun a => ⟨⟨a.down.down⟩, lift_lift (f a.down.down)⟩,
      fun b => ⟨⟨⟨b.down⟩⟩, lift_lift (f b.down)⟩⟩

theorem small_of_mem_small {x y : PSet.{max u v}} (hx : Small.{u, v} x) (hy : y ∈ x) :
    Small.{u, v} y := by
  obtain ⟨x0, hx0⟩ := hx
  obtain ⟨y0, _, he⟩ := (mem_lift.{u, v}).mp (mem_congr_right hx0 hy)
  exact ⟨y0, he⟩

theorem small_pair {x y : PSet.{max u v}} (hx : Small.{u, v} x) (hy : Small.{u, v} y) :
    Small.{u, v} (pair x y) := by
  obtain ⟨x0, hx0⟩ := hx
  obtain ⟨y0, hy0⟩ := hy
  exact ⟨pair x0 y0, (pair_congr hx0 hy0).trans (lift_pair.{u, v} x0 y0).symm⟩

theorem small_pempty : Small.{u, v} (pempty : PSet.{max u v}) :=
  ⟨pempty, (lift_pempty.{u, v}).symm⟩

/-- The stage of all `PSet.{u}` sets is closed under the model's operations. -/
theorem stage_univIn (ch : Choice.{u}) : Stage (univIn.{u, v}) where
  trans := fun hx hy => mem_univIn.mpr (small_of_mem_small (mem_univIn.mp hx) hy)
  subset := fun hx hs => mem_univIn.mpr (small_subset (mem_univIn.mp hx) hs)
  pair := fun hx hy => mem_univIn.mpr (small_pair (mem_univIn.mp hx) (mem_univIn.mp hy))
  empty := mem_univIn.mpr small_pempty
  sUnion := fun hx => mem_univIn.mpr (small_sUnion (mem_univIn.mp hx))
  powerset := fun hx => mem_univIn.mpr (small_powerset (mem_univIn.mp hx))
  image := fun hf hA hS => mem_univIn.mpr (small_sImage ch (mem_univIn.mp hA)
    (fun _ _ _ h => hf _ _ h) (fun x hx => mem_univIn.mp (hS x hx)))
  pi := fun hB hA hS => piSet_mem_univIn ch hA (fun _ _ _ h => hB _ _ h) hS

/-- Each stage is an element of the next one. -/
theorem univIn_mem_univIn : univIn.{u, max (u + 2) v} ∈ univIn.{u + 1, v} := by
  refine mem_univIn.mpr ⟨univ.{u}, ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · obtain ⟨x, hx⟩ := hz
    refine (mem_lift.{u + 1, max (u + 2) v}).mpr ⟨lift.{u, u + 1} x.down, ?_, ?_⟩
    · exact mem_univ.mpr ⟨x.down, Equiv.rfl⟩
    · exact hx.symm.trans (lift_lift.{u, u + 1, max (u + 2) v} x.down).symm
  · obtain ⟨y, hy, hzy⟩ := (mem_lift.{u + 1, max (u + 2) v}).mp hz
    obtain ⟨x, hx⟩ := mem_univ.mp hy
    exact ⟨⟨x⟩, (hzy.trans ((lift_equiv.{u + 1, max (u + 2) v} hx).trans
      (lift_lift.{u, u + 1, max (u + 2) v} x))).symm⟩

/-- The table of height 4 inside `PSet.{4}`. -/
def W4 : Nat → PSet.{4}
  | 1 => univIn.{0, 4}
  | 2 => univIn.{1, 4}
  | 3 => univIn.{2, 4}
  | _ => univIn.{3, 4}

theorem chain4 (c0 : Choice.{0}) (c1 : Choice.{1}) (c2 : Choice.{2}) (c3 : Choice.{3}) :
    Chain 4 W4 where
  stage := by
    intro k h1 h4
    match k, h1, h4 with
    | 1, _, _ => exact stage_univIn.{0, 4} c0
    | 2, _, _ => exact stage_univIn.{1, 4} c1
    | 3, _, _ => exact stage_univIn.{2, 4} c2
    | 4, _, _ => exact stage_univIn.{3, 4} c3
  step := by
    intro k h1 h4
    match k, h1, h4 with
    | 1, _, _ => exact univIn_mem_univIn.{0, 4}
    | 2, _, _ => exact univIn_mem_univIn.{1, 4}
    | 3, _, _ => exact univIn_mem_univIn.{2, 4}

theorem good4 (c0 : Choice.{0}) (c1 : Choice.{1}) (c2 : Choice.{2}) (c3 : Choice.{3})
    (M : Interp.{4}) (hU : M.U = U W4) : Good M 4 (Lvl W4) :=
  good_of_chain (chain4 c0 c1 c2 c3) M hU

end PSet

end Rcic.F3

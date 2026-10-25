import rcic.RcicF3Univ
import rcic.RcicF3Defs

/-!
# F3 carrier: small sets and universe closure

`Small.{u, v} x` (for `x : PSet.{max u v}`) says `x` is `≈` to a lifted
`PSet.{u}` set, i.e. `x ∈ univIn.{u, v}` (`mem_univIn`). Small.{u, v} sets are closed
under subsets, power sets, unions, pairs, ordered pairs and products, with no
choice. Images (`small_sImage.{u, v}`) and dependent products (`small_piSet.{u, v}`) need
a small representative for each fibre, a `∀∃`; this is the one place the F3
model uses its choice premise `Choice` (an indefinite-description
operator taken as a hypothesis, never an axiom, defined in `RcicF3Defs`;
`research/rcic/routec-f3/F3_PLAN.md`, D2). closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u v

namespace PSet

/-- Membership in `powerset` is subset inclusion. -/
theorem mem_powerset {x s : PSet.{u}} :
    x ∈ powerset s ↔ (∀ y, y ∈ x → y ∈ s) := by
  cases s with
  | mk α f =>
    constructor
    · rintro ⟨P, hP⟩ y hy
      obtain ⟨a, ha⟩ := hy
      obtain ⟨⟨a', _⟩, hfa'⟩ := hP.exists_mem_right a
      exact mem_congr_left (hfa'.trans ha) ⟨a', Equiv.refl _⟩
    · intro hsub
      refine ⟨fun a => f a ∈ x, ?_⟩
      apply ext; intro z; constructor
      · rintro ⟨⟨a, hPa⟩, hfa⟩
        obtain ⟨i, hi⟩ := hPa
        exact mem_congr_left (hi.trans hfa) ⟨i, Equiv.refl _⟩
      · rintro ⟨i, hi⟩
        obtain ⟨a, ha⟩ := hsub (x.Func i) ⟨i, Equiv.refl _⟩
        exact ⟨⟨a, mem_congr_left ha.symm ⟨i, Equiv.refl _⟩⟩, ha.trans hi⟩

theorem powerset_congr {s s' : PSet.{u}} (hs : Equiv s s') : Equiv (powerset s) (powerset s') :=
  ext fun _ => (mem_powerset.trans
    ⟨(fun h y hy => mem_congr_right hs (h y hy)),
     (fun h y hy => mem_congr_right hs.symm (h y hy))⟩).trans mem_powerset.symm

/-- Small.{u, v} sets: `≈` to a lifted set one universe down. -/
def Small (x : PSet.{max u v}) : Prop := ∃ y : PSet.{u}, Equiv x (lift.{u, v} y)


theorem Small.congr {x x' : PSet.{max u v}} (h : Equiv x x') (hx : Small.{u, v} x) : Small.{u, v} x' :=
  let ⟨y, hy⟩ := hx
  ⟨y, h.symm.trans hy⟩

theorem small_lift (y : PSet.{u}) : Small.{u, v} (lift.{u, v} y) := ⟨y, Equiv.refl _⟩

/-- A subset of a small set is small (no choice: separation one universe down). -/
theorem small_subset {s x : PSet.{max u v}} (hs : Small.{u, v} s) (hx : ∀ z, z ∈ x → z ∈ s) : Small.{u, v} x := by
  obtain ⟨s0, hs0⟩ := hs
  refine ⟨sep (fun y => lift.{u, v} y ∈ x) s0, ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · obtain ⟨y, hy, hzy⟩ := (mem_lift.{u, v}).mp (mem_congr_right hs0 (hx z hz))
    obtain ⟨i, hi⟩ := hy
    have hmem : lift.{u, v} (s0.Func i) ∈ x :=
      mem_congr_left (hzy.trans (lift_equiv.{u, v} hi.symm)) hz
    exact (mem_lift.{u, v}).mpr ⟨s0.Func i, mem_sep.mpr ⟨i, hmem, Equiv.refl _⟩,
      hzy.trans (lift_equiv.{u, v} hi.symm)⟩
  · obtain ⟨y, hy, hzy⟩ := (mem_lift.{u, v}).mp hz
    obtain ⟨i, hp, hi⟩ := mem_sep.mp hy
    exact mem_congr_left ((lift_equiv.{u, v} hi).trans hzy.symm) hp

theorem lift_sUnion (S : PSet.{u}) : Equiv (lift.{u, v} (sUnion S)) (sUnion (lift.{u, v} S)) := by
  apply ext; intro z; constructor
  · intro hz
    obtain ⟨y, hy, hzy⟩ := (mem_lift.{u, v}).mp hz
    obtain ⟨t, ht, hyt⟩ := mem_sUnion.mp hy
    exact mem_sUnion.mpr ⟨lift.{u, v} t, (lift_mem_lift.{u, v}).mpr ht,
      mem_congr_left hzy.symm ((lift_mem_lift.{u, v}).mpr hyt)⟩
  · intro hz
    obtain ⟨t, ht, hzt⟩ := mem_sUnion.mp hz
    obtain ⟨t0, ht0, htt0⟩ := (mem_lift.{u, v}).mp ht
    obtain ⟨y, hy, hzy⟩ := (mem_lift.{u, v}).mp (mem_congr_right htt0 hzt)
    exact (mem_lift.{u, v}).mpr ⟨y, mem_sUnion.mpr ⟨t0, ht0, hy⟩, hzy⟩

theorem small_sUnion {S : PSet.{max u v}} (hS : Small.{u, v} S) : Small.{u, v} (sUnion S) := by
  obtain ⟨S0, h⟩ := hS
  exact ⟨sUnion S0, (sUnion_congr h).trans (lift_sUnion.{u, v} S0).symm⟩

theorem lift_powerset (s : PSet.{u}) :
    Equiv (lift.{u, v} (powerset s)) (powerset (lift.{u, v} s)) := by
  apply ext; intro z; constructor
  · intro hz
    obtain ⟨w, hw, hzw⟩ := (mem_lift.{u, v}).mp hz
    refine mem_powerset.mpr fun y hy => ?_
    obtain ⟨v, hv, hyv⟩ := (mem_lift.{u, v}).mp (mem_congr_right hzw hy)
    exact mem_congr_left hyv.symm ((lift_mem_lift.{u, v}).mpr (mem_powerset.mp hw v hv))
  · intro hz
    have hsub := mem_powerset.mp hz
    obtain ⟨w, hw⟩ := small_subset.{u, v} (small_lift.{u, v} s) hsub
    refine (mem_lift.{u, v}).mpr ⟨w, mem_powerset.mpr fun v hv => ?_, hw⟩
    exact (lift_mem_lift.{u, v}).mp (hsub _ (mem_congr_right hw.symm ((lift_mem_lift.{u, v}).mpr hv)))

theorem small_powerset {s : PSet.{max u v}} (hs : Small.{u, v} s) : Small.{u, v} (powerset s) := by
  obtain ⟨s0, h⟩ := hs
  exact ⟨powerset s0, (powerset_congr h).trans (lift_powerset.{u, v} s0).symm⟩

theorem lift_singleton (x : PSet.{u}) :
    Equiv (lift.{u, v} (singleton x)) (singleton (lift.{u, v} x)) :=
  ext fun z => ⟨fun hz => by
      obtain ⟨y, hy, hzy⟩ := (mem_lift.{u, v}).mp hz
      exact mem_singleton.mpr (hzy.trans (lift_equiv.{u, v} (mem_singleton.mp hy))),
    fun hz => (mem_lift.{u, v}).mpr ⟨x, mem_singleton.mpr (Equiv.refl _), mem_singleton.mp hz⟩⟩

theorem lift_pair (x y : PSet.{u}) :
    Equiv (lift.{u, v} (pair x y)) (pair (lift.{u, v} x) (lift.{u, v} y)) :=
  ext fun z => ⟨fun hz => by
      obtain ⟨w, hw, hzw⟩ := (mem_lift.{u, v}).mp hz
      rcases mem_pair.mp hw with h | h
      · exact mem_pair.mpr (Or.inl (hzw.trans (lift_equiv.{u, v} h)))
      · exact mem_pair.mpr (Or.inr (hzw.trans (lift_equiv.{u, v} h))),
    fun hz => by
      rcases mem_pair.mp hz with h | h
      · exact (mem_lift.{u, v}).mpr ⟨x, mem_pair.mpr (Or.inl (Equiv.refl _)), h⟩
      · exact (mem_lift.{u, v}).mpr ⟨y, mem_pair.mpr (Or.inr (Equiv.refl _)), h⟩⟩

theorem lift_ordPair (x y : PSet.{u}) :
    Equiv (lift.{u, v} (ordPair x y)) (ordPair (lift.{u, v} x) (lift.{u, v} y)) :=
  (lift_pair.{u, v} _ _).trans (pair_congr (lift_singleton.{u, v} x) (lift_pair.{u, v} x y))

theorem lift_prod (A B : PSet.{u}) :
    Equiv (lift.{u, v} (prod A B)) (prod (lift.{u, v} A) (lift.{u, v} B)) := by
  apply ext; intro z; constructor
  · intro hz
    obtain ⟨w, hw, hzw⟩ := (mem_lift.{u, v}).mp hz
    obtain ⟨a, ha, b, hb, hwab⟩ := mem_prod.mp hw
    exact mem_prod.mpr ⟨lift.{u, v} a, (lift_mem_lift.{u, v}).mpr ha, lift.{u, v} b,
      (lift_mem_lift.{u, v}).mpr hb, hzw.trans ((lift_equiv.{u, v} hwab).trans (lift_ordPair.{u, v} a b))⟩
  · intro hz
    obtain ⟨a, ha, b, hb, hzab⟩ := mem_prod.mp hz
    obtain ⟨a0, ha0, haa0⟩ := (mem_lift.{u, v}).mp ha
    obtain ⟨b0, hb0, hbb0⟩ := (mem_lift.{u, v}).mp hb
    exact (mem_lift.{u, v}).mpr ⟨ordPair a0 b0, mem_prod.mpr ⟨a0, ha0, b0, hb0, Equiv.refl _⟩,
      hzab.trans ((ordPair_congr haa0 hbb0).trans (lift_ordPair.{u, v} a0 b0).symm)⟩

theorem prod_congr {A A' B B' : PSet.{u}} (hA : Equiv A A') (hB : Equiv B B') :
    Equiv (prod A B) (prod A' B') :=
  ext fun z => ⟨fun h => by
      obtain ⟨a, ha, b, hb, he⟩ := mem_prod.mp h
      exact mem_prod.mpr ⟨a, mem_congr_right hA ha, b, mem_congr_right hB hb, he⟩,
    fun h => by
      obtain ⟨a, ha, b, hb, he⟩ := mem_prod.mp h
      exact mem_prod.mpr ⟨a, mem_congr_right hA.symm ha, b, mem_congr_right hB.symm hb, he⟩⟩

theorem small_prod {A B : PSet.{max u v}} (hA : Small.{u, v} A) (hB : Small.{u, v} B) : Small.{u, v} (prod A B) := by
  obtain ⟨A0, hA0⟩ := hA
  obtain ⟨B0, hB0⟩ := hB
  exact ⟨prod A0 B0, (prod_congr hA0 hB0).trans (lift_prod.{u, v} A0 B0).symm⟩

theorem small_sep {s : PSet.{max u v}} (hs : Small.{u, v} s) (p : PSet.{max u v} → Prop) : Small.{u, v} (sep p s) :=
  small_subset.{u, v} hs fun _ hz => mem_sep_subset hz

/-- Images of small sets under small-valued, `≈`-respecting maps are small.
This is where the choice premise is used: one small representative per
fibre. -/
theorem small_sImage (ch : Choice.{u}) {A : PSet.{max u v}} {B : PSet.{max u v} → PSet.{max u v}}
    (hA : Small.{u, v} A) (hB : ∀ x y, x ∈ A → Equiv x y → Equiv (B x) (B y))
    (hS : ∀ x, x ∈ A → Small.{u, v} (B x)) : Small.{u, v} (sImage B A) := by
  obtain ⟨a, ha⟩ := hA
  have hin : ∀ i : a.Idx, lift.{u, v} (a.Func i) ∈ A := fun i =>
    mem_congr_right ha.symm ((lift_mem_lift.{u, v}).mpr ⟨i, Equiv.refl _⟩)
  let y : a.Idx → PSet.{u} := fun i =>
    (ch (fun y => Equiv (B (lift.{u, v} (a.Func i))) (lift.{u, v} y)) (hS _ (hin i))).1
  have hy : ∀ i, Equiv (B (lift.{u, v} (a.Func i))) (lift.{u, v} (y i)) := fun i =>
    (ch (fun y => Equiv (B (lift.{u, v} (a.Func i))) (lift.{u, v} y)) (hS _ (hin i))).2
  refine ⟨mk a.Idx y, ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · obtain ⟨j, hj⟩ := mem_sImage.mp hz
    have hAj : A.Func j ∈ A := ⟨j, Equiv.refl _⟩
    obtain ⟨w, hw, hjw⟩ := (mem_lift.{u, v}).mp (mem_congr_right ha hAj)
    obtain ⟨i, hi⟩ := hw
    have e1 : Equiv (B (A.Func j)) (B (lift.{u, v} (a.Func i))) :=
      hB _ _ hAj (hjw.trans (lift_equiv.{u, v} hi.symm))
    exact (mem_lift.{u, v}).mpr ⟨y i, ⟨i, Equiv.refl _⟩, hj.symm.trans (e1.trans (hy i))⟩
  · obtain ⟨w, hw, hzw⟩ := (mem_lift.{u, v}).mp hz
    obtain ⟨i, hi⟩ := hw
    obtain ⟨j, hj⟩ := hin i
    have e1 : Equiv (B (A.Func j)) (B (lift.{u, v} (a.Func i))) := hB _ _ ⟨j, Equiv.refl _⟩ hj
    exact mem_sImage.mpr ⟨j, (e1.trans (hy i)).trans ((lift_equiv.{u, v} hi).trans hzw.symm)⟩

/-- Dependent products of small families over small domains are small. -/
theorem small_piSet (ch : Choice.{u}) {A : PSet.{max u v}} {B : PSet.{max u v} → PSet.{max u v}}
    (hA : Small.{u, v} A) (hB : ∀ x y, x ∈ A → Equiv x y → Equiv (B x) (B y))
    (hS : ∀ x, x ∈ A → Small.{u, v} (B x)) : Small.{u, v} (piSet A B) :=
  small_sep.{u, v} (small_powerset.{u, v} (small_prod.{u, v} hA (small_sUnion.{u, v} (small_sImage.{u, v} ch hA hB hS)))) _

/-- The universe stage for `PSet.{u}`, inside any larger carrier. -/
def univIn : PSet.{max (u + 1) v} := mk (ULift.{v} PSet.{u}) (fun x => lift.{u, max (u + 1) v} x.down)

theorem mem_univIn {z : PSet.{max (u + 1) v}} :
    z ∈ univIn.{u, v} ↔ Small.{u, max (u + 1) v} z :=
  ⟨fun ⟨x, h⟩ => ⟨x.down, h.symm⟩, fun ⟨x, h⟩ => ⟨⟨x⟩, h.symm⟩⟩

/-- Universe closure: `piSet A B ∈ univIn` for a small domain and small fibres. -/
theorem piSet_mem_univIn (ch : Choice.{u}) {A : PSet.{max (u + 1) v}}
    {B : PSet.{max (u + 1) v} → PSet.{max (u + 1) v}}
    (hA : A ∈ univIn.{u, v}) (hB : ∀ x y, x ∈ A → Equiv x y → Equiv (B x) (B y))
    (hS : ∀ x, x ∈ A → B x ∈ univIn.{u, v}) : piSet A B ∈ univIn.{u, v} :=
  mem_univIn.mpr (small_piSet.{u, max (u + 1) v} ch (mem_univIn.mp hA) hB
    (fun x hx => mem_univIn.mp (hS x hx)))

end PSet

end Rcic.F3

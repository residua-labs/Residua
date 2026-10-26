import rcic.RcicF3KTWSpecPhi

/-!
# F3 S7 KT-2b-3c-1: the constructor sum of guarded signatures

`GSig.sum S` glues a small-indexed family `S : J → GSig.{u}` of guarded W-signatures
into one signature whose shapes are `Σ j, (S j).Sh`.  `iUnionT F` is the small-union
of a family of big sets; the two commute with the guarded operator:

- `lift_gphi_sum`: `lift (gphi (sum S) X) ≈ ⋃ j, lift (gphi (S j) X)`;
- `wshaped_sum`: if each `Φ j` is `WShaped` by `S j`, the pointwise union operator
  `fun X ↦ ⋃ j, Φ j X` is `WShaped` by `sum S`;
- `mono_sum` / `iUnionT_congr` / `iUnionT_sub`: the union respects `≈` and `⊆`.

`wshaped_phiSpec_sum` instantiates this at the semantic specs: the union of the
`phiSpec` operators of a family of layouts is W-shaped by the sum of their signatures.
Theory-agnostic; no choice except where the per-summand spec itself needs it.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u v

namespace PSet

/-- Disjoint sum of guarded signatures over a small index type. -/
def GSig.sum {J : Type u} (S : J → GSig.{u}) : GSig.{u} where
  Sh := Σ j : J, (S j).Sh
  br := fun p => (S p.1).br p.2
  code := fun p h => (S p.1).code p.2 h
  ok := fun p h => (S p.1).ok p.2 h
  code_congr := fun p h h' e => (S p.1).code_congr p.2 h h' e
  ok_congr := fun p h h' e => (S p.1).ok_congr p.2 h h' e

/-- Union of a small-indexed family of sets. -/
def iUnionT {J : Type u} (F : J → PSet.{max u v}) : PSet.{max u v} :=
  mk (Σ j : ULift.{v} J, (F j.down).Idx) (fun p => (F p.1.down).Func p.2)

theorem mem_iUnionT {J : Type u} {F : J → PSet.{max u v}} {z : PSet.{max u v}} :
    z ∈ iUnionT.{u, v} F ↔ ∃ j, z ∈ F j :=
  ⟨fun ⟨a, ha⟩ => ⟨a.1.down, a.2, ha⟩,
   fun ⟨j, i, hi⟩ => ⟨⟨⟨j⟩, i⟩, hi⟩⟩

theorem iUnionT_congr {J : Type u} {F G : J → PSet.{max u v}} (h : ∀ j, Equiv (F j) (G j)) :
    Equiv (iUnionT.{u, v} F) (iUnionT.{u, v} G) :=
  ⟨fun a => let ⟨i, hi⟩ := (h a.1.down).exists_mem_left a.2; ⟨⟨a.1, i⟩, hi⟩,
   fun b => let ⟨i, hi⟩ := (h b.1.down).exists_mem_right b.2; ⟨⟨b.1, i⟩, hi⟩⟩

theorem iUnionT_sub {J : Type u} {F G : J → PSet.{max u v}} (h : ∀ j, Sub (F j) (G j)) :
    Sub (iUnionT.{u, v} F) (iUnionT.{u, v} G) := by
  intro z hz
  obtain ⟨j, hj⟩ := mem_iUnionT.mp hz
  exact mem_iUnionT.mpr ⟨j, h j z hj⟩

/-- The guarded operator of a sum is the union of the summands' operators (lifted). -/
theorem lift_gphi_sum {J : Type u} (S : J → GSig.{u}) (X : PSet.{u}) :
    Equiv (lift.{u, v} (gphi (GSig.sum S) X)) (iUnionT.{u, v} (fun j => lift.{u, v} (gphi (S j) X))) := by
  apply ext; intro z
  rw [mem_lift]
  constructor
  · rintro ⟨y, ⟨⟨⟨j, s⟩, i, hok⟩, hy⟩, hz⟩
    exact mem_iUnionT.mpr ⟨j, mem_lift.mpr
      ⟨_, ⟨⟨s, i, hok⟩, Equiv.refl _⟩, hz.trans (lift_equiv.{u, v} hy.symm)⟩⟩
  · intro hz
    obtain ⟨j, hj⟩ := mem_iUnionT.mp hz
    obtain ⟨y, hy, hz⟩ := mem_lift.mp hj
    obtain ⟨⟨s, i, hok⟩, hy⟩ := hy
    exact ⟨y, ⟨⟨⟨j, s⟩, ⟨i, hok⟩⟩, hy⟩, hz⟩

/-- If each `Φ j` is W-shaped by `S j`, their pointwise union is W-shaped by `sum S`. -/
theorem wshaped_sum {J : Type u} {Φ : J → PSet.{max u v} → PSet.{max u v}} {S : J → GSig.{u}}
    (h : ∀ j, WShaped.{u, v} (Φ j) (S j)) :
    WShaped.{u, v} (fun X => iUnionT.{u, v} (fun j => Φ j X)) (GSig.sum S) :=
  ⟨fun X => (iUnionT_congr.{u, v} (fun j => (h j).at_lift X)).trans (lift_gphi_sum S X).symm⟩

/-- The pointwise union of monotone operators is monotone. -/
theorem mono_sum {J : Type u} {Φ : J → PSet.{max u v} → PSet.{max u v}}
    (h : ∀ j X Y, Sub X Y → Sub (Φ j X) (Φ j Y)) :
    ∀ X Y : PSet.{max u v}, Sub X Y → Sub (iUnionT.{u, v} (fun j => Φ j X)) (iUnionT.{u, v} (fun j => Φ j Y)) := by
  intro X Y hXY z hz
  obtain ⟨j, hj⟩ := mem_iUnionT.mp hz
  exact mem_iUnionT.mpr ⟨j, h j X Y hXY z hj⟩

/-- Constructor sum of semantic specs. -/
theorem wshaped_phiSpec_sum {J : Type u} {Sh : J → Type u} (L : ∀ j, Layout (Sh j)) (Sm : J → Sem.{max u v})
    {B : PSet.{max u v}} (cov : ∀ j, SpecCover (L j) (Sm j) B) (ch : Choice.{u}) :
    WShaped.{u, v} (fun X => iUnionT.{u, v} (fun j => phiSpec (L j) (Sm j) B X))
      (GSig.sum (fun j => (L j).sig (Sm j))) :=
  wshaped_sum fun j => wshaped_phiSpec (L j) (Sm j) (cov j) ch

end PSet

end Rcic.F3

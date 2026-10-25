import rcic.RcicF3Core

/-!
# F3 S6a: universe stages from a chain of closed sets

A `Stage` is a set closed under the operations the model uses (members,
subsets, pairs, the empty set, unions, powersets, images, dependent products). A
`Chain N W` is a sequence `W 1 ∈ W 2 ∈ … ∈ W N` of stages. From any chain we
build the universe table of the model:

- `Lvl W 0 S` : every element of `S` is `∅` (a proposition);
- `Lvl W (k+1) S` : `S ∈ W (k+1)` and `S` is dichotomous;
- `U W k` : the set of type values `tyv S` with `Lvl W k S`;

and prove `good_of_chain`: any interpretation with this table satisfies
`Good` up to `N`. The chain itself is built from Lean's universes in
`RcicF3Table`. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

/-- A set closed under the operations the model uses. -/
structure Stage (W : PSet.{T}) : Prop where
  trans : ∀ {x y : PSet.{T}}, x ∈ W → y ∈ x → y ∈ W
  subset : ∀ {x y : PSet.{T}}, x ∈ W → Subset y x → y ∈ W
  pair : ∀ {x y : PSet.{T}}, x ∈ W → y ∈ W → pair x y ∈ W
  empty : pempty ∈ W
  sUnion : ∀ {x : PSet.{T}}, x ∈ W → sUnion x ∈ W
  powerset : ∀ {x : PSet.{T}}, x ∈ W → powerset x ∈ W
  image : ∀ {A : PSet.{T}} {f : PSet.{T} → PSet.{T}},
    (∀ a a', Equiv a a' → Equiv (f a) (f a')) → A ∈ W → (∀ x, x ∈ A → f x ∈ W) → sImage f A ∈ W
  pi : ∀ {A : PSet.{T}} {B : PSet.{T} → PSet.{T}},
    (∀ a a', Equiv a a' → Equiv (B a) (B a')) → A ∈ W → (∀ x, x ∈ A → B x ∈ W) → piSet A B ∈ W

/-- A chain of stages `W 1 ∈ W 2 ∈ … ∈ W N`. -/
structure Chain (N : Nat) (W : Nat → PSet.{T}) : Prop where
  stage : ∀ k, 1 ≤ k → k ≤ N → Stage (W k)
  step : ∀ k, 1 ≤ k → k + 1 ≤ N → W k ∈ W (k + 1)

/-- The level predicate of the table. -/
def Lvl (W : Nat → PSet.{T}) : Nat → PSet.{T} → Prop
  | 0, S => ∀ y, y ∈ S → Equiv y pempty
  | k + 1, S => S ∈ W (k + 1) ∧ Dich S

/-- Propositions: the subsets of `{∅}`. -/
def propSets : PSet.{T} := sep (fun S => ∀ y, y ∈ S → Equiv y pempty) (powerset (singleton pempty))

/-- The universe table. -/
def U (W : Nat → PSet.{T}) : Nat → PSet.{T}
  | 0 => sImage tyv propSets
  | k + 1 => sImage tyv (sep Dich (W (k + 1)))

theorem mem_sImage_of {f : PSet.{T} → PSet.{T}} (hf : ∀ a a', Equiv a a' → Equiv (f a) (f a'))
    {A a : PSet.{T}} (ha : a ∈ A) : f a ∈ sImage f A := by
  obtain ⟨i, hi⟩ := ha
  exact mem_sImage.mpr ⟨i, hf _ _ hi⟩

theorem tyv_resp : ∀ a a' : PSet.{T}, Equiv a a' → Equiv (tyv a) (tyv a') := fun _ _ h => tyv_congr h

theorem mem_sImage_tyv {A x : PSet.{T}} :
    x ∈ sImage tyv A ↔ ∃ S, S ∈ A ∧ Equiv x (tyv S) := by
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_sImage.mp hx
    exact ⟨A.Func i, ⟨i, Equiv.rfl⟩, hi.symm⟩
  · rintro ⟨S, hS, hx⟩
    exact mem_congr_left hx.symm (mem_sImage_of tyv_resp hS)

theorem mem_propSets {S : PSet.{T}} : S ∈ propSets ↔ ∀ y, y ∈ S → Equiv y pempty := by
  constructor
  · intro h
    obtain ⟨i, hp, he⟩ := mem_sep.mp h
    intro y hy
    exact hp y (mem_congr_right he.symm hy)
  · intro h
    have hsub : S ∈ powerset (singleton pempty) :=
      mem_powerset.mpr fun z hz => mem_singleton.mpr (h z hz)
    obtain ⟨i, hi⟩ := hsub
    refine mem_sep.mpr ⟨i, fun y hy => h y (mem_congr_right hi hy), hi⟩

namespace Stage

variable {W : PSet.{T}} (hW : Stage W)
include hW

theorem singleton_mem {x : PSet.{T}} (hx : x ∈ W) : singleton x ∈ W :=
  hW.subset (hW.pair hx hx) fun _ hz => mem_pair.mpr (Or.inl (mem_singleton.mp hz))

theorem tyTag_mem : tyTag ∈ W := hW.singleton_mem hW.empty

theorem ordPair_mem {x y : PSet.{T}} (hx : x ∈ W) (hy : y ∈ W) : ordPair x y ∈ W :=
  hW.pair (hW.singleton_mem hx) (hW.pair hx hy)

theorem tyv_mem {S : PSet.{T}} (hS : S ∈ W) : tyv S ∈ W := hW.ordPair_mem hW.tyTag_mem hS

theorem propSets_mem : propSets ∈ W :=
  hW.subset (hW.powerset (hW.singleton_mem hW.empty)) fun _ hz => mem_sep_subset hz

theorem prop_mem {S : PSet.{T}} (hS : ∀ y, y ∈ S → Equiv y pempty) : S ∈ W :=
  hW.trans hW.propSets_mem (mem_propSets.mpr hS)

theorem table_mem {A : PSet.{T}} (hA : A ∈ W) : sImage tyv A ∈ W :=
  hW.image tyv_resp hA fun _ hx => hW.tyv_mem (hW.trans hA hx)

end Stage

section Chain

variable {N : Nat} {W : Nat → PSet.{T}} (hC : Chain N W)
include hC

theorem Chain.lift_le {k : Nat} (hk : 1 ≤ k) : ∀ d, k + d ≤ N → ∀ {x : PSet.{T}}, x ∈ W k → x ∈ W (k + d)
  | 0, _, _, hx => hx
  | d + 1, hd, x, hx => by
      have h1 := Chain.lift_le hk d (by omega) hx
      exact (hC.stage (k + d + 1) (by omega) hd).trans (hC.step (k + d) (by omega) hd) h1

theorem Chain.U_mem_succ {k : Nat} (hk : k + 1 ≤ N) : U W k ∈ W (k + 1) := by
  have hS := hC.stage (k + 1) (by omega) hk
  cases k with
  | zero => exact hS.table_mem hS.propSets_mem
  | succ k =>
      exact hS.table_mem (hS.subset (hC.step (k + 1) (by omega) hk) fun _ hz => mem_sep_subset hz)

theorem good_of_chain (M : Interp.{T}) (hU : M.U = U W) : Good M N (Lvl W) where
  congr := by
    intro k S S' hS he
    cases k with
    | zero => exact fun y hy => hS y (mem_congr_right he.symm hy)
    | succ k => exact ⟨mem_congr_left he hS.1, (dich_congr he).mp hS.2⟩
  dich := by
    intro k S hS
    cases k with
    | zero => exact Or.inl hS
    | succ k => exact hS.2
  lvl0 := Iff.rfl
  U_iff := by
    intro k _ x
    rw [hU]
    cases k with
    | zero =>
        show x ∈ sImage tyv propSets ↔ _
        rw [mem_sImage_tyv]
        exact ⟨fun ⟨S, hS, he⟩ => ⟨S, mem_propSets.mp hS, he⟩,
          fun ⟨S, hS, he⟩ => ⟨S, mem_propSets.mpr hS, he⟩⟩
    | succ k =>
        show x ∈ sImage tyv (sep Dich (W (k + 1))) ↔ _
        rw [mem_sImage_tyv]
        constructor
        · rintro ⟨S, hS, he⟩
          obtain ⟨i, hp, hi⟩ := mem_sep.mp hS
          exact ⟨S, ⟨mem_sep_subset hS, (dich_congr hi).mp hp⟩, he⟩
        · rintro ⟨S, ⟨hS, hd⟩, he⟩
          obtain ⟨i, hi⟩ := hS
          exact ⟨S, mem_sep.mpr ⟨i, (dich_congr hi.symm).mp hd, hi⟩, he⟩
  univ := by
    intro k hk
    rw [hU]
    refine ⟨hC.U_mem_succ hk, Or.inr fun h0 => ?_⟩
    have h0' : pempty ∈ sImage tyv (match k with
      | 0 => propSets
      | k + 1 => sep Dich (W (k + 1))) := by
      cases k <;> exact h0
    obtain ⟨S, _, he⟩ := mem_sImage_tyv.mp h0'
    exact tyv_ne_pempty S he.symm
  prop := by
    intro m S hm hmN hS
    cases m with
    | zero => exact absurd hm (by decide)
    | succ m => exact ⟨(hC.stage (m + 1) hm hmN).prop_mem hS, Or.inl hS⟩
  mono := by
    intro k m S hk hkm hmN hS
    cases k with
    | zero => exact absurd hk (by decide)
    | succ k =>
      cases m with
      | zero => exact absurd hkm (by omega)
      | succ m =>
        have := hC.lift_le hk (m - k) (by omega) hS.1
        rw [show k + 1 + (m - k) = m + 1 by omega] at this
        exact ⟨this, hS.2⟩
  pi := by
    intro m A B hm hmN hA hB hBm
    cases m with
    | zero => exact absurd hm (by decide)
    | succ m => exact ⟨(hC.stage (m + 1) hm hmN).pi hB hA.1 fun x hx => (hBm x hx).1, dich_piSet M.dec hB⟩

end Chain

end PSet

end Rcic.F3

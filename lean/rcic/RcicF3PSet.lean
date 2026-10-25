/-!
# F3 carrier: universe-polymorphic extensional sets

`PSet.{u}`: well-founded trees branching over `Type u`, with extensional
equivalence `≈` and `≈`-saturated membership. This is the landed
`RcicModelPSet` / `RcicModelOps` carrier (lane R1-b) made
universe-polymorphic, so that `PSet.{k}` can be collected into a set of
`PSet.{k+1}` (the universe stages of the F3 model,
`research/rcic/routec-f3/F3_PLAN.md`, D2). No quotient, no `Classical`.
closure_claim = 0.
-/

namespace Rcic.F3

universe u

/-- The model carrier: well-founded extensional trees. `mk α f` is the
set whose elements are the `f a`. -/
inductive PSet : Type (u + 1) where
  | mk (α : Type u) (f : α → PSet)

namespace PSet

/-- The index type of a set's element family. -/
def Idx : PSet.{u} → Type u
  | mk α _ => α

/-- The element family of a set. -/
def Func : (s : PSet.{u}) → s.Idx → PSet.{u}
  | mk _ f => f

/-- Extensional equivalence of sets. -/
def Equiv : PSet.{u} → PSet.{u} → Prop
  | mk _α f, mk _β g =>
      (∀ a, ∃ b, Equiv (f a) (g b)) ∧
      (∀ b, ∃ a, Equiv (f a) (g b))

/-- `≈`-saturated membership: `x ∈ mk α f` iff `x ≈ f a` for some `a`. -/
def Mem (s : PSet.{u}) (x : PSet.{u}) : Prop :=
  ∃ a : s.Idx, Equiv (s.Func a) x

instance : Membership PSet.{u} PSet.{u} := ⟨Mem⟩

/-- `∈` unfolds over `mk` as membership in the family. -/
theorem mem_def {x : PSet.{u}} {α : Type u} {f : α → PSet.{u}} :
    x ∈ mk α f ↔ ∃ a, Equiv (f a) x :=
  Iff.rfl

/-! ### `Equiv` is an equivalence -/

theorem Equiv.refl (x : PSet.{u}) : Equiv x x := by
  induction x with
  | mk α f ih => exact ⟨fun a => ⟨a, ih a⟩, fun a => ⟨a, ih a⟩⟩

theorem Equiv.symm {x y : PSet.{u}} : Equiv x y → Equiv y x := by
  revert y
  induction x with
  | mk α f ih =>
    intro y h
    cases y with
    | mk β g =>
      obtain ⟨h₁, h₂⟩ := h
      exact ⟨fun b => let ⟨a, ha⟩ := h₂ b; ⟨a, ih a ha⟩,
             fun a => let ⟨b, hb⟩ := h₁ a; ⟨b, ih a hb⟩⟩

theorem Equiv.trans {x y z : PSet.{u}} : Equiv x y → Equiv y z → Equiv x z := by
  revert y z
  induction x with
  | mk α f ih =>
    intro y z hxy hyz
    cases y with
    | mk β g =>
    cases z with
    | mk γ h =>
      obtain ⟨hf, hb⟩ := hxy
      obtain ⟨hg, hc⟩ := hyz
      constructor
      · intro a
        obtain ⟨b, hab⟩ := hf a
        obtain ⟨c, hbc⟩ := hg b
        exact ⟨c, ih a hab hbc⟩
      · intro c
        obtain ⟨b, hbc⟩ := hc c
        obtain ⟨a, hab⟩ := hb b
        exact ⟨a, ih a hab hbc⟩

theorem Equiv.rfl {x : PSet.{u}} : Equiv x x := Equiv.refl x

/-- Left-to-right component of `≈`, at the family level. -/
theorem Equiv.exists_mem_left {x y : PSet.{u}} (h : Equiv x y) (a : x.Idx) :
    ∃ b : y.Idx, Equiv (x.Func a) (y.Func b) := by
  cases x with
  | mk α f =>
  cases y with
  | mk β g =>
    obtain ⟨hf, _⟩ := h
    exact hf a

/-- Right-to-left component of `≈`, at the family level. -/
theorem Equiv.exists_mem_right {x y : PSet.{u}} (h : Equiv x y) (b : y.Idx) :
    ∃ a : x.Idx, Equiv (x.Func a) (y.Func b) := by
  cases x with
  | mk α f =>
  cases y with
  | mk β g =>
    obtain ⟨_, hb⟩ := h
    exact hb b

/-! ### Membership congruence -/

theorem mem_congr_left {x x' : PSet.{u}} {s : PSet.{u}} (h : Equiv x x') :
    x ∈ s → x' ∈ s :=
  fun ⟨a, ha⟩ => ⟨a, ha.trans h⟩

theorem mem_congr_right {x s s' : PSet.{u}} (h : Equiv s s') :
    x ∈ s → x ∈ s' :=
  fun ⟨a, ha⟩ =>
    let ⟨b, hb⟩ := h.exists_mem_left a
    ⟨b, hb.symm.trans ha⟩

theorem Equiv.mem_left {x x' : PSet.{u}} {s : PSet.{u}} (h : Equiv x x') :
    x ∈ s ↔ x' ∈ s :=
  ⟨mem_congr_left h, mem_congr_left h.symm⟩

theorem Equiv.mem_right {x : PSet.{u}} {s s' : PSet.{u}} (h : Equiv s s') :
    x ∈ s ↔ x ∈ s' :=
  ⟨mem_congr_right h, mem_congr_right h.symm⟩

/-- Extensionality: elementwise-`≈` equal sets are `≈`. -/
theorem ext {x y : PSet.{u}} (h : ∀ z, z ∈ x ↔ z ∈ y) : Equiv x y := by
  cases x with
  | mk α f =>
  cases y with
  | mk β g =>
    constructor
    · intro a
      have : f a ∈ mk α f := ⟨a, Equiv.refl _⟩
      obtain ⟨b, hb⟩ := (h (f a)).mp this
      exact ⟨b, hb.symm⟩
    · intro b
      have : g b ∈ mk β g := ⟨b, Equiv.refl _⟩
      obtain ⟨a, ha⟩ := (h (g b)).mpr this
      exact ⟨a, ha⟩

/-- `≈` agrees with elementwise membership. -/
theorem equiv_iff_mem {x y : PSet.{u}} :
    Equiv x y ↔ ∀ z, z ∈ x ↔ z ∈ y := by
  constructor
  · intro h z; exact h.mem_right
  · intro h; exact ext h

/-- Subset (up to `≈`). -/
def Subset (x y : PSet.{u}) : Prop := ∀ z, z ∈ x → z ∈ y

theorem Subset.refl (x : PSet.{u}) : Subset x x := fun _ h => h

theorem Subset.trans {x y z : PSet.{u}} (hxy : Subset x y) (hyz : Subset y z) :
    Subset x z := fun _ h => hyz _ (hxy _ h)

theorem Subset.equiv {x y : PSet.{u}} (h₁ : Subset x y) (h₂ : Subset y x) :
    Equiv x y :=
  ext fun _ => ⟨h₁ _, h₂ _⟩

/-! ### Small combinators -/

/-- The empty set. -/
def pempty : PSet.{u} := mk PEmpty PEmpty.elim

/-- Singleton `{x}`. -/
def singleton (x : PSet.{u}) : PSet.{u} := mk PUnit fun _ => x

/-- Unordered pair `{x, y}`. -/
def pair (x y : PSet.{u}) : PSet.{u} := mk (ULift Bool) fun
  | ⟨true⟩ => x
  | ⟨false⟩ => y

/-- Kuratowski ordered pair `{{x}, {x, y}}`. -/
def ordPair (x y : PSet.{u}) : PSet.{u} := pair (singleton x) (pair x y)

/-- `s ∪ {x}`. -/
def insert (x s : PSet.{u}) : PSet.{u} :=
  mk (Option s.Idx) fun
    | none => x
    | some a => s.Func a

/-- Union `⋃ s`. -/
def sUnion (s : PSet.{u}) : PSet.{u} :=
  mk (Σ i : s.Idx, (s.Func i).Idx) fun p => (s.Func p.1).Func p.2

/-- Separation `{x ∈ s | p x}`, where `p` sees representatives. -/
def sep (p : PSet.{u} → Prop) (s : PSet.{u}) : PSet.{u} :=
  mk {i : s.Idx // p (s.Func i)} fun ⟨i, _⟩ => s.Func i

/-- Image `{h x | x ∈ s}` (as a family over the index). -/
def sImage (h : PSet.{u} → PSet.{u}) (s : PSet.{u}) : PSet.{u} := mk s.Idx fun i => h (s.Func i)

theorem not_mem_pempty {x : PSet.{u}} : ¬ x ∈ pempty :=
  fun ⟨a, _⟩ => a.elim

theorem mem_singleton {x y : PSet.{u}} : x ∈ singleton y ↔ Equiv x y := by
  constructor
  · rintro ⟨_, ha⟩; exact ha.symm
  · intro h; exact ⟨PUnit.unit, h.symm⟩

theorem mem_pair {z x y : PSet.{u}} : z ∈ pair x y ↔ Equiv z x ∨ Equiv z y := by
  constructor
  · rintro ⟨⟨b⟩, hb⟩
    cases b with
    | true => exact Or.inl hb.symm
    | false => exact Or.inr hb.symm
  · rintro (h | h)
    · exact ⟨⟨true⟩, h.symm⟩
    · exact ⟨⟨false⟩, h.symm⟩

theorem mem_insert {z x : PSet.{u}} {s : PSet.{u}} :
    z ∈ insert x s ↔ Equiv z x ∨ z ∈ s := by
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | none => exact Or.inl hi.symm
    | some a => exact Or.inr ⟨a, hi⟩
  · rintro (h | ⟨a, ha⟩)
    · exact ⟨none, h.symm⟩
    · exact ⟨some a, ha⟩

theorem mem_sUnion {x : PSet.{u}} {s : PSet.{u}} :
    x ∈ sUnion s ↔ ∃ t, t ∈ s ∧ x ∈ t := by
  constructor
  · rintro ⟨⟨i, j⟩, h⟩
    exact ⟨s.Func i, ⟨i, Equiv.refl _⟩, ⟨j, h⟩⟩
  · rintro ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩
    obtain ⟨j', hj'⟩ := hi.exists_mem_right j
    exact ⟨⟨i, j'⟩, hj'.trans hj⟩

theorem mem_sep {x : PSet.{u}} {p : PSet.{u} → Prop} {s : PSet.{u}} :
    x ∈ sep p s ↔ ∃ i : s.Idx, p (s.Func i) ∧ Equiv (s.Func i) x := by
  constructor
  · rintro ⟨⟨i, hp⟩, he⟩; exact ⟨i, hp, he⟩
  · rintro ⟨i, hp, he⟩; exact ⟨⟨i, hp⟩, he⟩

theorem mem_sImage {x : PSet.{u}} {h : PSet.{u} → PSet.{u}} {s : PSet.{u}} :
    x ∈ sImage h s ↔ ∃ i : s.Idx, Equiv (h (s.Func i)) x :=
  Iff.rfl

theorem subset_insert {x s : PSet.{u}} : Subset s (insert x s) :=
  fun _ h => mem_insert.mpr (Or.inr h)

theorem insert_subset {x s t : PSet.{u}} (hx : x ∈ t) (hs : Subset s t) :
    Subset (insert x s) t := fun _ hz =>
  match mem_insert.mp hz with
  | Or.inl h => mem_congr_left h.symm hx
  | Or.inr h => hs _ h

/-- The empty denotation / default element `J₀ = ∅`. -/
def junk₀ : PSet.{u} := pempty

/-- The inhabited witness-token `J₁ = {∅}`. -/
def junk₁ : PSet.{u} := singleton pempty

theorem junk₁_mem : junk₀ ∈ junk₁ :=
  mem_singleton.mpr Equiv.rfl

theorem junk₀_ne_junk₁ : ¬ Equiv junk₀ junk₁ := by
  intro h
  have : junk₀ ∈ junk₁ := junk₁_mem
  have : junk₀ ∈ junk₀ := mem_congr_right h.symm this
  exact not_mem_pempty this

/-! ### Foundation -/

/-- Element-first membership relation (for `Acc`/`WellFounded`). -/
def elemOf (x s : PSet.{u}) : Prop := x ∈ s

/-- `Acc` transports across `≈`. -/
theorem acc_equiv {x y : PSet.{u}} (h : Equiv x y) (ha : Acc elemOf x) :
    Acc elemOf y :=
  Acc.intro y fun z hz =>
    match ha with
    | .intro _ hx => hx z (mem_congr_right h.symm hz)

/-- Every set is `∈`-accessible. -/
theorem acc_mem (x : PSet.{u}) : Acc elemOf x := by
  induction x with
  | mk α f ih =>
    apply Acc.intro
    rintro y ⟨a, ha⟩
    exact acc_equiv ha (ih a)

theorem mem_wf : WellFounded elemOf := ⟨acc_mem⟩

/-- Self-membership is impossible: `x ∈ x` gives `y ∈ x` with `y ≈ x`,
and `y ≈ x` puts an `≈`-copy of `y` back inside `y`. -/
theorem mem_irrefl_aux : ∀ s : PSet.{u}, ¬ ∃ y, y ∈ s ∧ Equiv y s :=
  fun s => mem_wf.induction s fun s ih => by
    show ¬ ∃ y, y ∈ s ∧ Equiv y s
    rintro ⟨y, hy_mem, hy_eq⟩
    obtain ⟨w, hw_mem, hw_eq⟩ : ∃ w, w ∈ y ∧ Equiv w y := by
      cases s with
      | mk α f =>
      cases y with
      | mk β g =>
        obtain ⟨a, ha⟩ := hy_mem
        obtain ⟨b, hgb⟩ := hy_eq.exists_mem_right a
        exact ⟨g b, ⟨b, Equiv.refl _⟩, hgb.trans ha⟩
    exact ih y hy_mem ⟨w, hw_mem, hw_eq⟩

/-- No set is a member of itself. -/
theorem mem_irrefl (x : PSet.{u}) : ¬ x ∈ x := by
  intro hx
  obtain ⟨a, ha⟩ := hx
  exact mem_irrefl_aux x ⟨x.Func a, ⟨a, Equiv.refl _⟩, ha⟩

/-! ### Finite ordinals (`σ`-codes for sorts live in `RcicModelOps`) -/

/-- The finite von Neumann ordinal `n` as a set. -/
def ord : Nat → PSet.{u}
  | 0 => pempty
  | n + 1 => insert (ord n) (ord n)

/-- Membership in a finite ordinal. -/
theorem ord_mem_iff {x : PSet.{u}} {n : Nat} :
    x ∈ ord n ↔ ∃ k, k < n ∧ Equiv x (ord k) := by
  induction n with
  | zero =>
    constructor
    · intro h; exact (not_mem_pempty h).elim
    · rintro ⟨_, hk, _⟩; exact (Nat.not_lt_zero _ hk).elim
  | succ n ih =>
    constructor
    · intro hx
      obtain (h | h) := mem_insert.mp hx
      · exact ⟨n, Nat.lt_succ_self _, h⟩
      · obtain ⟨k, hk, hek⟩ := ih.mp h
        exact ⟨k, Nat.lt_succ_of_lt hk, hek⟩
    · rintro ⟨k, hk, hek⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkn | rfl
      · exact mem_insert.mpr (Or.inr (ih.mpr ⟨k, hkn, hek⟩))
      · exact mem_insert.mpr (Or.inl hek)

/-- Distinct finite ordinals are extensionally distinct. -/
theorem ord_inj {k n : Nat} (h : Equiv (ord k) (ord n)) : k = n := by
  rcases Nat.lt_or_ge k n with hlt | hge
  · have : ord k ∈ ord n := ord_mem_iff.mpr ⟨k, hlt, Equiv.refl _⟩
    have : ord k ∈ ord k := mem_congr_right h.symm this
    exact (mem_irrefl (ord k) this).elim
  · rcases Nat.lt_or_ge n k with hgt | hge'
    · have : ord n ∈ ord k := ord_mem_iff.mpr ⟨n, hgt, Equiv.refl _⟩
      have : ord n ∈ ord n := mem_congr_right h this
      exact (mem_irrefl (ord n) this).elim
    · exact Nat.le_antisymm hge' hge

/-- Ordinals of distinct indices are inequivalent. -/
theorem ord_ne {k n : Nat} (h : k ≠ n) : ¬ Equiv (ord k) (ord n) :=
  fun he => h (ord_inj he)



/-! ### Congruence of the small combinators -/

theorem singleton_congr {a a' : PSet.{u}} (h : Equiv a a') :
    Equiv (singleton a) (singleton a') := by
  apply ext; intro z
  constructor
  · intro hz; exact mem_singleton.mpr ((mem_singleton.mp hz).trans h)
  · intro hz; exact mem_singleton.mpr ((mem_singleton.mp hz).trans h.symm)

theorem pair_congr {a a' b b' : PSet.{u}} (h₁ : Equiv a a') (h₂ : Equiv b b') :
    Equiv (pair a b) (pair a' b') := by
  apply ext; intro z
  constructor
  · intro hz
    rcases mem_pair.mp hz with h | h
    · exact mem_pair.mpr (Or.inl (h.trans h₁))
    · exact mem_pair.mpr (Or.inr (h.trans h₂))
  · intro hz
    rcases mem_pair.mp hz with h | h
    · exact mem_pair.mpr (Or.inl (h.trans h₁.symm))
    · exact mem_pair.mpr (Or.inr (h.trans h₂.symm))

theorem ordPair_congr {a a' b b' : PSet.{u}} (h₁ : Equiv a a') (h₂ : Equiv b b') :
    Equiv (ordPair a b) (ordPair a' b') :=
  pair_congr (singleton_congr h₁) (pair_congr h₁ h₂)

/-- `⋃` respects `≈`. -/
theorem sUnion_congr {s s' : PSet.{u}} (h : Equiv s s') :
    Equiv (sUnion s) (sUnion s') := by
  apply ext; intro z
  constructor <;> intro hz <;> obtain ⟨t, ht, hz'⟩ := mem_sUnion.mp hz
  · exact mem_sUnion.mpr ⟨t, mem_congr_right h ht, hz'⟩
  · exact mem_sUnion.mpr ⟨t, mem_congr_right h.symm ht, hz'⟩

/-! ### Membership lemmas -/

/-- `sep`'s members are members of `s`. -/
theorem mem_sep_subset {x : PSet.{u}} {p : PSet.{u} → Prop} {s : PSet.{u}} :
    x ∈ sep p s → x ∈ s := by
  rintro ⟨⟨i, _⟩, hi⟩
  exact ⟨i, hi⟩

/-- `⋃{x} ≈ x`. -/
theorem sUnion_singleton {x : PSet.{u}} : Equiv (sUnion (singleton x)) x := by
  apply ext; intro z
  constructor
  · intro h
    obtain ⟨t, ht, hz⟩ := mem_sUnion.mp h
    exact mem_congr_right (mem_singleton.mp ht) hz
  · intro h
    exact mem_sUnion.mpr ⟨x, mem_singleton.mpr Equiv.rfl, h⟩

/-- `⋃{A,B}` sees the members of `A` and of `B`. -/
theorem mem_sUnion_pair {z A B : PSet.{u}} :
    z ∈ sUnion (pair A B) ↔ z ∈ A ∨ z ∈ B := by
  constructor
  · intro h
    obtain ⟨t, ht, hz⟩ := mem_sUnion.mp h
    rcases mem_pair.mp ht with ht | ht
    · exact Or.inl (mem_congr_right ht hz)
    · exact Or.inr (mem_congr_right ht hz)
  · rintro (h | h)
    · exact mem_sUnion.mpr ⟨A, mem_pair.mpr (Or.inl Equiv.rfl), h⟩
    · exact mem_sUnion.mpr ⟨B, mem_pair.mpr (Or.inr Equiv.rfl), h⟩

/-- A conditional set, without a decision procedure: `≈ a` when `P` holds and
`≈ b` when `¬P` — each branch is `⋃{x ∈ {a} | P}`, which is `a` exactly on the
guarded case and empty otherwise. Unlike `cond`/`ite` this introduces no
`Decidable` instance into the value, so theorems quantifying over it pick up
no choice axiom. -/
def condP (P : Prop) (a b : PSet.{u}) : PSet.{u} :=
  sUnion (pair (sUnion (sep (fun _ => P) (singleton a)))
    (sUnion (sep (fun _ => ¬P) (singleton b))))

theorem mem_condP {P : Prop} {a b z : PSet.{u}} :
    z ∈ condP P a b ↔ (z ∈ a ∧ P) ∨ (z ∈ b ∧ ¬P) := by
  rw [condP, mem_sUnion_pair, mem_sUnion, mem_sUnion]
  constructor
  · rintro (⟨t, ht, hz⟩ | ⟨t, ht, hz⟩)
    · obtain ⟨i, hp, hti⟩ := mem_sep.mp ht
      exact Or.inl ⟨mem_congr_right hti.symm hz, hp⟩
    · obtain ⟨i, hp, hti⟩ := mem_sep.mp ht
      exact Or.inr ⟨mem_congr_right hti.symm hz, hp⟩
  · rintro (⟨hz, hp⟩ | ⟨hz, hp⟩)
    · exact Or.inl ⟨a, mem_sep.mpr ⟨PUnit.unit, hp, Equiv.refl _⟩, hz⟩
    · exact Or.inr ⟨b, mem_sep.mpr ⟨PUnit.unit, hp, Equiv.refl _⟩, hz⟩

theorem condP_congr {P P' : Prop} (hP : P ↔ P') {a a' b b' : PSet.{u}}
    (ha : Equiv a a') (hb : Equiv b b') : Equiv (condP P a b) (condP P' a' b') := by
  apply equiv_iff_mem.mpr; intro z
  rw [mem_condP, mem_condP]
  exact or_congr (and_congr (equiv_iff_mem.mp ha z) hP)
    (and_congr (equiv_iff_mem.mp hb z) (not_congr hP))

/-- The second component of a Kuratowski pair in `F` lives in `⋃⋃F`. -/
theorem mem_sUnion_sUnion_of_pair {F a b : PSet.{u}} (h : ordPair a b ∈ F) :
    b ∈ sUnion (sUnion F) :=
  mem_sUnion.mpr ⟨pair a b,
    mem_sUnion.mpr ⟨ordPair a b, h, mem_pair.mpr (Or.inr Equiv.rfl)⟩,
    mem_pair.mpr (Or.inr Equiv.rfl)⟩

/-- Likewise the first component. -/
theorem mem_sUnion_sUnion_of_pair_left {F a b : PSet.{u}} (h : ordPair a b ∈ F) :
    a ∈ sUnion (sUnion F) :=
  mem_sUnion.mpr ⟨pair a b,
    mem_sUnion.mpr ⟨ordPair a b, h, mem_pair.mpr (Or.inr Equiv.rfl)⟩,
    mem_pair.mpr (Or.inl Equiv.rfl)⟩

/-! ### Ordered-pair projections -/

/-- Intersection `⋂ s` = elements of `⋃ s` living in every member. -/
def sInter (s : PSet.{u}) : PSet.{u} :=
  sep (fun x => ∀ t, t ∈ s → x ∈ t) (sUnion s)

/-- First projection of a Kuratowski pair (junk-safe):
`pfst p = ⋃ ⋂ p`. -/
def pfst (p : PSet.{u}) : PSet.{u} := sUnion (sInter p)

theorem mem_sInter {x s : PSet.{u}} :
    x ∈ sInter s ↔ x ∈ sUnion s ∧ ∀ t, t ∈ s → x ∈ t := by
  constructor
  · rintro ⟨⟨i, hi⟩, hx⟩
    exact ⟨⟨i, hx⟩, fun t ht => mem_congr_left hx (hi t ht)⟩
  · rintro ⟨⟨i, hi⟩, hall⟩
    exact ⟨⟨i, fun t ht => mem_congr_left hi.symm (hall t ht)⟩, hi⟩

/-- `sInter` respects `≈`. -/
theorem sInter_congr {s s' : PSet.{u}} (h : Equiv s s') :
    Equiv (sInter s) (sInter s') := by
  apply ext; intro z
  rw [mem_sInter, mem_sInter]
  constructor <;> rintro ⟨hz, hall⟩
  · exact ⟨mem_congr_right (sUnion_congr h) hz,
      fun t ht => hall t (mem_congr_right h.symm ht)⟩
  · exact ⟨mem_congr_right (sUnion_congr h.symm) hz,
      fun t ht => hall t (mem_congr_right h ht)⟩

theorem singleton_equiv {a b : PSet.{u}} (h : Equiv (singleton a) (singleton b)) :
    Equiv a b :=
  mem_singleton.mp (mem_congr_right h (mem_singleton.mpr Equiv.rfl))

/-- The two-set case of Kuratowski injectivity: `{a,b} ≈ {c,d}` forces
the diagonal or the cross match (possibly both, when collapsed). -/
theorem pair_equiv {a b c d : PSet.{u}}
    (h : Equiv (pair a b) (pair c d)) :
    (Equiv a c ∧ Equiv b d) ∨ (Equiv a d ∧ Equiv b c) := by
  have ha : a ∈ pair c d :=
    mem_congr_right h (mem_pair.mpr (Or.inl Equiv.rfl))
  have hb : b ∈ pair c d :=
    mem_congr_right h (mem_pair.mpr (Or.inr Equiv.rfl))
  rcases mem_pair.mp ha with hac | had
  · rcases mem_pair.mp hb with hbc | hbd
    · -- a≈c, b≈c: use d ∈ {a,b} to collapse
      have hd : d ∈ pair a b :=
        mem_congr_right h.symm (mem_pair.mpr (Or.inr Equiv.rfl))
      rcases mem_pair.mp hd with hda | hdb
      · -- d ≈ a ≈ c ⇒ c ≈ d; b ≈ c ⇒ b ≈ d
        exact Or.inl ⟨hac, hbc.trans (hda.trans hac).symm⟩
      · exact Or.inl ⟨hac, hdb.symm⟩
    · exact Or.inl ⟨hac, hbd⟩
  · rcases mem_pair.mp hb with hbc | hbd
    · exact Or.inr ⟨had, hbc⟩
    · -- a≈d, b≈d: use c ∈ {a,b} to collapse
      have hc : c ∈ pair a b :=
        mem_congr_right h.symm (mem_pair.mpr (Or.inl Equiv.rfl))
      rcases mem_pair.mp hc with hca | hcb
      · -- c ≈ a ≈ d ⇒ d ≈ c; b ≈ d ⇒ b ≈ c
        exact Or.inr ⟨had, hbd.trans (hca.trans had).symm⟩
      · exact Or.inr ⟨had, hcb.symm⟩

/-- Kuratowski-pair injectivity. -/
theorem ordPair_equiv {a b c d : PSet.{u}}
    (h : Equiv (ordPair a b) (ordPair c d)) : Equiv a c ∧ Equiv b d := by
  rcases pair_equiv h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- {a}≈{c}, {a,b}≈{c,d}
    have hac : Equiv a c := singleton_equiv h1
    rcases pair_equiv h2 with ⟨_, hbd⟩ | ⟨had, hbc⟩
    · exact ⟨hac, hbd⟩
    · -- a≈d, b≈c; with a≈c: b ≈ c ≈ a ≈ d
      exact ⟨hac, hbc.trans (hac.symm.trans had)⟩
  · -- {a}≈{c,d}, {a,b}≈{c}: everything collapses
    have hca : Equiv c a :=
      mem_singleton.mp (mem_congr_right h1.symm
        (mem_pair.mpr (Or.inl Equiv.rfl)))
    have hda : Equiv d a :=
      mem_singleton.mp (mem_congr_right h1.symm
        (mem_pair.mpr (Or.inr Equiv.rfl)))
    have hbc : Equiv b c :=
      mem_singleton.mp (mem_congr_right h2
        (mem_pair.mpr (Or.inr Equiv.rfl)))
    exact ⟨hca.symm, hbc.trans hca |>.trans hda.symm⟩

/-- `⋂⟨a,b⟩ ≈ {a}`. -/
theorem sInter_ordPair {a b : PSet.{u}} :
    Equiv (sInter (ordPair a b)) (singleton a) := by
  apply ext; intro z
  constructor
  · intro hz
    exact (mem_sInter.mp hz).2 _ (mem_pair.mpr (Or.inl Equiv.rfl))
  · intro hz
    have hza : Equiv z a := mem_singleton.mp hz
    refine mem_sInter.mpr ⟨?_, ?_⟩
    · exact mem_sUnion.mpr ⟨singleton a,
        mem_pair.mpr (Or.inl Equiv.rfl), mem_singleton.mpr hza⟩
    · intro t ht
      rcases mem_pair.mp ht with ht | ht
      · exact mem_congr_right ht.symm (mem_singleton.mpr hza)
      · exact mem_congr_right ht.symm (mem_pair.mpr (Or.inl hza))

/-- `pfst ⟨a,b⟩ ≈ a`. -/
theorem pfst_pair {a b : PSet.{u}} : Equiv (pfst (ordPair a b)) a :=
  (sUnion_congr sInter_ordPair).trans sUnion_singleton

/-- `pfst` respects `≈`. -/
theorem pfst_congr {p q : PSet.{u}} (h : Equiv p q) : Equiv (pfst p) (pfst q) :=
  sUnion_congr (sInter_congr h)

/-! ### Function space and application -/

/-- Function application: `fapp F a = ⋃{b ∈ ⋃⋃F | ⟨a,b⟩ ∈ F}` — the
value of a functional graph, junk-safe otherwise. -/
def fapp (F a : PSet.{u}) : PSet.{u} :=
  sUnion (sep (fun b => ordPair a b ∈ F) (sUnion (sUnion F)))

/-- Graph of `g` on `A`: `{⟨a, g a⟩ | a ∈ A}`. -/
def mkLam (g : PSet.{u} → PSet.{u}) (A : PSet.{u}) : PSet.{u} :=
  sImage (fun a => ordPair a (g a)) A

/-- `g` is a functional graph on `A` with values in `B`. -/
def isFuncOn (A B : PSet.{u}) (g : PSet.{u}) : Prop :=
  (∀ a, a ∈ A → ∃ b, b ∈ B ∧ ordPair a b ∈ g) ∧
  (∀ p, p ∈ g → ∃ a, a ∈ A ∧ ∃ b, b ∈ B ∧ Equiv p (ordPair a b)) ∧
  (∀ a b b', ordPair a b ∈ g → ordPair a b' ∈ g → Equiv b b')

/-- Dependent variant: values land in `B a`. -/
def isFuncOnDep (A : PSet.{u}) (B : PSet.{u} → PSet.{u}) (g : PSet.{u}) : Prop :=
  (∀ a, a ∈ A → ∃ b, b ∈ B a ∧ ordPair a b ∈ g) ∧
  (∀ p, p ∈ g → ∃ a, a ∈ A ∧ ∃ b, b ∈ B a ∧ Equiv p (ordPair a b)) ∧
  (∀ a b b', ordPair a b ∈ g → ordPair a b' ∈ g → Equiv b b')

/-- Cartesian product `A × B` as a set of pairs. -/
def prod (A B : PSet.{u}) : PSet.{u} :=
  sUnion (sImage (fun a => sImage (ordPair a) B) A)

/-- Powerset `𝒫 s` = all `≈`-representable subsets, indexed by
predicates on the index type. -/
def powerset : PSet.{u} → PSet.{u}
  | mk α f => mk (α → Prop) fun P => mk { a : α // P a } fun ⟨a, _⟩ => f a

/-- Dependent function space. -/
def piSet (A : PSet.{u}) (B : PSet.{u} → PSet.{u}) : PSet.{u} :=
  sep (isFuncOnDep A B) (powerset (prod A (sUnion (sImage B A))))

/-- Cartesian product membership. -/
theorem mem_prod {p A B : PSet.{u}} :
    p ∈ prod A B ↔ ∃ a, a ∈ A ∧ ∃ b, b ∈ B ∧ Equiv p (ordPair a b) := by
  constructor
  · rintro ⟨⟨i, j⟩, hp⟩
    exact ⟨_, ⟨i, Equiv.refl _⟩, _, ⟨j, Equiv.refl _⟩, hp.symm⟩
  · rintro ⟨a, ⟨i, hi⟩, b, ⟨j, hj⟩, hp⟩
    exact ⟨⟨i, j⟩, (ordPair_congr hi hj).trans hp.symm⟩

/-- The value of a functional graph at `a`, given `⟨a,b⟩ ∈ F`, is `b`. -/
theorem fapp_eq_of_pair {A B F a b : PSet.{u}} (hF : isFuncOn A B F)
    (hab : ordPair a b ∈ F) : Equiv (fapp F a) b := by
  apply ext; intro z
  constructor
  · intro hz
    obtain ⟨t, ht, hz'⟩ := mem_sUnion.mp hz
    obtain ⟨⟨i, hi⟩, ht'⟩ := ht
    -- hi : ordPair a (Func i) ∈ F; uniqueness ⇒ Func i ≈ b
    have hb : Equiv ((sUnion (sUnion F)).Func i) b := hF.2.2 a _ b hi hab
    exact mem_congr_right (ht'.symm.trans hb) hz'
  · intro hz
    -- b ∈ sep: rep-level via ⋃⋃F membership and ⟨a,b⟩ ∈ F
    obtain ⟨i, hi⟩ := mem_sUnion_sUnion_of_pair hab
    have hQi : ordPair a ((sUnion (sUnion F)).Func i) ∈ F :=
      mem_congr_left (ordPair_congr Equiv.rfl hi.symm) hab
    refine mem_sUnion.mpr ⟨(sUnion (sUnion F)).Func i, ⟨⟨i, hQi⟩, ?_⟩,
      ?_⟩
    · exact Equiv.refl _
    · exact mem_congr_right hi.symm hz

/-- Applying a graph built by `mkLam` at `a ∈ A` gives `g a`. -/
theorem fapp_mkLam {g : PSet.{u} → PSet.{u}}
    (hg : ∀ x y : PSet.{u}, Equiv x y → Equiv (g x) (g y))
    {A a : PSet.{u}} (ha : a ∈ A) :
    Equiv (fapp (mkLam g A) a) (g a) := by
  -- ⟨a, g a⟩ ∈ mkLam g A, and every ⟨a,·⟩ ∈ mkLam has · ≈ g a
  obtain ⟨i, hi⟩ := ha
  have hpair : ordPair a (g a) ∈ mkLam g A :=
    ⟨i, ordPair_congr hi (hg _ _ hi)⟩
  have hF : isFuncOn A (sImage g A) (mkLam g A) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨j, hj⟩ := hx
      exact ⟨g (A.Func j), ⟨j, Equiv.refl _⟩,
        ⟨j, ordPair_congr hj Equiv.rfl⟩⟩
    · intro p hp
      obtain ⟨j, hj⟩ := hp
      exact ⟨A.Func j, ⟨j, Equiv.refl _⟩, g (A.Func j), ⟨j, Equiv.refl _⟩,
        hj.symm⟩
    · intro x b b' hb hb'
      obtain ⟨j, hj⟩ := hb
      obtain ⟨j', hj'⟩ := hb'
      obtain ⟨hxj, hbj⟩ := ordPair_equiv hj
      obtain ⟨hxj', hbj'⟩ := ordPair_equiv hj'
      -- b ≈ g(Aj) , b' ≈ g(Aj') , Aj ≈ x ≈ Aj' ⇒ b ≈ b'
      exact hbj.symm.trans ((hg _ _ (hxj.trans hxj'.symm)).trans hbj')
  exact fapp_eq_of_pair hF hpair

/-- Eta for graphs: re-graphing `fapp F` over `A` recovers `F`. -/
theorem mkLam_fapp {A B F : PSet.{u}} (hF : isFuncOn A B F) :
    Equiv (mkLam (fun a => fapp F a) A) F := by
  apply ext; intro p
  constructor
  · intro hp
    obtain ⟨i, hi⟩ := hp
    -- hi : Equiv (ordPair (A.Func i) (fapp F (A.Func i))) p
    obtain ⟨b, _, hab⟩ := hF.1 (A.Func i) ⟨i, Equiv.refl _⟩
    have hfapp : Equiv (fapp F (A.Func i)) b := fapp_eq_of_pair hF hab
    exact mem_congr_left ((ordPair_congr Equiv.rfl hfapp.symm).trans hi) hab
  · intro hp
    obtain ⟨a, ha, b, _, hp'⟩ := hF.2.1 p hp
    obtain ⟨i, hi⟩ := ha
    -- ⟨Ai, b⟩ ∈ F by transport, so fapp (Ai) ≈ b
    have hab' : ordPair (A.Func i) b ∈ F :=
      mem_congr_left (hp'.trans (ordPair_congr hi.symm Equiv.rfl)) hp
    have hfapp : Equiv (fapp F (A.Func i)) b := fapp_eq_of_pair hF hab'
    exact ⟨i, (ordPair_congr hi hfapp).trans hp'.symm⟩


/-- The domain set of a functional graph is its first-component image:
`sImage pfst F` recovers `A` exactly when `F` is functional on `A`. This is
the λ-IH domain the `ihAt` pi-case uses — see `RcicF3RecCore`. -/
theorem sImage_pfst_of_isFuncOnDep {A F : PSet.{u}} {B : PSet.{u} → PSet.{u}}
    (hF : isFuncOnDep A B F) : Equiv (sImage pfst F) A := by
  apply ext; intro p; constructor
  · intro hp
    obtain ⟨i, hi⟩ := hp
    obtain ⟨a, ha, _, _, he⟩ := hF.2.1 (F.Func i) ⟨i, Equiv.refl _⟩
    exact mem_congr_left (((pfst_congr he).trans pfst_pair).symm.trans hi) ha
  · intro hp
    obtain ⟨i, hi⟩ := hp
    obtain ⟨b, _, hab⟩ := hF.1 (A.Func i) ⟨i, Equiv.refl _⟩
    obtain ⟨j, hj⟩ := hab
    exact ⟨j, ((pfst_congr hj).trans pfst_pair).trans hi⟩

/-- The first-component image of the empty graph is empty. -/
theorem sImage_pfst_pempty : Equiv (sImage pfst (pempty.{u})) pempty := by
  apply ext; intro p; constructor
  · intro hp; obtain ⟨i, _⟩ := hp; exact i.elim
  · intro hp; obtain ⟨i, _⟩ := hp; exact i.elim


end PSet

end Rcic.F3

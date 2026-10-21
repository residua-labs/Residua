/-!
# RcicModelPSet — model carrier `PS`

Lane R1-b segment S1 (scope: `sortRow` + consistency only;
`piRow`/`famAppRow` remain `W-F05b-PiRow`).

The consistency model interprets `Expr` denotationally into `PS`:
hereditarily `Type 0`-branching well-founded trees, a `PSet`-style
carrier. `≈` is extensional equivalence; `∈` is `≈`-saturated
membership. No quotient, no `Classical`: all later reasoning is
up to `≈`.

`closure_claim = 0`.
-/

namespace Rcic.Model

/-- The model carrier: well-founded extensional trees. `mk α f` is the
set whose elements are the `f a`. -/
inductive PS : Type 1 where
  | mk (α : Type) (f : α → PS)

namespace PS

/-- The index type of a set's element family. -/
def Idx : PS → Type
  | mk α _ => α

/-- The element family of a set. -/
def Func : (s : PS) → s.Idx → PS
  | mk _ f => f

/-- Extensional equivalence of sets. -/
def Equiv : PS → PS → Prop
  | mk _α f, mk _β g =>
      (∀ a, ∃ b, Equiv (f a) (g b)) ∧
      (∀ b, ∃ a, Equiv (f a) (g b))

/-- `≈`-saturated membership: `x ∈ mk α f` iff `x ≈ f a` for some `a`. -/
def Mem (s : PS) (x : PS) : Prop :=
  ∃ a : s.Idx, Equiv (s.Func a) x

instance : Membership PS PS := ⟨Mem⟩

/-- `∈` unfolds over `mk` as membership in the family. -/
theorem mem_def {x : PS} {α : Type} {f : α → PS} :
    x ∈ mk α f ↔ ∃ a, Equiv (f a) x :=
  Iff.rfl

/-! ### `Equiv` is an equivalence -/

theorem Equiv.refl (x : PS) : Equiv x x := by
  induction x with
  | mk α f ih => exact ⟨fun a => ⟨a, ih a⟩, fun a => ⟨a, ih a⟩⟩

theorem Equiv.symm {x y : PS} : Equiv x y → Equiv y x := by
  revert y
  induction x with
  | mk α f ih =>
    intro y h
    cases y with
    | mk β g =>
      obtain ⟨h₁, h₂⟩ := h
      exact ⟨fun b => let ⟨a, ha⟩ := h₂ b; ⟨a, ih a ha⟩,
             fun a => let ⟨b, hb⟩ := h₁ a; ⟨b, ih a hb⟩⟩

theorem Equiv.trans {x y z : PS} : Equiv x y → Equiv y z → Equiv x z := by
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

theorem Equiv.rfl {x : PS} : Equiv x x := Equiv.refl x

/-- Left-to-right component of `≈`, at the family level. -/
theorem Equiv.exists_mem_left {x y : PS} (h : Equiv x y) (a : x.Idx) :
    ∃ b : y.Idx, Equiv (x.Func a) (y.Func b) := by
  cases x with
  | mk α f =>
  cases y with
  | mk β g =>
    obtain ⟨hf, _⟩ := h
    exact hf a

/-- Right-to-left component of `≈`, at the family level. -/
theorem Equiv.exists_mem_right {x y : PS} (h : Equiv x y) (b : y.Idx) :
    ∃ a : x.Idx, Equiv (x.Func a) (y.Func b) := by
  cases x with
  | mk α f =>
  cases y with
  | mk β g =>
    obtain ⟨_, hb⟩ := h
    exact hb b

/-! ### Membership congruence -/

theorem mem_congr_left {x x' : PS} {s : PS} (h : Equiv x x') :
    x ∈ s → x' ∈ s :=
  fun ⟨a, ha⟩ => ⟨a, ha.trans h⟩

theorem mem_congr_right {x s s' : PS} (h : Equiv s s') :
    x ∈ s → x ∈ s' :=
  fun ⟨a, ha⟩ =>
    let ⟨b, hb⟩ := h.exists_mem_left a
    ⟨b, hb.symm.trans ha⟩

theorem Equiv.mem_left {x x' : PS} {s : PS} (h : Equiv x x') :
    x ∈ s ↔ x' ∈ s :=
  ⟨mem_congr_left h, mem_congr_left h.symm⟩

theorem Equiv.mem_right {x : PS} {s s' : PS} (h : Equiv s s') :
    x ∈ s ↔ x ∈ s' :=
  ⟨mem_congr_right h, mem_congr_right h.symm⟩

/-- Extensionality: elementwise-`≈` equal sets are `≈`. -/
theorem ext {x y : PS} (h : ∀ z, z ∈ x ↔ z ∈ y) : Equiv x y := by
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
theorem equiv_iff_mem {x y : PS} :
    Equiv x y ↔ ∀ z, z ∈ x ↔ z ∈ y := by
  constructor
  · intro h z; exact h.mem_right
  · intro h; exact ext h

/-- Subset (up to `≈`). -/
def Subset (x y : PS) : Prop := ∀ z, z ∈ x → z ∈ y

theorem Subset.refl (x : PS) : Subset x x := fun _ h => h

theorem Subset.trans {x y z : PS} (hxy : Subset x y) (hyz : Subset y z) :
    Subset x z := fun _ h => hyz _ (hxy _ h)

theorem Subset.equiv {x y : PS} (h₁ : Subset x y) (h₂ : Subset y x) :
    Equiv x y :=
  ext fun _ => ⟨h₁ _, h₂ _⟩

/-! ### Small combinators -/

/-- The empty set. -/
def pempty : PS := mk Empty Empty.elim

/-- Singleton `{x}`. -/
def singleton (x : PS) : PS := mk PUnit fun _ => x

/-- Unordered pair `{x, y}`. -/
def pair (x y : PS) : PS := mk Bool fun
  | true => x
  | false => y

/-- Kuratowski ordered pair `{{x}, {x, y}}`. -/
def ordPair (x y : PS) : PS := pair (singleton x) (pair x y)

/-- `s ∪ {x}`. -/
def insert (x s : PS) : PS :=
  mk (Option s.Idx) fun
    | none => x
    | some a => s.Func a

/-- Union `⋃ s`. -/
def sUnion (s : PS) : PS :=
  mk (Σ i : s.Idx, (s.Func i).Idx) fun p => (s.Func p.1).Func p.2

/-- Separation `{x ∈ s | p x}`, where `p` sees representatives. -/
def sep (p : PS → Prop) (s : PS) : PS :=
  mk {i : s.Idx // p (s.Func i)} fun ⟨i, _⟩ => s.Func i

/-- Image `{h x | x ∈ s}` (as a family over the index). -/
def sImage (h : PS → PS) (s : PS) : PS := mk s.Idx fun i => h (s.Func i)

theorem not_mem_pempty {x : PS} : ¬ x ∈ pempty :=
  fun ⟨a, _⟩ => a.elim

theorem mem_singleton {x y : PS} : x ∈ singleton y ↔ Equiv x y := by
  constructor
  · rintro ⟨_, ha⟩; exact ha.symm
  · intro h; exact ⟨PUnit.unit, h.symm⟩

theorem mem_pair {z x y : PS} : z ∈ pair x y ↔ Equiv z x ∨ Equiv z y := by
  constructor
  · rintro ⟨b, hb⟩
    cases b with
    | true => exact Or.inl hb.symm
    | false => exact Or.inr hb.symm
  · rintro (h | h)
    · exact ⟨true, h.symm⟩
    · exact ⟨false, h.symm⟩

theorem mem_insert {z x : PS} {s : PS} :
    z ∈ insert x s ↔ Equiv z x ∨ z ∈ s := by
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | none => exact Or.inl hi.symm
    | some a => exact Or.inr ⟨a, hi⟩
  · rintro (h | ⟨a, ha⟩)
    · exact ⟨none, h.symm⟩
    · exact ⟨some a, ha⟩

theorem mem_sUnion {x : PS} {s : PS} :
    x ∈ sUnion s ↔ ∃ t, t ∈ s ∧ x ∈ t := by
  constructor
  · rintro ⟨⟨i, j⟩, h⟩
    exact ⟨s.Func i, ⟨i, Equiv.refl _⟩, ⟨j, h⟩⟩
  · rintro ⟨t, ⟨i, hi⟩, ⟨j, hj⟩⟩
    obtain ⟨j', hj'⟩ := hi.exists_mem_right j
    exact ⟨⟨i, j'⟩, hj'.trans hj⟩

theorem mem_sep {x : PS} {p : PS → Prop} {s : PS} :
    x ∈ sep p s ↔ ∃ i : s.Idx, p (s.Func i) ∧ Equiv (s.Func i) x := by
  constructor
  · rintro ⟨⟨i, hp⟩, he⟩; exact ⟨i, hp, he⟩
  · rintro ⟨i, hp, he⟩; exact ⟨⟨i, hp⟩, he⟩

theorem mem_sImage {x : PS} {h : PS → PS} {s : PS} :
    x ∈ sImage h s ↔ ∃ i : s.Idx, Equiv (h (s.Func i)) x :=
  Iff.rfl

theorem subset_insert {x s : PS} : Subset s (insert x s) :=
  fun _ h => mem_insert.mpr (Or.inr h)

theorem insert_subset {x s t : PS} (hx : x ∈ t) (hs : Subset s t) :
    Subset (insert x s) t := fun _ hz =>
  match mem_insert.mp hz with
  | Or.inl h => mem_congr_left h.symm hx
  | Or.inr h => hs _ h

/-- The empty denotation / default element `J₀ = ∅`. -/
def junk₀ : PS := pempty

/-- The inhabited witness-token `J₁ = {∅}`. -/
def junk₁ : PS := singleton pempty

theorem junk₁_mem : junk₀ ∈ junk₁ :=
  mem_singleton.mpr Equiv.rfl

theorem junk₀_ne_junk₁ : ¬ Equiv junk₀ junk₁ := by
  intro h
  have : junk₀ ∈ junk₁ := junk₁_mem
  have : junk₀ ∈ junk₀ := mem_congr_right h.symm this
  exact not_mem_pempty this

/-! ### Foundation -/

/-- Element-first membership relation (for `Acc`/`WellFounded`). -/
def elemOf (x s : PS) : Prop := x ∈ s

/-- `Acc` transports across `≈`. -/
theorem acc_equiv {x y : PS} (h : Equiv x y) (ha : Acc elemOf x) :
    Acc elemOf y :=
  Acc.intro y fun z hz =>
    match ha with
    | .intro _ hx => hx z (mem_congr_right h.symm hz)

/-- Every set is `∈`-accessible. -/
theorem acc_mem (x : PS) : Acc elemOf x := by
  induction x with
  | mk α f ih =>
    apply Acc.intro
    rintro y ⟨a, ha⟩
    exact acc_equiv ha (ih a)

theorem mem_wf : WellFounded elemOf := ⟨acc_mem⟩

/-- Self-membership is impossible: `x ∈ x` gives `y ∈ x` with `y ≈ x`,
and `y ≈ x` puts an `≈`-copy of `y` back inside `y`. -/
theorem mem_irrefl_aux : ∀ s : PS, ¬ ∃ y, y ∈ s ∧ Equiv y s :=
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
theorem mem_irrefl (x : PS) : ¬ x ∈ x := by
  intro hx
  obtain ⟨a, ha⟩ := hx
  exact mem_irrefl_aux x ⟨x.Func a, ⟨a, Equiv.refl _⟩, ha⟩

/-! ### Finite ordinals (`σ`-codes for sorts live in `RcicModelOps`) -/

/-- The finite von Neumann ordinal `n` as a set. -/
def ord : Nat → PS
  | 0 => pempty
  | n + 1 => insert (ord n) (ord n)

/-- Membership in a finite ordinal. -/
theorem ord_mem_iff {x : PS} {n : Nat} :
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

end PS
end Rcic.Model

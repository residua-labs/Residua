/-!
# F-ι★-8 — the foundation-multiset measure (plain-side S3)

`research/rcic/irr-postponement/MEASURE_F8.md` / `MEASURE_F8_FORMAL.md`:
the `(d,s)` pair does NOT close the `U → X → P → U` cycle; the accepted
measure is the foundation multiset over the top bundle's derivation DAG,
lex-paired with total member size. No `Multiset`/Dershowitz–Manna
machinery exists on-tree (two searches; no Batteries/mathlib), so this
module is self-contained on `List Nat`:

- `vecSum L` : `Σ_{x∈l} (L+1)^x` — the `Nat` termination witness.
- `MulLT` : the multiset order in DM-step form — `Perm n (X ++ out)`,
  `Perm m (X ++ inn)`, `out ≠ []`, every `inn`-element below some
  `out`-element. The transitive closure of single-element
  Dershowitz–Manna steps.
- `MulLTBound` : `MulLT` + the maintained fan-out bound `|inn| ≤ L`;
  `vecSum`-sound. This is the form the recursion maintains.
- `mulLTBound_wf` : WF of the bounded relation — what
  `termination_by` consumes at the mutual.
- `FM`/`S`/`muLt` : the bundle measure `μ = (FM, S)`, parameterized on
  each member's `found` (cited-leaf ranks ≺ h₀) and `dsize`.
- `E0…E5` : the per-edge descent statements of MEASURE_F8_FORMAL §4,
  as generic lemmas over `found`/`dsize`.
-/

namespace Rcic.S3

/-! ## power facts (private — no stdlib-name guesses) -/

private theorem pow_pos {b : Nat} (hb : 0 < b) : ∀ x : Nat, 0 < b ^ x
  | 0 => Nat.zero_lt_one
  | x + 1 => by
    rw [Nat.pow_succ]
    exact Nat.mul_pos (pow_pos hb x) hb

private theorem pow_le_of_le {b : Nat} (hb : 0 < b) {x y : Nat}
    (h : x ≤ y) : b ^ x ≤ b ^ y := by
  obtain ⟨k, rfl⟩ := Nat.le.dest h
  rw [Nat.pow_add]
  exact Nat.le_mul_of_pos_right (b ^ x) (pow_pos hb k)

private theorem pow_lt_of_lt {b : Nat} (hb : 1 < b) {x y : Nat}
    (h : x < y) : b ^ x < b ^ y := by
  obtain ⟨k, rfl⟩ := Nat.le.dest (Nat.le_of_lt h)
  cases k with
  | zero => exact absurd h (Nat.lt_irrefl x)
  | succ k =>
    -- goal: b^x < b^(x + (k+1))
    rw [Nat.pow_add]
    have hbk : 1 < b ^ (k+1) := by
      rw [Nat.pow_succ]
      have hp : 0 < b ^ k := pow_pos (show 0 < b by omega) k
      have hle : b ≤ b ^ k * b := by
        calc b = 1 * b := (Nat.one_mul b).symm
          _ ≤ b ^ k * b := Nat.mul_le_mul_right _ hp
      omega
    have hx : 0 < b ^ x := pow_pos (show 0 < b by omega) x
    calc b ^ x = b ^ x * 1 := (Nat.mul_one _).symm
      _ < b ^ x * b ^ (k+1) := Nat.mul_lt_mul_of_pos_left hbk hx

/-! ## `vecSum` : the `Nat` witness -/

/-- `Σ_{x∈l} (L+1)^x` — the multiset-to-`Nat` measure. `L` is a global
    bound on the number of members the recursion can introduce per step;
    under `|inn| ≤ L` every DM step strictly decreases the sum. -/
def vecSum (L : Nat) (l : List Nat) : Nat := (l.map (fun x => (L+1)^x)).sum

theorem vecSum_nil (L : Nat) : vecSum L [] = 0 := rfl

theorem vecSum_cons (L : Nat) (x : Nat) (l : List Nat) :
    vecSum L (x :: l) = (L+1)^x + vecSum L l := by
  simp only [vecSum, List.map_cons, List.sum_cons]

theorem vecSum_append (L : Nat) (m n : List Nat) :
    vecSum L (m ++ n) = vecSum L m + vecSum L n := by
  induction m with
  | nil => simp [vecSum]
  | cons x xs ih =>
    rw [List.cons_append, vecSum_cons, vecSum_cons, ih]
    omega

theorem vecSum_perm (L : Nat) {m n : List Nat} (h : m.Perm n) :
    vecSum L m = vecSum L n := by
  induction h
  · rfl
  · rename_i x _ ih
    rw [vecSum_cons, vecSum_cons, ih]
  · rename_i x y l
    rw [vecSum_cons, vecSum_cons, vecSum_cons, vecSum_cons]
    omega
  · rename_i _ _ ih1 ih2
    rw [ih1, ih2]

/-- every member contributes a positive power: the sum is positive on
    nonempty lists. -/
theorem vecSum_pos (L : Nat) {l : List Nat} (hne : l ≠ []) :
    0 < vecSum L l := by
  cases l with
  | nil => exact absurd rfl hne
  | cons x xs =>
    rw [vecSum_cons]
    have hp : 0 < (L+1)^x := pow_pos (Nat.succ_pos L) x
    omega

/-- a member's power is dominated by the sum. -/
theorem pow_le_vecSum_of_mem (L : Nat) {l : List Nat} {x : Nat}
    (h : x ∈ l) : (L+1)^x ≤ vecSum L l := by
  induction l with
  | nil => exact absurd h (List.not_mem_nil x)
  | cons y ys ih =>
    rw [vecSum_cons]
    cases h with
    | head => omega
    | tail _ hys =>
      have := ih hys
      omega

/-! ## `maxOf` : the list max as a fold -/

/-- the maximum of a list, as a `foldl` from `0`. -/
def maxOf (l : List Nat) : Nat := l.foldl Nat.max 0

/-- `Nat.max`-stated bridges — `rw` matches `Nat.max`, not `Max.max`. -/
private theorem nmax_eq_left {a b : Nat} (h : b ≤ a) :
    Nat.max a b = a := Nat.max_eq_left h

private theorem nmax_eq_right {a b : Nat} (h : a ≤ b) :
    Nat.max a b = b := Nat.max_eq_right h

private theorem nmax_le_left (a b : Nat) : a ≤ Nat.max a b :=
  Nat.le_max_left a b

private theorem nmax_le_right (a b : Nat) : b ≤ Nat.max a b :=
  Nat.le_max_right a b

theorem foldl_max_ge (l : List Nat) (a : Nat) : a ≤ l.foldl Nat.max a := by
  induction l generalizing a with
  | nil => exact Nat.le_refl a
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (nmax_le_left a x) (ih _)

theorem mem_le_foldl_max {x : Nat} {l : List Nat} (h : x ∈ l) (a : Nat) :
    x ≤ l.foldl Nat.max a := by
  induction l generalizing a with
  | nil => exact absurd h (List.not_mem_nil x)
  | cons y ys ih =>
    cases h with
    | head =>
      simp only [List.foldl_cons]
      exact Nat.le_trans (nmax_le_right a x) (foldl_max_ge ys _)
    | tail _ hys =>
      simp only [List.foldl_cons]
      exact ih hys _

theorem foldl_max_mem_or (l : List Nat) (a : Nat) :
    l.foldl Nat.max a = a ∨ l.foldl Nat.max a ∈ l := by
  induction l generalizing a with
  | nil => left; rfl
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases ih (a.max y) with h1 | h2
    · rcases Nat.le_total y a with hya | hay
      · left
        have e : Nat.max a y = a := nmax_eq_left hya
        rw [e] at h1 ⊢
        exact h1
      · right
        have e : Nat.max a y = y := nmax_eq_right hay
        rw [e] at h1 ⊢
        rw [h1]
        exact List.mem_cons_self y ys
    · right; exact List.mem_cons_of_mem y h2

theorem maxOf_le {x : Nat} {l : List Nat} (h : x ∈ l) : x ≤ maxOf l :=
  mem_le_foldl_max h 0

theorem maxOf_mem {l : List Nat} (hne : l ≠ []) : maxOf l ∈ l := by
  rcases foldl_max_mem_or l 0 with h | h
  · cases l with
    | nil => exact absurd rfl hne
    | cons y ys =>
      have hy : y ≤ maxOf (y :: ys) := maxOf_le (List.mem_cons_self y ys)
      have e : maxOf (y :: ys) = 0 := h
      rw [e] at hy
      have hy0 : y = 0 := Nat.eq_zero_of_le_zero hy
      rw [e, hy0]
      exact List.mem_cons_self 0 ys
  · exact h

/-- elements all `< B` sum to at most `|l| * (L+1)^(pred B)` — the
    per-element bound, counted. -/
theorem vecSum_le_length_pow (L : Nat) {l : List Nat} {B : Nat}
    (h : ∀ x ∈ l, x < B) : vecSum L l ≤ l.length * (L+1)^B.pred := by
  induction l with
  | nil => simp [vecSum]
  | cons x xs ih =>
    have hx : x < B := h x (List.mem_cons_self x xs)
    have hxs : ∀ y ∈ xs, y < B := fun y hy => h y (List.mem_cons_of_mem x hy)
    rw [vecSum_cons, List.length_cons]
    have hxp : (L+1)^x ≤ (L+1)^B.pred := by
      apply pow_le_of_le (Nat.succ_pos L)
      exact Nat.le_pred_of_lt hx
    calc (L+1)^x + vecSum L xs
        ≤ (L+1)^B.pred + xs.length * (L+1)^B.pred :=
          Nat.add_le_add hxp (ih hxs)
      _ = (xs.length + 1) * (L+1)^B.pred := by
          rw [Nat.add_comm, Nat.add_mul, Nat.one_mul]

/-- the spawn bound: at most `L` elements each `< B` sum to strictly
    less than `(L+1)^B`. The heart of `vecSum`-soundness for the DM step
    "replace `B` by `≤ L` smaller elements". -/
theorem vecSum_lt_pow_of_forall_lt (L : Nat) {l : List Nat} {B : Nat}
    (hB : 0 < B) (h : ∀ x ∈ l, x < B) (hlen : l.length ≤ L) :
    vecSum L l < (L+1)^B := by
  have h1 := vecSum_le_length_pow L h
  have h2 : l.length * (L+1)^B.pred ≤ L * (L+1)^B.pred :=
    Nat.mul_le_mul_right _ hlen
  have hpow : 0 < (L+1)^B.pred := pow_pos (Nat.succ_pos L) _
  have h3 : L * (L+1)^B.pred < (L+1) * (L+1)^B.pred :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self L) hpow
  have h4 : (L+1) * (L+1)^B.pred = (L+1)^B := by
    calc (L+1) * (L+1)^B.pred = (L+1)^B.pred * (L+1) := Nat.mul_comm _ _
      _ = (L+1)^(B.pred.succ) := (Nat.pow_succ _ _).symm
      _ = (L+1)^B := by rw [Nat.succ_pred_eq_of_pos hB]
  exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) (by rw [h4] at h3; exact h3)

/-! ## `MulLT` and DM-step soundness -/

/-- sub-multiset, permutation-form: `m` fits inside `n`. -/
def subMul (m n : List Nat) : Prop := ∃ m', n.Perm (m ++ m')

/-- strict sub-multiset: inclusion with a nonempty complement. -/
def subMulStrict (m n : List Nat) : Prop :=
  ∃ m', m' ≠ [] ∧ n.Perm (m ++ m')

/-- the multiset order, DM-step form: `n` decomposes into a shared part
    `X` plus a nonempty remainder `out`; `m` shares `X` and replaces
    `out` by `inn`, where every `inn`-element is strictly below some
    `out`-element. `X` may be empty — "replace everything by smaller"
    is still a strict decrease. This is the transitive closure of the
    single-element Dershowitz–Manna steps. -/
def MulLT (m n : List Nat) : Prop :=
  ∃ X inn out, m.Perm (X ++ inn) ∧ n.Perm (X ++ out) ∧ out ≠ [] ∧
    (∀ y ∈ inn, ∃ x ∈ out, y < x)

/-- `MulLT` with the maintained fan-out bound `|inn| ≤ L` — the form the
    recursion maintains, and the form `vecSum` consumes. -/
def MulLTBound (L : Nat) (m n : List Nat) : Prop :=
  ∃ X inn out, m.Perm (X ++ inn) ∧ n.Perm (X ++ out) ∧ out ≠ [] ∧
    (∀ y ∈ inn, ∃ x ∈ out, y < x) ∧ inn.length ≤ L

theorem MulLTBound.mulLT {L : Nat} {m n : List Nat}
    (h : MulLTBound L m n) : MulLT m n := by
  rcases h with ⟨X, inn, out, hm, hn, hout, hb, _⟩
  exact ⟨X, inn, out, hm, hn, hout, hb⟩

/-- DM-step soundness for `vecSum` — the strict decrease. -/
theorem vecSum_lt_of_dmStep (L : Nat) {X inn out : List Nat}
    (hout : out ≠ [])
    (h : ∀ y ∈ inn, ∃ x ∈ out, y < x)
    (hlen : inn.length ≤ L) :
    vecSum L (X ++ inn) < vecSum L (X ++ out) := by
  rw [vecSum_append, vecSum_append]
  have hpos : 0 < vecSum L out := vecSum_pos L hout
  cases inn with
  | nil =>
    rw [vecSum_nil]
    exact Nat.add_lt_add_left hpos _
  | cons a as =>
    rcases h a (List.mem_cons_self a as) with ⟨x, hx, hax⟩
    have hmx : x ≤ maxOf out := maxOf_le hx
    have hB : 0 < maxOf out :=
      Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hax) hmx
    have hall : ∀ y ∈ a :: as, y < maxOf out := by
      intro y hy
      rcases h y hy with ⟨x', hx', hlt⟩
      exact Nat.lt_of_lt_of_le hlt (maxOf_le hx')
    have hsum := vecSum_lt_pow_of_forall_lt L hB hall hlen
    have hmem : (L+1)^(maxOf out) ≤ vecSum L out :=
      pow_le_vecSum_of_mem L (maxOf_mem hout)
    exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le hsum hmem) _

/-- the core WF lemma: a bounded DM step strictly decreases `vecSum`. -/
theorem mulLTBound_desc (L : Nat) {m n : List Nat} (h : MulLTBound L m n) :
    vecSum L m < vecSum L n := by
  rcases h with ⟨X, inn, out, hm, hn, hout, hb, hl⟩
  rw [vecSum_perm L hm, vecSum_perm L hn]
  exact vecSum_lt_of_dmStep L hout hb hl

/-- WF of the bounded DM order: every `MulLTBound L` step strictly
    decreases `vecSum L`, so the relation is well-founded. Stated as
    inverse image of `Nat.lt` — what `termination_by` consumes. -/
theorem mulLTBound_wf (L : Nat) :
    WellFounded (fun m n : List Nat => vecSum L m < vecSum L n) :=
  InvImage.wf (fun l : List Nat => vecSum L l) Nat.lt_wfRel.wf

/-! ## the generators: producing `MulLT`/`MulLTBound` -/

/-- strict sub-multiset ⇒ bounded `MulLT` (remove `r` nonempty, insert
    nothing — `inn = []`, bound free). -/
theorem mulLTBound_of_subMulStrict (L : Nat) {m n : List Nat}
    (h : subMulStrict m n) : MulLTBound L m n := by
  rcases h with ⟨r, hr, hperm⟩
  refine ⟨m, [], r, ?_, hperm, hr,
      fun y hy => absurd hy (List.not_mem_nil y), Nat.zero_le L⟩
  rw [List.append_nil]

/-- "replace everything": every element of `m` is below some element of
    the nonempty `n` — the spawn edge (E3). -/
theorem mulLTBound_of_forall_lt (L : Nat) {m n : List Nat} (hn : n ≠ [])
    (h : ∀ y ∈ m, ∃ x ∈ n, y < x) (hlen : m.length ≤ L) :
    MulLTBound L m n :=
  ⟨[], m, n, List.Perm.refl m, List.Perm.refl n, hn, h, hlen⟩

/-- "replace one element": `a :: X` is below `X ++ (b :: r)` when
    `a < b` — the child keeps the shared part `X` and swaps one member
    for a strictly smaller rank (E4's shape). -/
theorem mulLTBound_of_replace (L : Nat) {X : List Nat} {a b : Nat}
    {r : List Nat} (h : a < b) (hL : 0 < L) :
    MulLTBound L (a :: X) (X ++ b :: r) := by
  refine ⟨X, [a], b :: r, ?_, List.Perm.refl _, List.cons_ne_nil b r, ?_, ?_⟩
  · exact (List.perm_append_singleton a X).symm
  · intro y hy
    cases hy with
    | head => exact ⟨b, List.mem_cons_self b r, h⟩
    | tail _ hys => exact absurd hys (List.not_mem_nil y)
  · exact Nat.succ_le_of_lt hL

/-- `x :: u ++ v ~ u ++ x :: v` — the middle-cons perm (when the
    witnessing element sits mid-list). -/
theorem perm_cons_mid {α : Type} (x : α) (u v : List α) :
    (x :: u ++ v).Perm (u ++ x :: v) := by
  induction u with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    show (x :: y :: (ys ++ v)).Perm (y :: (ys ++ x :: v))
    exact (List.Perm.swap y x (ys ++ v)).trans (List.Perm.cons y ih)

/-- the membership split: `x ∈ l → ∃ u v, l = u ++ x :: v`. -/
theorem mem_split {α : Type} {x : α} {l : List α} (h : x ∈ l) :
    ∃ u v, l = u ++ x :: v := by
  induction l with
  | nil => exact absurd h (List.not_mem_nil x)
  | cons y ys ih =>
    cases h with
    | head => exact ⟨[], ys, rfl⟩
    | tail _ hys =>
      rcases ih hys with ⟨u, v, rfl⟩
      exact ⟨y :: u, v, by rw [List.cons_append]⟩

/-- single-member extraction: `x ∈ l → l ~ [x] ++ w`. -/
theorem perm_of_mem_extract {α : Type} {x : α} {l : List α}
    (h : x ∈ l) : ∃ w, l.Perm ([x] ++ w) := by
  rcases mem_split h with ⟨u, v, rfl⟩
  exact ⟨u ++ v, (perm_cons_mid x u v).symm⟩

/-- `MulLT` transports across perms on both sides. -/
theorem MulLT.transPerm {m m' n n' : List Nat}
    (hm : m.Perm m') (h : MulLT m' n') (hn : n.Perm n') : MulLT m n := by
  rcases h with ⟨X, inn, out, hm', hn', hout, hb⟩
  exact ⟨X, inn, out, hm.trans hm', hn.trans hn', hout, hb⟩

theorem MulLTBound.transPerm {L : Nat} {m m' n n' : List Nat}
    (hm : m.Perm m') (h : MulLTBound L m' n') (hn : n.Perm n') :
    MulLTBound L m n := by
  rcases h with ⟨X, inn, out, hm', hn', hout, hb, hl⟩
  exact ⟨X, inn, out, hm.trans hm', hn.trans hn', hout, hb, hl⟩

/-! ## the bundle layer: `FM`, `S`, `muLt`, and E0–E5 -/

/-- a member's foundation rank — the multiset of cited-leaf ranks
    `≺ h₀` it is the join of. -/
def FM (f : α → Nat) (l : List α) : List Nat := l.map f

/-- the secondary measure: total member size. -/
def S (d : α → Nat) (l : List α) : Nat := (l.map d).sum

/-- the lex measure value the recursion cites: `vecSum` of the
    foundation multiset, then total size. -/
def muVal (L : Nat) (f : α → Nat) (d : α → Nat) (l : List α) : Nat × Nat :=
  (vecSum L (FM f l), S d l)

/-- `μ` descent: `FM` strictly decreases (`MulLTBound`), else `FM` is
    unchanged (a perm — `vecSum` equal) and `S` strictly decreases. -/
def muLt (L : Nat) (f d : α → Nat) (m n : List α) : Prop :=
  MulLTBound L (FM f m) (FM f n) ∨ (FM f m).Perm (FM f n) ∧ S d m < S d n

/-- E0/E1/E2 — strict sub-multiset of members descends on `FM`.
    Covers: bundle-of-premises ⊊ top, cited-member-as-bundle ⊊ top,
    children-of-member ⊊ top (all `l ~ l' ++ r`, `r ≠ []`). -/
theorem fm_desc_subMul (L : Nat) (f : α → Nat) {l l' : List α} {r : List α}
    (h : l.Perm (l' ++ r)) (hr : r ≠ []) :
    MulLTBound L (FM f l') (FM f l) := by
  apply mulLTBound_of_subMulStrict L
  refine ⟨r.map f, ?_, ?_⟩
  · intro he
    apply hr
    cases r with
    | nil => rfl
    | cons a as => exact absurd he (List.cons_ne_nil (f a) (as.map f))
  · show (l.map f).Perm (l'.map f ++ r.map f)
    rw [← List.map_append]
    exact List.Perm.map f h

/-- E3 — spawn: every child-rank is below some top-rank; `l` nonempty.
    `|m| ≤ L` is the recursion's fan-out bound. -/
theorem fm_desc_spawn (L : Nat) (f : α → Nat) {m l : List α} (hl : l ≠ [])
    (h : ∀ y ∈ m.map f, ∃ x ∈ l.map f, y < x) (hlen : m.length ≤ L) :
    MulLTBound L (FM f m) (FM f l) := by
  have hl' : FM f l ≠ [] := by
    intro he
    apply hl
    cases l with
    | nil => rfl
    | cons a as => exact absurd he (List.cons_ne_nil (f a) (as.map f))
  have hlen' : (m.map f).length ≤ L := by
    rw [List.length_map]; exact hlen
  exact mulLTBound_of_forall_lt L hl' h hlen'

/-- E3′ — the form the call site supplies: each child member's rank is
    below a specific top member's rank. -/
theorem fm_desc_spawn_mem (L : Nat) (f : α → Nat) {m l : List α} {x : α}
    (hx : x ∈ l) (h : ∀ y ∈ m, f y < f x) (hlen : m.length ≤ L) :
    MulLTBound L (FM f m) (FM f l) := by
  apply fm_desc_spawn L f _ _ hlen
  · intro he
    have hx' : f x ∈ l.map f := List.mem_map.mpr ⟨x, hx, rfl⟩
    rw [he] at hx'
    exact absurd hx' (List.not_mem_nil (f x))
  · intro y hy
    simp only [List.mem_map] at hy
    rcases hy with ⟨m', hm', rfl⟩
    exact ⟨f x, List.mem_map.mpr ⟨x, hx, rfl⟩, h m' hm'⟩

/-- E4 — replace-one: the child FM keeps a sub-part `m'` of the top and
    swaps the max-ranked member for a smaller rank. -/
theorem fm_desc_replace (L : Nat) (f : α → Nat) {m m' l r : List α}
    {a x : α}
    (hm : (FM f m).Perm (FM f ([a] ++ m')))
    (hl : (FM f l).Perm (FM f (m' ++ x :: r)))
    (h : f a < f x) (hL : 0 < L) :
    MulLTBound L (FM f m) (FM f l) := by
  have step : MulLTBound L (FM f ([a] ++ m')) (FM f (m' ++ x :: r)) := by
    rw [show FM f ([a] ++ m') = f a :: FM f m' from rfl,
        show FM f (m' ++ x :: r) = FM f m' ++ (f x :: FM f r) from
          List.map_append f m' (x :: r)]
    exact mulLTBound_of_replace L h hL
  exact MulLTBound.transPerm hm step hl

/-- E5 — same `FM` (up to perm), strictly smaller `S`. -/
theorem muLt_of_fm_eq_s_lt (L : Nat) (f d : α → Nat) {m n : List α}
    (hfm : (FM f m).Perm (FM f n)) (hs : S d m < S d n) :
    muLt L f d m n :=
  Or.inr ⟨hfm, hs⟩

/-- the E0–E4 entry point: a bounded `FM` descent is a `muLt`. -/
theorem muLt_of_mulLTBound (L : Nat) (f d : α → Nat) {m n : List α}
    (h : MulLTBound L (FM f m) (FM f n)) : muLt L f d m n :=
  Or.inl h

/-- any `muLt` descent is a `muVal` descent — the terminating statement
    the mutual's `decreasing_by` cites. -/
theorem muLt_muVal_lt (L : Nat) (f d : α → Nat) {m n : List α}
    (h : muLt L f d m n) :
    (muVal L f d m).1 < (muVal L f d n).1 ∨
    ((muVal L f d m).1 = (muVal L f d n).1 ∧
     (muVal L f d m).2 < (muVal L f d n).2) := by
  cases h with
  | inl hmul =>
    left
    show vecSum L (FM f m) < vecSum L (FM f n)
    exact mulLTBound_desc L hmul
  | inr h2 =>
    right
    rcases h2 with ⟨hperm, hs⟩
    show vecSum L (FM f m) = vecSum L (FM f n) ∧ S d m < S d n
    exact ⟨vecSum_perm L hperm, hs⟩

end Rcic.S3

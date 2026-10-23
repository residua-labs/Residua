import Lean

/-!
Nat Farkas certificate for nonnegative linear inequalities.

A row `(cs, b)` means `dot cs x ≤ b`. A certificate `lam : List Nat` is accepted
when `lamᵀ A ≥ c` columnwise and `lam · b ≤ d`. Search is outside this checker.
`closure_claim = 0`.

Nat coefficients cannot divide. `2x ≤ 10 → x ≤ 5` is outside the fragment:
`nat_no_div` is that refusal.
-/

namespace Rcic.Assay.Farkas

def dot : List Nat → List Nat → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: as, b :: bs => a * b + dot as bs

def scale (k : Nat) : List Nat → List Nat
  | [] => []
  | a :: as => k * a :: scale k as

def addL : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addL xs ys

def lincomb : List Nat → List (List Nat) → List Nat
  | [], _ => []
  | _, [] => []
  | k :: ks, r :: rs => addL (scale k r) (lincomb ks rs)

def col : List (List Nat) → Nat → List Nat
  | [], _ => []
  | r :: rs, j => r.getD j 0 :: col rs j

def lengthsOk (rows : List (List Nat)) (bs cs lam : List Nat) : Bool :=
  decide (rows.length = lam.length) &&
  decide (bs.length = lam.length) &&
  rows.all fun r => decide (r.length = cs.length)

def colsOk (lam : List Nat) (rows : List (List Nat)) (cs : List Nat) : Bool :=
  (List.range cs.length).all fun j => decide (cs.getD j 0 ≤ dot lam (col rows j))

def certOk (rows : List (List Nat)) (bs cs : List Nat) (d : Nat) (lam : List Nat) : Bool :=
  lengthsOk rows bs cs lam && colsOk lam rows cs && decide (dot lam bs ≤ d)

theorem dot_scale (k : Nat) (r x : List Nat) : dot (scale k r) x = k * dot r x := by
  induction r generalizing x with
  | nil => cases x <;> simp [dot, scale]
  | cons a as ih =>
    cases x with
    | nil => simp [dot, scale]
    | cons b bs =>
      simp only [dot, scale, ih, Nat.mul_add, Nat.mul_assoc]

theorem scale_length (k : Nat) (r : List Nat) : (scale k r).length = r.length := by
  induction r with
  | nil => simp [scale]
  | cons _ _ ih => simp [scale, ih]

theorem addL_nil_right (a : List Nat) : addL a [] = a := by
  cases a <;> rfl

private theorem cons_ne_nil_length {α : Type} {a : α} {as : List α} :
    (a :: as).length ≠ 0 := by
  rw [List.length_cons, ← Nat.succ_eq_add_one]
  exact Nat.succ_ne_zero as.length

private theorem zero_lt_cons_length {α : Type} {a : α} {as : List α} :
    0 < (a :: as).length := by
  rw [List.length_cons, ← Nat.succ_eq_add_one]
  exact Nat.succ_pos as.length

private theorem succ_lt_cons_length {α : Type} {a : α} {as : List α} {j : Nat}
    (h : j < as.length) : j + 1 < (a :: as).length := by
  rw [List.length_cons]
  exact Nat.add_lt_add_right h 1

theorem addL_length {a b : List Nat} (h : a.length = b.length) :
    (addL a b).length = a.length := by
  induction a generalizing b with
  | nil => simp at h; simp [h, addL]
  | cons _ as ih =>
    cases b with
    | nil => simp at h
    | cons _ bs =>
      have h' : as.length = bs.length := by simpa [List.length_cons] using h
      simp [addL, ih h']

theorem addL_getD (a b : List Nat) (j : Nat) (ha : j < a.length) (hb : j < b.length) :
    (addL a b).getD j 0 = a.getD j 0 + b.getD j 0 := by
  induction a generalizing b j with
  | nil => simp at ha
  | cons p ps ih =>
    cases b with
    | nil => simp at hb
    | cons q qs =>
      cases j with
      | zero => simp [addL, List.getD_cons_zero]
      | succ j =>
        simp only [addL, List.getD_cons_succ]
        apply ih
        · simp [List.length_cons] at ha; omega
        · simp [List.length_cons] at hb; omega

theorem scale_getD (k : Nat) (r : List Nat) (j : Nat) (hj : j < r.length) :
    (scale k r).getD j 0 = k * r.getD j 0 := by
  induction r generalizing j with
  | nil => simp at hj
  | cons a as ih =>
    cases j with
    | zero => simp [scale]
    | succ j =>
      simp only [scale, List.getD_cons_succ]
      apply ih
      simp [List.length_cons] at hj
      omega

theorem dot_add {a b x : List Nat} (ha : a.length = x.length) (hb : b.length = x.length) :
    dot (addL a b) x = dot a x + dot b x := by
  induction x generalizing a b with
  | nil =>
    cases a with
    | nil =>
      cases b with
      | nil => simp only [dot, addL]
      | cons => exact absurd hb cons_ne_nil_length
    | cons => exact absurd ha cons_ne_nil_length
  | cons v vs ih =>
    cases a with
    | nil => exact absurd ha.symm cons_ne_nil_length
    | cons p ps =>
      cases b with
      | nil => exact absurd hb.symm cons_ne_nil_length
      | cons q qs =>
        have ha' : ps.length = vs.length := by
          rw [List.length_cons, List.length_cons] at ha
          exact Nat.add_right_cancel ha
        have hb' : qs.length = vs.length := by
          rw [List.length_cons, List.length_cons] at hb
          exact Nat.add_right_cancel hb
        simp only [addL, dot]
        rw [ih ha' hb', Nat.add_mul]
        ac_rfl

theorem lincomb_length_pos (lam : List Nat) (r : List Nat) (rs : List (List Nat)) (n : Nat)
    (hlen : lam.length = (r :: rs).length)
    (hrows : ∀ s, s ∈ r :: rs → s.length = n) :
    (lincomb lam (r :: rs)).length = n := by
  cases lam with
  | nil => exact absurd hlen.symm cons_ne_nil_length
  | cons k ks =>
    have hr : r.length = n := hrows r (List.mem_cons_self _ _)
    have hrest : ∀ s, s ∈ rs → s.length = n := fun s hs => hrows s (List.mem_cons_of_mem _ hs)
    have hk : ks.length = rs.length := by
      rw [List.length_cons, List.length_cons] at hlen
      exact Nat.add_right_cancel hlen
    cases rs with
    | nil =>
      cases ks with
      | nil => simp only [lincomb, addL_nil_right, scale_length, hr]
      | cons => exact absurd hk cons_ne_nil_length
    | cons s ss =>
      have ihlen : (lincomb ks (s :: ss)).length = n :=
        lincomb_length_pos ks s ss n hk hrest
      have hs : (scale k r).length = (lincomb ks (s :: ss)).length := by
        rw [scale_length, hr, ihlen]
      simp only [lincomb]
      rw [addL_length hs, scale_length, hr]
termination_by rs

theorem lincomb_getD (lam : List Nat) (rows : List (List Nat)) (n j : Nat)
    (hlen : lam.length = rows.length)
    (hrows : ∀ r, r ∈ rows → r.length = n)
    (hj : j < n) :
    (lincomb lam rows).getD j 0 = dot lam (col rows j) := by
  induction lam generalizing rows with
  | nil =>
    cases rows with
    | nil => simp only [lincomb, col, dot, List.getD_nil]
    | cons => exact absurd hlen.symm cons_ne_nil_length
  | cons k ks ih =>
    cases rows with
    | nil => exact absurd hlen cons_ne_nil_length
    | cons r rs =>
      have hr : r.length = n := hrows r (List.mem_cons_self _ _)
      have hrest : ∀ s, s ∈ rs → s.length = n := fun s hs => hrows s (List.mem_cons_of_mem _ hs)
      have hk : ks.length = rs.length := by
        rw [List.length_cons, List.length_cons] at hlen
        exact Nat.add_right_cancel hlen
      have ih' := ih rs hk hrest
      have hscale : j < (scale k r).length := by
        rw [scale_length, hr]
        exact hj
      cases rs with
      | nil =>
        cases ks with
        | nil =>
          simp only [lincomb, addL_nil_right]
          rw [scale_getD k r j (hr.symm ▸ hj)]
          simp only [col, dot, Nat.add_zero]
        | cons => exact absurd hk cons_ne_nil_length
      | cons s ss =>
        have hrestLen : (lincomb ks (s :: ss)).length = n :=
          lincomb_length_pos ks s ss n hk hrest
        have hadd := addL_getD (scale k r) (lincomb ks (s :: ss)) j hscale (hrestLen.symm ▸ hj)
        simp only [lincomb]
        rw [hadd, scale_getD k r j (hr.symm ▸ hj), ih']
        simp only [col, dot]

theorem dot_lincomb {lam : List Nat} {rows : List (List Nat)} {x : List Nat}
    (hlen : lam.length = rows.length)
    (hrows : ∀ r, r ∈ rows → r.length = x.length) :
    dot (lincomb lam rows) x = dot lam (rows.map fun r => dot r x) := by
  induction lam generalizing rows with
  | nil =>
    cases rows with
    | nil => simp only [lincomb, dot, List.map]
    | cons => exact absurd hlen.symm cons_ne_nil_length
  | cons k ks ih =>
    cases rows with
    | nil => exact absurd hlen cons_ne_nil_length
    | cons r rs =>
      have hr : r.length = x.length := hrows r (List.mem_cons_self _ _)
      have hrest : ∀ s, s ∈ rs → s.length = x.length := fun s hs => hrows s (List.mem_cons_of_mem _ hs)
      have hk : ks.length = rs.length := by
        rw [List.length_cons, List.length_cons] at hlen
        exact Nat.add_right_cancel hlen
      cases rs with
      | nil =>
        cases ks with
        | nil => simp only [lincomb, addL_nil_right, dot, List.map, dot_scale, Nat.add_zero]
        | cons => exact absurd hk cons_ne_nil_length
      | cons s ss =>
        have hlenS : (scale k r).length = x.length := by rw [scale_length, hr]
        have hlenR : (lincomb ks (s :: ss)).length = x.length :=
          lincomb_length_pos ks s ss x.length hk hrest
        simp only [lincomb, dot]
        rw [dot_add hlenS hlenR, dot_scale, ih hk hrest]

theorem dot_le_of_getD {cs v x : List Nat}
    (hx : x.length = cs.length)
    (h : ∀ j, j < cs.length → cs.getD j 0 ≤ v.getD j 0) :
    dot cs x ≤ dot v x := by
  induction x generalizing cs v with
  | nil =>
    cases cs with
    | nil => cases v <;> exact Nat.le_refl 0
    | cons => exact absurd hx.symm cons_ne_nil_length
  | cons y ys ih =>
    cases cs with
    | nil => exact absurd hx cons_ne_nil_length
    | cons c ct =>
      have hx' : ys.length = ct.length := by
        rw [List.length_cons, List.length_cons] at hx
        exact Nat.add_right_cancel hx
      cases v with
      | nil =>
        have hc0 : c ≤ 0 := by
          simpa only [List.getD_cons_zero, List.getD_nil] using h 0 zero_lt_cons_length
        have hc : c = 0 := Nat.eq_zero_of_le_zero hc0
        have hrest : ∀ j, j < ct.length → ct.getD j 0 ≤ ([] : List Nat).getD j 0 := by
          intro j hj
          simpa only [List.getD_cons_succ, List.getD_nil] using h (j + 1) (succ_lt_cons_length hj)
        have ih' := ih hx' hrest
        simp only [dot, hc, Nat.zero_mul, Nat.zero_add] at ih' ⊢
        exact ih'
      | cons w ws =>
        have hc : c ≤ w := by
          simpa only [List.getD_cons_zero] using h 0 zero_lt_cons_length
        have hrest : ∀ j, j < ct.length → ct.getD j 0 ≤ ws.getD j 0 := by
          intro j hj
          simpa only [List.getD_cons_succ] using h (j + 1) (succ_lt_cons_length hj)
        have ih' := ih hx' hrest
        simp only [dot]
        exact Nat.add_le_add (Nat.mul_le_mul_right y hc) ih'

theorem dot_le_bounds {lam : List Nat} {rows : List (List Nat)} {bs x : List Nat}
    (hlen : lam.length = rows.length)
    (hbs : bs.length = rows.length)
    (hhyp : ∀ i, i < rows.length → dot (rows.getD i []) x ≤ bs.getD i 0) :
    dot lam (rows.map fun r => dot r x) ≤ dot lam bs := by
  induction lam generalizing rows bs with
  | nil => exact Nat.le_refl 0
  | cons k ks ih =>
    cases rows with
    | nil => exact absurd hlen cons_ne_nil_length
    | cons r rs =>
      cases bs with
      | nil => exact absurd hbs.symm cons_ne_nil_length
      | cons b bt =>
        have hk : ks.length = rs.length := by
          rw [List.length_cons, List.length_cons] at hlen
          exact Nat.add_right_cancel hlen
        have hb : bt.length = rs.length := by
          rw [List.length_cons, List.length_cons] at hbs
          exact Nat.add_right_cancel hbs
        have h0 : dot r x ≤ b := by
          simpa only [List.getD_cons_zero] using hhyp 0 zero_lt_cons_length
        have hrest : ∀ i, i < rs.length → dot (rs.getD i []) x ≤ bt.getD i 0 := by
          intro i hi
          simpa only [List.getD_cons_succ] using hhyp (i + 1) (succ_lt_cons_length hi)
        have ih' := ih hk hb hrest
        simp only [List.map_cons, dot]
        exact Nat.add_le_add (Nat.mul_le_mul_left k h0) ih'

theorem cols_le {lam : List Nat} {rows : List (List Nat)} {cs : List Nat}
    (h : colsOk lam rows cs = true) {j : Nat} (hj : j < cs.length) :
    cs.getD j 0 ≤ dot lam (col rows j) := by
  have hall := List.all_eq_true.mp h
  have hdecide := hall j (List.mem_range.mpr hj)
  simpa [decide_eq_true_iff] using hdecide

theorem lengths_of_cert {rows : List (List Nat)} {bs cs lam : List Nat} {d : Nat}
    (h : certOk rows bs cs d lam = true) :
    rows.length = lam.length ∧ bs.length = lam.length ∧
      (∀ r, r ∈ rows → r.length = cs.length) ∧ colsOk lam rows cs = true ∧
      dot lam bs ≤ d := by
  have h1 : (lengthsOk rows bs cs lam = true ∧ colsOk lam rows cs = true) ∧ dot lam bs ≤ d := by
    simpa [certOk, Bool.and_eq_true, decide_eq_true_iff] using h
  rcases h1 with ⟨⟨hlen, hcols⟩, hbound⟩
  have h2 :
      (rows.length = lam.length ∧ bs.length = lam.length) ∧
        (∀ r, r ∈ rows → r.length = cs.length) := by
    simpa [lengthsOk, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true] using hlen
  rcases h2 with ⟨⟨hlenR, hlenB⟩, hrows⟩
  exact ⟨hlenR, hlenB, hrows, hcols, hbound⟩

theorem farkas_sound {rows : List (List Nat)} {bs cs : List Nat} {d : Nat} {lam : List Nat}
    (hok : certOk rows bs cs d lam = true)
    (x : List Nat)
    (hx : x.length = cs.length)
    (hhyp : ∀ i, i < rows.length → dot (rows.getD i []) x ≤ bs.getD i 0) :
    dot cs x ≤ d := by
  rcases lengths_of_cert hok with ⟨hlenR, hlenB, hrows, hcols, hbound⟩
  have hget : ∀ j, j < cs.length → cs.getD j 0 ≤ (lincomb lam rows).getD j 0 := by
    intro j hj
    have hcol := cols_le hcols hj
    have heq := lincomb_getD lam rows cs.length j hlenR.symm hrows hj
    rw [← heq] at hcol
    exact hcol
  have hle : dot cs x ≤ dot (lincomb lam rows) x := dot_le_of_getD hx hget
  have hrowsx : ∀ r, r ∈ rows → r.length = x.length := by
    intro r hr
    exact (hrows r hr).trans hx.symm
  have heq : dot (lincomb lam rows) x = dot lam (rows.map fun r => dot r x) :=
    dot_lincomb hlenR.symm hrowsx
  have hmap : dot lam (rows.map fun r => dot r x) ≤ dot lam bs :=
    dot_le_bounds hlenR.symm (hlenB.trans hlenR.symm) hhyp
  exact Nat.le_trans hle (Nat.le_trans (Nat.le_of_eq heq) (Nat.le_trans hmap hbound))

/-- `2 * x ≤ 10` does not yield `x ≤ 5` from a Nat multiplier. `λ = [1]` fails the bound. -/
theorem nat_no_div : certOk [[2]] [10] [1] 5 [1] = false := by
  decide

-- Concrete dots used by the 20 fresh goals. Right-associated, so three-variable
-- sums are stated with `Nat.add_assoc` at the use site.
private theorem dot_10 (x y : Nat) : dot [1, 0] [x, y] = x := by
  simp [dot, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add]

private theorem dot_01 (x y : Nat) : dot [0, 1] [x, y] = y := by
  simp [dot, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add]

private theorem dot_1 (x : Nat) : dot [1] [x] = x := by
  simp [dot, Nat.one_mul, Nat.add_zero]

private theorem dot_11 (x y : Nat) : dot [1, 1] [x, y] = x + y := by
  simp [dot, Nat.one_mul, Nat.add_zero]

private theorem dot_100 (x y z : Nat) : dot [1, 0, 0] [x, y, z] = x := by
  simp [dot, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add]

private theorem dot_010 (x y z : Nat) : dot [0, 1, 0] [x, y, z] = y := by
  simp [dot, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add]

private theorem dot_001 (x y z : Nat) : dot [0, 0, 1] [x, y, z] = z := by
  simp [dot, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add]

private theorem dot_111 (x y z : Nat) : dot [1, 1, 1] [x, y, z] = x + (y + z) := by
  simp [dot, Nat.one_mul, Nat.add_zero]

private theorem dot_0 (x : Nat) : dot [0] [x] = 0 := by
  simp [dot, Nat.zero_mul, Nat.add_zero]

private theorem dot_101 (x y z : Nat) : dot [1, 0, 1] [x, y, z] = x + z := by
  simp [dot, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add]

private theorem dot_110 (x y z : Nat) : dot [1, 1, 0] [x, y, z] = x + y := by
  simp [dot, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add]

/-!
Twenty fresh goals. None of these replaces a landed R-CIC lemma.
Each `gNN` is the certificate proof. Each `gNN_omega` is the same statement
closed by `omega`, for the kernel-cost comparison below.
-/

theorem g01 (x y : Nat) (h : x + y ≤ 3) : x ≤ 3 := by
  have hc : certOk [[1, 1]] [3] [1, 0] 3 [1] = true := by decide
  have hdot : dot [1, 0] [x, y] ≤ 3 :=
    farkas_sound hc [x, y] rfl (by
      intro i hi
      have : i = 0 := by
        simp [List.length_cons, List.length_nil] at hi
        omega
      subst this
      simpa [List.getD_cons_zero, dot_11] using h)
  simpa [dot_10] using hdot

theorem g01_omega (x y : Nat) (h : x + y ≤ 3) : x ≤ 3 := by omega

theorem g02 (x y : Nat) (h : x + y ≤ 3) : y ≤ 3 := by
  have hc : certOk [[1, 1]] [3] [0, 1] 3 [1] = true := by decide
  have hdot : dot [0, 1] [x, y] ≤ 3 :=
    farkas_sound hc [x, y] rfl (by
      intro i hi
      have : i = 0 := by
        simp [List.length_cons, List.length_nil] at hi
        omega
      subst this
      simpa [List.getD_cons_zero, dot_11] using h)
  simpa [dot_01] using hdot

theorem g02_omega (x y : Nat) (h : x + y ≤ 3) : y ≤ 3 := by omega

theorem g03 (x : Nat) (h : x ≤ 1) : x ≤ 1 := by
  have hc : certOk [[1]] [1] [1] 1 [1] = true := by decide
  have hdot : dot [1] [x] ≤ 1 :=
    farkas_sound hc [x] rfl (by
      intro i hi
      have : i = 0 := by
        simp [List.length_cons, List.length_nil] at hi
        omega
      subst this
      simpa [List.getD_cons_zero, dot_1] using h)
  simpa [dot_1] using hdot

theorem g03_omega (x : Nat) (h : x ≤ 1) : x ≤ 1 := by omega

theorem g04 (x : Nat) (h : x ≤ 1) : x ≤ 2 := by
  have hc : certOk [[1]] [1] [1] 2 [1] = true := by decide
  have hdot : dot [1] [x] ≤ 2 :=
    farkas_sound hc [x] rfl (by
      intro i hi
      have : i = 0 := by
        simp [List.length_cons, List.length_nil] at hi
        omega
      subst this
      simpa [List.getD_cons_zero, dot_1] using h)
  simpa [dot_1] using hdot

theorem g04_omega (x : Nat) (h : x ≤ 1) : x ≤ 2 := by omega

theorem g05 (x y z : Nat) (h : x + y + z ≤ 9) : x ≤ 9 := by
  have hc : certOk [[1, 1, 1]] [9] [1, 0, 0] 9 [1] = true := by decide
  have hdot : dot [1, 0, 0] [x, y, z] ≤ 9 :=
    farkas_sound hc [x, y, z] rfl (by
      intro i hi
      have : i = 0 := by
        simp [List.length_cons, List.length_nil] at hi
        omega
      subst this
      simpa [List.getD_cons_zero, dot_111, Nat.add_assoc] using h)
  simpa [dot_100] using hdot

theorem g05_omega (x y z : Nat) (h : x + y + z ≤ 9) : x ≤ 9 := by omega

theorem g06 (x y z : Nat) (h : x + y + z ≤ 9) : y ≤ 9 := by
  have hc : certOk [[1, 1, 1]] [9] [0, 1, 0] 9 [1] = true := by decide
  have hdot : dot [0, 1, 0] [x, y, z] ≤ 9 :=
    farkas_sound hc [x, y, z] rfl (by
      intro i hi
      have : i = 0 := by
        simp [List.length_cons, List.length_nil] at hi
        omega
      subst this
      simpa [List.getD_cons_zero, dot_111, Nat.add_assoc] using h)
  simpa [dot_010] using hdot

theorem g06_omega (x y z : Nat) (h : x + y + z ≤ 9) : y ≤ 9 := by omega

theorem g07 (x y z : Nat) (h : x + y + z ≤ 9) : z ≤ 9 := by
  have hc : certOk [[1, 1, 1]] [9] [0, 0, 1] 9 [1] = true := by decide
  have hdot : dot [0, 0, 1] [x, y, z] ≤ 9 :=
    farkas_sound hc [x, y, z] rfl (by
      intro i hi
      have : i = 0 := by
        simp [List.length_cons, List.length_nil] at hi
        omega
      subst this
      simpa [List.getD_cons_zero, dot_111, Nat.add_assoc] using h)
  simpa [dot_001] using hdot

theorem g07_omega (x y z : Nat) (h : x + y + z ≤ 9) : z ≤ 9 := by omega

theorem g08 (x y : Nat) (hx : x ≤ 2) (hy : y ≤ 3) : x + y ≤ 5 := by
  have hc : certOk [[1, 0], [0, 1]] [2, 3] [1, 1] 5 [1, 1] = true := by decide
  have hdot : dot [1, 1] [x, y] ≤ 5 :=
    farkas_sound hc [x, y] rfl (by
      intro i hi
      cases i with
      | zero => simpa [List.getD_cons_zero, dot_10] using hx
      | succ i =>
        have : i = 0 := by
          simp [List.length_cons, List.length_nil] at hi
          omega
        subst this
        simpa [List.getD_cons_succ, List.getD_cons_zero, dot_01] using hy)
  simpa [dot_11] using hdot

theorem g08_omega (x y : Nat) (hx : x ≤ 2) (hy : y ≤ 3) : x + y ≤ 5 := by omega

theorem g09 (x : Nat) (h : x ≤ 5) : x ≤ 5 := by
  have hc : certOk [[1]] [5] [1] 5 [1] = true := by decide
  have hdot : dot [1] [x] ≤ 5 :=
    farkas_sound hc [x] rfl (by
      intro i hi
      have : i = 0 := by
        simp [List.length_cons, List.length_nil] at hi
        omega
      subst this
      simpa [List.getD_cons_zero, dot_1] using h)
  simpa [dot_1] using hdot

theorem g09_omega (x : Nat) (h : x ≤ 5) : x ≤ 5 := by omega

theorem g10 (y : Nat) (h : y ≤ 5) : y ≤ 5 := by
  have hc : certOk [[1]] [5] [1] 5 [1] = true := by decide
  have hdot : dot [1] [y] ≤ 5 :=
    farkas_sound hc [y] rfl (by
      intro i hi
      have : i = 0 := by
        simp [List.length_cons, List.length_nil] at hi
        omega
      subst this
      simpa [List.getD_cons_zero, dot_1] using h)
  simpa [dot_1] using hdot

theorem g10_omega (y : Nat) (h : y ≤ 5) : y ≤ 5 := by omega

theorem g11 (x y : Nat) (hxy : x + y ≤ 4) (hy : y ≤ 1) : x ≤ 4 := by
  have hc : certOk [[1, 1], [0, 1]] [4, 1] [1, 0] 4 [1, 0] = true := by decide
  have hdot : dot [1, 0] [x, y] ≤ 4 :=
    farkas_sound hc [x, y] rfl (by
      intro i hi
      cases i with
      | zero => simpa [List.getD_cons_zero, dot_11] using hxy
      | succ i =>
        have : i = 0 := by
          simp [List.length_cons, List.length_nil] at hi
          omega
        subst this
        simpa [List.getD_cons_succ, List.getD_cons_zero, dot_01] using hy)
  simpa [dot_10] using hdot

theorem g11_omega (x y : Nat) (hxy : x + y ≤ 4) (hy : y ≤ 1) : x ≤ 4 := by omega

theorem g12 (x : Nat) (h : x ≤ 0) : x ≤ 0 := by
  have hc : certOk [[1]] [0] [1] 0 [1] = true := by decide
  have hdot : dot [1] [x] ≤ 0 :=
    farkas_sound hc [x] rfl (by
      intro i hi
      have : i = 0 := by
        simp [List.length_cons, List.length_nil] at hi
        omega
      subst this
      simpa [List.getD_cons_zero, dot_1] using h)
  simpa [dot_1] using hdot

theorem g12_omega (x : Nat) (h : x ≤ 0) : x ≤ 0 := by omega

theorem g13 (x y : Nat) (h : x ≤ 7) : x ≤ 7 := by
  have hc : certOk [[1, 0]] [7] [1, 0] 7 [1] = true := by decide
  have hdot : dot [1, 0] [x, y] ≤ 7 :=
    farkas_sound hc [x, y] rfl (by
      intro i hi
      have : i = 0 := by
        simp [List.length_cons, List.length_nil] at hi
        omega
      subst this
      simpa [List.getD_cons_zero, dot_10] using h)
  simpa [dot_10] using hdot

theorem g13_omega (x _y : Nat) (h : x ≤ 7) : x ≤ 7 := by omega

theorem g14 (a b c : Nat) (ha : a ≤ 3) (hb : b ≤ 3) (hc : c ≤ 3) : a + b + c ≤ 9 := by
  have hcert : certOk [[1, 0, 0], [0, 1, 0], [0, 0, 1]] [3, 3, 3] [1, 1, 1] 9 [1, 1, 1] = true := by decide
  have hdot : dot [1, 1, 1] [a, b, c] ≤ 9 :=
    farkas_sound hcert [a, b, c] rfl (by
      intro i hi
      cases i with
      | zero => simpa [List.getD_cons_zero, dot_100] using ha
      | succ i =>
        cases i with
        | zero => simpa [List.getD_cons_succ, List.getD_cons_zero, dot_010] using hb
        | succ i =>
          have : i = 0 := by
            simp [List.length_cons, List.length_nil] at hi
            omega
          subst this
          simpa [List.getD_cons_succ, List.getD_cons_zero, dot_001] using hc)
  simpa [dot_111, Nat.add_assoc] using hdot

theorem g14_omega (a b c : Nat) (ha : a ≤ 3) (hb : b ≤ 3) (hc : c ≤ 3) : a + b + c ≤ 9 := by omega

theorem g15 (a b : Nat) (ha : a ≤ 3) (hb : b ≤ 3) : a + b ≤ 9 := by
  have hc : certOk [[1, 0], [0, 1]] [3, 3] [1, 1] 9 [1, 1] = true := by decide
  have hdot : dot [1, 1] [a, b] ≤ 9 :=
    farkas_sound hc [a, b] rfl (by
      intro i hi
      cases i with
      | zero => simpa [List.getD_cons_zero, dot_10] using ha
      | succ i =>
        have : i = 0 := by
          simp [List.length_cons, List.length_nil] at hi
          omega
        subst this
        simpa [List.getD_cons_succ, List.getD_cons_zero, dot_01] using hb)
  simpa [dot_11] using hdot

theorem g15_omega (a b : Nat) (ha : a ≤ 3) (hb : b ≤ 3) : a + b ≤ 9 := by omega

theorem g16 (x y : Nat) (hxy : x + y ≤ 5) (hx : x ≤ 2) : x ≤ 5 := by
  have hc : certOk [[1, 1], [1, 0]] [5, 2] [1, 0] 5 [0, 1] = true := by decide
  have hdot : dot [1, 0] [x, y] ≤ 5 :=
    farkas_sound hc [x, y] rfl (by
      intro i hi
      cases i with
      | zero => simpa [List.getD_cons_zero, dot_11] using hxy
      | succ i =>
        have : i = 0 := by
          simp [List.length_cons, List.length_nil] at hi
          omega
        subst this
        simpa [List.getD_cons_succ, List.getD_cons_zero, dot_10] using hx)
  simpa [dot_10] using hdot

theorem g16_omega (x y : Nat) (_hxy : x + y ≤ 5) (hx : x ≤ 2) : x ≤ 5 := by omega

theorem g17 (x y : Nat) (hxy : x + y ≤ 5) (hx : x ≤ 2) : x + y ≤ 7 := by
  have hc : certOk [[1, 1], [1, 0]] [5, 2] [1, 1] 7 [1, 0] = true := by decide
  have hdot : dot [1, 1] [x, y] ≤ 7 :=
    farkas_sound hc [x, y] rfl (by
      intro i hi
      cases i with
      | zero => simpa [List.getD_cons_zero, dot_11] using hxy
      | succ i =>
        have : i = 0 := by
          simp [List.length_cons, List.length_nil] at hi
          omega
        subst this
        simpa [List.getD_cons_succ, List.getD_cons_zero, dot_10] using hx)
  simpa [dot_11] using hdot

theorem g17_omega (x y : Nat) (hxy : x + y ≤ 5) (_hx : x ≤ 2) : x + y ≤ 7 := by omega

theorem g18 (p q r : Nat) (hp : p ≤ 4) (hq : q ≤ 1) (hr : r ≤ 1) : p + q + r ≤ 6 := by
  have hcert : certOk [[1, 0, 0], [0, 1, 0], [0, 0, 1]] [4, 1, 1] [1, 1, 1] 6 [1, 1, 1] = true := by decide
  have hdot : dot [1, 1, 1] [p, q, r] ≤ 6 :=
    farkas_sound hcert [p, q, r] rfl (by
      intro i hi
      cases i with
      | zero => simpa [List.getD_cons_zero, dot_100] using hp
      | succ i =>
        cases i with
        | zero => simpa [List.getD_cons_succ, List.getD_cons_zero, dot_010] using hq
        | succ i =>
          have : i = 0 := by
            simp [List.length_cons, List.length_nil] at hi
            omega
          subst this
          simpa [List.getD_cons_succ, List.getD_cons_zero, dot_001] using hr)
  simpa [dot_111, Nat.add_assoc] using hdot

theorem g18_omega (p q r : Nat) (hp : p ≤ 4) (hq : q ≤ 1) (hr : r ≤ 1) : p + q + r ≤ 6 := by omega

theorem g19 (x : Nat) (h : x ≤ 8) : 0 ≤ 0 := by
  have hc : certOk [[1]] [8] [0] 0 [0] = true := by decide
  have hdot : dot [0] [x] ≤ 0 :=
    farkas_sound hc [x] rfl (by
      intro i hi
      have : i = 0 := by
        simp [List.length_cons, List.length_nil] at hi
        omega
      subst this
      simpa [List.getD_cons_zero, dot_1] using h)
  simpa only [dot_0] using hdot

theorem g19_omega (x : Nat) (_h : x ≤ 8) : 0 ≤ 0 := by omega

theorem g20 (x y z : Nat) (hxy : x + y ≤ 2) (hz : z ≤ 2) : x + z ≤ 4 := by
  have hc : certOk [[1, 1, 0], [0, 0, 1]] [2, 2] [1, 0, 1] 4 [1, 1] = true := by decide
  have hdot : dot [1, 0, 1] [x, y, z] ≤ 4 :=
    farkas_sound hc [x, y, z] rfl (by
      intro i hi
      cases i with
      | zero => simpa [List.getD_cons_zero, dot_110] using hxy
      | succ i =>
        have : i = 0 := by
          simp [List.length_cons, List.length_nil] at hi
          omega
        subst this
        simpa [List.getD_cons_succ, List.getD_cons_zero, dot_001] using hz)
  simpa [dot_101] using hdot

theorem g20_omega (x y z : Nat) (hxy : x + y ≤ 2) (hz : z ≤ 2) : x + z ≤ 4 := by omega

/-!
Kernel cost of the 20 certificate proofs against the 20 `omega` proofs.
Node count is the structural size of the stored proof term. Time is one
`Kernel.check` per term. The median of an even sample is the pair of middle
values after sorting (indexes 9 and 10). `nodes_drop` / `time_drop` are true
only when both ends of that pair are strictly smaller for the certificate.
In-tree replacement of landed lemmas is not this measurement.
-/

open Lean

private def exprSize : Expr → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .mvar _ => 1
  | .sort _ => 1
  | .const _ _ => 1
  | .app f a => 1 + exprSize f + exprSize a
  | .lam _ d b _ => 1 + exprSize d + exprSize b
  | .forallE _ d b _ => 1 + exprSize d + exprSize b
  | .letE _ t v b _ => 1 + exprSize t + exprSize v + exprSize b
  | .lit _ => 1
  | .mdata _ e => 1 + exprSize e
  | .proj _ _ e => 1 + exprSize e

private def midPair (xs : Array Nat) : Nat × Nat :=
  let ys := xs.qsort (· < ·)
  (ys.getD (ys.size / 2 - 1) 0, ys.getD (ys.size / 2) 0)

private def kex : KernelException → String
  | .unknownConstant _ n => s!"unknownConstant {n}"
  | .alreadyDeclared _ n => s!"alreadyDeclared {n}"
  | .declTypeMismatch _ _ _ => "declTypeMismatch"
  | .declHasMVars _ n _ => s!"declHasMVars {n}"
  | .declHasFVars _ n _ => s!"declHasFVars {n}"
  | .funExpected _ _ _ => "funExpected"
  | .typeExpected _ _ _ => "typeExpected"
  | .letTypeMismatch _ _ _ _ _ => "letTypeMismatch"
  | .exprTypeMismatch _ _ _ _ => "exprTypeMismatch"
  | .appTypeMismatch _ _ _ _ _ => "appTypeMismatch"
  | .invalidProj _ _ _ => "invalidProj"
  | .thmTypeIsNotProp _ n _ => s!"thmTypeIsNotProp {n}"
  | .other msg => msg
  | .deterministicTimeout => "deterministicTimeout"
  | .excessiveMemory => "excessiveMemory"
  | .deepRecursion => "deepRecursion"
  | .interrupted => "interrupted"

private def farkasGoals : List Name := [
  ``g01, ``g02, ``g03, ``g04, ``g05, ``g06, ``g07, ``g08, ``g09, ``g10,
  ``g11, ``g12, ``g13, ``g14, ``g15, ``g16, ``g17, ``g18, ``g19, ``g20
]

private def omegaGoals : List Name := [
  ``g01_omega, ``g02_omega, ``g03_omega, ``g04_omega, ``g05_omega,
  ``g06_omega, ``g07_omega, ``g08_omega, ``g09_omega, ``g10_omega,
  ``g11_omega, ``g12_omega, ``g13_omega, ``g14_omega, ``g15_omega,
  ``g16_omega, ``g17_omega, ``g18_omega, ``g19_omega, ``g20_omega
]

open Elab.Command in
run_cmd do
  let env ← getEnv
  let measure (n : Name) : CommandElabM (Nat × Nat) := do
    let some ci := env.find? n | throwError "[assay_farkas_cost] missing {n}"
    let some e := ci.value? | throwError "[assay_farkas_cost] no value {n}"
    let sz := exprSize e
    let t0 ← IO.monoNanosNow
    match Kernel.check env {} e with
    | .ok _ =>
      let t1 ← IO.monoNanosNow
      pure (sz, t1 - t0)
    | .error ex =>
      throwError "[assay_farkas_cost] kernel check failed {n}: {kex ex}"
  let mut fnodes : Array Nat := #[]
  let mut ftime : Array Nat := #[]
  let mut onodes : Array Nat := #[]
  let mut otime : Array Nat := #[]
  for n in farkasGoals do
    let (sz, dt) ← measure n
    fnodes := fnodes.push sz
    ftime := ftime.push dt
  for n in omegaGoals do
    let (sz, dt) ← measure n
    onodes := onodes.push sz
    otime := otime.push dt
  let (fnLo, fnHi) := midPair fnodes
  let (onLo, onHi) := midPair onodes
  let (ftLo, ftHi) := midPair ftime
  let (otLo, otHi) := midPair otime
  let nodesDrop := fnLo < onLo && fnHi < onHi
  let timeDrop := ftLo < otLo && ftHi < otHi
  let line :=
    s!"[assay_farkas_cost] n=20 in_tree_replacement=false " ++
    s!"farkas_nodes={fnodes} omega_nodes={onodes} " ++
    s!"farkas_ns={ftime} omega_ns={otime} " ++
    s!"med_nodes_farkas={fnLo},{fnHi} med_nodes_omega={onLo},{onHi} " ++
    s!"med_ns_farkas={ftLo},{ftHi} med_ns_omega={otLo},{otHi} " ++
    s!"nodes_drop={nodesDrop} time_drop={timeDrop}"
  logInfo line
  IO.println line

end Rcic.Assay.Farkas

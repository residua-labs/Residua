import rcic.RcicSynBvarWk
import rcic.RcicSynSubst

/-!
# Syntactic sortRow, build step 3ah — `esub` moves a resolved index

`research/rcic/semantic/S3_ES_ARMS.md` §33. `instantiate_eq_bvar` already
splits the index. What was missing is how `resolve` sees the inserted
disposition. `insertDisp d j ρ` is the disposition list of the inner
typing. `esub` inserts `drop` or `keep`. `lsub` inserts `drop` or
`inline`.

Below the hole (`i < j`), and with the hole in range (`j ≤ ρ.length`),
insertion does not change `resolve`. At or above it, a `drop` or an
`inline` leaves the erased index, and a `keep` is one `ETm.lift` at
`countKeep (ρ.take j)`. The hole itself is the existing `resolve_insertDisp_drop` / `_keep`.
An `inline` at the hole returns the value lifted at cutoff 0 by
`countKeep` of the prefix: each newer `keep` is one `ETm.lift 0 1`.

A short list is not one of these. `j > ρ.length` puts the disposition
at the end, and an index that lands on it is not the in-range equation.

Not proved. The `esub` and `lsub` arms of `bvarEps`. On `keep`, `esub`
is `ETm.inst` of the value into the body (`ETm.inst_lift_id` cancels
the `hi_keep` lift). `lsub` inlines `hv.eps`, and the hole's image is
that value lifted by the newer `keep`s. `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- Inserting a disposition strictly above `i` does not change
    `resolve ρ i`, when the hole is in range. -/
theorem resolve_insertDisp_lo (d : Disp) (ρ : List Disp) (j i : Nat)
    (hij : i < j) (hlen : j ≤ ρ.length) :
    resolve (insertDisp d j ρ) i = resolve ρ i := by
  induction i generalizing ρ j with
  | zero =>
    cases j with
    | zero => exact absurd hij (Nat.not_lt_zero _)
    | succ j =>
      cases ρ with
      | nil =>
        simp only [List.length_nil] at hlen
        exact absurd hlen (Nat.not_succ_le_zero j)
      | cons hd _ =>
        cases hd <;> rfl
  | succ i ih =>
    cases j with
    | zero => exact absurd hij (Nat.not_lt_zero _)
    | succ j =>
      have hij' : i < j := Nat.lt_of_succ_lt_succ hij
      cases ρ with
      | nil =>
        simp only [List.length_nil] at hlen
        exact absurd hlen (Nat.not_succ_le_zero j)
      | cons hd ρ =>
        have hlen' : j ≤ ρ.length := by
          simp only [List.length_cons] at hlen
          exact Nat.le_of_succ_le_succ hlen
        cases hd with
        | keep =>
          simp only [insertDisp, resolve]
          exact congrArg (·.lift 0 1) (ih ρ j hij' hlen')
        | drop =>
          simp only [insertDisp, resolve, ih ρ j hij' hlen']
        | inline _ =>
          simp only [insertDisp, resolve, ih ρ j hij' hlen']

/-- A `drop` at `j ≤ i` is not an erased slot. The inner index `i + 1`
    resolves as the outer index `i`. -/
theorem resolve_insertDisp_hi_drop (ρ : List Disp) (j i : Nat)
    (hj : j ≤ i) (hlen : j ≤ ρ.length) :
    resolve (insertDisp .drop j ρ) (i + 1) = resolve ρ i := by
  induction j generalizing ρ i with
  | zero =>
    rw [insertDisp_zero, resolve_drop_succ]
  | succ j ih =>
    cases i with
    | zero => exact absurd hj (Nat.not_succ_le_zero _)
    | succ i =>
      have hj' : j ≤ i := Nat.le_of_succ_le_succ hj
      cases ρ with
      | nil =>
        simp only [List.length_nil] at hlen
        exact absurd hlen (Nat.not_succ_le_zero j)
      | cons hd ρ =>
        have hlen' : j ≤ ρ.length := by
          simp only [List.length_cons] at hlen
          exact Nat.le_of_succ_le_succ hlen
        cases hd with
        | keep =>
          simp only [insertDisp, resolve]
          exact congrArg (·.lift 0 1) (ih ρ i hj' hlen')
        | drop =>
          simp only [insertDisp, resolve, ih ρ i hj' hlen']
        | inline _ =>
          simp only [insertDisp, resolve, ih ρ i hj' hlen']

/-- An `inline` at `j ≤ i` is not an erased slot either. -/
theorem resolve_insertDisp_hi_inline (ρ : List Disp) (j i : Nat) (v : ETm)
    (hj : j ≤ i) (hlen : j ≤ ρ.length) :
    resolve (insertDisp (.inline v) j ρ) (i + 1) = resolve ρ i := by
  induction j generalizing ρ i with
  | zero =>
    rw [insertDisp_zero, resolve_inline_succ]
  | succ j ih =>
    cases i with
    | zero => exact absurd hj (Nat.not_succ_le_zero _)
    | succ i =>
      have hj' : j ≤ i := Nat.le_of_succ_le_succ hj
      cases ρ with
      | nil =>
        simp only [List.length_nil] at hlen
        exact absurd hlen (Nat.not_succ_le_zero j)
      | cons hd ρ =>
        have hlen' : j ≤ ρ.length := by
          simp only [List.length_cons] at hlen
          exact Nat.le_of_succ_le_succ hlen
        cases hd with
        | keep =>
          simp only [insertDisp, resolve]
          exact congrArg (·.lift 0 1) (ih ρ i hj' hlen')
        | drop =>
          simp only [insertDisp, resolve, ih ρ i hj' hlen']
        | inline _ =>
          simp only [insertDisp, resolve, ih ρ i hj' hlen']

/-- A `keep` at `j ≤ i` is one erased slot. The lift is `countKeep` of
    the prefix before `j`. -/
theorem resolve_insertDisp_hi_keep (ρ : List Disp) (j i : Nat)
    (hj : j ≤ i) (hlen : j ≤ ρ.length) :
    resolve (insertDisp .keep j ρ) (i + 1) =
      (resolve ρ i).lift (countKeep (ρ.take j)) 1 := by
  induction j generalizing ρ i with
  | zero =>
    rw [insertDisp_zero, resolve_keep_succ]
    simp only [List.take_zero, countKeep]
  | succ j ih =>
    cases i with
    | zero => exact absurd hj (Nat.not_succ_le_zero _)
    | succ i =>
      have hj' : j ≤ i := Nat.le_of_succ_le_succ hj
      cases ρ with
      | nil =>
        simp only [List.length_nil] at hlen
        exact absurd hlen (Nat.not_succ_le_zero j)
      | cons hd ρ =>
        have hlen' : j ≤ ρ.length := by
          simp only [List.length_cons] at hlen
          exact Nat.le_of_succ_le_succ hlen
        cases hd with
        | keep =>
          simp only [insertDisp, resolve, List.take_succ_cons, countKeep]
          rw [ih ρ i hj' hlen']
          have hs := lift_shift (countKeep (ρ.take j)) 0 (resolve ρ i)
          simpa only [Nat.zero_add] using hs.symm
        | drop =>
          simp only [insertDisp, resolve, List.take_succ_cons, countKeep,
            ih ρ i hj' hlen']
        | inline _ =>
          simp only [insertDisp, resolve, List.take_succ_cons, countKeep,
            ih ρ i hj' hlen']

/-- Inserting `inline v` at source index `j` makes `j` erase to `v`
    lifted at cutoff 0 by the newer `keep`s, when `j` is in range. -/
theorem resolve_insertDisp_inline (j : Nat) (v : ETm) (ρ : List Disp)
    (hj : j ≤ ρ.length) :
    resolve (insertDisp (.inline v) j ρ) j =
      v.lift 0 (countKeep (ρ.take j)) := by
  induction j generalizing ρ with
  | zero =>
    simp only [insertDisp, resolve, List.take_zero, countKeep]
    exact (ETm.lift_zero 0 v).symm
  | succ j ih =>
    cases ρ with
    | nil => exact absurd hj (Nat.not_succ_le_zero j)
    | cons hd ρ =>
      have hj' : j ≤ ρ.length := by
        simp only [List.length_cons] at hj
        exact Nat.le_of_succ_le_succ hj
      cases hd with
      | keep =>
        simp only [insertDisp, resolve, List.take_succ_cons, countKeep]
        rw [ih ρ hj']
        exact ETm.lift_lift_merge 1 (countKeep (ρ.take j)) 0 0
          (Nat.le_refl 0) (Nat.zero_le _) v
      | drop =>
        simp only [insertDisp, resolve, List.take_succ_cons, countKeep,
          ih ρ hj']
      | inline _ =>
        simp only [insertDisp, resolve, List.take_succ_cons, countKeep,
          ih ρ hj']

end Rcic.Syn

#print axioms Rcic.Syn.resolve_insertDisp_lo
#print axioms Rcic.Syn.resolve_insertDisp_hi_drop
#print axioms Rcic.Syn.resolve_insertDisp_hi_inline
#print axioms Rcic.Syn.resolve_insertDisp_hi_keep
#print axioms Rcic.Syn.resolve_insertDisp_inline

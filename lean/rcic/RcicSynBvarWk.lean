import rcic.RcicSynErase

/-!
# Syntactic sortRow, build step 3af — `wk` moves a resolved index

`research/rcic/semantic/S3_ES_ARMS.md` §31. `bvarEps` returns `other` on
`wk`. The index arithmetic is already `lift_eq_bvar`. What was missing is
how `resolve` sees the inserted disposition.

`removeAt ρ c` is the disposition list of the inner typing. Below the
cutoff (`i < c`) that removal does not change `resolve`. At or above it,
a `drop` or an `inline` leaves the erased index, and a `keep` is one
`ETm.lift` at `countKeep (ρ.take c)`. A missing entry (`ρ[c]? = none`)
does not: a short list resolves to `bvar i₀`, and `bvar (i₀ + 1)` is a
different term. That is the out-of-range case.

Not proved. The `wk` arm of `bvarEps` still returns `other`. `esub` and
`lsub` move an index the same way, and the hole returns the replacement.
`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- Pass a one-slot lift through a later one. Cutoff `c` on the inside,
    cutoff `c + k` on the outside, is cutoff `c + k + 1` on a term already
    lifted at `c`. -/
theorem lift_shift (k c : Nat) (t : ETm) :
    (t.lift c 1).lift (c + k + 1) 1 = (t.lift (c + k) 1).lift c 1 := by
  induction t generalizing c with
  | bvar i =>
    by_cases hc : c ≤ i
    · by_cases hk : c + k ≤ i
      · conv =>
          lhs
          rw [ETm.lift, if_pos hc]
          rw [ETm.lift, if_pos (Nat.add_le_add_right hk 1)]
        conv =>
          rhs
          rw [ETm.lift, if_pos hk]
          rw [ETm.lift, if_pos (Nat.le_trans hc (Nat.le_succ i))]
      · conv =>
          lhs
          rw [ETm.lift, if_pos hc]
          rw [ETm.lift, if_neg (fun h => hk (Nat.le_of_succ_le_succ h))]
        conv =>
          rhs
          rw [ETm.lift, if_neg hk]
          rw [ETm.lift, if_pos hc]
    · have hk : ¬ c + k ≤ i := fun h => hc (Nat.le_trans (Nat.le_add_right c k) h)
      conv =>
        lhs
        rw [ETm.lift, if_neg hc]
        rw [ETm.lift, if_neg (fun h => hk (Nat.le_trans (Nat.le_succ (c + k)) h))]
      conv =>
        rhs
        rw [ETm.lift, if_neg hk]
        rw [ETm.lift, if_neg hc]
  | star => rfl
  | sort _ => rfl
  | const _ _ => rfl
  | app _ _ ihf iha =>
    rw [ETm.lift, ETm.lift, ETm.lift, ETm.lift, ihf c, iha c]
  | lam _ ih =>
    rw [ETm.lift, ETm.lift, ETm.lift, ETm.lift]
    congr 1
    rw [show c + k + 1 + 1 = (c + 1) + k + 1 by omega]
    rw [show c + k + 1 = (c + 1) + k by omega]
    exact ih (c + 1)
  | pi _ _ iha ihb =>
    rw [ETm.lift, ETm.lift, ETm.lift, ETm.lift]
    congr 1
    · exact iha c
    · rw [show c + k + 1 + 1 = (c + 1) + k + 1 by omega]
      rw [show c + k + 1 = (c + 1) + k by omega]
      exact ihb (c + 1)

/-- Removing a disposition strictly above `i` does not change `resolve ρ i`. -/
theorem resolve_removeAt_lo (ρ : List Disp) (c i : Nat) (h : i < c) :
    resolve (removeAt ρ c) i = resolve ρ i := by
  induction i generalizing ρ c with
  | zero =>
    cases c with
    | zero => exact absurd h (Nat.not_lt_zero _)
    | succ _ =>
      cases ρ with
      | nil => rfl
      | cons d _ =>
        cases d <;> rfl
  | succ i ih =>
    cases c with
    | zero => exact absurd h (Nat.not_lt_zero _)
    | succ c =>
      have h' : i < c := Nat.lt_of_succ_lt_succ h
      cases ρ with
      | nil => rfl
      | cons d ρ =>
        cases d with
        | keep => simp only [removeAt, resolve, ih ρ c h']
        | drop => simp only [removeAt, resolve, ih ρ c h']
        | inline _ => simp only [removeAt, resolve, ih ρ c h']

/-- A `drop` at `c ≤ i₀` is not an erased slot. The outer index `i₀ + 1`
    resolves as the inner index `i₀`. -/
theorem resolve_removeAt_hi_drop (ρ : List Disp) (c i₀ : Nat)
    (hc : c ≤ i₀) (hk : ρ[c]? = some .drop) :
    resolve (removeAt ρ c) i₀ = resolve ρ (i₀ + 1) := by
  induction c generalizing ρ i₀ with
  | zero =>
    cases ρ with
    | nil =>
      simp only [List.getElem?_nil] at hk
      cases hk
    | cons d ρ =>
      simp only [List.getElem?_cons_zero] at hk
      cases d <;> cases hk
      simp only [removeAt, resolve]
  | succ c ih =>
    cases i₀ with
    | zero => exact absurd hc (Nat.not_succ_le_zero _)
    | succ i₀ =>
      cases ρ with
      | nil =>
        simp only [List.getElem?_nil] at hk
        cases hk
      | cons d ρ =>
        have hk' : ρ[c]? = some .drop := by
          simpa only [List.getElem?_cons_succ] using hk
        have hc' : c ≤ i₀ := Nat.le_of_succ_le_succ hc
        cases d with
        | keep => simp only [removeAt, resolve, ih ρ i₀ hc' hk']
        | drop => simp only [removeAt, resolve, ih ρ i₀ hc' hk']
        | inline _ => simp only [removeAt, resolve, ih ρ i₀ hc' hk']

/-- An `inline` at `c ≤ i₀` is not an erased slot either. -/
theorem resolve_removeAt_hi_inline (ρ : List Disp) (c i₀ : Nat) (v : ETm)
    (hc : c ≤ i₀) (hk : ρ[c]? = some (.inline v)) :
    resolve (removeAt ρ c) i₀ = resolve ρ (i₀ + 1) := by
  induction c generalizing ρ i₀ with
  | zero =>
    cases ρ with
    | nil =>
      simp only [List.getElem?_nil] at hk
      cases hk
    | cons d ρ =>
      simp only [List.getElem?_cons_zero] at hk
      cases d <;> cases hk
      simp only [removeAt, resolve]
  | succ c ih =>
    cases i₀ with
    | zero => exact absurd hc (Nat.not_succ_le_zero _)
    | succ i₀ =>
      cases ρ with
      | nil =>
        simp only [List.getElem?_nil] at hk
        cases hk
      | cons d ρ =>
        have hk' : ρ[c]? = some (.inline v) := by
          simpa only [List.getElem?_cons_succ] using hk
        have hc' : c ≤ i₀ := Nat.le_of_succ_le_succ hc
        cases d with
        | keep => simp only [removeAt, resolve, ih ρ i₀ hc' hk']
        | drop => simp only [removeAt, resolve, ih ρ i₀ hc' hk']
        | inline _ => simp only [removeAt, resolve, ih ρ i₀ hc' hk']

/-- A `keep` at `c ≤ i₀` is one erased slot. The lift is
    `countKeep` of the prefix before `c`. -/
theorem resolve_removeAt_hi_keep (ρ : List Disp) (c i₀ : Nat)
    (hc : c ≤ i₀) (hk : ρ[c]? = some .keep) :
    (resolve (removeAt ρ c) i₀).lift (countKeep (ρ.take c)) 1 =
      resolve ρ (i₀ + 1) := by
  induction c generalizing ρ i₀ with
  | zero =>
    cases ρ with
    | nil =>
      simp only [List.getElem?_nil] at hk
      cases hk
    | cons d ρ =>
      simp only [List.getElem?_cons_zero] at hk
      cases d <;> cases hk
      simp only [removeAt, resolve, List.take_zero, countKeep]
  | succ c ih =>
    cases i₀ with
    | zero => exact absurd hc (Nat.not_succ_le_zero _)
    | succ i₀ =>
      cases ρ with
      | nil =>
        simp only [List.getElem?_nil] at hk
        cases hk
      | cons d ρ =>
        have hk' : ρ[c]? = some .keep := by
          simpa only [List.getElem?_cons_succ] using hk
        have hc' : c ≤ i₀ := Nat.le_of_succ_le_succ hc
        cases d with
        | keep =>
          simp only [removeAt, resolve, List.take_succ_cons, countKeep]
          rw [← ih ρ i₀ hc' hk']
          have hs := lift_shift (countKeep (ρ.take c)) 0 (resolve (removeAt ρ c) i₀)
          simpa only [Nat.zero_add] using hs
        | drop =>
          simp only [removeAt, resolve, List.take_succ_cons, countKeep,
            ih ρ i₀ hc' hk']
        | inline _ =>
          simp only [removeAt, resolve, List.take_succ_cons, countKeep,
            ih ρ i₀ hc' hk']

end Rcic.Syn

#print axioms Rcic.Syn.lift_shift
#print axioms Rcic.Syn.resolve_removeAt_lo
#print axioms Rcic.Syn.resolve_removeAt_hi_drop
#print axioms Rcic.Syn.resolve_removeAt_hi_inline
#print axioms Rcic.Syn.resolve_removeAt_hi_keep

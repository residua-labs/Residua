import rcic.RcicSynTable

/-!
# `RcicDispShapeLetJ` — S14 §7: `DispShape` for a let entry inserted at a general cutoff `j`

`research/rcic/sortrow/S14_SHIFTED_VALUE_SCOPE.md` §7 names the missing piece: main's
`dispShape_insertDisp_let` (RcicSynTable.lean) constructs
`DispShape Γ (insertDisp (letDisp ev) j ρ)` only at `j = 0`; the shifted-value work needs
the same construction at a general nonzero cutoff.

The range premise is exactly what the original lsub/esub `hget : Γ[j]? = some (.letBinding t v)`
supplies: `j < Γ.length` from the lookup, hence `j ≤ ρ.length` through the context/display
length equality (`DispShape.length_eq`, with `(substRemove v j Γ).length = Γ.length - 1`).
It is stated explicitly as `hj : j ≤ ρ.length` — consumers derive it from `hget` — and the
short-list control `not_dispShape_insertDisp_letJ_short` shows the conclusion is
unattainable without it (`insertDisp d 1 [] = [d]`; `DispShape [] [d]` has no constructor).

Contents:

- `dispShape_insertDisp_letJ_drop` / `dispShape_insertDisp_letJ_inline`: the construction
  for the two let-entry payloads (`.drop`, `.inline w`), reusing the `j = 0` lemma's proof
  shape extended by induction on `j` through the context spine (same cons/`j+1` shape as
  `dispShape_insertDisp_drop`/`_keep`).
- `dispShape_insertDisp_letJ`: the `letDisp ev` consumer-facing form — the general-`j`
  analogue of main's `dispShape_insertDisp_let`.
- `not_dispShape_insertDisp_letJ_short`: short-list control (`ρ = []`, `j = 1`).

Additive only; `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- `DispShape` for `insertDisp .drop j ρ` when the entry at `j` is a let binding.
    Base case reuses the `j = 0` shape (`dispShape_let_clause` with `ev = .star`):
    the head is the removed let, `insertDisp .drop 0 ρ = .drop :: ρ`. The `j + 1`
    step peels the head disposition and recurses on the tail. -/
theorem dispShape_insertDisp_letJ_drop (v : Expr Nat) :
    {Γ : LCtx} → {j : Nat} → {t : Expr Nat} →
    Γ[j]? = some (.letBinding t v) → {ρ : List Disp} →
    j ≤ ρ.length → DispShape (substRemove v j Γ) ρ →
    DispShape Γ (insertDisp .drop j ρ)
  | [], j, _, hget, _, _, _ => by cases j <;> cases hget
  | _ :: _, 0, _, hget, _, _, hs => by
      simp only [List.getElem?_cons_zero] at hget
      cases Option.some.inj hget
      exact .letDrop hs
  | .assumption _ :: _, j + 1, _, hget, _, hj, hs => by
      simp only [List.getElem?_cons_succ] at hget
      cases hs with
      | assumptionKeep hs₀ =>
          exact .assumptionKeep (dispShape_insertDisp_letJ_drop v hget (by
            simp only [List.length_cons] at hj; omega) hs₀)
      | assumptionDrop hs₀ =>
          exact .assumptionDrop (dispShape_insertDisp_letJ_drop v hget (by
            simp only [List.length_cons] at hj; omega) hs₀)
  | .letBinding _ _ :: _, j + 1, _, hget, _, hj, hs => by
      simp only [List.getElem?_cons_succ] at hget
      cases hs with
      | letDrop hs₀ =>
          exact .letDrop (dispShape_insertDisp_letJ_drop v hget (by
            simp only [List.length_cons] at hj; omega) hs₀)
      | letInline hs₀ =>
          exact .letInline (dispShape_insertDisp_letJ_drop v hget (by
            simp only [List.length_cons] at hj; omega) hs₀)

/-- `DispShape` for `insertDisp (.inline w) j ρ` when the entry at `j` is a let binding.
    Same induction on `j` as `_drop`; at `j = 0` the `letInline` clause applies. -/
theorem dispShape_insertDisp_letJ_inline (v : Expr Nat) (w : ETm) :
    {Γ : LCtx} → {j : Nat} → {t : Expr Nat} →
    Γ[j]? = some (.letBinding t v) → {ρ : List Disp} →
    j ≤ ρ.length → DispShape (substRemove v j Γ) ρ →
    DispShape Γ (insertDisp (.inline w) j ρ)
  | [], j, _, hget, _, _, _ => by cases j <;> cases hget
  | _ :: _, 0, _, hget, _, _, hs => by
      simp only [List.getElem?_cons_zero] at hget
      cases Option.some.inj hget
      exact .letInline hs
  | .assumption _ :: _, j + 1, _, hget, _, hj, hs => by
      simp only [List.getElem?_cons_succ] at hget
      cases hs with
      | assumptionKeep hs₀ =>
          exact .assumptionKeep (dispShape_insertDisp_letJ_inline v w hget (by
            simp only [List.length_cons] at hj; omega) hs₀)
      | assumptionDrop hs₀ =>
          exact .assumptionDrop (dispShape_insertDisp_letJ_inline v w hget (by
            simp only [List.length_cons] at hj; omega) hs₀)
  | .letBinding _ _ :: _, j + 1, _, hget, _, hj, hs => by
      simp only [List.getElem?_cons_succ] at hget
      cases hs with
      | letDrop hs₀ =>
          exact .letDrop (dispShape_insertDisp_letJ_inline v w hget (by
            simp only [List.length_cons] at hj; omega) hs₀)
      | letInline hs₀ =>
          exact .letInline (dispShape_insertDisp_letJ_inline v w hget (by
            simp only [List.length_cons] at hj; omega) hs₀)

/-- The general-`j` analogue of main's `dispShape_insertDisp_let`: `DispShape` for
    `insertDisp (letDisp ev) j ρ` — `letDisp .star = .drop`, any other `ev` gives
    `.inline ev`, so both payloads dispatch to the two lemmas above. -/
theorem dispShape_insertDisp_letJ (v : Expr Nat) {Γ : LCtx} {j : Nat} {t : Expr Nat}
    (hget : Γ[j]? = some (.letBinding t v)) {ρ : List Disp} (hj : j ≤ ρ.length)
    (hs : DispShape (substRemove v j Γ) ρ) (ev : ETm) :
    DispShape Γ (insertDisp (letDisp ev) j ρ) := by
  cases ev with
  | star => exact dispShape_insertDisp_letJ_drop v hget hj hs
  | bvar i => exact dispShape_insertDisp_letJ_inline v (.bvar i) hget hj hs
  | sort h => exact dispShape_insertDisp_letJ_inline v (.sort h) hget hj hs
  | const r h => exact dispShape_insertDisp_letJ_inline v (.const r h) hget hj hs
  | app f a => exact dispShape_insertDisp_letJ_inline v (.app f a) hget hj hs
  | lam b => exact dispShape_insertDisp_letJ_inline v (.lam b) hget hj hs
  | pi A B => exact dispShape_insertDisp_letJ_inline v (.pi A B) hget hj hs

/-- Short-list control (the `ρ = []`, `j = 1` edge): `insertDisp` appends the payload at
    the end of a short display (`insertDisp d 1 [] = [d]`), so no `DispShape [] _` can
    hold it — `DispShape.length_eq` forces `1 = 0`. The `j ≤ ρ.length` premise is
    load-bearing, not cosmetic. -/
theorem not_dispShape_insertDisp_letJ_short (d : Disp) :
    ¬ DispShape ([] : LCtx) (insertDisp d 1 ([] : List Disp)) := by
  intro h
  have e : insertDisp d 1 ([] : List Disp) = [d] := rfl
  rw [e] at h
  cases h

end Rcic.Syn

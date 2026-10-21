import rcic.RcicAnnWk
import rcic.RcicAnnSubstCalc

/-!
# M2-s (1) — context lookups commute with insertion, on the copy

`RcicCtxMorph.lean`'s lookup lemmas on `LCtxA`, in ONE general form each: with
the insertion inside the context (`c ≤ Γ.length`, the bound `WkSpecA.ok`
carries), looking the SHIFTED index up in the extended context is looking the
index up in the original and lifting the answer — on `Option`, so the `none`
side is covered too (the head step's ζ-local arm and the type synthesis read
`none` as "no value"/"unbound", and a weakening proof must preserve those).
The `some`-only forms of the tree are corollaries.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- the index shift of `liftA c 1` on a variable. -/
def shiftIdx (c i : Nat) : Nat := if c ≤ i then i + 1 else i

theorem liftA_bvar (c i : Nat) : liftA c 1 (.bvar i) = .bvar (shiftIdx c i) := by
  simp only [liftA, shiftIdx]
  split <;> rfl

theorem shiftIdx_succ (c i : Nat) : shiftIdx (c + 1) (i + 1) = shiftIdx c i + 1 := by
  simp only [shiftIdx]
  by_cases h : c ≤ i
  · simp [h, Nat.succ_le_succ h]
  · have : ¬ c + 1 ≤ i + 1 := fun h' => h (Nat.le_of_succ_le_succ h')
    simp [h, this]

theorem shiftIdx_succ_zero (c : Nat) : shiftIdx (c + 1) 0 = 0 := by
  simp [shiftIdx]

/-! ## tail lookups compose with a 0-cutoff lift (P2 merge) -/

theorem lookupTypeA_cons_succ (y : LocalDeclA) (Δ : LCtxA) (i : Nat) :
    lookupTypeA (y :: Δ) (i + 1) = (lookupTypeA Δ i).map (liftA 0 1) := by
  simp only [lookupTypeA, List.get?_cons_succ]
  match h : Δ.get? i with
  | none => simp
  | some (.assumption a) =>
      simp only [Option.map_some']
      rw [liftA_liftA_merge 1 (i+1) 0 0 (by omega) (by omega)]
  | some (.letBinding a v) =>
      simp only [Option.map_some']
      rw [liftA_liftA_merge 1 (i+1) 0 0 (by omega) (by omega)]

theorem lookupValueA_cons_succ (y : LocalDeclA) (Δ : LCtxA) (i : Nat) :
    lookupValueA (y :: Δ) (i + 1) = (lookupValueA Δ i).map (liftA 0 1) := by
  simp only [lookupValueA, List.get?_cons_succ]
  match h : Δ.get? i with
  | none => simp
  | some (.assumption a) => simp
  | some (.letBinding a v) =>
      simp only [Option.map_some']
      rw [liftA_liftA_merge 1 (i+1) 0 0 (by omega) (by omega)]

theorem lookupTypeA_cons_zero_assumption (a : ExprA) (Δ : LCtxA) :
    lookupTypeA (.assumption a :: Δ) 0 = some (liftA 0 1 a) := rfl
theorem lookupTypeA_cons_zero_let (a v : ExprA) (Δ : LCtxA) :
    lookupTypeA (.letBinding a v :: Δ) 0 = some (liftA 0 1 a) := rfl
theorem lookupValueA_cons_zero_assumption (a : ExprA) (Δ : LCtxA) :
    lookupValueA (.assumption a :: Δ) 0 = none := rfl
theorem lookupValueA_cons_zero_let (a v : ExprA) (Δ : LCtxA) :
    lookupValueA (.letBinding a v :: Δ) 0 = some (liftA 0 1 v) := rfl

/-- a lift at `0` then at `c + 1` is a lift at `c` then at `0` (P1 at the
    binder). -/
theorem liftA_zero_succ_swap (c : Nat) (e : ExprA) :
    liftA 0 1 (liftA c 1 e) = liftA (c + 1) 1 (liftA 0 1 e) := by
  rw [liftA_liftA_permute 1 1 c 0 (by omega), show 1 + c = c + 1 from by omega]

/-! ## the general commutations -/

/-- looking the shifted index up in the extended context is looking the index
    up in the original and lifting the answer (types). -/
theorem lookupTypeA_insertAtA (d : LocalDeclA) :
    (c : Nat) → (Γ : LCtxA) → c ≤ Γ.length → (i : Nat) →
      lookupTypeA (insertAtA d c Γ) (shiftIdx c i) = (lookupTypeA Γ i).map (liftA c 1)
  | 0, Γ, _, i => by
      simp only [insertAtA, shiftIdx, Nat.zero_le, if_true]
      exact lookupTypeA_cons_succ d Γ i
  | c + 1, [], hc, _ => by simp at hc
  | c + 1, x :: Γ', hc, 0 => by
      rw [shiftIdx_succ_zero]
      cases x with
      | assumption a =>
          simp only [insertAtA, liftDeclA, lookupTypeA_cons_zero_assumption, Option.map_some']
          rw [liftA_zero_succ_swap]
      | letBinding a v =>
          simp only [insertAtA, liftDeclA, lookupTypeA_cons_zero_let, Option.map_some']
          rw [liftA_zero_succ_swap]
  | c + 1, x :: Γ', hc, i + 1 => by
      rw [shiftIdx_succ]
      simp only [insertAtA]
      rw [lookupTypeA_cons_succ, lookupTypeA_cons_succ,
        lookupTypeA_insertAtA d c Γ' (by simpa using Nat.le_of_succ_le_succ hc) i]
      cases lookupTypeA Γ' i with
      | none => rfl
      | some A => simp only [Option.map_some']; rw [liftA_zero_succ_swap]

theorem lookupValueA_insertAtA (d : LocalDeclA) :
    (c : Nat) → (Γ : LCtxA) → c ≤ Γ.length → (i : Nat) →
      lookupValueA (insertAtA d c Γ) (shiftIdx c i) = (lookupValueA Γ i).map (liftA c 1)
  | 0, Γ, _, i => by
      simp only [insertAtA, shiftIdx, Nat.zero_le, if_true]
      exact lookupValueA_cons_succ d Γ i
  | c + 1, [], hc, _ => by simp at hc
  | c + 1, x :: Γ', hc, 0 => by
      rw [shiftIdx_succ_zero]
      cases x with
      | assumption a =>
          simp only [insertAtA, liftDeclA, lookupValueA_cons_zero_assumption, Option.map_none']
      | letBinding a v =>
          simp only [insertAtA, liftDeclA, lookupValueA_cons_zero_let, Option.map_some']
          rw [liftA_zero_succ_swap]
  | c + 1, x :: Γ', hc, i + 1 => by
      rw [shiftIdx_succ]
      simp only [insertAtA]
      rw [lookupValueA_cons_succ, lookupValueA_cons_succ,
        lookupValueA_insertAtA d c Γ' (by simpa using Nat.le_of_succ_le_succ hc) i]
      cases lookupValueA Γ' i with
      | none => rfl
      | some v => simp only [Option.map_some']; rw [liftA_zero_succ_swap]

/-- the extended context is one longer. -/
theorem insertAtA_length (d : LocalDeclA) :
    (c : Nat) → (Γ : LCtxA) → c ≤ Γ.length → (insertAtA d c Γ).length = Γ.length + 1
  | 0, Γ, _ => rfl
  | c + 1, [], hc => by simp at hc
  | c + 1, x :: Γ', hc => by
      simp only [insertAtA, List.length_cons]
      rw [insertAtA_length d c Γ' (by simpa using Nat.le_of_succ_le_succ hc)]

/-! ## the tree's four `some` forms, as corollaries -/

theorem lookupTypeA_insertAtA_lt (d : LocalDeclA) {c i : Nat} {Γ : LCtxA} {A : ExprA}
    (hc : c ≤ Γ.length) (hic : i < c) (h : lookupTypeA Γ i = some A) :
    lookupTypeA (insertAtA d c Γ) i = some (liftA c 1 A) := by
  have := lookupTypeA_insertAtA d c Γ hc i
  simp only [shiftIdx, if_neg (Nat.not_le.mpr hic), h, Option.map_some'] at this
  exact this

theorem lookupTypeA_insertAtA_ge (d : LocalDeclA) {c i : Nat} {Γ : LCtxA} {A : ExprA}
    (hc : c ≤ Γ.length) (hic : c ≤ i) (h : lookupTypeA Γ i = some A) :
    lookupTypeA (insertAtA d c Γ) (i + 1) = some (liftA c 1 A) := by
  have := lookupTypeA_insertAtA d c Γ hc i
  simp only [shiftIdx, if_pos hic, h, Option.map_some'] at this
  exact this

theorem lookupValueA_insertAtA_lt (d : LocalDeclA) {c i : Nat} {Γ : LCtxA} {v : ExprA}
    (hc : c ≤ Γ.length) (hic : i < c) (h : lookupValueA Γ i = some v) :
    lookupValueA (insertAtA d c Γ) i = some (liftA c 1 v) := by
  have := lookupValueA_insertAtA d c Γ hc i
  simp only [shiftIdx, if_neg (Nat.not_le.mpr hic), h, Option.map_some'] at this
  exact this

theorem lookupValueA_insertAtA_ge (d : LocalDeclA) {c i : Nat} {Γ : LCtxA} {v : ExprA}
    (hc : c ≤ Γ.length) (hic : c ≤ i) (h : lookupValueA Γ i = some v) :
    lookupValueA (insertAtA d c Γ) (i + 1) = some (liftA c 1 v) := by
  have := lookupValueA_insertAtA d c Γ hc i
  simp only [shiftIdx, if_pos hic, h, Option.map_some'] at this
  exact this

#print axioms lookupTypeA_insertAtA
#print axioms lookupValueA_insertAtA
#print axioms insertAtA_length

end Rcic.Declarative.Ann

import rcic.RcicLevelDec

namespace Rcic.Declarative

/-!
## Total valuations and the exact partial-valuation level equality

The evaluator in `RcicDeclarative` uses partial valuations, including the
short-circuiting zero branch of `imax`. For this particular level algebra,
equality at every total valuation nevertheless implies the exact `eqN`.

The key invariant is constructive: filling every missing parameter with `k`
preserves an already defined result, while an undefined result becomes at
least `k`. Thus a partial disagreement gives an explicit total disagreement.
This is a lemma about levels; conversion soundness is a separate obligation.
-/

/- Reuses the existing RcicLevelDec.evalTotal; no duplicate evaluator. -/

/-- The partial evaluator agrees with `evalTotal` on total valuations. -/
theorem eval_some_total (ν : Nat → Nat) (l : Level) :
    eval (fun i => some (ν i)) l = some (evalTotal ν l) :=
  eval_total ν l

/-- Complete a partial valuation by assigning `k` to each missing parameter. -/
def completeValuation (ρ : Nat → Option Nat) (k : Nat) : Nat → Nat :=
  fun i => (ρ i).getD k

/-- A defined evaluation survives completion; an undefined evaluation grows
to at least the value assigned to all missing parameters. -/
theorem evalTotal_complete_spec (ρ : Nat → Option Nat) (k : Nat) (l : Level) :
    match eval ρ l with
    | some n => evalTotal (completeValuation ρ k) l = n
    | none => k ≤ evalTotal (completeValuation ρ k) l := by
  induction l with
  | zero => rfl
  | succ l ih =>
      cases h : eval ρ l with
      | none =>
          have hl : k ≤ evalTotal (completeValuation ρ k) l := by
            simpa [h] using ih
          simpa [eval, evalTotal, h] using
            Nat.le_trans hl (Nat.le_succ (evalTotal (completeValuation ρ k) l))
      | some n =>
          have hl : evalTotal (completeValuation ρ k) l = n := by
            simpa [h] using ih
          simp [eval, evalTotal, h, hl]
  | max a b iha ihb =>
      cases ha : eval ρ a with
      | none =>
          have hla : k ≤ evalTotal (completeValuation ρ k) a := by
            simpa [ha] using iha
          simpa [eval, evalTotal, ha] using
            Nat.le_trans hla (Nat.le_max_left
              (evalTotal (completeValuation ρ k) a)
              (evalTotal (completeValuation ρ k) b))
      | some na =>
          have hla : evalTotal (completeValuation ρ k) a = na := by
            simpa [ha] using iha
          cases hb : eval ρ b with
          | none =>
              have hlb : k ≤ evalTotal (completeValuation ρ k) b := by
                simpa [hb] using ihb
              simpa [eval, evalTotal, ha, hb] using
                Nat.le_trans hlb (Nat.le_max_right
                  (evalTotal (completeValuation ρ k) a)
                  (evalTotal (completeValuation ρ k) b))
          | some nb =>
              have hlb : evalTotal (completeValuation ρ k) b = nb := by
                simpa [hb] using ihb
              simp [eval, evalTotal, ha, hb, hla, hlb]
  | imax a b iha ihb =>
      cases hb : eval ρ b with
      | none =>
          have hlb : k ≤ evalTotal (completeValuation ρ k) b := by
            simpa [hb] using ihb
          by_cases hz : evalTotal (completeValuation ρ k) b = 0
          · simpa [eval, evalTotal, hb, hz] using hlb
          · simpa [eval, evalTotal, hb, hz] using
              Nat.le_trans hlb (Nat.le_max_right
                (evalTotal (completeValuation ρ k) a)
                (evalTotal (completeValuation ρ k) b))
      | some nb =>
          have hlb : evalTotal (completeValuation ρ k) b = nb := by
            simpa [hb] using ihb
          by_cases hz : nb = 0
          · simp [eval, evalTotal, hb, hlb, hz]
          · cases ha : eval ρ a with
            | none =>
                have hla : k ≤ evalTotal (completeValuation ρ k) a := by
                  simpa [ha] using iha
                simpa [eval, evalTotal, ha, hb, hlb, hz] using
                  Nat.le_trans hla (Nat.le_max_left
                    (evalTotal (completeValuation ρ k) a) nb)
            | some na =>
                have hla : evalTotal (completeValuation ρ k) a = na := by
                  simpa [ha] using iha
                simp [eval, evalTotal, ha, hb, hla, hlb, hz]
  | param i =>
      cases h : ρ i <;> simp [eval, evalTotal, completeValuation, h]

/-- Completion preserves any result already defined by the partial evaluator. -/
theorem evalTotal_complete_of_some (ρ : Nat → Option Nat) (k : Nat)
    (l : Level) {n : Nat} (h : eval ρ l = some n) :
    evalTotal (completeValuation ρ k) l = n := by
  simpa [h] using evalTotal_complete_spec ρ k l

/-- An undefined level evaluates above the completion parameter. -/
theorem evalTotal_complete_of_none (ρ : Nat → Option Nat) (k : Nat)
    (l : Level) (h : eval ρ l = none) :
    k ≤ evalTotal (completeValuation ρ k) l := by
  simpa [h] using evalTotal_complete_spec ρ k l

/-- An explicit total valuation separating any partial disagreement:
fill missing parameters with one more than both defined endpoint values. -/
def separatingTotalValuation (ρ : Nat → Option Nat) (l r : Level) : Nat → Nat :=
  completeValuation ρ (max ((eval ρ l).getD 0) ((eval ρ r).getD 0) + 1)

/-- A partial disagreement has a constructively specified total witness. -/
theorem evalTotal_separating_ne (ρ : Nat → Option Nat) (l r : Level)
    (hne : eval ρ l ≠ eval ρ r) :
    evalTotal (separatingTotalValuation ρ l r) l ≠
      evalTotal (separatingTotalValuation ρ l r) r := by
  cases hl : eval ρ l with
  | none =>
      cases hr : eval ρ r with
      | none => exact False.elim (hne (hl.trans hr.symm))
      | some nr =>
          have hleft := evalTotal_complete_of_none ρ (nr + 1) l hl
          have hright := evalTotal_complete_of_some ρ (nr + 1) r hr
          simp only [separatingTotalValuation, hl, hr, Option.getD_none,
            Option.getD_some, Nat.zero_max]
          intro heq
          rw [heq, hright] at hleft
          exact Nat.not_succ_le_self nr hleft
  | some nl =>
      cases hr : eval ρ r with
      | none =>
          have hleft := evalTotal_complete_of_some ρ (nl + 1) l hl
          have hright := evalTotal_complete_of_none ρ (nl + 1) r hr
          simp only [separatingTotalValuation, hl, hr, Option.getD_none,
            Option.getD_some, Nat.max_zero]
          intro heq
          rw [← heq, hleft] at hright
          exact Nat.not_succ_le_self nl hright
      | some nr =>
          have hleft := evalTotal_complete_of_some ρ (max nl nr + 1) l hl
          have hright := evalTotal_complete_of_some ρ (max nl nr + 1) r hr
          simp only [separatingTotalValuation, hl, hr, Option.getD_some]
          intro heq
          have hvalues : nl = nr := hleft.symm.trans (heq.trans hright)
          exact hne (hl.trans ((congrArg some hvalues).trans hr.symm))

/-- The same separating witness stated using the original `Option` evaluator. -/
theorem eval_separating_total_ne (ρ : Nat → Option Nat) (l r : Level)
    (hne : eval ρ l ≠ eval ρ r) :
    eval (fun i => some (separatingTotalValuation ρ l r i)) l ≠
      eval (fun i => some (separatingTotalValuation ρ l r i)) r := by
  rw [eval_some_total, eval_some_total]
  intro h
  exact evalTotal_separating_ne ρ l r hne (Option.some.inj h)

/-- Equality under all total natural-number valuations implies the exact
equality quantified over all partial valuations in `RcicDeclarative.eqN`. -/
theorem eqN_of_evalTotal_eq {l r : Level}
    (h : ∀ ν : Nat → Nat, evalTotal ν l = evalTotal ν r) : eqN l r := by
  intro ρ
  by_cases heq : eval ρ l = eval ρ r
  · exact heq
  · exact False.elim (evalTotal_separating_ne ρ l r heq
      (h (separatingTotalValuation ρ l r)))

/-- Total-valuation equality and exact partial-valuation equality coincide. -/
theorem evalTotal_eq_iff_eqN (l r : Level) :
    (∀ ν : Nat → Nat, evalTotal ν l = evalTotal ν r) ↔ eqN l r := by
  constructor
  · exact eqN_of_evalTotal_eq
  · intro h ν
    have heq := h (fun i => some (ν i))
    rw [eval_some_total, eval_some_total] at heq
    exact Option.some.inj heq

end Rcic.Declarative

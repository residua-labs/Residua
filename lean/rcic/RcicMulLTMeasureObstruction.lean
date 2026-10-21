import rcic.RcicMulLT

/-!
# Two obstructions to the proposed natural-number foundation measure

These statements concern the *existing* `Rcic.S3.MulLT`, not a new
ordering. A finite pool of allowed values does not bound multiplicity.
More strongly, no natural-number function strictly decreases along every
unbounded DM step, even on lists containing only 0 and 1.

This does not refute well-foundedness of `MulLT`, nor any R-CIC typing
theorem. It identifies why an accessibility proof is needed once the
unproved fan-out bound is removed. It also does not supply the missing
strict-decrease certificates for the actual U/X/P calls.
-/

namespace Rcic.S3

def zeroCopies : Nat → List Nat
  | 0 => []
  | k + 1 => 0 :: zeroCopies k

theorem zeroCopies_length (k : Nat) : (zeroCopies k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [zeroCopies, List.length_cons, ih]

theorem eq_zero_of_mem_zeroCopies {k y : Nat} (h : y ∈ zeroCopies k) : y = 0 := by
  induction k with
  | zero => exact False.elim (List.not_mem_nil y h)
  | succ k ih =>
    cases h with
    | head => rfl
    | tail _ h => exact ih h

/-- Removing one zero is a genuine DM step. -/
theorem mulLT_zeroCopies_succ (k : Nat) :
    MulLT (zeroCopies k) (zeroCopies (k + 1)) := by
  refine ⟨zeroCopies k, [], [0], ?_, ?_, ?_, ?_⟩
  · simpa only [List.append_nil] using List.Perm.refl (zeroCopies k)
  · exact (List.perm_append_singleton 0 (zeroCopies k)).symm
  · exact List.cons_ne_nil 0 []
  · intro y hy
    exact False.elim (List.not_mem_nil y hy)

/-- One 1 may be replaced by arbitrarily many zeros. -/
theorem mulLT_zeroCopies_one (k : Nat) : MulLT (zeroCopies k) [1] := by
  refine ⟨[], zeroCopies k, [1], List.Perm.refl _, List.Perm.refl _,
    List.cons_ne_nil 1 [], ?_⟩
  intro y hy
  have hy0 := eq_zero_of_mem_zeroCopies hy
  subst y
  exact ⟨1, List.mem_cons_self 1 [], by decide⟩

/-- A finite support of size two does not bound the number of citations
    by two. The proposed weight is equal on this strict DM step. -/
theorem finite_support_does_not_bound_fanout :
    MulLT [0, 0, 0] [1] ∧
    (∀ y ∈ ([0, 0, 0] : List Nat), y ∈ ([0, 1] : List Nat)) ∧
    ¬ ([0, 0, 0] : List Nat).length ≤ 2 ∧
    vecSum 2 [0, 0, 0] = vecSum 2 [1] := by
  refine ⟨mulLT_zeroCopies_one 3, ?_, by decide, by decide⟩
  intro y hy
  have hy0 : y = 0 := eq_zero_of_mem_zeroCopies (k := 3) hy
  subst y
  exact List.mem_cons_self 0 [1]

/-- The problem cannot be repaired by choosing some other global Nat
    weight for unbounded DM. A root `[1]` has descendants with arbitrarily
    long finite chains below them. -/
theorem no_nat_rank_for_mulLT :
    ¬ ∃ rank : List Nat → Nat,
      ∀ {m n : List Nat}, MulLT m n → rank m < rank n := by
  rintro ⟨rank, hdecrease⟩
  have hlength : ∀ k : Nat, k ≤ rank (zeroCopies k) := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hstep := hdecrease (mulLT_zeroCopies_succ k)
      exact Nat.le_trans (Nat.succ_le_succ ih) (Nat.succ_le_of_lt hstep)
  have hbelow := hdecrease (mulLT_zeroCopies_one (rank [1]))
  have hlarge := hlength (rank [1])
  exact Nat.not_lt_of_ge hlarge hbelow

end Rcic.S3

#print axioms Rcic.S3.finite_support_does_not_bound_fanout
#print axioms Rcic.S3.no_nat_rank_for_mulLT

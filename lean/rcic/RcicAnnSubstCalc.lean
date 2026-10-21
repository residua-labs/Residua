import rcic.RcicAnnSyntax

/-!
# M2-s (0) — the substitution calculus on the annotated copy

`RcicSubstCalc.lean`'s eight de Bruijn commutation lemmas (P0–P6), transcribed
onto `ExprA` with the same statement forms (the shifting summand on the LEFT of
the varying cutoff, so binder recursion is definitional) and the same proofs;
the annotation is carried through every binder untouched, so no lemma mentions
it. Ground for M2-a (the relation weakens along worlds) and M2-s (`HasTyA` /
`ConvA` weaken and substitute). Reuse, not a rewrite.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- leaf normaliser for bvar goals: unfold, split every ite, close each leaf by
    rfl / index arithmetic / contradiction. -/
macro "bvarA_leaves" : tactic =>
  `(tactic| ((repeat' (first | (simp only [liftA, instantiateA]) | split)) <;>
             (first | rfl | (exfalso; omega) | (congr 1 <;> omega))))

/-- P0: lifting by zero is the identity. -/
theorem liftA_zero (c : Nat) (e : ExprA) : liftA c 0 e = e := by
  induction e generalizing c with
  | bvar i => bvarA_leaves
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx => simp only [liftA, ihf, ihx] <;> try rfl
  | lam a _ b iha ihb => simp only [liftA, iha, ihb] <;> try rfl
  | pi a _ b _ iha ihb => simp only [liftA, iha, ihb] <;> try rfl
  | letE a v b iha ihv ihb => simp only [liftA, iha, ihv, ihb] <;> try rfl
  | lit t => rfl

/-- P1 (permute): a lift at a lower cutoff commutes past one at a higher
    cutoff, pushing the higher cutoff up by the lower amount. -/
theorem liftA_liftA_permute (m n c c' : Nat) (h : c' ≤ c) (e : ExprA) :
    liftA c' m (liftA c n e) = liftA (m + c) n (liftA c' m e) := by
  induction e generalizing c c' with
  | bvar i => bvarA_leaves
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx => simp only [liftA, ihf _ _ h, ihx _ _ h] <;> try rfl
  | lam a _ b iha ihb =>
      simp only [liftA, iha _ _ h, ihb (c+1) (c'+1) (by omega)] <;> try rfl
  | pi a _ b _ iha ihb =>
      simp only [liftA, iha _ _ h, ihb (c+1) (c'+1) (by omega)] <;> try rfl
  | letE a v b iha ihv ihb =>
      simp only [liftA, iha _ _ h, ihv _ _ h, ihb (c+1) (c'+1) (by omega)] <;> try rfl
  | lit t => rfl

/-- P2 (merge): a lift whose cutoff lands inside the gap opened by another
    lift merges into a single lift of the summed amount. -/
theorem liftA_liftA_merge (m n c c' : Nat) (h1 : c ≤ c') (h2 : c' ≤ n + c) (e : ExprA) :
    liftA c' m (liftA c n e) = liftA c (n + m) e := by
  induction e generalizing c c' with
  | bvar i => bvarA_leaves
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx => simp only [liftA, ihf _ _ h1 h2, ihx _ _ h1 h2] <;> try rfl
  | lam a _ b iha ihb =>
      simp only [liftA, iha _ _ h1 h2, ihb (c+1) (c'+1) (by omega) (by omega)] <;> try rfl
  | pi a _ b _ iha ihb =>
      simp only [liftA, iha _ _ h1 h2, ihb (c+1) (c'+1) (by omega) (by omega)] <;> try rfl
  | letE a v b iha ihv ihb =>
      simp only [liftA, iha _ _ h1 h2, ihv _ _ h1 h2,
        ihb (c+1) (c'+1) (by omega) (by omega)] <;> try rfl
  | lit t => rfl

/-- P3 (lift past an instantiation below its cutoff): for `j ≤ c`. -/
theorem liftA_instantiateA_low (a c j : Nat) (r : ExprA) (h : j ≤ c) (e : ExprA) :
    liftA c a (instantiateA j r e) =
      instantiateA j (liftA c a r) (liftA (c + 1) a e) := by
  induction e generalizing c j r with
  | bvar i => bvarA_leaves
  | sort l => rfl
  | const r' ls => rfl
  | app f x ihf ihx => simp only [liftA, instantiateA, ihf _ _ _ h, ihx _ _ _ h] <;> try rfl
  | lam A _ b ihA ihb =>
      have e2 : liftA 0 1 (liftA c a r) = liftA (c + 1) a (liftA 0 1 r) := by
        rw [liftA_liftA_permute 1 a c 0 (by omega) r,
            show 1 + c = c + 1 from by omega]
      simp only [liftA, instantiateA, ihA _ _ _ h,
        ihb (c+1) (j+1) (liftA 0 1 r) (by omega), e2] <;> try rfl
  | pi A _ b _ ihA ihb =>
      have e2 : liftA 0 1 (liftA c a r) = liftA (c + 1) a (liftA 0 1 r) := by
        rw [liftA_liftA_permute 1 a c 0 (by omega) r,
            show 1 + c = c + 1 from by omega]
      simp only [liftA, instantiateA, ihA _ _ _ h,
        ihb (c+1) (j+1) (liftA 0 1 r) (by omega), e2] <;> try rfl
  | letE A v b ihA ihv ihb =>
      have e2 : liftA 0 1 (liftA c a r) = liftA (c + 1) a (liftA 0 1 r) := by
        rw [liftA_liftA_permute 1 a c 0 (by omega) r,
            show 1 + c = c + 1 from by omega]
      simp only [liftA, instantiateA, ihA _ _ _ h, ihv _ _ _ h,
        ihb (c+1) (j+1) (liftA 0 1 r) (by omega), e2] <;> try rfl
  | lit t => rfl

/-- P4 (lift past an instantiation at-or-above its cutoff): for `c ≤ j`, the
    instantiation index shifts by the lift amount. -/
theorem liftA_instantiateA_high (a c j : Nat) (s : ExprA) (h : c ≤ j) (e : ExprA) :
    liftA c a (instantiateA j s e) =
      instantiateA (a + j) (liftA c a s) (liftA c a e) := by
  induction e generalizing c j s with
  | bvar i => bvarA_leaves
  | sort l => rfl
  | const r' ls => rfl
  | app f x ihf ihx => simp only [liftA, instantiateA, ihf _ _ _ h, ihx _ _ _ h] <;> try rfl
  | lam A _ b ihA ihb =>
      have e2 : liftA 0 1 (liftA c a s) = liftA (c + 1) a (liftA 0 1 s) := by
        rw [liftA_liftA_permute 1 a c 0 (by omega) s,
            show 1 + c = c + 1 from by omega]
      simp only [liftA, instantiateA, ihA _ _ _ h,
        ihb (c+1) (j+1) (liftA 0 1 s) (by omega), e2] <;> try rfl
  | pi A _ b _ ihA ihb =>
      have e2 : liftA 0 1 (liftA c a s) = liftA (c + 1) a (liftA 0 1 s) := by
        rw [liftA_liftA_permute 1 a c 0 (by omega) s,
            show 1 + c = c + 1 from by omega]
      simp only [liftA, instantiateA, ihA _ _ _ h,
        ihb (c+1) (j+1) (liftA 0 1 s) (by omega), e2] <;> try rfl
  | letE A v b ihA ihv ihb =>
      have e2 : liftA 0 1 (liftA c a s) = liftA (c + 1) a (liftA 0 1 s) := by
        rw [liftA_liftA_permute 1 a c 0 (by omega) s,
            show 1 + c = c + 1 from by omega]
      simp only [liftA, instantiateA, ihA _ _ _ h, ihv _ _ _ h,
        ihb (c+1) (j+1) (liftA 0 1 s) (by omega), e2] <;> try rfl
  | lit t => rfl

/-- P5 (cancel): instantiating anywhere inside the gap a lift opened consumes
    one unit of the gap; the replacement is never consulted. -/
theorem instantiateA_liftA_cancel (a c j : Nat) (r : ExprA)
    (h1 : c ≤ j) (h2 : j < a + c) (e : ExprA) :
    instantiateA j r (liftA c a e) = liftA c (a - 1) e := by
  induction e generalizing c j r with
  | bvar i => bvarA_leaves
  | sort l => rfl
  | const r' ls => rfl
  | app f x ihf ihx => simp only [liftA, instantiateA, ihf _ _ _ h1 h2, ihx _ _ _ h1 h2] <;> try rfl
  | lam A _ b ihA ihb =>
      simp only [liftA, instantiateA, ihA _ _ _ h1 h2,
        ihb (c+1) (j+1) (liftA 0 1 r) (by omega) (by omega)] <;> try rfl
  | pi A _ b _ ihA ihb =>
      simp only [liftA, instantiateA, ihA _ _ _ h1 h2,
        ihb (c+1) (j+1) (liftA 0 1 r) (by omega) (by omega)] <;> try rfl
  | letE A v b ihA ihv ihb =>
      simp only [liftA, instantiateA, ihA _ _ _ h1 h2, ihv _ _ _ h1 h2,
        ihb (c+1) (j+1) (liftA 0 1 r) (by omega) (by omega)] <;> try rfl
  | lit t => rfl

/-- P5 at the classic corner: `instantiateA j r (liftA j 1 e) = e`. -/
theorem instantiateA_liftA_id (j : Nat) (r : ExprA) (e : ExprA) :
    instantiateA j r (liftA j 1 e) = e := by
  rw [instantiateA_liftA_cancel 1 j j r (Nat.le_refl j) (by omega), liftA_zero]

/-- P6 (inst-inst commutation — the substitution lemma's engine): for `j ≤ k`. -/
theorem instantiateA_instantiateA (j k : Nat) (r s : ExprA) (h : j ≤ k) (e : ExprA) :
    instantiateA k s (instantiateA j r e) =
      instantiateA j (instantiateA k s r)
        (instantiateA (k + 1) (liftA j 1 s) e) := by
  induction e generalizing j k r s with
  | bvar i =>
      by_cases hik : i = k + 1
      · subst hik
        have hjne : ¬ (k + 1 = j) := by omega
        have hj1 : j < k + 1 := by omega
        simp only [instantiateA, if_neg hjne, if_pos hj1,
          show k + 1 - 1 = k from by omega, if_pos rfl, if_true, instantiateA_liftA_id]
      · bvarA_leaves
  | sort l => rfl
  | const r' ls => rfl
  | app f x ihf ihx => simp only [instantiateA, ihf _ _ _ _ h, ihx _ _ _ _ h] <;> try rfl
  | lam A _ b ihA ihb =>
      have e1 : liftA 0 1 (instantiateA k s r) =
          instantiateA (k + 1) (liftA 0 1 s) (liftA 0 1 r) := by
        rw [liftA_instantiateA_high 1 0 k s (by omega) r,
            show 1 + k = k + 1 from by omega]
      have e2 : liftA 0 1 (liftA j 1 s) = liftA (j + 1) 1 (liftA 0 1 s) := by
        rw [liftA_liftA_permute 1 1 j 0 (by omega) s,
            show 1 + j = j + 1 from by omega]
      simp only [instantiateA, ihA _ _ _ _ h,
        ihb (j+1) (k+1) (liftA 0 1 r) (liftA 0 1 s) (by omega), e1, e2] <;> try rfl
  | pi A _ b _ ihA ihb =>
      have e1 : liftA 0 1 (instantiateA k s r) =
          instantiateA (k + 1) (liftA 0 1 s) (liftA 0 1 r) := by
        rw [liftA_instantiateA_high 1 0 k s (by omega) r,
            show 1 + k = k + 1 from by omega]
      have e2 : liftA 0 1 (liftA j 1 s) = liftA (j + 1) 1 (liftA 0 1 s) := by
        rw [liftA_liftA_permute 1 1 j 0 (by omega) s,
            show 1 + j = j + 1 from by omega]
      simp only [instantiateA, ihA _ _ _ _ h,
        ihb (j+1) (k+1) (liftA 0 1 r) (liftA 0 1 s) (by omega), e1, e2] <;> try rfl
  | letE A v b ihA ihv ihb =>
      have e1 : liftA 0 1 (instantiateA k s r) =
          instantiateA (k + 1) (liftA 0 1 s) (liftA 0 1 r) := by
        rw [liftA_instantiateA_high 1 0 k s (by omega) r,
            show 1 + k = k + 1 from by omega]
      have e2 : liftA 0 1 (liftA j 1 s) = liftA (j + 1) 1 (liftA 0 1 s) := by
        rw [liftA_liftA_permute 1 1 j 0 (by omega) s,
            show 1 + j = j + 1 from by omega]
      simp only [instantiateA, ihA _ _ _ _ h, ihv _ _ _ _ h,
        ihb (j+1) (k+1) (liftA 0 1 r) (liftA 0 1 s) (by omega), e1, e2] <;> try rfl
  | lit t => rfl

/-- the annotation sorts are untouched by every operation: `instantiateLevelsA`
    commutes with `liftA` and `instantiateA` when the replacement is instantiated
    alongside. -/
theorem instantiateLevelsA_liftA (ls : List Level) (c a : Nat) (e : ExprA) :
    instantiateLevelsA ls (liftA c a e) = liftA c a (instantiateLevelsA ls e) := by
  induction e generalizing c with
  | bvar i => simp only [liftA, instantiateLevelsA]; split <;> rfl
  | sort l => rfl
  | const r ms => rfl
  | app f x ihf ihx => simp only [liftA, instantiateLevelsA, ihf, ihx]
  | lam a _ b iha ihb => simp only [liftA, instantiateLevelsA, iha, ihb]
  | pi a _ b _ iha ihb => simp only [liftA, instantiateLevelsA, iha, ihb]
  | letE a v b iha ihv ihb => simp only [liftA, instantiateLevelsA, iha, ihv, ihb]
  | lit t => rfl

#print axioms liftA_zero
#print axioms liftA_liftA_permute
#print axioms liftA_liftA_merge
#print axioms liftA_instantiateA_low
#print axioms liftA_instantiateA_high
#print axioms instantiateA_liftA_cancel
#print axioms instantiateA_liftA_id
#print axioms instantiateA_instantiateA
#print axioms instantiateLevelsA_liftA

end Rcic.Declarative.Ann

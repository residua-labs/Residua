/-
RCIC substitution calculus — the de Bruijn commutation infrastructure for
02's preservation metatheory (DT-003..016, DT-021..023).

INFRASTRUCTURE, not interface mechanization: these are the lift/instantiate
commutation lemmas the knife-2 batch named as its load-bearing bottleneck.
The DT interface theorems remain the batch's delivery (00 §16 M-010).

M-002a: every definition in these statements (lift / instantiate) is the
pinned entry set of RcicDeclarative's carrier guards (rcic-expr-subst rows
call lift and instantiate directly).

Statement forms put the shifting summand on the LEFT of the varying cutoff
(`m + c`, `a + j`) so that binder recursion `x + (c+1) ≡ (x+c)+1` is
DEFINITIONAL and the structural cases close by the IH verbatim.
-/
import rcic.RcicDeclarative

namespace Rcic.Declarative

variable {R : Type}

/-- Leaf normalizer for bvar goals: unfold, split every ite, close each
leaf by rfl / index arithmetic / contradiction. -/
macro "bvar_leaves" : tactic =>
  `(tactic| ((repeat' (first | (simp only [lift, instantiate]) | split)) <;>
             (first | rfl | (exfalso; omega) | (congr 1 <;> omega))))

/-- P0: lifting by zero is the identity. -/
theorem lift_zero (c : Nat) (e : Expr R) : lift c 0 e = e := by
  induction e generalizing c with
  | bvar i => bvar_leaves
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx => simp only [lift, ihf, ihx] <;> try rfl
  | lam a b iha ihb => simp only [lift, iha, ihb] <;> try rfl
  | pi a b iha ihb => simp only [lift, iha, ihb] <;> try rfl
  | letE a v b iha ihv ihb => simp only [lift, iha, ihv, ihb] <;> try rfl
  | lit t => rfl

/-- P1 (permute): a lift at a lower cutoff commutes past one at a higher
cutoff, pushing the higher cutoff up by the lower amount. -/
theorem lift_lift_permute (m n c c' : Nat) (h : c' ≤ c) (e : Expr R) :
    lift c' m (lift c n e) = lift (m + c) n (lift c' m e) := by
  induction e generalizing c c' with
  | bvar i => bvar_leaves
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx => simp only [lift, ihf _ _ h, ihx _ _ h] <;> try rfl
  | lam a b iha ihb =>
      simp only [lift, iha _ _ h, ihb (c+1) (c'+1) (by omega)] <;> try rfl
  | pi a b iha ihb =>
      simp only [lift, iha _ _ h, ihb (c+1) (c'+1) (by omega)] <;> try rfl
  | letE a v b iha ihv ihb =>
      simp only [lift, iha _ _ h, ihv _ _ h, ihb (c+1) (c'+1) (by omega)] <;> try rfl
  | lit t => rfl

/-- P2 (merge): a lift whose cutoff lands inside the gap opened by another
lift merges into a single lift of the summed amount. -/
theorem lift_lift_merge (m n c c' : Nat) (h1 : c ≤ c') (h2 : c' ≤ n + c) (e : Expr R) :
    lift c' m (lift c n e) = lift c (n + m) e := by
  induction e generalizing c c' with
  | bvar i => bvar_leaves
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx => simp only [lift, ihf _ _ h1 h2, ihx _ _ h1 h2] <;> try rfl
  | lam a b iha ihb =>
      simp only [lift, iha _ _ h1 h2, ihb (c+1) (c'+1) (by omega) (by omega)] <;> try rfl
  | pi a b iha ihb =>
      simp only [lift, iha _ _ h1 h2, ihb (c+1) (c'+1) (by omega) (by omega)] <;> try rfl
  | letE a v b iha ihv ihb =>
      simp only [lift, iha _ _ h1 h2, ihv _ _ h1 h2,
        ihb (c+1) (c'+1) (by omega) (by omega)] <;> try rfl
  | lit t => rfl

/-- P3 (lift past an instantiation below its cutoff): for `j ≤ c`. -/
theorem lift_instantiate_low (a c j : Nat) (r : Expr R) (h : j ≤ c) (e : Expr R) :
    lift c a (instantiate j r e) =
      instantiate j (lift c a r) (lift (c + 1) a e) := by
  induction e generalizing c j r with
  | bvar i => bvar_leaves
  | sort l => rfl
  | const r' ls => rfl
  | app f x ihf ihx => simp only [lift, instantiate, ihf _ _ _ h, ihx _ _ _ h] <;> try rfl
  | lam A b ihA ihb =>
      have e2 : lift 0 1 (lift c a r) = lift (c + 1) a (lift 0 1 r) := by
        rw [lift_lift_permute 1 a c 0 (by omega) r,
            show 1 + c = c + 1 from by omega]
      simp only [lift, instantiate, ihA _ _ _ h,
        ihb (c+1) (j+1) (lift 0 1 r) (by omega), e2] <;> try rfl
  | pi A b ihA ihb =>
      have e2 : lift 0 1 (lift c a r) = lift (c + 1) a (lift 0 1 r) := by
        rw [lift_lift_permute 1 a c 0 (by omega) r,
            show 1 + c = c + 1 from by omega]
      simp only [lift, instantiate, ihA _ _ _ h,
        ihb (c+1) (j+1) (lift 0 1 r) (by omega), e2] <;> try rfl
  | letE A v b ihA ihv ihb =>
      have e2 : lift 0 1 (lift c a r) = lift (c + 1) a (lift 0 1 r) := by
        rw [lift_lift_permute 1 a c 0 (by omega) r,
            show 1 + c = c + 1 from by omega]
      simp only [lift, instantiate, ihA _ _ _ h, ihv _ _ _ h,
        ihb (c+1) (j+1) (lift 0 1 r) (by omega), e2] <;> try rfl
  | lit t => rfl

/-- P4 (lift past an instantiation at-or-above its cutoff): for `c ≤ j`,
the instantiation index shifts by the lift amount. -/
theorem lift_instantiate_high (a c j : Nat) (s : Expr R) (h : c ≤ j) (e : Expr R) :
    lift c a (instantiate j s e) =
      instantiate (a + j) (lift c a s) (lift c a e) := by
  induction e generalizing c j s with
  | bvar i => bvar_leaves
  | sort l => rfl
  | const r' ls => rfl
  | app f x ihf ihx => simp only [lift, instantiate, ihf _ _ _ h, ihx _ _ _ h] <;> try rfl
  | lam A b ihA ihb =>
      have e2 : lift 0 1 (lift c a s) = lift (c + 1) a (lift 0 1 s) := by
        rw [lift_lift_permute 1 a c 0 (by omega) s,
            show 1 + c = c + 1 from by omega]
      simp only [lift, instantiate, ihA _ _ _ h,
        ihb (c+1) (j+1) (lift 0 1 s) (by omega), e2] <;> try rfl
  | pi A b ihA ihb =>
      have e2 : lift 0 1 (lift c a s) = lift (c + 1) a (lift 0 1 s) := by
        rw [lift_lift_permute 1 a c 0 (by omega) s,
            show 1 + c = c + 1 from by omega]
      simp only [lift, instantiate, ihA _ _ _ h,
        ihb (c+1) (j+1) (lift 0 1 s) (by omega), e2] <;> try rfl
  | letE A v b ihA ihv ihb =>
      have e2 : lift 0 1 (lift c a s) = lift (c + 1) a (lift 0 1 s) := by
        rw [lift_lift_permute 1 a c 0 (by omega) s,
            show 1 + c = c + 1 from by omega]
      simp only [lift, instantiate, ihA _ _ _ h, ihv _ _ _ h,
        ihb (c+1) (j+1) (lift 0 1 s) (by omega), e2] <;> try rfl
  | lit t => rfl

/-- P5 (cancel): instantiating anywhere inside the gap a lift opened
consumes one unit of the gap; the replacement is never consulted. -/
theorem instantiate_lift_cancel (a c j : Nat) (r : Expr R)
    (h1 : c ≤ j) (h2 : j < a + c) (e : Expr R) :
    instantiate j r (lift c a e) = lift c (a - 1) e := by
  induction e generalizing c j r with
  | bvar i => bvar_leaves
  | sort l => rfl
  | const r' ls => rfl
  | app f x ihf ihx => simp only [lift, instantiate, ihf _ _ _ h1 h2, ihx _ _ _ h1 h2] <;> try rfl
  | lam A b ihA ihb =>
      simp only [lift, instantiate, ihA _ _ _ h1 h2,
        ihb (c+1) (j+1) (lift 0 1 r) (by omega) (by omega)] <;> try rfl
  | pi A b ihA ihb =>
      simp only [lift, instantiate, ihA _ _ _ h1 h2,
        ihb (c+1) (j+1) (lift 0 1 r) (by omega) (by omega)] <;> try rfl
  | letE A v b ihA ihv ihb =>
      simp only [lift, instantiate, ihA _ _ _ h1 h2, ihv _ _ _ h1 h2,
        ihb (c+1) (j+1) (lift 0 1 r) (by omega) (by omega)] <;> try rfl
  | lit t => rfl

/-- P5 at the classic corner: `instantiate j r (lift j 1 e) = e`. -/
theorem instantiate_lift_id (j : Nat) (r : Expr R) (e : Expr R) :
    instantiate j r (lift j 1 e) = e := by
  rw [instantiate_lift_cancel 1 j j r (Nat.le_refl j) (by omega), lift_zero]

/-- P6 (inst-inst commutation — the substitution lemma's engine): for
`j ≤ k`. -/
theorem instantiate_instantiate (j k : Nat) (r s : Expr R) (h : j ≤ k) (e : Expr R) :
    instantiate k s (instantiate j r e) =
      instantiate j (instantiate k s r)
        (instantiate (k + 1) (lift j 1 s) e) := by
  induction e generalizing j k r s with
  | bvar i =>
      by_cases hik : i = k + 1
      · subst hik
        have hjne : ¬ (k + 1 = j) := by omega
        have hj1 : j < k + 1 := by omega
        simp only [instantiate, if_neg hjne, if_pos hj1,
          show k + 1 - 1 = k from by omega, if_pos rfl, if_true, instantiate_lift_id]
      · bvar_leaves
  | sort l => rfl
  | const r' ls => rfl
  | app f x ihf ihx => simp only [instantiate, ihf _ _ _ _ h, ihx _ _ _ _ h] <;> try rfl
  | lam A b ihA ihb =>
      have e1 : lift 0 1 (instantiate k s r) =
          instantiate (k + 1) (lift 0 1 s) (lift 0 1 r) := by
        rw [lift_instantiate_high 1 0 k s (by omega) r,
            show 1 + k = k + 1 from by omega]
      have e2 : lift 0 1 (lift j 1 s) = lift (j + 1) 1 (lift 0 1 s) := by
        rw [lift_lift_permute 1 1 j 0 (by omega) s,
            show 1 + j = j + 1 from by omega]
      simp only [instantiate, ihA _ _ _ _ h,
        ihb (j+1) (k+1) (lift 0 1 r) (lift 0 1 s) (by omega), e1, e2] <;> try rfl
  | pi A b ihA ihb =>
      have e1 : lift 0 1 (instantiate k s r) =
          instantiate (k + 1) (lift 0 1 s) (lift 0 1 r) := by
        rw [lift_instantiate_high 1 0 k s (by omega) r,
            show 1 + k = k + 1 from by omega]
      have e2 : lift 0 1 (lift j 1 s) = lift (j + 1) 1 (lift 0 1 s) := by
        rw [lift_lift_permute 1 1 j 0 (by omega) s,
            show 1 + j = j + 1 from by omega]
      simp only [instantiate, ihA _ _ _ _ h,
        ihb (j+1) (k+1) (lift 0 1 r) (lift 0 1 s) (by omega), e1, e2] <;> try rfl
  | letE A v b ihA ihv ihb =>
      have e1 : lift 0 1 (instantiate k s r) =
          instantiate (k + 1) (lift 0 1 s) (lift 0 1 r) := by
        rw [lift_instantiate_high 1 0 k s (by omega) r,
            show 1 + k = k + 1 from by omega]
      have e2 : lift 0 1 (lift j 1 s) = lift (j + 1) 1 (lift 0 1 s) := by
        rw [lift_lift_permute 1 1 j 0 (by omega) s,
            show 1 + j = j + 1 from by omega]
      simp only [instantiate, ihA _ _ _ _ h, ihv _ _ _ _ h,
        ihb (j+1) (k+1) (lift 0 1 r) (lift 0 1 s) (by omega), e1, e2] <;> try rfl
  | lit t => rfl

end Rcic.Declarative

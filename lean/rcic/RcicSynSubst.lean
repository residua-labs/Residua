import rcic.RcicSynE

/-!
# Syntactic sortRow, build step 2b-0 — de Bruijn algebra on erased terms

`research/rcic/semantic/S2_ERASED_E.md` §4. The `lift`/`inst` commutations that step 2b's
confluence proofs consume, ported from `RcicSubstCalc.lean:30-209` (`Expr`) to `ETm`. `ETm.inst`
has `instantiate`'s clauses verbatim, so each proof is the `Expr` proof without the `letE`/`lit`
cases and with a `star` case. Also here: closed terms are fixed by `lift`/`inst` (the constant
rules' right-hand sides), and both distribute over spines.
-/

namespace Rcic.Syn

open Rcic.Declarative

namespace ETm

/-- leaf normalizer for `bvar` goals: unfold, split every `if`, close by `rfl` or arithmetic. -/
macro "etm_bvar_leaves" : tactic =>
  `(tactic| ((repeat' (first | (simp only [ETm.lift, ETm.inst]) | split)) <;>
             (first | rfl | (exfalso; omega) | (congr 1 <;> omega))))

theorem lift_zero (c : Nat) (e : ETm) : lift c 0 e = e := by
  induction e generalizing c with
  | bvar i => etm_bvar_leaves
  | star => rfl
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx => simp only [lift, ihf, ihx]
  | lam b ihb => simp only [lift, ihb]
  | pi a b iha ihb => simp only [lift, iha, ihb]

theorem lift_lift_permute (m n c c' : Nat) (h : c' ≤ c) (e : ETm) :
    lift c' m (lift c n e) = lift (m + c) n (lift c' m e) := by
  induction e generalizing c c' with
  | bvar i => etm_bvar_leaves
  | star => rfl
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx => simp only [lift, ihf _ _ h, ihx _ _ h]
  | lam b ihb => simp only [lift, ihb (c+1) (c'+1) (by omega)]; rfl
  | pi a b iha ihb => simp only [lift, iha _ _ h, ihb (c+1) (c'+1) (by omega)]; rfl

theorem lift_lift_merge (m n c c' : Nat) (h1 : c ≤ c') (h2 : c' ≤ n + c) (e : ETm) :
    lift c' m (lift c n e) = lift c (n + m) e := by
  induction e generalizing c c' with
  | bvar i => etm_bvar_leaves
  | star => rfl
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx => simp only [lift, ihf _ _ h1 h2, ihx _ _ h1 h2]
  | lam b ihb => simp only [lift, ihb (c+1) (c'+1) (by omega) (by omega)]
  | pi a b iha ihb => simp only [lift, iha _ _ h1 h2, ihb (c+1) (c'+1) (by omega) (by omega)]

theorem lift_lift_one (c : Nat) (e : ETm) : lift 0 1 (lift c 1 e) = lift (c + 1) 1 (lift 0 1 e) := by
  rw [lift_lift_permute 1 1 c 0 (Nat.zero_le c) e, Nat.add_comm 1 c]

theorem lift_inst_low (a c j : Nat) (r : ETm) (h : j ≤ c) (e : ETm) :
    lift c a (inst j r e) = inst j (lift c a r) (lift (c + 1) a e) := by
  induction e generalizing c j r with
  | bvar i => etm_bvar_leaves
  | star => rfl
  | sort l => rfl
  | const r' ls => rfl
  | app f x ihf ihx => simp only [lift, inst, ihf _ _ _ h, ihx _ _ _ h]
  | lam b ihb =>
      have e2 : lift 0 1 (lift c a r) = lift (c + 1) a (lift 0 1 r) := by
        rw [lift_lift_permute 1 a c 0 (by omega) r, show 1 + c = c + 1 from by omega]
      simp only [lift, inst, ihb (c+1) (j+1) (lift 0 1 r) (by omega), e2]
  | pi A b ihA ihb =>
      have e2 : lift 0 1 (lift c a r) = lift (c + 1) a (lift 0 1 r) := by
        rw [lift_lift_permute 1 a c 0 (by omega) r, show 1 + c = c + 1 from by omega]
      simp only [lift, inst, ihA _ _ _ h, ihb (c+1) (j+1) (lift 0 1 r) (by omega), e2]

theorem lift_inst_high (a c j : Nat) (s : ETm) (h : c ≤ j) (e : ETm) :
    lift c a (inst j s e) = inst (a + j) (lift c a s) (lift c a e) := by
  induction e generalizing c j s with
  | bvar i => etm_bvar_leaves
  | star => rfl
  | sort l => rfl
  | const r' ls => rfl
  | app f x ihf ihx => simp only [lift, inst, ihf _ _ _ h, ihx _ _ _ h]
  | lam b ihb =>
      have e2 : lift 0 1 (lift c a s) = lift (c + 1) a (lift 0 1 s) := by
        rw [lift_lift_permute 1 a c 0 (by omega) s, show 1 + c = c + 1 from by omega]
      simp only [lift, inst, ihb (c+1) (j+1) (lift 0 1 s) (by omega), e2]; rfl
  | pi A b ihA ihb =>
      have e2 : lift 0 1 (lift c a s) = lift (c + 1) a (lift 0 1 s) := by
        rw [lift_lift_permute 1 a c 0 (by omega) s, show 1 + c = c + 1 from by omega]
      simp only [lift, inst, ihA _ _ _ h, ihb (c+1) (j+1) (lift 0 1 s) (by omega), e2]; rfl

theorem inst_lift_cancel (a c j : Nat) (r : ETm) (h1 : c ≤ j) (h2 : j < a + c) (e : ETm) :
    inst j r (lift c a e) = lift c (a - 1) e := by
  induction e generalizing c j r with
  | bvar i => etm_bvar_leaves
  | star => rfl
  | sort l => rfl
  | const r' ls => rfl
  | app f x ihf ihx => simp only [lift, inst, ihf _ _ _ h1 h2, ihx _ _ _ h1 h2]
  | lam b ihb => simp only [lift, inst, ihb (c+1) (j+1) (lift 0 1 r) (by omega) (by omega)]
  | pi A b ihA ihb =>
      simp only [lift, inst, ihA _ _ _ h1 h2, ihb (c+1) (j+1) (lift 0 1 r) (by omega) (by omega)]

theorem inst_lift_id (j : Nat) (r : ETm) (e : ETm) : inst j r (lift j 1 e) = e := by
  rw [inst_lift_cancel 1 j j r (Nat.le_refl j) (by omega), lift_zero]

theorem inst_inst (j k : Nat) (r s : ETm) (h : j ≤ k) (e : ETm) :
    inst k s (inst j r e) = inst j (inst k s r) (inst (k + 1) (lift j 1 s) e) := by
  induction e generalizing j k r s with
  | bvar i =>
      cases Nat.decEq i (k + 1) with
      | isTrue hik =>
          subst hik
          have hjne : ¬ (k + 1 = j) := by omega
          have hj1 : j < k + 1 := by omega
          simp only [inst, if_neg hjne, if_pos hj1, show k + 1 - 1 = k from by omega, if_pos rfl,
            if_true, inst_lift_id]
      | isFalse hik => etm_bvar_leaves
  | star => rfl
  | sort l => rfl
  | const r' ls => rfl
  | app f x ihf ihx => simp only [inst, ihf _ _ _ _ h, ihx _ _ _ _ h]
  | lam b ihb =>
      have e1 : lift 0 1 (inst k s r) = inst (k + 1) (lift 0 1 s) (lift 0 1 r) := by
        rw [lift_inst_high 1 0 k s (by omega) r, show 1 + k = k + 1 from by omega]
      have e2 : lift 0 1 (lift j 1 s) = lift (j + 1) 1 (lift 0 1 s) := by
        rw [lift_lift_permute 1 1 j 0 (by omega) s, show 1 + j = j + 1 from by omega]
      simp only [inst, ihb (j+1) (k+1) (lift 0 1 r) (lift 0 1 s) (by omega), e1, e2]
  | pi A b ihA ihb =>
      have e1 : lift 0 1 (inst k s r) = inst (k + 1) (lift 0 1 s) (lift 0 1 r) := by
        rw [lift_inst_high 1 0 k s (by omega) r, show 1 + k = k + 1 from by omega]
      have e2 : lift 0 1 (lift j 1 s) = lift (j + 1) 1 (lift 0 1 s) := by
        rw [lift_lift_permute 1 1 j 0 (by omega) s, show 1 + j = j + 1 from by omega]
      simp only [inst, ihA _ _ _ _ h, ihb (j+1) (k+1) (lift 0 1 r) (lift 0 1 s) (by omega), e1, e2]

/-! ## closed terms -/

theorem ClosedAt.mono {k k' : Nat} (h : k ≤ k') {e : ETm} (hc : ClosedAt k e) : ClosedAt k' e := by
  induction e generalizing k k' with
  | bvar i => exact Nat.lt_of_lt_of_le hc h
  | star => trivial
  | sort l => trivial
  | const r ls => trivial
  | app f x ihf ihx => exact ⟨ihf h hc.1, ihx h hc.2⟩
  | lam b ihb => exact ihb (Nat.succ_le_succ h) hc
  | pi a b iha ihb => exact ⟨iha h hc.1, ihb (Nat.succ_le_succ h) hc.2⟩

theorem lift_closed {k : Nat} {e : ETm} (hc : ClosedAt k e) {c : Nat} (h : k ≤ c) (n : Nat) :
    lift c n e = e := by
  induction e generalizing k c with
  | bvar i =>
      have hi : ¬ c ≤ i := fun h' => Nat.lt_irrefl i (Nat.lt_of_lt_of_le hc (Nat.le_trans h h'))
      simp only [lift, if_neg hi]
  | star => rfl
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx => simp only [lift, ihf hc.1 h, ihx hc.2 h]
  | lam b ihb => simp only [lift, ihb hc (Nat.succ_le_succ h)]
  | pi a b iha ihb => simp only [lift, iha hc.1 h, ihb hc.2 (Nat.succ_le_succ h)]

theorem inst_closed {k : Nat} {e : ETm} (hc : ClosedAt k e) {j : Nat} (h : k ≤ j) (r : ETm) :
    inst j r e = e := by
  induction e generalizing k j r with
  | bvar i =>
      have hi : ¬ i = j := fun h' => Nat.lt_irrefl i (Nat.lt_of_lt_of_le hc (h' ▸ h))
      have hi' : ¬ j < i := fun h' => Nat.lt_asymm h' (Nat.lt_of_lt_of_le hc h)
      simp only [inst, if_neg hi, if_neg hi']
  | star => rfl
  | sort l => rfl
  | const r ls => rfl
  | app f x ihf ihx => simp only [inst, ihf hc.1 h, ihx hc.2 h]
  | lam b ihb => simp only [inst, ihb hc (Nat.succ_le_succ h)]
  | pi a b iha ihb => simp only [inst, iha hc.1 h, ihb hc.2 (Nat.succ_le_succ h)]

theorem lift_closed0 {e : ETm} (hc : ClosedAt 0 e) (c n : Nat) : lift c n e = e :=
  lift_closed hc (Nat.zero_le c) n

theorem inst_closed0 {e : ETm} (hc : ClosedAt 0 e) (j : Nat) (r : ETm) : inst j r e = e :=
  inst_closed hc (Nat.zero_le j) r

/-! ## spines -/

theorem lift_appN (c n : Nat) (f : ETm) (xs : List ETm) :
    lift c n (appN f xs) = appN (lift c n f) (xs.map (lift c n)) := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [appN, ih, lift, List.map_cons]

theorem inst_appN (j : Nat) (r : ETm) (f : ETm) (xs : List ETm) :
    inst j r (appN f xs) = appN (inst j r f) (xs.map (inst j r)) := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [appN, ih, inst, List.map_cons]

theorem instLevels_appN (ls : List Level) (f : ETm) (xs : List ETm) :
    instLevels ls (appN f xs) = appN (instLevels ls f) (xs.map (instLevels ls)) := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [appN, ih, instLevels, List.map_cons]

end ETm

end Rcic.Syn

#print axioms Rcic.Syn.ETm.lift_zero
#print axioms Rcic.Syn.ETm.lift_lift_permute
#print axioms Rcic.Syn.ETm.lift_lift_merge
#print axioms Rcic.Syn.ETm.lift_lift_one
#print axioms Rcic.Syn.ETm.lift_inst_low
#print axioms Rcic.Syn.ETm.lift_inst_high
#print axioms Rcic.Syn.ETm.inst_lift_cancel
#print axioms Rcic.Syn.ETm.inst_lift_id
#print axioms Rcic.Syn.ETm.inst_inst
#print axioms Rcic.Syn.ETm.ClosedAt.mono
#print axioms Rcic.Syn.ETm.lift_closed
#print axioms Rcic.Syn.ETm.inst_closed
#print axioms Rcic.Syn.ETm.lift_closed0
#print axioms Rcic.Syn.ETm.inst_closed0
#print axioms Rcic.Syn.ETm.lift_appN
#print axioms Rcic.Syn.ETm.inst_appN
#print axioms Rcic.Syn.ETm.instLevels_appN

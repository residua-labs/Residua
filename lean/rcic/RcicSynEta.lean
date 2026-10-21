import rcic.RcicSynSubst

/-!
# Syntactic sortRow, build step 2b-1 — CR(η)

`research/rcic/semantic/S2_ERASED_E.md` §4.2. η on erased terms has the diamond property up to
equality (`etaStep_diamond`): two η steps from one term coincide or close with one step each.
So CR(`EtaStep`) needs no termination argument (`confluent_etaStep`).

The only non-trivial overlap is a step inside the `F` of a redex `λ. F↑ 0`. It is closed by:
* η stable under `lift` (`etaStep_lift`);
* η reflected by `lift` (`etaStep_lift_inv`): a step out of a lifted term is a lifted step.
The second rests on `lift_eq_lift_inv`: if `X` lifted at a cutoff above `d` equals `H` lifted by
one at `d`, then `X` is itself lifted at `d`.
-/

namespace Rcic.Syn

open Rcic.Declarative

namespace ETm

/-! ## inversion of `lift` -/

theorem lift_eq_app_inv {c k : Nat} {F f a : ETm} (h : lift c k F = .app f a) :
    ∃ F₁ F₂, F = .app F₁ F₂ ∧ lift c k F₁ = f ∧ lift c k F₂ = a := by
  cases F with
  | bvar i => simp only [lift] at h; split at h <;> cases h
  | app F₁ F₂ =>
      simp only [lift] at h
      cases h
      exact ⟨F₁, F₂, rfl, rfl, rfl⟩
  | star => cases h
  | sort _ => cases h
  | const _ _ => cases h
  | lam _ => cases h
  | pi _ _ => cases h

theorem lift_eq_lam_inv {c k : Nat} {F b : ETm} (h : lift c k F = .lam b) :
    ∃ B, F = .lam B ∧ lift (c + 1) k B = b := by
  cases F with
  | bvar i => simp only [lift] at h; split at h <;> cases h
  | lam B =>
      simp only [lift] at h
      cases h
      exact ⟨B, rfl, rfl⟩
  | star => cases h
  | sort _ => cases h
  | const _ _ => cases h
  | app _ _ => cases h
  | pi _ _ => cases h

theorem lift_eq_pi_inv {c k : Nat} {F a b : ETm} (h : lift c k F = .pi a b) :
    ∃ A B, F = .pi A B ∧ lift c k A = a ∧ lift (c + 1) k B = b := by
  cases F with
  | bvar i => simp only [lift] at h; split at h <;> cases h
  | pi A B =>
      simp only [lift] at h
      cases h
      exact ⟨A, B, rfl, rfl, rfl⟩
  | star => cases h
  | sort _ => cases h
  | const _ _ => cases h
  | app _ _ => cases h
  | lam _ => cases h

theorem lift_succ_eq_bvar_zero {c k : Nat} {F : ETm} (h : lift (c + 1) k F = .bvar 0) :
    F = .bvar 0 := by
  cases F with
  | bvar i =>
      simp only [lift] at h
      split at h
      · injection h with h'; exfalso; omega
      · injection h with h'; rw [h']
  | star => cases h
  | sort _ => cases h
  | const _ _ => cases h
  | app _ _ => simp only [lift] at h; cases h
  | lam _ => simp only [lift] at h; cases h
  | pi _ _ => simp only [lift] at h; cases h

theorem lift_one_eq_bvar {d m : Nat} {H : ETm} (h : lift d 1 H = .bvar m) :
    ∃ n, H = .bvar n ∧ m = (if d ≤ n then n + 1 else n) := by
  cases H with
  | bvar n =>
      refine ⟨n, rfl, ?_⟩
      simp only [lift] at h
      split at h
      · rename_i hn; injection h with h'; rw [if_pos hn, h']
      · rename_i hn; injection h with h'; rw [if_neg hn, h']
  | star => cases h
  | sort _ => cases h
  | const _ _ => cases h
  | app _ _ => simp only [lift] at h; cases h
  | lam _ => simp only [lift] at h; cases h
  | pi _ _ => simp only [lift] at h; cases h

/-- if `X` lifted at a cutoff above `d` equals `H` lifted by one at `d`, then `X` is itself a lift at
    `d`, and `H` is that term lifted at the shifted cutoff. -/
theorem lift_eq_lift_inv (c k : Nat) : (X : ETm) → (d : Nat) → {H : ETm} →
    lift (c + d + 1) k X = lift d 1 H → ∃ H', X = lift d 1 H' ∧ H = lift (c + d) k H'
  | .bvar i, d, H, h => by
      have hX : lift (c + d + 1) k (.bvar i) =
          .bvar (if c + d + 1 ≤ i then i + k else i) := by
        simp only [lift]; split <;> rfl
      rw [hX] at h
      obtain ⟨n, rfl, hm⟩ := lift_one_eq_bvar h.symm
      cases Nat.decLe (c + d + 1) i with
      | isTrue hi =>
          rw [if_pos hi] at hm
          cases Nat.decLe d n with
          | isTrue hn =>
              rw [if_pos hn] at hm
              refine ⟨.bvar (i - 1), ?_, ?_⟩
              · simp only [lift, if_pos (show d ≤ i - 1 by omega)]
                exact congrArg ETm.bvar (by omega)
              · simp only [lift, if_pos (show c + d ≤ i - 1 by omega)]
                exact congrArg ETm.bvar (by omega)
          | isFalse hn =>
              rw [if_neg hn] at hm
              exact absurd hm (by omega)
      | isFalse hi =>
          rw [if_neg hi] at hm
          cases Nat.decLe d n with
          | isTrue hn =>
              rw [if_pos hn] at hm
              refine ⟨.bvar n, ?_, ?_⟩
              · simp only [lift, if_pos hn]; exact congrArg ETm.bvar (by omega)
              · simp only [lift, if_neg (show ¬ c + d ≤ n by omega)]
          | isFalse hn =>
              rw [if_neg hn] at hm
              refine ⟨.bvar n, ?_, ?_⟩
              · simp only [lift, if_neg hn]; exact congrArg ETm.bvar (by omega)
              · simp only [lift, if_neg (show ¬ c + d ≤ n by omega)]
  | .star, d, H, h => by
      cases H with
      | star => exact ⟨.star, rfl, rfl⟩
      | bvar n => simp only [lift] at h; split at h <;> cases h
      | sort _ => cases h
      | const _ _ => cases h
      | app _ _ => cases h
      | lam _ => cases h
      | pi _ _ => cases h
  | .sort l, d, H, h => by
      cases H with
      | sort l' => cases h; exact ⟨.sort l, rfl, rfl⟩
      | bvar n => simp only [lift] at h; split at h <;> cases h
      | star => cases h
      | const _ _ => cases h
      | app _ _ => cases h
      | lam _ => cases h
      | pi _ _ => cases h
  | .const r ls, d, H, h => by
      cases H with
      | const r' ls' => cases h; exact ⟨.const r ls, rfl, rfl⟩
      | bvar n => simp only [lift] at h; split at h <;> cases h
      | star => cases h
      | sort _ => cases h
      | app _ _ => cases h
      | lam _ => cases h
      | pi _ _ => cases h
  | .app f a, d, H, h => by
      obtain ⟨H₁, H₂, rfl, h₁, h₂⟩ := lift_eq_app_inv h.symm
      obtain ⟨F₁, rfl, rfl⟩ := lift_eq_lift_inv c k f d h₁.symm
      obtain ⟨F₂, rfl, rfl⟩ := lift_eq_lift_inv c k a d h₂.symm
      exact ⟨.app F₁ F₂, rfl, rfl⟩
  | .lam b, d, H, h => by
      obtain ⟨B, rfl, hB⟩ := lift_eq_lam_inv h.symm
      obtain ⟨B', rfl, rfl⟩ := lift_eq_lift_inv c k b (d + 1) hB.symm
      exact ⟨.lam B', rfl, rfl⟩
  | .pi a b, d, H, h => by
      obtain ⟨A, B, rfl, hA, hB⟩ := lift_eq_pi_inv h.symm
      obtain ⟨A', rfl, rfl⟩ := lift_eq_lift_inv c k a d hA.symm
      obtain ⟨B', rfl, rfl⟩ := lift_eq_lift_inv c k b (d + 1) hB.symm
      exact ⟨.pi A' B', rfl, rfl⟩

theorem lift_inj : {k c : Nat} → {x y : ETm} → lift c k x = lift c k y → x = y
  | 0, c, x, y, h => by rwa [lift_zero, lift_zero] at h
  | k + 1, c, x, y, h => by
      rw [← lift_lift_merge 1 k c c (Nat.le_refl c) (Nat.le_add_left c k),
        ← lift_lift_merge 1 k c c (Nat.le_refl c) (Nat.le_add_left c k)] at h
      have h1 := congrArg (inst c .star) h
      rw [inst_lift_id, inst_lift_id] at h1
      exact lift_inj h1

end ETm

/-! ## η and `lift` -/

theorem etaStep_lift {a b : ETm} (h : EtaStep a b) (c k : Nat) :
    EtaStep (a.lift c k) (b.lift c k) := by
  induction h generalizing c with
  | eta F =>
      have e : ETm.lift (c + 1) k (F.lift 0 1) = (F.lift c k).lift 0 1 := by
        rw [ETm.lift_lift_permute 1 k c 0 (Nat.zero_le c) F, Nat.add_comm 1 c]
      have e0 : ETm.lift (c + 1) k (.bvar 0) = .bvar 0 := by
        simp only [ETm.lift, if_neg (show ¬ c + 1 ≤ 0 by omega)]
      simp only [ETm.lift] at e0 ⊢
      rw [e, e0]
      exact .eta _
  | appL a _ ih => exact .appL _ (ih c)
  | appR f _ ih => exact .appR _ (ih c)
  | lam _ ih => exact .lam (ih (c + 1))
  | piL b _ ih => exact .piL _ (ih c)
  | piR a _ ih => exact .piR _ (ih (c + 1))

theorem etaStep_lift_inv {c k : Nat} {F G : ETm} (h : EtaStep (F.lift c k) G) :
    ∃ G', G = G'.lift c k ∧ EtaStep F G' := by
  generalize hT : F.lift c k = T at h
  induction h generalizing F c with
  | eta H =>
      obtain ⟨B, rfl, hB⟩ := ETm.lift_eq_lam_inv hT
      obtain ⟨B₁, B₂, rfl, h₁, h₂⟩ := ETm.lift_eq_app_inv hB
      have hz := ETm.lift_succ_eq_bvar_zero h₂
      subst hz
      obtain ⟨H', rfl, rfl⟩ := ETm.lift_eq_lift_inv c k B₁ 0 h₁
      exact ⟨H', rfl, .eta H'⟩
  | appL a _ ih =>
      obtain ⟨F₁, F₂, rfl, h₁, rfl⟩ := ETm.lift_eq_app_inv hT
      obtain ⟨G', rfl, hG⟩ := ih h₁
      exact ⟨.app G' F₂, rfl, .appL _ hG⟩
  | appR f _ ih =>
      obtain ⟨F₁, F₂, rfl, rfl, h₂⟩ := ETm.lift_eq_app_inv hT
      obtain ⟨G', rfl, hG⟩ := ih h₂
      exact ⟨.app F₁ G', rfl, .appR _ hG⟩
  | lam _ ih =>
      obtain ⟨B, rfl, hB⟩ := ETm.lift_eq_lam_inv hT
      obtain ⟨G', rfl, hG⟩ := ih hB
      exact ⟨.lam G', rfl, .lam hG⟩
  | piL b _ ih =>
      obtain ⟨A, B, rfl, hA, rfl⟩ := ETm.lift_eq_pi_inv hT
      obtain ⟨G', rfl, hG⟩ := ih hA
      exact ⟨.pi G' B, rfl, .piL _ hG⟩
  | piR a _ ih =>
      obtain ⟨A, B, rfl, rfl, hB⟩ := ETm.lift_eq_pi_inv hT
      obtain ⟨G', rfl, hG⟩ := ih hB
      exact ⟨.pi A G', rfl, .piR _ hG⟩

theorem etaStep_bvar_normal (i : Nat) (t : ETm) : ¬ EtaStep (.bvar i) t := by
  intro h
  generalize hs : ETm.bvar i = s at h
  cases h <;> cases hs

/-! ## the diamond -/

/-- the overlap at an η redex: a step inside the redex body, against the contraction. -/
theorem eta_root_overlap {F c : ETm}
    (h : EtaStep (.app (F.lift 0 1) (.bvar 0)) c) : ∃ F', c = .app (F'.lift 0 1) (.bvar 0) ∧ EtaStep F F' := by
  generalize hs : ETm.app (F.lift 0 1) (.bvar 0) = s at h
  cases h with
  | eta => cases hs
  | appL _ hf =>
      cases hs
      obtain ⟨F', rfl, hF⟩ := etaStep_lift_inv hf
      exact ⟨F', rfl, hF⟩
  | appR _ hx =>
      cases hs
      exact absurd hx (etaStep_bvar_normal 0 _)
  | lam => cases hs
  | piL => cases hs
  | piR => cases hs

/-- η has the diamond property up to equality. -/
theorem etaStep_diamond {a b c : ETm} (h1 : EtaStep a b) (h2 : EtaStep a c) :
    b = c ∨ ∃ d, EtaStep b d ∧ EtaStep c d := by
  induction h1 generalizing c with
  | eta F =>
      generalize hs : ETm.lam (.app (F.lift 0 1) (.bvar 0)) = s at h2
      cases h2 with
      | eta F₂ =>
          injection hs with hs1
          injection hs1 with hs2 _
          exact .inl (ETm.lift_inj hs2)
      | lam hb =>
          cases hs
          obtain ⟨F', rfl, hF⟩ := eta_root_overlap hb
          exact .inr ⟨F', hF, .eta F'⟩
      | appL => cases hs
      | appR => cases hs
      | piL => cases hs
      | piR => cases hs
  | appL a h ih =>
      generalize hs : ETm.app _ a = s at h2
      cases h2 with
      | appL _ h' =>
          cases hs
          rcases ih h' with rfl | ⟨d, hd1, hd2⟩
          · exact .inl rfl
          · exact .inr ⟨_, .appL _ hd1, .appL _ hd2⟩
      | appR _ h' =>
          cases hs
          exact .inr ⟨_, .appR _ h', .appL _ h⟩
      | eta => cases hs
      | lam => cases hs
      | piL => cases hs
      | piR => cases hs
  | appR f h ih =>
      generalize hs : ETm.app f _ = s at h2
      cases h2 with
      | appL _ h' =>
          cases hs
          exact .inr ⟨_, .appL _ h', .appR _ h⟩
      | appR _ h' =>
          cases hs
          rcases ih h' with rfl | ⟨d, hd1, hd2⟩
          · exact .inl rfl
          · exact .inr ⟨_, .appR _ hd1, .appR _ hd2⟩
      | eta => cases hs
      | lam => cases hs
      | piL => cases hs
      | piR => cases hs
  | @lam b b' h ih =>
      generalize hs : ETm.lam b = s at h2
      cases h2 with
      | eta F =>
          cases hs
          obtain ⟨F', rfl, hF⟩ := eta_root_overlap h
          exact .inr ⟨F', .eta F', hF⟩
      | lam h' =>
          cases hs
          rcases ih h' with rfl | ⟨d, hd1, hd2⟩
          · exact .inl rfl
          · exact .inr ⟨_, .lam hd1, .lam hd2⟩
      | appL => cases hs
      | appR => cases hs
      | piL => cases hs
      | piR => cases hs
  | piL b h ih =>
      generalize hs : ETm.pi _ b = s at h2
      cases h2 with
      | piL _ h' =>
          cases hs
          rcases ih h' with rfl | ⟨d, hd1, hd2⟩
          · exact .inl rfl
          · exact .inr ⟨_, .piL _ hd1, .piL _ hd2⟩
      | piR _ h' =>
          cases hs
          exact .inr ⟨_, .piR _ h', .piL _ h⟩
      | eta => cases hs
      | appL => cases hs
      | appR => cases hs
      | lam => cases hs
  | piR a h ih =>
      generalize hs : ETm.pi a _ = s at h2
      cases h2 with
      | piL _ h' =>
          cases hs
          exact .inr ⟨_, .piL _ h', .piR _ h⟩
      | piR _ h' =>
          cases hs
          rcases ih h' with rfl | ⟨d, hd1, hd2⟩
          · exact .inl rfl
          · exact .inr ⟨_, .piR _ hd1, .piR _ hd2⟩
      | eta => cases hs
      | appL => cases hs
      | appR => cases hs
      | lam => cases hs

/-- η or equality. -/
def EtaRefl (a b : ETm) : Prop := a = b ∨ EtaStep a b

theorem etaRefl_diamond {a b c : ETm} (hb : EtaRefl a b) (hc : EtaRefl a c) :
    ∃ d, EtaRefl b d ∧ EtaRefl c d := by
  rcases hb with rfl | hb
  · exact ⟨c, hc, .inl rfl⟩
  rcases hc with rfl | hc
  · exact ⟨b, .inl rfl, .inr hb⟩
  rcases etaStep_diamond hb hc with rfl | ⟨d, h1, h2⟩
  · exact ⟨b, .inl rfl, .inl rfl⟩
  · exact ⟨d, .inr h1, .inr h2⟩

/-- CR(η), step 2b's second obligation. -/
theorem confluent_etaStep : Confluent EtaStep := by
  have up : ∀ {a b : ETm}, RStar EtaStep a b → RStar EtaRefl a b :=
    fun h => rstar_mono (fun h' => Or.inr h') h
  have down : ∀ {a b : ETm}, RStar EtaRefl a b → RStar EtaStep a b :=
    fun h => rstar_flatten (rstar_mono (fun h' => rstar_of_refl h') h)
  intro a b c hb hc
  obtain ⟨d, h1, h2⟩ := confluent_of_diamond etaRefl_diamond (up hb) (up hc)
  exact ⟨d, down h1, down h2⟩

end Rcic.Syn

#print axioms Rcic.Syn.ETm.lift_eq_app_inv
#print axioms Rcic.Syn.ETm.lift_eq_lam_inv
#print axioms Rcic.Syn.ETm.lift_eq_pi_inv
#print axioms Rcic.Syn.ETm.lift_succ_eq_bvar_zero
#print axioms Rcic.Syn.ETm.lift_one_eq_bvar
#print axioms Rcic.Syn.ETm.lift_eq_lift_inv
#print axioms Rcic.Syn.ETm.lift_inj
#print axioms Rcic.Syn.etaStep_lift
#print axioms Rcic.Syn.etaStep_lift_inv
#print axioms Rcic.Syn.etaStep_bvar_normal
#print axioms Rcic.Syn.eta_root_overlap
#print axioms Rcic.Syn.etaStep_diamond
#print axioms Rcic.Syn.etaRefl_diamond
#print axioms Rcic.Syn.confluent_etaStep

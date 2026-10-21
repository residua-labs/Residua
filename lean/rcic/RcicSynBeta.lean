import rcic.RcicSynCommute

/-!
# Syntactic sortRow, build step 2b-3 — CR(β) by parallel reduction

`research/rcic/semantic/S2_ERASED_E.md` §4.1. Obligation 1, CR(`RStep tbl`), is split once more
by Hindley–Rosen into CR(β), CR(constant rules) and their strong commutation. This module is
CR(β): Tait–Martin-Löf parallel reduction `PB` on erased terms, its substitution lemma, and its
diamond (`pb_diamond`), hence `confluent_betaStep`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- one β step, closed under congruence. -/
inductive BetaStep : ETm → ETm → Prop
  | beta (M N : ETm) : BetaStep (.app (.lam M) N) (ETm.inst 0 N M)
  | appL {f f' : ETm} (a : ETm) (h : BetaStep f f') : BetaStep (.app f a) (.app f' a)
  | appR (f : ETm) {a a' : ETm} (h : BetaStep a a') : BetaStep (.app f a) (.app f a')
  | lam {b b' : ETm} (h : BetaStep b b') : BetaStep (.lam b) (.lam b')
  | piL {a a' : ETm} (b : ETm) (h : BetaStep a a') : BetaStep (.pi a b) (.pi a' b)
  | piR (a : ETm) {b b' : ETm} (h : BetaStep b b') : BetaStep (.pi a b) (.pi a b')

/-- parallel β reduction. -/
inductive PB : ETm → ETm → Prop
  | bvar (i : Nat) : PB (.bvar i) (.bvar i)
  | star : PB .star .star
  | sort (l : Level) : PB (.sort l) (.sort l)
  | const (r : Nat) (ls : List Level) : PB (.const r ls) (.const r ls)
  | app {f f' a a' : ETm} (hf : PB f f') (ha : PB a a') : PB (.app f a) (.app f' a')
  | lam {b b' : ETm} (hb : PB b b') : PB (.lam b) (.lam b')
  | pi {a a' b b' : ETm} (ha : PB a a') (hb : PB b b') : PB (.pi a b) (.pi a' b')
  | beta {M M' N N' : ETm} (hM : PB M M') (hN : PB N N') :
      PB (.app (.lam M) N) (ETm.inst 0 N' M')

theorem pb_refl : (t : ETm) → PB t t
  | .bvar i => .bvar i
  | .star => .star
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app f a => .app (pb_refl f) (pb_refl a)
  | .lam b => .lam (pb_refl b)
  | .pi a b => .pi (pb_refl a) (pb_refl b)

theorem pb_of_betaStep {a b : ETm} (h : BetaStep a b) : PB a b := by
  induction h with
  | beta M N => exact .beta (pb_refl M) (pb_refl N)
  | appL a _ ih => exact .app ih (pb_refl a)
  | appR f _ ih => exact .app (pb_refl f) ih
  | lam _ ih => exact .lam ih
  | piL b _ ih => exact .pi ih (pb_refl b)
  | piR a _ ih => exact .pi (pb_refl a) ih

theorem betaStar_app {f f' a a' : ETm} (hf : RStar BetaStep f f') (ha : RStar BetaStep a a') :
    RStar BetaStep (.app f a) (.app f' a') :=
  (rstar_congr (g := fun t => ETm.app t a) (fun h => .appL _ h) hf).trans'
    (rstar_congr (g := fun t => ETm.app f' t) (fun h => .appR _ h) ha)

theorem betaStar_pi {a a' b b' : ETm} (ha : RStar BetaStep a a') (hb : RStar BetaStep b b') :
    RStar BetaStep (.pi a b) (.pi a' b') :=
  (rstar_congr (g := fun t => ETm.pi t b) (fun h => .piL _ h) ha).trans'
    (rstar_congr (g := fun t => ETm.pi a' t) (fun h => .piR _ h) hb)

theorem betaStar_lam {b b' : ETm} (hb : RStar BetaStep b b') :
    RStar BetaStep (.lam b) (.lam b') :=
  rstar_congr (g := ETm.lam) (fun h => .lam h) hb

theorem betaStar_of_pb {a b : ETm} (h : PB a b) : RStar BetaStep a b := by
  induction h with
  | bvar => exact .refl _
  | star => exact .refl _
  | sort => exact .refl _
  | const => exact .refl _
  | app _ _ ihf iha => exact betaStar_app ihf iha
  | lam _ ih => exact betaStar_lam ih
  | pi _ _ iha ihb => exact betaStar_pi iha ihb
  | beta _ _ ihM ihN =>
      exact (betaStar_app (betaStar_lam ihM) ihN).trans' (.single (.beta _ _))

theorem pb_lift {a b : ETm} (h : PB a b) (c k : Nat) : PB (a.lift c k) (b.lift c k) := by
  induction h generalizing c with
  | bvar i => exact pb_refl _
  | star => exact .star
  | sort l => exact .sort l
  | const r ls => exact .const r ls
  | app _ _ ihf iha => exact .app (ihf c) (iha c)
  | lam _ ih => exact .lam (ih (c + 1))
  | pi _ _ iha ihb => exact .pi (iha c) (ihb (c + 1))
  | @beta M M' N N' _ _ ihM ihN =>
      rw [ETm.lift_inst_low k c 0 N' (Nat.zero_le c) M']
      exact .beta (ihM (c + 1)) (ihN c)

/-- the substitution lemma for `PB`. -/
theorem pb_inst {M M' : ETm} (h : PB M M') :
    (j : Nat) → {N N' : ETm} → PB N N' → PB (ETm.inst j N M) (ETm.inst j N' M') := by
  induction h with
  | bvar i =>
      intro j N N' hN
      simp only [ETm.inst]
      split
      · exact hN
      · exact pb_refl _
  | star => intro _ _ _ _; exact .star
  | sort l => intro _ _ _ _; exact .sort l
  | const r ls => intro _ _ _ _; exact .const r ls
  | app _ _ ihf iha => intro j N N' hN; exact .app (ihf j hN) (iha j hN)
  | lam _ ih => intro j N N' hN; exact .lam (ih (j + 1) (pb_lift hN 0 1))
  | pi _ _ iha ihb => intro j N N' hN; exact .pi (iha j hN) (ihb (j + 1) (pb_lift hN 0 1))
  | @beta M M' A A' _ _ ihM ihA =>
      intro j N N' hN
      rw [ETm.inst_inst 0 j A' N' (Nat.zero_le j) M']
      exact .beta (ihM (j + 1) (pb_lift hN 0 1)) (ihA j hN)

theorem pb_lam_inv {M X : ETm} (h : PB (.lam M) X) : ∃ M', X = .lam M' ∧ PB M M' := by
  generalize hs : ETm.lam M = s at h
  cases h with
  | lam hb => cases hs; exact ⟨_, rfl, hb⟩
  | bvar => cases hs
  | star => cases hs
  | sort => cases hs
  | const => cases hs
  | app => cases hs
  | pi => cases hs
  | beta => cases hs

/-- the diamond property of `PB` (Tait–Martin-Löf). -/
theorem pb_diamond {a b c : ETm} (h1 : PB a b) (h2 : PB a c) : ∃ d, PB b d ∧ PB c d := by
  induction h1 generalizing c with
  | bvar i => exact ⟨c, h2, pb_refl c⟩
  | star => exact ⟨c, h2, pb_refl c⟩
  | sort l => exact ⟨c, h2, pb_refl c⟩
  | const r ls => exact ⟨c, h2, pb_refl c⟩
  | @app f f' a a' hf ha ihf iha =>
      generalize hs : ETm.app f a = s at h2
      cases h2 with
      | app hf' ha' =>
          cases hs
          obtain ⟨df, h1f, h2f⟩ := ihf hf'
          obtain ⟨da, h1a, h2a⟩ := iha ha'
          exact ⟨.app df da, .app h1f h1a, .app h2f h2a⟩
      | beta hM hN =>
          cases hs
          obtain ⟨df, h1f, h2f⟩ := ihf (.lam hM)
          obtain ⟨M₁, rfl, hM₁⟩ := pb_lam_inv hf
          obtain ⟨D, rfl, hD₁⟩ := pb_lam_inv h1f
          obtain ⟨D', hD', hD₂⟩ := pb_lam_inv h2f
          cases hD'
          obtain ⟨dn, h1n, h2n⟩ := iha hN
          exact ⟨ETm.inst 0 dn D, .beta hD₁ h1n, pb_inst hD₂ 0 h2n⟩
      | bvar => cases hs
      | star => cases hs
      | sort => cases hs
      | const => cases hs
      | lam => cases hs
      | pi => cases hs
  | @lam b b' hb ih =>
      generalize hs : ETm.lam b = s at h2
      cases h2 with
      | lam hb' =>
          cases hs
          obtain ⟨d, h1, h2⟩ := ih hb'
          exact ⟨.lam d, .lam h1, .lam h2⟩
      | bvar => cases hs
      | star => cases hs
      | sort => cases hs
      | const => cases hs
      | app => cases hs
      | pi => cases hs
      | beta => cases hs
  | @pi a a' b b' ha hb iha ihb =>
      generalize hs : ETm.pi a b = s at h2
      cases h2 with
      | pi ha' hb' =>
          cases hs
          obtain ⟨da, h1a, h2a⟩ := iha ha'
          obtain ⟨db, h1b, h2b⟩ := ihb hb'
          exact ⟨.pi da db, .pi h1a h1b, .pi h2a h2b⟩
      | bvar => cases hs
      | star => cases hs
      | sort => cases hs
      | const => cases hs
      | app => cases hs
      | lam => cases hs
      | beta => cases hs
  | @beta M M' N N' hM hN ihM ihN =>
      generalize hs : ETm.app (.lam M) N = s at h2
      cases h2 with
      | app hf' ha' =>
          cases hs
          obtain ⟨M₂, rfl, hM₂⟩ := pb_lam_inv hf'
          obtain ⟨D, h1, h2⟩ := ihM hM₂
          obtain ⟨dn, h1n, h2n⟩ := ihN ha'
          exact ⟨ETm.inst 0 dn D, pb_inst h1 0 h1n, .beta h2 h2n⟩
      | beta hM' hN' =>
          cases hs
          obtain ⟨D, h1, h2⟩ := ihM hM'
          obtain ⟨dn, h1n, h2n⟩ := ihN hN'
          exact ⟨ETm.inst 0 dn D, pb_inst h1 0 h1n, pb_inst h2 0 h2n⟩
      | bvar => cases hs
      | star => cases hs
      | sort => cases hs
      | const => cases hs
      | lam => cases hs
      | pi => cases hs

/-- CR(β). -/
theorem confluent_betaStep : Confluent BetaStep := by
  have down : ∀ {a b : ETm}, RStar PB a b → RStar BetaStep a b :=
    fun h => rstar_flatten (rstar_mono betaStar_of_pb h)
  intro a b c hb hc
  obtain ⟨d, h1, h2⟩ := confluent_of_diamond pb_diamond (rstar_mono pb_of_betaStep hb)
    (rstar_mono pb_of_betaStep hc)
  exact ⟨d, down h1, down h2⟩

end Rcic.Syn

#print axioms Rcic.Syn.pb_refl
#print axioms Rcic.Syn.pb_of_betaStep
#print axioms Rcic.Syn.betaStar_app
#print axioms Rcic.Syn.betaStar_pi
#print axioms Rcic.Syn.betaStar_lam
#print axioms Rcic.Syn.betaStar_of_pb
#print axioms Rcic.Syn.pb_lift
#print axioms Rcic.Syn.pb_inst
#print axioms Rcic.Syn.pb_lam_inv
#print axioms Rcic.Syn.pb_diamond
#print axioms Rcic.Syn.confluent_betaStep

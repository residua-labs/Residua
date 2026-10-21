import rcic.RcicSynSREqnAnswer

/-!
# RcicSynSREqnLevelGate — row 14: the levels gate modulo eqN is vacuous

cc 2026-10-21 05:45Z brief, lane glm/sr4-eqn (#7809). The refuted gate
(`cl_const_levels_gate_refuted`: `eqNList ls ls'` + `levelsBounded n ls`
does NOT give `levelsBounded n ls'` — the imax zero-arm collapse
`eqN .zero (.imax (.param 1) .zero)` carries bounded lists to unbounded
ones) is ACCEPTED. The brief's alternative: restate the congruence modulo
eqN — `levelsBounded` of eqN-normal forms, or any eqN-invariant bound —
and prove that version, or show no eqN-invariant bound suffices. Measured,
this module takes the second branch, universally:

* **Any** `B : Nat → List Level → Bool` that is eqNList-invariant and FEEDS
  the syntactic premise (`B n ls = true → levelsBounded n ls = true`) must
  REJECT the raw list `[.zero]` itself (`eqn_inv_feed_rejects_zero`): the
  collapse `.zero ~ₙ .imax (.param n) .zero` carries bounded lists to
  unbounded ones. This covers every eqN-invariant restatement at once —
  normal-form bounds included: a normalizer bound accepts `[.zero]`
  (`.zero` is normal), so it can never feed the constructor's syntactic
  `hwf`.
* And the loss is inhabited: the raw list `[.zero]` is legitimately
  bounded at every `n` (`levelsBounded_zero_list`, `rfl`) — the syntactic
  gate admits it, every feeding eqN-invariant `B` refuses it
  (`eqn_inv_bound_loses_zero_cell`). So the eqN-invariant restatement is
  not a restatement: it strictly loses cells the landed gate admits.

Verdict: the const node's `hwf` premise is irreducibly syntactic; the
transport route's fragment boundary cannot be moved by re-bounding modulo
eqN. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the collapse at every depth -/

/-- The imax zero-arm collapse at every parameter index: `.zero` is eqN to
    `.imax (.param n) .zero` for EVERY `n` (the zero arm evaluates away the
    first argument), while the latter carries an unbounded parameter. -/
theorem eqN_zero_imax_paramN (n : Nat) :
    eqN Level.zero (Level.imax (Level.param n) Level.zero) :=
  fun _ => rfl

/-- The collapse's unbounded side at every depth `n`: the parameter `n` is
    out of range for the bound `n` itself. -/
theorem levelsBounded_imax_param_self (n : Nat) :
    levelsBounded n [Level.imax (Level.param n) Level.zero] = false := by
  simp [levelsBounded, levelBounded, Nat.lt_irrefl]

/-! ## §2 no eqN-invariant bound suffices -/

/-- THE pin: every `B` that is eqN-invariant and feeds the constructor's
    syntactic premise must reject `.zero` itself — the collapse carries any
    acceptance of `.zero` to the unbounded `.imax (.param n) .zero`, which
    the feed would then have to admit as bounded. All premises inhabited;
    kernel-checked for arbitrary `B` (universally quantified). -/
theorem eqn_inv_feed_rejects_zero (B : Nat → List Level → Bool)
    (hinv : ∀ (n : Nat) (ls ls' : List Level), eqNList ls ls' →
      B n ls = true → B n ls' = true)
    (hfeed : ∀ (n : Nat) (ls : List Level), B n ls = true →
      levelsBounded n ls = true)
    (n : Nat) : B n [Level.zero] = false := by
  cases hb : B n [Level.zero] with
  | false => rfl
  | true =>
      have hcl : eqNList [Level.zero] [Level.imax (Level.param n) Level.zero] :=
        ⟨eqN_zero_imax_paramN n, True.intro⟩
      have h2 : levelsBounded n [Level.imax (Level.param n) Level.zero] = true :=
        hfeed n _ (hinv n _ _ hcl hb)
      rw [levelsBounded_imax_param_self n] at h2
      exact absurd h2 (by decide)

/-- The inhabited loss: the raw list `[.zero]` is legitimately bounded at
    every depth (no parameters at all). -/
theorem levelsBounded_zero_list (n : Nat) :
    levelsBounded n [Level.zero] = true := rfl

/-- So the eqN-invariant route strictly loses cells the syntactic gate
    admits: no feeding eqN-invariant `B` ever accepts `[.zero]`'s entry,
    while `levelsBounded` does. The gate cannot be restated modulo eqN. -/
theorem eqn_inv_bound_loses_zero_cell (B : Nat → List Level → Bool)
    (hinv : ∀ (n : Nat) (ls ls' : List Level), eqNList ls ls' →
      B n ls = true → B n ls' = true)
    (hfeed : ∀ (n : Nat) (ls : List Level), B n ls = true →
      levelsBounded n ls = true)
    (n : Nat) : ¬ (B n [Level.zero] = true) :=
  fun h => absurd h (by simp [eqn_inv_feed_rejects_zero B hinv hfeed n])

#print axioms Rcic.Syn.eqN_zero_imax_paramN
#print axioms Rcic.Syn.levelsBounded_imax_param_self
#print axioms Rcic.Syn.eqn_inv_feed_rejects_zero
#print axioms Rcic.Syn.levelsBounded_zero_list
#print axioms Rcic.Syn.eqn_inv_bound_loses_zero_cell

end Rcic.Syn

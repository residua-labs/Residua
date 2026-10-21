/-
# S14 SCOPE-2/3 — `eps_support` for the repaired `eps`; `shifted_value_scope`

`research/rcic/sortrow/S14_SHIFTED_VALUE_SCOPE.md` §5/§6, on top of
`devin/p-rfct-r2`'s repaired `TyP.eps` (Π proof domain via `piSlot`, `lsub`
inline payload via `localize κ r`) and SCOPE-1's `DisplayFits` / `termFree_lt`.

The support relation (S14 §2):
```
  ∀ k, EFree k (D.eps σ ρ) → ∃ i, NFree i e ∧ EFree k (resolve ρ i)
```
— every free index of the erasure sits in the actual resolve of some source
free index. It is NOT `FV(eps) ⊆ FV(e)`: inline payloads carry frees the source
never had. The theorem needs only `D.AssumpPref` (every transport node sits
under an assumption prefix) plus the structural `DisplayFits` — no `EnvWfT`,
no `CtxWfT`, no source well-formedness, no `LevelHom σ`.

Two spec constraints honored verbatim:

* `lsub` arm uses ONLY `free_restore_iff` on the restored inline payload —
  never `AvoidPrefix` of `hv` (that would re-create the §4 circle).
* `wk` arm handles `c ≥ Γ.length` via `TyP.termFree_lt` + `DisplayFits`
  (`ρ[c]? = none` forces `c ≥ ρ.length ≥ insertAt-length > Γ.length`, so every
  source free index is below the cutoff). No `AssumpCut`.

§6 then derives `AvoidPrefix κ 0 (hv.eps σ ρ)` for the original `lsub` value —
the repair's losslessness premise — from `eps_support` + `resolve_suffix`.

(Dependencies: `RcicERScope1` for `DisplayFits`/`termFree_lt`/`nfree_*`;
`RcicERScope0` for `EFree`/`free_restore_iff`/`resolve_suffix`;
`RcicSynBvarEsub`/`RcicSynBvarWk` for the `insertDisp`/`removeAt` resolve
equations — all transitively via `RcicERScope1`.)
-/

import rcic.RcicERScope1

namespace Rcic.Syn
open Rcic.Declarative

/-! ## §1 `NFree` intro directions (converses of SCOPE-1's forward lemmas) -/

/-- Reverse of `nfree_lift`: a low untouched index or a high index lowered by
    `k` rebuilds a free index of the lift. -/
theorem nfree_lift_of {c k i : Nat} {e : Expr Nat} :
    (i < c ∧ NFree i e) ∨ (c + k ≤ i ∧ NFree (i - k) e) → NFree i (lift c k e) := by
  induction e generalizing c k i with
  | bvar m =>
      rintro (⟨hlt, hm⟩ | ⟨hge, hm⟩)
      · have hm' : i = m := hm
        simp only [lift]
        rw [if_neg (by omega : ¬ c ≤ m)]
        exact hm
      · simp only [lift]
        have hm' : i - k = m := hm
        rw [if_pos (by omega)]
        show i = m + k
        omega
  | sort l => rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact False.elim h
  | const r ls => rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact False.elim h
  | app f a ihf iha =>
      rintro (⟨hlt, h⟩ | ⟨hge, h⟩)
      · rcases h with h | h
        · exact .inl (ihf (.inl ⟨hlt, h⟩))
        · exact .inr (iha (.inl ⟨hlt, h⟩))
      · rcases h with h | h
        · exact .inl (ihf (.inr ⟨hge, h⟩))
        · exact .inr (iha (.inr ⟨hge, h⟩))
  | lam A b ihA ihb =>
      rintro (⟨hlt, h⟩ | ⟨hge, h⟩)
      · rcases h with h | h
        · exact .inl (ihA (.inl ⟨hlt, h⟩))
        · exact .inr (ihb (.inl ⟨by omega, h⟩))
      · rcases h with h | h
        · exact .inl (ihA (.inr ⟨hge, h⟩))
        · refine .inr (ihb (.inr ⟨by omega, ?_⟩))
          have he : i - k + 1 = i + 1 - k := by omega
          rwa [he] at h
  | pi A B ihA ihB =>
      rintro (⟨hlt, h⟩ | ⟨hge, h⟩)
      · rcases h with h | h
        · exact .inl (ihA (.inl ⟨hlt, h⟩))
        · exact .inr (ihB (.inl ⟨by omega, h⟩))
      · rcases h with h | h
        · exact .inl (ihA (.inr ⟨hge, h⟩))
        · refine .inr (ihB (.inr ⟨by omega, ?_⟩))
          have he : i - k + 1 = i + 1 - k := by omega
          rwa [he] at h
  | letE A v b ihA ihv ihb =>
      rintro (⟨hlt, h⟩ | ⟨hge, h⟩)
      · rcases h with h | h | h
        · exact .inl (ihA (.inl ⟨hlt, h⟩))
        · exact .inr (.inl (ihv (.inl ⟨hlt, h⟩)))
        · exact .inr (.inr (ihb (.inl ⟨by omega, h⟩)))
      · rcases h with h | h | h
        · exact .inl (ihA (.inr ⟨hge, h⟩))
        · exact .inr (.inl (ihv (.inr ⟨hge, h⟩)))
        · refine .inr (.inr (ihb (.inr ⟨by omega, ?_⟩)))
          have he : i - k + 1 = i + 1 - k := by omega
          rwa [he] at h
  | lit t => rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact False.elim h

/-- Reverse of `nfree_instantiate`: untouched low, shifted-down high, or — when
    the target actually occurs (`NFree j e`) — a free index of the replacement. -/
theorem nfree_instantiate_of {i j : Nat} {r e : Expr Nat} :
    (i < j ∧ NFree i e) ∨ (j ≤ i ∧ NFree (i + 1) e) ∨ (NFree j e ∧ NFree i r) →
    NFree i (instantiate j r e) := by
  induction e generalizing i j r with
  | bvar m =>
      rintro (⟨hlt, hm⟩ | ⟨hge, hm⟩ | ⟨hocc, hr⟩)
      · have hm' : i = m := hm
        simp only [instantiate]
        rw [if_neg (by omega : ¬ m = j), if_neg (by omega : ¬ j < m)]
        exact hm
      · have hm' : i + 1 = m := hm
        simp only [instantiate]
        rw [if_neg (by omega : ¬ m = j), if_pos (by omega : j < m)]
        show i = m - 1
        omega
      · have hm' : j = m := hocc
        simp only [instantiate]
        rw [if_pos (by omega : m = j)]
        exact hr
  | sort l => rintro (⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩) <;> exact False.elim h
  | const r' ls => rintro (⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩) <;> exact False.elim h
  | app f a ihf iha =>
      rintro (⟨hlt, h⟩ | ⟨hge, h⟩ | ⟨hocc, hr⟩)
      · rcases h with h | h
        · exact .inl (ihf (.inl ⟨hlt, h⟩))
        · exact .inr (iha (.inl ⟨hlt, h⟩))
      · rcases h with h | h
        · exact .inl (ihf (.inr (.inl ⟨hge, h⟩)))
        · exact .inr (iha (.inr (.inl ⟨hge, h⟩)))
      · rcases hocc with hocc | hocc
        · exact .inl (ihf (.inr (.inr ⟨hocc, hr⟩)))
        · exact .inr (iha (.inr (.inr ⟨hocc, hr⟩)))
  | lam A b ihA ihb =>
      rintro (⟨hlt, h⟩ | ⟨hge, h⟩ | ⟨hocc, hr⟩)
      · rcases h with h | h
        · exact .inl (ihA (.inl ⟨hlt, h⟩))
        · exact .inr (ihb (.inl ⟨by omega, h⟩))
      · rcases h with h | h
        · exact .inl (ihA (.inr (.inl ⟨hge, h⟩)))
        · exact .inr (ihb (.inr (.inl ⟨by omega, h⟩)))
      · rcases hocc with hocc | hocc
        · have hih : (i < j ∧ NFree i A) ∨ (j ≤ i ∧ NFree (i + 1) A) ∨
              (NFree j A ∧ NFree i r) := .inr (.inr ⟨hocc, hr⟩)
          exact .inl (ihA hih)
        · refine .inr (ihb (.inr (.inr ⟨hocc, ?_⟩)))
          exact nfree_lift_of (.inr ⟨by omega, hr⟩)
  | pi A B ihA ihB =>
      rintro (⟨hlt, h⟩ | ⟨hge, h⟩ | ⟨hocc, hr⟩)
      · rcases h with h | h
        · exact .inl (ihA (.inl ⟨hlt, h⟩))
        · exact .inr (ihB (.inl ⟨by omega, h⟩))
      · rcases h with h | h
        · exact .inl (ihA (.inr (.inl ⟨hge, h⟩)))
        · exact .inr (ihB (.inr (.inl ⟨by omega, h⟩)))
      · rcases hocc with hocc | hocc
        · have hih : (i < j ∧ NFree i A) ∨ (j ≤ i ∧ NFree (i + 1) A) ∨
              (NFree j A ∧ NFree i r) := .inr (.inr ⟨hocc, hr⟩)
          exact .inl (ihA hih)
        · refine .inr (ihB (.inr (.inr ⟨hocc, ?_⟩)))
          exact nfree_lift_of (.inr ⟨by omega, hr⟩)
  | letE A v b ihA ihv ihb =>
      rintro (⟨hlt, h⟩ | ⟨hge, h⟩ | ⟨hocc, hr⟩)
      · rcases h with h | h | h
        · exact .inl (ihA (.inl ⟨hlt, h⟩))
        · exact .inr (.inl (ihv (.inl ⟨hlt, h⟩)))
        · exact .inr (.inr (ihb (.inl ⟨by omega, h⟩)))
      · rcases h with h | h | h
        · exact .inl (ihA (.inr (.inl ⟨hge, h⟩)))
        · exact .inr (.inl (ihv (.inr (.inl ⟨hge, h⟩))))
        · exact .inr (.inr (ihb (.inr (.inl ⟨by omega, h⟩))))
      · rcases hocc with hocc | hocc | hocc
        · have hih : (i < j ∧ NFree i A) ∨ (j ≤ i ∧ NFree (i + 1) A) ∨
              (NFree j A ∧ NFree i r) := .inr (.inr ⟨hocc, hr⟩)
          exact .inl (ihA hih)
        · have hih : (i < j ∧ NFree i v) ∨ (j ≤ i ∧ NFree (i + 1) v) ∨
              (NFree j v ∧ NFree i r) := .inr (.inr ⟨hocc, hr⟩)
          exact .inr (.inl (ihv hih))
        · refine .inr (.inr (ihb (.inr (.inr ⟨hocc, ?_⟩))))
          exact nfree_lift_of (.inr ⟨by omega, hr⟩)
  | lit t => rintro (⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩) <;> exact False.elim h

/-- `instantiateLevels` leaves de Bruijn indices alone — source support is
    carried over verbatim. -/
theorem nfree_instLevels_rev {i : Nat} {e : Expr Nat} (ls : List Level) :
    NFree i e → NFree i (instantiateLevels ls e) := by
  induction e generalizing i with
  | bvar m => intro h; exact h
  | sort l => intro h; exact False.elim h
  | const r ls' => intro h; exact False.elim h
  | app f a ihf iha =>
      intro h
      rcases h with h | h
      · exact .inl (ihf h)
      · exact .inr (iha h)
  | lam A b ihA ihb =>
      intro h
      rcases h with h | h
      · exact .inl (ihA h)
      · exact .inr (ihb h)
  | pi A B ihA ihB =>
      intro h
      rcases h with h | h
      · exact .inl (ihA h)
      · exact .inr (ihB h)
  | letE A v b ihA ihv ihb =>
      intro h
      rcases h with h | h | h
      · exact .inl (ihA h)
      · exact .inr (.inl (ihv h))
      · exact .inr (.inr (ihb h))
  | lit t => intro h; exact False.elim h

/-- `natExpand` builds only `const`/`app` — no free de Bruijn index. -/
theorem nfree_natExpand {i : Nat} : (t : Nat) → NFree i (natExpand t) → False
  | 0 => fun h => False.elim h
  | n + 1 => fun h => by
      rcases h with h | h
      · exact False.elim h
      · exact nfree_natExpand n h

/-! ## §2 `EFree` of `ETm.inst`, with the occurrence evidence -/

/-- A free index of `inst j r q` is a low untouched index, a high index that
    came down one, or a free index of the replacement `r` — in which case the
    target index `j` genuinely occurs in `q` (`EFree j q` is the evidence). -/
theorem efree_inst {i j : Nat} {r q : ETm} :
    EFree i (ETm.inst j r q) →
      (i < j ∧ EFree i q) ∨ (j ≤ i ∧ EFree (i + 1) q) ∨ (EFree j q ∧ EFree i r) := by
  induction q generalizing i j r with
  | bvar m =>
      intro h
      simp only [ETm.inst] at h
      split at h
      · rename_i hm
        subst hm
        exact .inr (.inr ⟨rfl, h⟩)
      · split at h
        · rename_i hm hj
          have : i = m - 1 := h
          subst this
          exact .inr (.inl ⟨by omega, by show m - 1 + 1 = m; omega⟩)
        · rename_i hm hj
          have : i = m := h
          subst this
          exact .inl ⟨by omega, rfl⟩
  | star => intro h; exact h.elim
  | sort l => intro h; exact False.elim h
  | const c ls => intro h; exact h.elim
  | app f a ihf iha =>
      intro h
      rcases h with h | h
      · rcases ihf h with h | h | h
        · exact .inl ⟨h.1, .inl h.2⟩
        · exact .inr (.inl ⟨h.1, .inl h.2⟩)
        · exact .inr (.inr ⟨.inl h.1, h.2⟩)
      · rcases iha h with h | h | h
        · exact .inl ⟨h.1, .inr h.2⟩
        · exact .inr (.inl ⟨h.1, .inr h.2⟩)
        · exact .inr (.inr ⟨.inr h.1, h.2⟩)
  | lam b ihb =>
      intro h
      rcases ihb h with h | h | h
      · exact .inl ⟨by omega, h.2⟩
      · exact .inr (.inl ⟨by omega, h.2⟩)
      · refine .inr (.inr ⟨h.1, ?_⟩)
        rcases (efree_lift _ 0).mp h.2 with h' | h'
        · exact absurd h'.1 (Nat.not_lt_zero _)
        · have : i + 1 - 1 = i := by omega
          rw [this] at h'
          exact h'.2
  | pi a b iha ihb =>
      intro h
      rcases h with h | h
      · rcases iha h with h | h | h
        · exact .inl ⟨h.1, .inl h.2⟩
        · exact .inr (.inl ⟨h.1, .inl h.2⟩)
        · exact .inr (.inr ⟨.inl h.1, h.2⟩)
      · rcases ihb h with h | h | h
        · exact .inl ⟨by omega, .inr h.2⟩
        · exact .inr (.inl ⟨by omega, .inr h.2⟩)
        · refine .inr (.inr ⟨.inr h.1, ?_⟩)
          rcases (efree_lift _ 0).mp h.2 with h' | h'
          · exact absurd h'.1 (Nat.not_lt_zero _)
          · have : i + 1 - 1 = i := by omega
            rw [this] at h'
            exact h'.2

/-! ## §3 assumption-entry plumbing and the prefix-free bound -/

/-- `d ∈ Γ.take n` from a positional lookup inside the take. -/
theorem mem_take_of_getElem? {Γ : LCtx} {i n : Nat} {d : LocalDecl}
    (h : Γ[i]? = some d) (hn : i < n) : d ∈ Γ.take n := by
  have h' : (Γ.take n)[i]? = some d := by
    rw [List.getElem?_take, if_pos hn]
    exact h
  exact List.getElem?_mem h' 

/-- Positional form of `AssumptionPrefix`: an in-range index below `j` names an
    `.assumption` entry. -/
theorem assumptionPrefix_getElem {Γ : LCtx} {j s : Nat}
    (hap : AssumptionPrefix Γ j) (hsj : s < j) (hsl : s < Γ.length) :
    ∃ t, Γ[s]? = some (.assumption t) := by
  obtain ⟨d, hd⟩ : ∃ d, Γ[s]? = some d :=
    ⟨Γ[s], List.getElem?_eq_some_iff.mpr ⟨hsl, rfl⟩⟩
  obtain ⟨A, hA⟩ := hap d (mem_take_of_getElem? hd hsj)
  exact ⟨A, hA ▸ hd⟩

/-- `substRemove` instDecl's the entries below `j`; the declaration kind is
    untouched, so an assumption entry stays `.assumption` after the map. -/
theorem substRemove_getElem?_assumption_lo {v : Expr Nat} {j s : Nat} {Γ : LCtx}
    {t : Expr Nat} (hsj : s < j) (h : Γ[s]? = some (.assumption t)) :
    ∃ t', (substRemove v j Γ)[s]? = some (.assumption t') := by
  induction s generalizing j Γ with
  | zero =>
      cases j with
      | zero => exact absurd hsj (Nat.not_lt_zero _)
      | succ j' =>
          cases Γ with
          | nil => simp at h
          | cons x Γ' =>
              simp only [substRemove_succ_cons, List.getElem?_cons_zero]
              simp only [List.getElem?_cons_zero, Option.some.injEq] at h
              subst h
              exact ⟨_, rfl⟩
  | succ s' ih =>
      cases j with
      | zero => exact absurd hsj (Nat.not_lt_zero _)
      | succ j' =>
          cases Γ with
          | nil => simp at h
          | cons x Γ' =>
              simp only [substRemove_succ_cons, List.getElem?_cons_succ]
              simp only [List.getElem?_cons_succ] at h
              exact ih (by omega) h

/-- `insertAt` liftDecl's the entries above the cutoff (positions `< c`); the
    declaration kind is untouched, so an assumption entry stays `.assumption`. -/
theorem insertAt_getElem?_assumption_lo {d : LocalDecl} {c s : Nat} {Γ : LCtx}
    {t : Expr Nat} (hsc : s < c) (h : Γ[s]? = some (.assumption t)) :
    ∃ t', (insertAt d c Γ)[s]? = some (.assumption t') := by
  induction s generalizing c Γ with
  | zero =>
      cases c with
      | zero => exact absurd hsc (Nat.not_lt_zero _)
      | succ c' =>
          cases Γ with
          | nil => simp at h
          | cons x Γ' =>
              simp only [insertAt_succ_cons, List.getElem?_cons_zero]
              simp only [List.getElem?_cons_zero, Option.some.injEq] at h
              subst h
              exact ⟨_, rfl⟩
  | succ s' ih =>
      cases c with
      | zero => exact absurd hsc (Nat.not_lt_zero _)
      | succ c' =>
          cases Γ with
          | nil => simp at h
          | cons x Γ' =>
              simp only [insertAt_succ_cons, List.getElem?_cons_succ]
              simp only [List.getElem?_cons_succ] at h
              exact ih (by omega) h

/-- The prefix-vacuity bound: below an assumption-only prefix of length `j`,
    `resolve ρ s` is `.star` or a `.bvar` whose index is the prefix's keep count
    — so any free index of it is strictly below `countKeep (ρ.take j)`. This is
    where `AssumptionPrefix` does its work in the transport arms: inline
    payloads cannot hide below `j`, so a free numeral at-or-above `κ` cannot be
    smuggled in through a low source variable. -/
theorem resolve_frees_lt {Δ : LCtx} {ρ : List Disp} {j s x : Nat}
    (hf : DisplayFits Δ ρ)
    (hassum : ∀ s', s' ≤ s → ∃ t, Δ[s']? = some (.assumption t))
    (hsj : s < j) (hsl : s < Δ.length)
    (h2 : EFree x (resolve ρ s)) : x < countKeep (ρ.take j) := by
  induction hf generalizing j s x with
  | nil ρ' =>
      simp only [List.length_nil] at hsl
      exact absurd hsl (Nat.not_lt_zero _)
  | assumptionKeep h₀ ih =>
      rename_i A Γ' ρ'
      cases s with
      | zero =>
          have hx : x = 0 := h2
          subst hx
          cases j with
          | zero => exact absurd hsj (Nat.not_lt_zero _)
          | succ j' =>
              simp only [List.take_succ_cons, countKeep]
              exact Nat.succ_pos _
      | succ s' =>
          rw [resolve_keep_succ] at h2
          rcases (efree_lift _ 0).mp h2 with h' | h'
          · exact absurd h'.1 (Nat.not_lt_zero _)
          · cases j with
            | zero => exact absurd hsj (Nat.not_lt_zero _)
            | succ j' =>
                have hassum' : ∀ s'', s'' ≤ s' →
                    ∃ t, Γ'[s'']? = some (.assumption t) := by
                  intro s'' hs''
                  obtain ⟨t, ht⟩ := hassum (s'' + 1) (by omega)
                  rw [List.getElem?_cons_succ] at ht
                  exact ⟨t, ht⟩
                have hlt := ih hassum' (by omega : s' < j')
                    (by simp only [List.length_cons] at hsl; omega) h'.2
                simp only [List.take_succ_cons, countKeep]
                omega
  | assumptionDrop h₀ ih =>
      rename_i A Γ' ρ'
      cases s with
      | zero =>
          rw [resolve_drop_zero] at h2
          exact h2.elim
      | succ s' =>
          rw [resolve_drop_succ] at h2
          cases j with
          | zero => exact absurd hsj (Nat.not_lt_zero _)
          | succ j' =>
              have hassum' : ∀ s'', s'' ≤ s' →
                  ∃ t, Γ'[s'']? = some (.assumption t) := by
                intro s'' hs''
                obtain ⟨t, ht⟩ := hassum (s'' + 1) (by omega)
                rw [List.getElem?_cons_succ] at ht
                exact ⟨t, ht⟩
              have hlt := ih hassum' (by omega : s' < j')
                  (by simp only [List.length_cons] at hsl; omega) h2
              simp only [List.take_succ_cons, countKeep]
              exact hlt
  | letDrop h₀ ih =>
      rename_i A v' Γ' ρ'
      cases s with
      | zero =>
          obtain ⟨t, ht⟩ := hassum 0 (Nat.le_refl 0)
          simp only [List.getElem?_cons_zero, Option.some.injEq] at ht
          nomatch ht
      | succ s' =>
          rw [resolve_drop_succ] at h2
          cases j with
          | zero => exact absurd hsj (Nat.not_lt_zero _)
          | succ j' =>
              have hassum' : ∀ s'', s'' ≤ s' →
                  ∃ t, Γ'[s'']? = some (.assumption t) := by
                intro s'' hs''
                obtain ⟨t, ht⟩ := hassum (s'' + 1) (by omega)
                rw [List.getElem?_cons_succ] at ht
                exact ⟨t, ht⟩
              have hlt := ih hassum' (by omega : s' < j')
                  (by simp only [List.length_cons] at hsl; omega) h2
              simp only [List.take_succ_cons, countKeep]
              exact hlt
  | letInline h₀ ih =>
      rename_i A v' w' Γ' ρ'
      cases s with
      | zero =>
          obtain ⟨t, ht⟩ := hassum 0 (Nat.le_refl 0)
          simp only [List.getElem?_cons_zero, Option.some.injEq] at ht
          nomatch ht
      | succ s' =>
          rw [resolve_inline_succ] at h2
          cases j with
          | zero => exact absurd hsj (Nat.not_lt_zero _)
          | succ j' =>
              have hassum' : ∀ s'', s'' ≤ s' →
                  ∃ t, Γ'[s'']? = some (.assumption t) := by
                intro s'' hs''
                obtain ⟨t, ht⟩ := hassum (s'' + 1) (by omega)
                rw [List.getElem?_cons_succ] at ht
                exact ⟨t, ht⟩
              have hlt := ih hassum' (by omega : s' < j')
                  (by simp only [List.length_cons] at hsl; omega) h2
              simp only [List.take_succ_cons, countKeep]
              exact hlt

/-- The inserted `keep` at position `j` resolves to the prefix's erased count —
    the erased slot the replacement will land in. Mirrors
    `resolve_insertDisp_inline`. -/
theorem resolve_insertDisp_keep_hit (ρ : List Disp) (j : Nat)
    (hj : j ≤ ρ.length) :
    resolve (insertDisp .keep j ρ) j = .bvar (countKeep (ρ.take j)) := by
  induction j generalizing ρ with
  | zero =>
    simp only [insertDisp, resolve, List.take_zero, countKeep]
  | succ j ih =>
    cases ρ with
    | nil => exact absurd hj (Nat.not_succ_le_zero j)
    | cons hd ρ =>
      have hj' : j ≤ ρ.length := by
        simp only [List.length_cons] at hj
        exact Nat.le_of_succ_le_succ hj
      cases hd with
      | keep =>
        simp only [insertDisp, resolve, List.take_succ_cons, countKeep]
        rw [ih ρ hj']
        simp only [ETm.lift, if_pos (Nat.zero_le _)]
      | drop =>
        simp only [insertDisp, resolve, List.take_succ_cons, countKeep, ih ρ hj']
      | inline _ =>
        simp only [insertDisp, resolve, List.take_succ_cons, countKeep, ih ρ hj']

/-- The inserted `drop` at position `j` erases to `★`. -/
theorem resolve_insertDisp_drop_hit (ρ : List Disp) (j : Nat)
    (hj : j ≤ ρ.length) :
    resolve (insertDisp .drop j ρ) j = .star := by
  induction j generalizing ρ with
  | zero => rfl
  | succ j ih =>
    cases ρ with
    | nil => exact absurd hj (Nat.not_succ_le_zero j)
    | cons hd ρ =>
      have hj' : j ≤ ρ.length := by
        simp only [List.length_cons] at hj
        exact Nat.le_of_succ_le_succ hj
      cases hd with
      | keep =>
        simp only [insertDisp, resolve, List.take_succ_cons, countKeep]
        rw [ih ρ hj']
        simp only [ETm.lift]
      | drop =>
        simp only [insertDisp, resolve, List.take_succ_cons, countKeep, ih ρ hj']
      | inline _ =>
        simp only [insertDisp, resolve, List.take_succ_cons, countKeep, ih ρ hj']

/-- `appOut` never invents a free index: any free index of the output is a free
    index of one of the two inputs. -/
theorem efree_appOut {f a : ETm} {k : Nat} :
    EFree k (appOut f a) → EFree k f ∨ EFree k a := by
  cases f with
  | star => intro h; exact h.elim
  | _ =>
      cases a with
      | star => intro h; exact .inl h
      | _ =>
          intro h
          rcases h with h | h
          · exact .inl h
          · exact .inr h

/-- `lamOut` (a kept λ-erasure) exposes the body's free indices one deeper. -/
theorem efree_lamOut {q : ETm} {k : Nat} :
    EFree k (lamOut q) → EFree (k + 1) q := by
  cases q with
  | star => intro h; exact h.elim
  | _ => intro h; exact h

/-- `cctx` swaps the head assumption's *type*, not its kind — the display fit
    carries across unchanged. -/
theorem DisplayFits.assumption_congr {A A' : Expr Nat} {Γ : LCtx} {ρ : List Disp}
    (h : DisplayFits (.assumption A' :: Γ) ρ) :
    DisplayFits (.assumption A :: Γ) ρ := by
  cases h with
  | assumptionKeep h₀ => exact .assumptionKeep h₀
  | assumptionDrop h₀ => exact .assumptionDrop h₀

/-! ## §4 `eps_support` — the fifteen-arm structural induction (S14 §5)

Every free index `k` of an erasure is witnessed by a source free index `i`
whose displayed slot `resolve ρ i` carries `k`. The transport arms are where
`AssumpPref` pays out: below an assumption-only prefix no `inline` payload can
hide, so erased-position bookkeeping is exact. `wk` with `c > Γ.length` needs
no extra hypothesis — `termFree_lt` bounds every source free index by the
context length, which is already below `c`. The `lsub` hit case goes through
`free_restore_iff` only: no `AvoidPrefix` of the replacement is assumed. -/

theorem TyP.eps_support {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} :
    (D : TyP E n Γ e T) → (σ : Level → Level) → D.AssumpPref →
    (ρ : List Disp) → DisplayFits Γ ρ →
    ∀ k, EFree k (D.eps σ ρ) → ∃ i, NFree i e ∧ EFree k (resolve ρ i) := fun
  | .sort .., _, _, _, _, _, hk => False.elim hk
  | .bvar _ _ _ i _ u _ _, σ, _, ρ, _, k, hk => by
      cases hu : levelIsZero (σ u) with
      | true =>
          rw [eps_bvar_proof hu] at hk
          exact False.elim hk
      | false =>
          rw [eps_bvar_rel hu] at hk
          exact ⟨i, rfl, hk⟩
  | .const _ _ _ _ _ _ _ u _ _ _ _ _, σ, _, ρ, _, k, hk => by
      cases hu : levelIsZero (σ u) with
      | true =>
          rw [eps_const_proof hu] at hk
          exact False.elim hk
      | false =>
          rw [eps_const_rel hu] at hk
          exact False.elim hk
  | .pi _ _ _ _ u _ _ hA hB, σ, hap, ρ, hf, k, hk => by
      obtain ⟨hA_ap, hB_ap⟩ := hap
      cases hu : levelIsZero (σ u) with
      | true =>
          rw [eps_pi_drop hu] at hk
          rcases (hk : EFree k _ ∨ EFree (k + 1) _) with hk | hk
          · obtain ⟨i, hi, h2⟩ := TyP.eps_support hA σ hA_ap ρ hf k hk
            exact ⟨i, .inl hi, h2⟩
          · rw [piSlot_true] at hk
            rcases (efree_lift _ 0).mp hk with h' | h'
            · exact absurd h'.1 (Nat.not_lt_zero _)
            · rw [Nat.add_sub_cancel] at h'
              obtain ⟨i, hi, h2⟩ := TyP.eps_support hB σ hB_ap (.drop :: ρ)
                  (.assumptionDrop hf) k h'.2
              cases i with
              | zero =>
                  rw [resolve_drop_zero] at h2
                  exact False.elim h2
              | succ i' =>
                  rw [resolve_drop_succ] at h2
                  exact ⟨i', .inr hi, h2⟩
      | false =>
          rw [eps_pi_keep hu] at hk
          rcases (hk : EFree k _ ∨ EFree (k + 1) _) with hk | hk
          · obtain ⟨i, hi, h2⟩ := TyP.eps_support hA σ hA_ap ρ hf k hk
            exact ⟨i, .inl hi, h2⟩
          · obtain ⟨i, hi, h2⟩ := TyP.eps_support hB σ hB_ap (.keep :: ρ)
                (.assumptionKeep hf) (k + 1) hk
            cases i with
            | zero =>
                rw [resolve_keep_zero] at h2
                have : k + 1 = 0 := h2
                exact (by omega : False).elim
            | succ i' =>
                rw [resolve_keep_succ] at h2
                rcases (efree_lift _ 0).mp h2 with h' | h'
                · exact absurd h'.1 (Nat.not_lt_zero _)
                · rw [Nat.add_sub_cancel] at h'
                  exact ⟨i', .inr hi, h'.2⟩
  | .lam _ _ _ _ u _ _ _ hA hbody hB, σ, hap, ρ, hf, k, hk => by
      obtain ⟨-, hb_ap, -⟩ := hap
      cases hu : levelIsZero (σ u) with
      | true =>
          rw [eps_lam_drop hu] at hk
          obtain ⟨i, hi, h2⟩ := TyP.eps_support hbody σ hb_ap (.drop :: ρ)
              (.assumptionDrop hf) k hk
          cases i with
          | zero =>
              rw [resolve_drop_zero] at h2
              exact False.elim h2
          | succ i' =>
              rw [resolve_drop_succ] at h2
              exact ⟨i', .inr hi, h2⟩
      | false =>
          rw [eps_lam_keep_eq hA hbody hB ρ hu] at hk
          obtain ⟨i, hi, h2⟩ := TyP.eps_support hbody σ hb_ap (.keep :: ρ)
              (.assumptionKeep hf) (k + 1) (efree_lamOut hk)
          cases i with
          | zero =>
              rw [resolve_keep_zero] at h2
              have : k + 1 = 0 := h2
              exact (by omega : False).elim
          | succ i' =>
              rw [resolve_keep_succ] at h2
              rcases (efree_lift _ 0).mp h2 with h' | h'
              · exact absurd h'.1 (Nat.not_lt_zero _)
              · rw [Nat.add_sub_cancel] at h'
                exact ⟨i', .inr hi, h'.2⟩
  | .app _ _ _ _ _ _ _ _ hf_ ha hT, σ, hap, ρ, hfits, k, hk => by
      obtain ⟨hf_ap, ha_ap, -⟩ := hap
      rw [eps_app_eq hf_ ha hT σ ρ] at hk
      rcases efree_appOut hk with hk | hk
      · obtain ⟨i, hi, h2⟩ := TyP.eps_support hf_ σ hf_ap ρ hfits k hk
        exact ⟨i, .inl hi, h2⟩
      · obtain ⟨i, hi, h2⟩ := TyP.eps_support ha σ ha_ap ρ hfits k hk
        exact ⟨i, .inr hi, h2⟩
  | .letE _ _ _ _ _ _ _ _ _ hA hv hb hT, σ, hap, ρ, hfits, k, hk => by
      obtain ⟨-, hv_ap, hb_ap, -⟩ := hap
      rw [let_eps_eq hA hv hb hT σ ρ] at hk
      by_cases hst : hv.eps σ ρ = .star
      · rw [hst] at hk
        obtain ⟨i, hi, h2⟩ := TyP.eps_support hb σ hb_ap (.drop :: ρ)
            (.letDrop hfits) k hk
        cases i with
        | zero =>
            rw [resolve_drop_zero] at h2
            exact False.elim h2
        | succ i' =>
            rw [resolve_drop_succ] at h2
            exact ⟨i', .inr (.inr hi), h2⟩
      · have hl : letDisp (hv.eps σ ρ) = .inline (hv.eps σ ρ) := by
          cases hve : hv.eps σ ρ <;> simp_all [letDisp]
        rw [hl] at hk
        obtain ⟨i, hi, h2⟩ := TyP.eps_support hb σ hb_ap
            (.inline (hv.eps σ ρ) :: ρ) (.letInline hfits) k hk
        cases i with
        | zero =>
            rw [resolve_inline_zero] at h2
            obtain ⟨i', hi', h2'⟩ := TyP.eps_support hv σ hv_ap ρ hfits k h2
            exact ⟨i', .inr (.inl hi'), h2'⟩
        | succ i' =>
            rw [resolve_inline_succ] at h2
            exact ⟨i', .inr (.inr hi), h2⟩
  | .lit _ _ _ _ _ hexp, σ, hexp_ap, ρ, hfits, k, hk => by
      rw [eps_lit σ ρ] at hk
      obtain ⟨i, hi, -⟩ := TyP.eps_support hexp σ hexp_ap ρ hfits k hk
      exact (nfree_natExpand _ hi).elim
  | .conv _ _ _ _ _ _ _ h hc, σ, hap, ρ, hfits, k, hk => by
      rw [eps_conv σ ρ] at hk
      exact TyP.eps_support h σ hap.1 ρ hfits k hk
  | .wk _ _ Γ _ _ d c D, σ, hap, ρ, hfits, k, hk => by
      obtain ⟨hap_c, hD_ap⟩ := hap
      cases hkc : ρ[c]? with
      | none =>
          rw [eps_wk_not_keep (.inl hkc)] at hk
          obtain ⟨i, hi, h2⟩ := TyP.eps_support D σ hD_ap (removeAt ρ c)
              (displayFits_wk hfits) k hk
          have hi' := TyP.termFree_lt D hi
          have hc : Γ.length + 1 ≤ ρ.length := by
            have := DisplayFits.length_le hfits
            rwa [insertAt_length] at this
          have hcb : ρ.length ≤ c := by
            rcases Nat.lt_or_ge c ρ.length with hltc | hgec
            · rw [List.getElem?_eq_some_iff.mpr ⟨hltc, rfl⟩] at hkc
              exact Option.noConfusion hkc
            · exact hgec
          rw [resolve_removeAt_lo ρ c i (by omega)] at h2
          exact ⟨i, nfree_lift_of (.inl ⟨by omega, hi⟩), h2⟩
      | some dρ =>
          cases dρ with
          | keep =>
              rw [eps_wk_keep hkc] at hk
              rcases (efree_lift _ _).mp hk with h' | h'
              · -- k < countKeep (ρ.take c); the free index is below the gap.
                obtain ⟨i, hi, h2⟩ := TyP.eps_support D σ hD_ap (removeAt ρ c)
                    (displayFits_wk hfits) k h'.2
                rcases Nat.lt_or_ge i c with hlt | hge
                · rw [resolve_removeAt_lo ρ c i hlt] at h2
                  exact ⟨i, nfree_lift_of (.inl ⟨hlt, hi⟩), h2⟩
                · have h2' : EFree k (resolve ρ (i + 1)) :=
                    resolve_removeAt_hi_keep ρ c i hge hkc ▸
                      (efree_lift _ _).mpr (.inl ⟨h'.1, h2⟩)
                  exact ⟨i + 1, nfree_lift_of (.inr ⟨by omega, hi⟩), h2'⟩
              · -- countKeep (ρ.take c) + 1 ≤ k; the free index is above the gap.
                obtain ⟨i, hi, h2⟩ := TyP.eps_support D σ hD_ap (removeAt ρ c)
                    (displayFits_wk hfits) (k - 1) h'.2
                rcases Nat.lt_or_ge i c with hlt | hge
                · -- below the cutoff, resolve ρ i is assumption-slot: its frees
                  -- stay under countKeep — contradicting k - 1 ≥ countKeep.
                  rw [resolve_removeAt_lo ρ c i hlt] at h2
                  have hi' := TyP.termFree_lt D hi
                  have hbnd := resolve_frees_lt hfits
                    (fun s hs => match assumptionPrefix_getElem hap_c
                        (by omega : s < c) (by omega : s < Γ.length) with
                      | ⟨t, ht⟩ =>
                        insertAt_getElem?_assumption_lo (by omega) ht) hlt
                    (by
                      rw [insertAt_length]; omega) h2
                  exact (by omega : False).elim
                · have h2' : EFree k (resolve ρ (i + 1)) :=
                    resolve_removeAt_hi_keep ρ c i hge hkc ▸
                      (efree_lift _ _).mpr (.inr ⟨h'.1, h2⟩)
                  exact ⟨i + 1, nfree_lift_of (.inr ⟨by omega, hi⟩), h2'⟩
          | drop =>
              rw [eps_wk_not_keep (.inr (.inl hkc))] at hk
              obtain ⟨i, hi, h2⟩ := TyP.eps_support D σ hD_ap (removeAt ρ c)
                  (displayFits_wk hfits) k hk
              rcases Nat.lt_or_ge i c with hlt | hge
              · rw [resolve_removeAt_lo ρ c i hlt] at h2
                exact ⟨i, nfree_lift_of (.inl ⟨hlt, hi⟩), h2⟩
              · rw [resolve_removeAt_hi_drop ρ c i hge hkc] at h2
                exact ⟨i + 1, nfree_lift_of (.inr ⟨by omega, hi⟩), h2⟩
          | inline v =>
              rw [eps_wk_not_keep (.inr (.inr ⟨v, hkc⟩))] at hk
              obtain ⟨i, hi, h2⟩ := TyP.eps_support D σ hD_ap (removeAt ρ c)
                  (displayFits_wk hfits) k hk
              rcases Nat.lt_or_ge i c with hlt | hge
              · rw [resolve_removeAt_lo ρ c i hlt] at h2
                exact ⟨i, nfree_lift_of (.inl ⟨hlt, hi⟩), h2⟩
              · rw [resolve_removeAt_hi_inline ρ c i v hge hkc] at h2
                exact ⟨i + 1, nfree_lift_of (.inr ⟨by omega, hi⟩), h2⟩
  | .esub _ _ Γ _ _ _ v j u D hget hv hvT, σ, hap, ρ, hfits, k, hk => by
      obtain ⟨hap_j, hD_ap, hv_ap, -⟩ := hap
      have hj := getElem?_lt_length hget
      have hjl : j ≤ ρ.length := by
        have := DisplayFits.length_le hfits
        rw [substRemove_length_lt hj] at this
        omega
      have hassum : ∀ s', s' < j → ∃ t, (substRemove v j Γ)[s']? =
          some (.assumption t) := by
        intro s hs
        obtain ⟨t, ht⟩ := assumptionPrefix_getElem hap_j hs (by omega)
        exact substRemove_getElem?_assumption_lo hs ht
      cases hu : levelIsZero (σ u) with
      | true =>
          rw [eps_esub_drop hu] at hk
          obtain ⟨i, hi, h2⟩ := TyP.eps_support D σ hD_ap
              (insertDisp .drop j ρ) (displayFits_esub_drop hget hfits) k hk
          rcases Nat.lt_trichotomy i j with hlt | heq | hgt
          · rw [resolve_insertDisp_lo .drop ρ j i hlt hjl] at h2
            exact ⟨i, nfree_instantiate_of (.inl ⟨hlt, hi⟩), h2⟩
          · rw [heq] at h2
            rw [resolve_insertDisp_drop_hit ρ j hjl] at h2
            exact False.elim h2
          · obtain ⟨i₀, rfl, hge'⟩ : ∃ i₀, i = i₀ + 1 ∧ j ≤ i₀ :=
              ⟨i - 1, (Nat.sub_add_cancel (Nat.zero_lt_of_lt hgt)).symm, Nat.le_sub_one_of_lt hgt⟩
            rw [resolve_insertDisp_hi_drop ρ j i₀ hge' hjl] at h2
            exact ⟨i₀, nfree_instantiate_of (.inr (.inl ⟨hge', hi⟩)), h2⟩
      | false =>
          rw [eps_esub_keep hu] at hk
          rcases efree_inst hk with h' | h' | h'
          · -- k < κ ∧ EFree k q' — the query side, low slot.
            obtain ⟨i, hi, h2⟩ := TyP.eps_support D σ hD_ap
                (insertDisp .keep j ρ) (displayFits_esub_keep hget hfits) k h'.2
            rcases Nat.lt_trichotomy i j with hlt | heq | hgt
            · rw [resolve_insertDisp_lo .keep ρ j i hlt hjl] at h2
              exact ⟨i, nfree_instantiate_of (.inl ⟨hlt, hi⟩), h2⟩
            · rw [heq] at h2
              rw [resolve_insertDisp_keep_hit ρ j hjl] at h2
              have : k = countKeep (ρ.take j) := h2
              exact (by omega : False).elim
            · obtain ⟨i₀, rfl, hge'⟩ : ∃ i₀, i = i₀ + 1 ∧ j ≤ i₀ :=
                ⟨i - 1, (Nat.sub_add_cancel (Nat.zero_lt_of_lt hgt)).symm, Nat.le_sub_one_of_lt hgt⟩
              rw [resolve_insertDisp_hi_keep ρ j i₀ hge' hjl] at h2
              rcases (efree_lift _ _).mp h2 with h'' | h''
              · exact ⟨i₀, nfree_instantiate_of (.inr (.inl ⟨hge', hi⟩)), h''.2⟩
              · exact absurd h''.1 (by omega)
          · -- κ ≤ k ∧ EFree (k+1) q' — the query side, shifted high slot.
            obtain ⟨i, hi, h2⟩ := TyP.eps_support D σ hD_ap
                (insertDisp .keep j ρ) (displayFits_esub_keep hget hfits)
                (k + 1) h'.2
            rcases Nat.lt_trichotomy i j with hlt | heq | hgt
            · rw [resolve_insertDisp_lo .keep ρ j i hlt hjl] at h2
              have hbnd := resolve_frees_lt hfits
                (fun s hs => hassum s (by omega : s < j)) hlt
                (by rw [substRemove_length_lt hj]; omega) h2
              exact (by omega : False).elim
            · rw [heq] at h2
              rw [resolve_insertDisp_keep_hit ρ j hjl] at h2
              have : k + 1 = countKeep (ρ.take j) := h2
              exact (by omega : False).elim
            · obtain ⟨i₀, rfl, hge'⟩ : ∃ i₀, i = i₀ + 1 ∧ j ≤ i₀ :=
                ⟨i - 1, (Nat.sub_add_cancel (Nat.zero_lt_of_lt hgt)).symm, Nat.le_sub_one_of_lt hgt⟩
              rw [resolve_insertDisp_hi_keep ρ j i₀ hge' hjl] at h2
              rcases (efree_lift _ _).mp h2 with h'' | h''
              · exact (by omega : False).elim
              · rw [Nat.add_sub_cancel] at h''
                exact ⟨i₀, nfree_instantiate_of (.inr (.inl ⟨hge', hi⟩)), h''.2⟩
          · -- EFree κ q' ∧ EFree k r — the index-j slot occurs; the freed index
            -- k lands in the replacement's support.
            obtain ⟨hocc, hr⟩ := h'
            obtain ⟨i, hi, h2⟩ := TyP.eps_support D σ hD_ap
                (insertDisp .keep j ρ) (displayFits_esub_keep hget hfits)
                (countKeep (ρ.take j)) hocc
            rcases Nat.lt_trichotomy i j with hlt | heq | hgt
            · rw [resolve_insertDisp_lo .keep ρ j i hlt hjl] at h2
              have hbnd := resolve_frees_lt hfits
                (fun s hs => hassum s (by omega : s < j)) hlt
                (by rw [substRemove_length_lt hj]; omega) h2
              exact (by omega : False).elim
            · rw [heq] at hi
              -- hi : NFree j e — the occurrence; hr routes to hv's support.
              obtain ⟨i', hi', h2'⟩ := TyP.eps_support hv σ hv_ap ρ hfits k hr
              exact ⟨i', nfree_instantiate_of (.inr (.inr ⟨hi, hi'⟩)), h2'⟩
            · obtain ⟨i₀, rfl, hge'⟩ : ∃ i₀, i = i₀ + 1 ∧ j ≤ i₀ :=
                ⟨i - 1, (Nat.sub_add_cancel (Nat.zero_lt_of_lt hgt)).symm, Nat.le_sub_one_of_lt hgt⟩
              rw [resolve_insertDisp_hi_keep ρ j i₀ hge' hjl] at h2
              rcases (efree_lift _ _).mp h2 with h'' | h''
              · exact (by omega : False).elim
              · exact (by omega : False).elim
  | .lsub _ _ Γ _ _ _ v j _ D hget hv hvT, σ, hap, ρ, hfits, k, hk => by
      obtain ⟨hap_j, hD_ap, hv_ap, -⟩ := hap
      have hj := getElem?_lt_length hget
      have hjl : j ≤ ρ.length := by
        have := DisplayFits.length_le hfits
        rw [substRemove_length_lt hj] at this
        omega
      have hassum : ∀ s', s' < j → ∃ t, (substRemove v j Γ)[s']? =
          some (.assumption t) := by
        intro s hs
        obtain ⟨t, ht⟩ := assumptionPrefix_getElem hap_j hs (by omega)
        exact substRemove_getElem?_assumption_lo hs ht
      rw [lsub_eps_eq D hget hv hvT σ ρ] at hk
      by_cases hst : hv.eps σ ρ = .star
      · rw [hst] at hk
        -- lsubDisp κ .star = .drop — defeq; phrase the fit for the same term.
        obtain ⟨i, hi, h2⟩ := TyP.eps_support D σ hD_ap
            (insertDisp .drop j ρ)
            (displayFits_lsub_drop hget hfits) k hk
        rcases Nat.lt_trichotomy i j with hlt | heq | hgt
        · rw [resolve_insertDisp_lo _ ρ j i hlt hjl] at h2
          exact ⟨i, nfree_instantiate_of (.inl ⟨hlt, hi⟩), h2⟩
        · rw [heq] at h2
          rw [resolve_insertDisp_drop_hit ρ j hjl] at h2
          exact False.elim h2
        · obtain ⟨i₀, rfl, hge'⟩ : ∃ i₀, i = i₀ + 1 ∧ j ≤ i₀ :=
            ⟨i - 1, (Nat.sub_add_cancel (Nat.zero_lt_of_lt hgt)).symm, Nat.le_sub_one_of_lt hgt⟩
          rw [resolve_insertDisp_hi_drop ρ j i₀ hge' hjl] at h2
          exact ⟨i₀, nfree_instantiate_of (.inr (.inl ⟨hge', hi⟩)), h2⟩
      · have hl : lsubDisp (countKeep (ρ.take j)) (hv.eps σ ρ) =
            .inline (localize (countKeep (ρ.take j)) (hv.eps σ ρ)) := by
          cases hve : hv.eps σ ρ <;> simp_all [lsubDisp]
        rw [hl] at hk
        obtain ⟨i, hi, h2⟩ := TyP.eps_support D σ hD_ap
            (insertDisp (.inline (localize (countKeep (ρ.take j))
              (hv.eps σ ρ))) j ρ)
            (displayFits_lsub_inline hget hfits) k hk
        rcases Nat.lt_trichotomy i j with hlt | heq | hgt
        · rw [resolve_insertDisp_lo _ ρ j i hlt hjl] at h2
          exact ⟨i, nfree_instantiate_of (.inl ⟨hlt, hi⟩), h2⟩
        · rw [heq] at h2
          rw [heq] at hi
          -- the hit slot: resolve gives (localize κ r).lift 0 κ = restore κ r —
          -- free_restore_iff decodes it back to r's own support.
          rw [resolve_insertDisp_inline j _ ρ hjl] at h2
          have hr : EFree k (restore (countKeep (ρ.take j)) (hv.eps σ ρ)) := h2
          have hrr := (free_restore_iff k _ _).mp hr
          obtain ⟨i', hi', h2'⟩ := TyP.eps_support hv σ hv_ap ρ hfits k hrr.1
          exact ⟨i', nfree_instantiate_of (.inr (.inr ⟨hi, hi'⟩)), h2'⟩
        · obtain ⟨i₀, rfl, hge'⟩ : ∃ i₀, i = i₀ + 1 ∧ j ≤ i₀ :=
            ⟨i - 1, (Nat.sub_add_cancel (Nat.zero_lt_of_lt hgt)).symm, Nat.le_sub_one_of_lt hgt⟩
          rw [resolve_insertDisp_hi_inline ρ j i₀ _ hge' hjl] at h2
          exact ⟨i₀, nfree_instantiate_of (.inr (.inl ⟨hge', hi⟩)), h2⟩
  | .linst _ _ _ _ _ _ ls _ _ D, σ, hD_ap, ρ, hfits, k, hk => by
      rw [eps_linst σ ρ] at hk
      obtain ⟨i, hi, h2⟩ := TyP.eps_support D _ hD_ap ρ
          (displayFits_linst ls hfits) k hk
      exact ⟨i, nfree_instLevels_rev ls hi, h2⟩
  | .ewk _ _ _ _ _ _ _ D, σ, hD_ap, ρ, hfits, k, hk => by
      rw [eps_ewk σ ρ] at hk
      exact TyP.eps_support D σ hD_ap ρ hfits k hk
  | .cctx _ _ _ _ _ _ _ _ D _, σ, hap, ρ, hfits, k, hk => by
      obtain ⟨hD_ap, -⟩ := hap
      rw [eps_cctx σ ρ] at hk
      exact TyP.eps_support D σ hD_ap ρ
        (DisplayFits.assumption_congr hfits) k hk
  termination_by structural D _ _ _ _ _ _ => D

/-- A free index of `lift 0 j v` sits at or above `j`. -/
theorem nfree_lift_zero_ge {v : Expr Nat} {i j : Nat} :
    NFree i (lift 0 j v) → j ≤ i := by
  intro h
  rcases nfree_lift h with h' | h'
  · exact absurd h'.1 (Nat.not_lt_zero _)
  · simp only [Nat.zero_add] at h'
    exact h'.1

/-- If every free index of `q` misses the window `[d, d + κ)`, `q` avoids the
    prefix — the pointwise-to-structural bridge for `AvoidPrefix`. -/
theorem avoidPrefix_of_efree {q : ETm} {κ d : Nat}
    (h : ∀ i, EFree i q → i < d ∨ d + κ ≤ i) : AvoidPrefix κ d q := by
  induction q generalizing d with
  | bvar m => exact h m rfl
  | star => trivial
  | sort _ => trivial
  | const _ _ => trivial
  | app f a ihf iha =>
      exact ⟨ihf (fun i hi => h i (.inl hi)), iha (fun i hi => h i (.inr hi))⟩
  | lam b ihb =>
      apply ihb
      intro i hi
      cases i with
      | zero => exact .inl (Nat.zero_lt_succ _)
      | succ i' =>
          have hq : EFree i' (.lam b) := by
            simp only [EFree]; exact hi
          rcases h i' hq with h' | h'
          · exact .inl (by omega)
          · exact .inr (by omega)
  | pi a b iha ihb =>
      refine ⟨iha (fun i hi => h i (.inl hi)), ihb ?_⟩
      intro i hi
      cases i with
      | zero => exact .inl (Nat.zero_lt_succ _)
      | succ i' =>
          have hq : EFree i' (.pi a b) := by
            simp only [EFree]; exact .inr hi
          rcases h i' hq with h' | h'
          · exact .inl (by omega)
          · exact .inr (by omega)

/-- S14 §6: the original `lsub` value's erasure avoids the erased prefix —
    every free index of `hv.eps σ ρ` is at or above `κ = countKeep (ρ.take j)`.
    Composed from `eps_support`, `nfree_lift_zero_ge` (the `lift 0 j v` subject
    carries no index below `j`), and `resolve_suffix`. No `AvoidPrefix` of `hv`
    is assumed and no suffix typing is needed. -/
theorem shifted_value_scope {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t v : Expr Nat} {j : Nat} (σ : Level → Level)
    {ρ : List Disp}
    (hget : Γ[j]? = some (.letBinding t v))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hAP : hv.AssumpPref)
    (hρ : DisplayFits (substRemove v j Γ) ρ) :
    AvoidPrefix (countKeep (ρ.take j)) 0 (hv.eps σ ρ) := by
  have hj := getElem?_lt_length hget
  have hjl : j ≤ ρ.length := by
    have := DisplayFits.length_le hρ
    rw [substRemove_length_lt hj] at this
    omega
  apply avoidPrefix_of_efree
  intro x hx
  obtain ⟨i, hi, h2⟩ := TyP.eps_support hv σ hAP ρ hρ x hx
  have hji : j ≤ i := nfree_lift_zero_ge hi
  obtain ⟨i₀, rfl⟩ : ∃ i₀, i = j + i₀ := ⟨i - j, by omega⟩
  rw [resolve_suffix ρ j i₀ hjl] at h2
  rcases (efree_lift _ _).mp h2 with h' | h'
  · exact absurd h'.1 (Nat.not_lt_zero _)
  · right
    have : 0 + countKeep (ρ.take j) ≤ x := h'.1
    simp only [Nat.zero_add] at this
    omega

end Rcic.Syn

#print axioms Rcic.Syn.nfree_lift_of
#print axioms Rcic.Syn.nfree_instantiate_of
#print axioms Rcic.Syn.nfree_instLevels_rev
#print axioms Rcic.Syn.nfree_natExpand
#print axioms Rcic.Syn.efree_inst
#print axioms Rcic.Syn.mem_take_of_getElem?
#print axioms Rcic.Syn.assumptionPrefix_getElem
#print axioms Rcic.Syn.substRemove_getElem?_assumption_lo
#print axioms Rcic.Syn.insertAt_getElem?_assumption_lo
#print axioms Rcic.Syn.efree_appOut
#print axioms Rcic.Syn.efree_lamOut
#print axioms Rcic.Syn.DisplayFits.assumption_congr
#print axioms Rcic.Syn.nfree_lift_zero_ge
#print axioms Rcic.Syn.resolve_frees_lt
#print axioms Rcic.Syn.resolve_insertDisp_keep_hit
#print axioms Rcic.Syn.resolve_insertDisp_drop_hit
#print axioms Rcic.Syn.TyP.eps_support
#print axioms Rcic.Syn.avoidPrefix_of_efree
#print axioms Rcic.Syn.shifted_value_scope

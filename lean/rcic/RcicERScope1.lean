import rcic.RcicERScope0
import rcic.RcicSynTable
import rcic.RcicSynBelowBoundary

/-!
# SCOPE-1 — `DisplayFits` and `termFree_lt` (S14 §3, §5, §7; #7369)

The shifted-value-scope route needs a structural context/display fit that is
weaker than `DispShape`: a `TyP.wk` at a cutoff *past* the source context is
still a legal `AssumpPref` input (`AssumptionPrefix` never includes
`c ≤ Γ.length`), so the target display is allowed to be longer than the source
context. `DisplayFits` is exactly §3's inductive — `nil` accepts any tail —
and this module proves:

- `DisplayFits.of_dispShape` / `DisplayFits.length_le` live in
  `RcicSynBelowBoundary` (batch 135) — defined once there, reused here.
- `displayFits_wk` — the `wk` edge: `insertAt` on the context, `removeAt` on
  the display, in either range. This is the out-of-range-`wk` support step of
  §5: the structural fit survives even when `removeAt` does not land on the
  inserted slot.
- `displayFits_insertDisp_assumption` / `displayFits_insertDisp_letBinding`
  and the four real `esub`/`lsub` call shapes (`_keep`, `_drop`, `_inline`):
  `substRemove` on the context, `insertDisp` on the display.
- `TyP.termFree_lt` (§5): any free de Bruijn index of the subject is below
  the context length — premise-free, only `NFree` from SCOPE-0 (`#7374`).
  The `wk` arm goes through `nfree_lift`; `esub`/`lsub` through
  `nfree_instantiate`; `linst` through `nfree_instLevels`.

No `isTransport`-free premise, no `c ≤ Γ.length` anywhere, `closure_claim = 0`.
-/

namespace Rcic.Syn
open Rcic.Declarative

/-! ## §1 `DisplayFits` (S14 §3) — defined once in `RcicSynBelowBoundary` -/

-- `DisplayFits`, `DisplayFits.length_le`, `DisplayFits.of_dispShape` are
-- imported from `rcic.RcicSynBelowBoundary` (batch 135); the inductive there
-- is S14 §3's verbatim shape — `nil` accepts any display tail.

/-! ## §2 length and lookup arithmetic -/

theorem insertAt_length (d : LocalDecl) (c : Nat) (Γ : LCtx) :
    (insertAt d c Γ).length = Γ.length + 1 := by
  induction Γ generalizing c with
  | nil => cases c <;> rfl
  | cons x Γ' ih =>
      cases c with
      | zero => rfl
      | succ c' => simp only [insertAt_succ_cons, List.length_cons, ih]

theorem substRemove_length_lt {v : Expr Nat} {j : Nat} {Γ : LCtx}
    (hj : j < Γ.length) : (substRemove v j Γ).length = Γ.length - 1 := by
  induction Γ generalizing j with
  | nil => exact absurd hj (Nat.not_lt_zero _)
  | cons x Γ' ih =>
      cases j with
      | zero => simp only [substRemove_zero_cons, List.length_cons]; omega
      | succ j' =>
          have hj' : j' < Γ'.length := by
            simp only [List.length_cons] at hj; omega
          simp only [substRemove_succ_cons, List.length_cons]
          rw [ih hj']
          omega

theorem lookupType_lt_length {Γ : LCtx} {i : Nat} {A : Expr Nat}
    (h : lookupType Γ i = some A) : i < Γ.length := by
  by_cases hi : i < Γ.length
  · exact hi
  · unfold lookupType at h
    rw [List.get?_eq_none.mpr (by omega : Γ.length ≤ i)] at h
    exact Option.noConfusion h

theorem getElem?_lt_length {α : Type} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : i < l.length :=
  (List.getElem?_eq_some_iff.mp h).1

/-! ## §3 preservation under the real transport shapes -/

/-- The `wk` edge: the source call erases against `removeAt ρ c`, where the
    target context `insertAt d c Γ` fitted `ρ`. Holds for every `c` — when the
    cutoff is out of range, `insertAt` lands the entry at the end and the tail
    is absorbed by `DisplayFits.nil`; when `removeAt` reaches past `ρ` the
    first `Γ.length` aligned entries are untouched. -/
theorem displayFits_wk {d : LocalDecl} {c : Nat} {Γ : LCtx} {ρ : List Disp}
    (h : DisplayFits (insertAt d c Γ) ρ) : DisplayFits Γ (removeAt ρ c) := by
  induction Γ generalizing c ρ with
  | nil => exact .nil _
  | cons x Γ' ih =>
      cases c with
      | zero =>
          simp only [insertAt_zero] at h
          cases h with
          | assumptionKeep h₀ => exact h₀
          | assumptionDrop h₀ => exact h₀
          | letDrop h₀ => exact h₀
          | letInline h₀ => exact h₀
      | succ c' =>
          simp only [insertAt_succ_cons] at h
          cases x with
          | assumption A =>
              cases h with
              | assumptionKeep h₀ => exact .assumptionKeep (ih h₀)
              | assumptionDrop h₀ => exact .assumptionDrop (ih h₀)
          | letBinding A v =>
              cases h with
              | letDrop h₀ => exact .letDrop (ih h₀)
              | letInline h₀ => exact .letInline (ih h₀)

/-- The `esub`/`lsub` edge, assumption entry: the source context
    `substRemove v j Γ` fitted `ρ`, and the main derivation erases against
    `insertDisp d j ρ` — the removed `.assumption` slot takes `keep` or
    `drop`. -/
theorem displayFits_insertDisp_assumption {v t : Expr Nat} {j : Nat} {Γ : LCtx}
    {ρ : List Disp} {d : Disp} (hd : d = .keep ∨ d = .drop)
    (hget : Γ[j]? = some (.assumption t)) (h : DisplayFits (substRemove v j Γ) ρ) :
    DisplayFits Γ (insertDisp d j ρ) := by
  induction Γ generalizing j ρ with
  | nil => simp at hget
  | cons x Γ' ih =>
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst hget
          rcases hd with rfl | rfl
          · exact .assumptionKeep h
          · exact .assumptionDrop h
      | succ j' =>
          simp only [List.getElem?_cons_succ] at hget
          cases x with
          | assumption A =>
              simp only [substRemove_succ_cons, instDecl] at h
              cases h with
              | assumptionKeep h₀ => exact .assumptionKeep (ih hget h₀)
              | assumptionDrop h₀ => exact .assumptionDrop (ih hget h₀)
          | letBinding A _w =>
              simp only [substRemove_succ_cons, instDecl] at h
              cases h with
              | letDrop h₀ => exact .letDrop (ih hget h₀)
              | letInline h₀ => exact .letInline (ih hget h₀)

/-- The `lsub` edge, let-binding entry: the removed `.letBinding` slot takes
    `drop` or `inline r`. -/
theorem displayFits_insertDisp_letBinding {v t : Expr Nat} {j : Nat} {Γ : LCtx}
    {ρ : List Disp} {d : Disp} (hd : d = .drop ∨ ∃ r, d = .inline r)
    (hget : Γ[j]? = some (.letBinding t v)) (h : DisplayFits (substRemove v j Γ) ρ) :
    DisplayFits Γ (insertDisp d j ρ) := by
  induction Γ generalizing j ρ with
  | nil => simp at hget
  | cons x Γ' ih =>
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst hget
          rcases hd with rfl | ⟨r, rfl⟩
          · exact .letDrop h
          · exact .letInline h
      | succ j' =>
          simp only [List.getElem?_cons_succ] at hget
          cases x with
          | assumption A =>
              simp only [substRemove_succ_cons, instDecl] at h
              cases h with
              | assumptionKeep h₀ => exact .assumptionKeep (ih hget h₀)
              | assumptionDrop h₀ => exact .assumptionDrop (ih hget h₀)
          | letBinding A _w =>
              simp only [substRemove_succ_cons, instDecl] at h
              cases h with
              | letDrop h₀ => exact .letDrop (ih hget h₀)
              | letInline h₀ => exact .letInline (ih hget h₀)

theorem displayFits_esub_keep {v t : Expr Nat} {j : Nat} {Γ : LCtx} {ρ : List Disp}
    (hget : Γ[j]? = some (.assumption t)) (h : DisplayFits (substRemove v j Γ) ρ) :
    DisplayFits Γ (insertDisp .keep j ρ) :=
  displayFits_insertDisp_assumption (.inl rfl) hget h

theorem displayFits_esub_drop {v t : Expr Nat} {j : Nat} {Γ : LCtx} {ρ : List Disp}
    (hget : Γ[j]? = some (.assumption t)) (h : DisplayFits (substRemove v j Γ) ρ) :
    DisplayFits Γ (insertDisp .drop j ρ) :=
  displayFits_insertDisp_assumption (.inr rfl) hget h

theorem displayFits_lsub_drop {v t : Expr Nat} {j : Nat} {Γ : LCtx} {ρ : List Disp}
    (hget : Γ[j]? = some (.letBinding t v)) (h : DisplayFits (substRemove v j Γ) ρ) :
    DisplayFits Γ (insertDisp .drop j ρ) :=
  displayFits_insertDisp_letBinding (.inl rfl) hget h

theorem displayFits_lsub_inline {v t : Expr Nat} {j : Nat} {Γ : LCtx} {ρ : List Disp}
    {r : ETm} (hget : Γ[j]? = some (.letBinding t v))
    (h : DisplayFits (substRemove v j Γ) ρ) :
    DisplayFits Γ (insertDisp (.inline r) j ρ) :=
  displayFits_insertDisp_letBinding (.inr ⟨r, rfl⟩) hget h

/-- The `linst` edge: `instLvlsCtx` preserves declaration kinds, so the target
    fit transports back to the source for arbitrary `ls`, `Γ`, `ρ` — no source
    validity, no exact length; structural induction on `Γ`. -/
theorem displayFits_linst (ls : List Level) :
    {Γ : LCtx} → {ρ : List Disp} →
    DisplayFits (instLvlsCtx ls Γ) ρ → DisplayFits Γ ρ
  | [], _, h => by
      cases h
      exact .nil _
  | .assumption _ :: _, _, h => by
      cases h with
      | assumptionKeep h₀ => exact .assumptionKeep (displayFits_linst ls h₀)
      | assumptionDrop h₀ => exact .assumptionDrop (displayFits_linst ls h₀)
  | .letBinding _ _ :: _, _, h => by
      cases h with
      | letDrop h₀ => exact .letDrop (displayFits_linst ls h₀)
      | letInline h₀ => exact .letInline (displayFits_linst ls h₀)

/-! ## §4 `NFree` structural algebra -/

/-- `lift c k` pushes every free index `≥ c` up by `k`: a free `i` of the
    lifted term is either an untouched low index (`i < c`) or a high index
    lowered by `k` (`c + k ≤ i`, `NFree (i - k)` of the source). -/
theorem nfree_lift {c k i : Nat} {e : Expr Nat} :
    NFree i (lift c k e) → (i < c ∧ NFree i e) ∨ (c + k ≤ i ∧ NFree (i - k) e) := by
  induction e generalizing c k i with
  | bvar j =>
      intro hi
      simp only [lift] at hi
      by_cases hc : c ≤ j
      · rw [if_pos hc] at hi
        have hij : i = j + k := hi
        exact .inr ⟨by omega, by show i - k = j; omega⟩
      · rw [if_neg hc] at hi
        have hij : i = j := hi
        exact .inl ⟨by omega, hi⟩
  | sort l => intro hi; exact hi.elim
  | const r ls => intro hi; exact hi.elim
  | app f a ihf iha =>
      intro hi
      have h' : NFree i (lift c k f) ∨ NFree i (lift c k a) := hi
      rcases h' with h' | h'
      · rcases ihf h' with h | h
        · exact .inl ⟨h.1, .inl h.2⟩
        · exact .inr ⟨h.1, .inl h.2⟩
      · rcases iha h' with h | h
        · exact .inl ⟨h.1, .inr h.2⟩
        · exact .inr ⟨h.1, .inr h.2⟩
  | lam A b ihA ihb =>
      intro hi
      have h' : NFree i (lift c k A) ∨ NFree (i + 1) (lift (c + 1) k b) := hi
      rcases h' with h' | h'
      · rcases ihA h' with h | h
        · exact .inl ⟨h.1, .inl h.2⟩
        · exact .inr ⟨h.1, .inl h.2⟩
      · rcases ihb h' with h | h
        · exact .inl ⟨by omega, .inr h.2⟩
        · refine .inr ⟨by omega, .inr ?_⟩
          have he : i + 1 - k = i - k + 1 := by omega
          rw [he] at h
          exact h.2
  | pi A B ihA ihB =>
      intro hi
      have h' : NFree i (lift c k A) ∨ NFree (i + 1) (lift (c + 1) k B) := hi
      rcases h' with h' | h'
      · rcases ihA h' with h | h
        · exact .inl ⟨h.1, .inl h.2⟩
        · exact .inr ⟨h.1, .inl h.2⟩
      · rcases ihB h' with h | h
        · exact .inl ⟨by omega, .inr h.2⟩
        · refine .inr ⟨by omega, .inr ?_⟩
          have he : i + 1 - k = i - k + 1 := by omega
          rw [he] at h
          exact h.2
  | letE A v b ihA ihv ihb =>
      intro hi
      have h' : NFree i (lift c k A) ∨
          NFree i (lift c k v) ∨ NFree (i + 1) (lift (c + 1) k b) := hi
      rcases h' with h' | h' | h'
      · rcases ihA h' with h | h
        · exact .inl ⟨h.1, .inl h.2⟩
        · exact .inr ⟨h.1, .inl h.2⟩
      · rcases ihv h' with h | h
        · exact .inl ⟨h.1, .inr (.inl h.2)⟩
        · exact .inr ⟨h.1, .inr (.inl h.2)⟩
      · rcases ihb h' with h | h
        · exact .inl ⟨by omega, .inr (.inr h.2)⟩
        · refine .inr ⟨by omega, .inr (.inr ?_)⟩
          have he : i + 1 - k = i - k + 1 := by omega
          rw [he] at h
          exact h.2
  | lit t => intro hi; exact hi.elim

/-- Under a binder the replacement is `lift 0 1 r`; a free `i + 1` of it is a
    free `i` of `r`. -/
theorem nfree_lift_zero_one_succ {r : Expr Nat} {i : Nat}
    (h : NFree (i + 1) (lift 0 1 r)) : NFree i r := by
  rcases nfree_lift h with h0 | h1
  · exact absurd h0.1 (Nat.not_lt_zero _)
  · rw [Nat.add_sub_cancel] at h1
    exact h1.2

/-- `instantiate j r` replaces index `j`, lowers higher indices by one: a free
    `i` of the result is either an untouched low index, a high index that came
    down from `i + 1`, or a free index of the replacement `r` itself. -/
theorem nfree_instantiate {r e : Expr Nat} {i j : Nat} :
    NFree i (instantiate j r e) →
      (i < j ∧ NFree i e) ∨ (j ≤ i ∧ NFree (i + 1) e) ∨ NFree i r := by
  induction e generalizing i j r with
  | bvar m =>
      intro hi
      simp only [instantiate] at hi
      by_cases hm : m = j
      · rw [if_pos hm] at hi
        exact .inr (.inr hi)
      · rw [if_neg hm] at hi
        by_cases hjm : j < m
        · rw [if_pos hjm] at hi
          have hij : i = m - 1 := hi
          refine .inr (.inl ⟨by omega, ?_⟩)
          show i + 1 = m
          omega
        · rw [if_neg hjm] at hi
          have hij : i = m := hi
          exact .inl ⟨by omega, hi⟩
  | sort l => intro hi; exact hi.elim
  | const c ls => intro hi; exact hi.elim
  | app f a ihf iha =>
      intro hi
      have h' : NFree i (instantiate j r f) ∨ NFree i (instantiate j r a) := hi
      rcases h' with h' | h'
      · rcases ihf h' with h | h | h
        · exact .inl ⟨h.1, .inl h.2⟩
        · exact .inr (.inl ⟨h.1, .inl h.2⟩)
        · exact .inr (.inr h)
      · rcases iha h' with h | h | h
        · exact .inl ⟨h.1, .inr h.2⟩
        · exact .inr (.inl ⟨h.1, .inr h.2⟩)
        · exact .inr (.inr h)
  | lam A b ihA ihb =>
      intro hi
      have h' : NFree i (instantiate j r A) ∨
          NFree (i + 1) (instantiate (j + 1) (lift 0 1 r) b) := hi
      rcases h' with h' | h'
      · rcases ihA h' with h | h | h
        · exact .inl ⟨h.1, .inl h.2⟩
        · exact .inr (.inl ⟨h.1, .inl h.2⟩)
        · exact .inr (.inr h)
      · rcases ihb h' with h | h | h
        · exact .inl ⟨by omega, .inr h.2⟩
        · exact .inr (.inl ⟨by omega, .inr h.2⟩)
        · exact .inr (.inr (nfree_lift_zero_one_succ h))
  | pi A B ihA ihB =>
      intro hi
      have h' : NFree i (instantiate j r A) ∨
          NFree (i + 1) (instantiate (j + 1) (lift 0 1 r) B) := hi
      rcases h' with h' | h'
      · rcases ihA h' with h | h | h
        · exact .inl ⟨h.1, .inl h.2⟩
        · exact .inr (.inl ⟨h.1, .inl h.2⟩)
        · exact .inr (.inr h)
      · rcases ihB h' with h | h | h
        · exact .inl ⟨by omega, .inr h.2⟩
        · exact .inr (.inl ⟨by omega, .inr h.2⟩)
        · exact .inr (.inr (nfree_lift_zero_one_succ h))
  | letE A v b ihA ihv ihb =>
      intro hi
      have h' : NFree i (instantiate j r A) ∨ NFree i (instantiate j r v) ∨
          NFree (i + 1) (instantiate (j + 1) (lift 0 1 r) b) := hi
      rcases h' with h' | h' | h'
      · rcases ihA h' with h | h | h
        · exact .inl ⟨h.1, .inl h.2⟩
        · exact .inr (.inl ⟨h.1, .inl h.2⟩)
        · exact .inr (.inr h)
      · rcases ihv h' with h | h | h
        · exact .inl ⟨h.1, .inr (.inl h.2)⟩
        · exact .inr (.inl ⟨h.1, .inr (.inl h.2)⟩)
        · exact .inr (.inr h)
      · rcases ihb h' with h | h | h
        · exact .inl ⟨by omega, .inr (.inr h.2)⟩
        · exact .inr (.inl ⟨by omega, .inr (.inr h.2)⟩)
        · exact .inr (.inr (nfree_lift_zero_one_succ h))
  | lit t => intro hi; exact hi.elim

/-- Level instantiation does not move term free indices. -/
theorem nfree_instLevels {ls : List Level} {e : Expr Nat} {i : Nat} :
    NFree i (instantiateLevels ls e) → NFree i e := by
  induction e generalizing i with
  | bvar j => exact id
  | sort l => exact id
  | const r ms => exact id
  | app f a ihf iha =>
      intro hi
      have h' : NFree i (instantiateLevels ls f) ∨ NFree i (instantiateLevels ls a) := hi
      rcases h' with h' | h'
      · exact .inl (ihf h')
      · exact .inr (iha h')
  | lam A b ihA ihb =>
      intro hi
      have h' : NFree i (instantiateLevels ls A) ∨ NFree (i + 1) (instantiateLevels ls b) := hi
      rcases h' with h' | h'
      · exact .inl (ihA h')
      · exact .inr (ihb h')
  | pi A B ihA ihB =>
      intro hi
      have h' : NFree i (instantiateLevels ls A) ∨ NFree (i + 1) (instantiateLevels ls B) := hi
      rcases h' with h' | h'
      · exact .inl (ihA h')
      · exact .inr (ihB h')
  | letE A v b ihA ihv ihb =>
      intro hi
      have h' : NFree i (instantiateLevels ls A) ∨ NFree i (instantiateLevels ls v) ∨
          NFree (i + 1) (instantiateLevels ls b) := hi
      rcases h' with h' | h' | h'
      · exact .inl (ihA h')
      · exact .inr (.inl (ihv h'))
      · exact .inr (.inr (ihb h'))
  | lit t => exact id

/-! ## §5 `termFree_lt` -/

/-- §5's independent source-scope lemma: a free de Bruijn index of the typed
    subject is always below the context length. Premise-free — it reads only
    the original typing structure and the `bvar` lookup, no `EnvWfT`,
    `CtxWfT`, `AssumpPref` or hcoh. The `wk`/`esub`/`lsub`/`linst` arms ride
    the §4 algebra; every other arm is a direct recursion. (Written as a
    `match` like `TyP.eps`: `TyP` is mutual with `CvP`, so `induction` does
    not apply.) -/
theorem TyP.termFree_lt {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    {i : Nat} : (D : TyP E n Γ e T) → NFree i e → i < Γ.length
  | .sort _ _ _ _ _ _, hi => hi.elim
  | .bvar _ _ _ j _ _ h _, hi => by
      have hij : i = j := hi
      subst hij
      exact lookupType_lt_length h
  | .const _ _ _ _ _ _ _ _ _ _ _ _ _, hi => hi.elim
  | .pi _ _ _ A _ B _ hA hB, hi => by
      have h' : NFree i A ∨ NFree (i + 1) B := hi
      rcases h' with h' | h'
      · exact TyP.termFree_lt hA h'
      · have := TyP.termFree_lt hB h'
        simp only [List.length_cons] at this
        omega
  | .lam _ _ _ A _ body _ _ hA hbody _, hi => by
      have h' : NFree i A ∨ NFree (i + 1) body := hi
      rcases h' with h' | h'
      · exact TyP.termFree_lt hA h'
      · have := TyP.termFree_lt hbody h'
        simp only [List.length_cons] at this
        omega
  | .app _ _ _ f a _ _ _ hf ha _, hi => by
      have h' : NFree i f ∨ NFree i a := hi
      rcases h' with h' | h'
      · exact TyP.termFree_lt hf h'
      · exact TyP.termFree_lt ha h'
  | .letE _ _ _ A _ value _ body _ hA hv hb _, hi => by
      have h' : NFree i A ∨ NFree i value ∨ NFree (i + 1) body := hi
      rcases h' with h' | h' | h'
      · exact TyP.termFree_lt hA h'
      · exact TyP.termFree_lt hv h'
      · have := TyP.termFree_lt hb h'
        simp only [List.length_cons] at this
        omega
  | .lit _ _ _ _ _ _, hi => hi.elim
  | .conv _ _ _ _ _ _ _ h _, hi => TyP.termFree_lt h hi
  | .wk _ _ _ _ _ _ c D, hi => by
      rcases nfree_lift hi with ⟨hlt, hi'⟩ | ⟨hge, hi'⟩
      · rw [insertAt_length]
        exact Nat.lt_succ_of_lt (TyP.termFree_lt D hi')
      · rw [insertAt_length]
        have := TyP.termFree_lt D hi'
        omega
  | .esub _ _ _ _ _ _ _ j _ D hget hv _, hi => by
      have hj := getElem?_lt_length hget
      rcases nfree_instantiate hi with ⟨hlt, hi'⟩ | ⟨hge, hi'⟩ | hi'
      · rw [substRemove_length_lt hj]; omega
      · rw [substRemove_length_lt hj]
        have := TyP.termFree_lt D hi'
        omega
      · exact TyP.termFree_lt hv hi'
  | .lsub _ _ _ _ _ _ _ j _ D hget hv _, hi => by
      have hj := getElem?_lt_length hget
      rcases nfree_instantiate hi with ⟨hlt, hi'⟩ | ⟨hge, hi'⟩ | hi'
      · rw [substRemove_length_lt hj]; omega
      · rw [substRemove_length_lt hj]
        have := TyP.termFree_lt D hi'
        omega
      · exact TyP.termFree_lt hv hi'
  | .linst _ _ _ _ _ _ ls _ _ D, hi => by
      have := TyP.termFree_lt D (nfree_instLevels hi)
      simp only [instLvlsCtx, List.length_map]
      exact this
  | .ewk _ _ _ _ _ _ _ D, hi => TyP.termFree_lt D hi
  | .cctx _ _ _ _ _ _ _ _ D _, hi => by
      have := TyP.termFree_lt D hi
      exact this

end Rcic.Syn

#print axioms Rcic.Syn.DisplayFits.length_le
#print axioms Rcic.Syn.displayFits_wk
#print axioms Rcic.Syn.displayFits_linst
#print axioms Rcic.Syn.TyP.termFree_lt

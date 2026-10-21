import rcic.RcicSynSRBetaZetaEpsWNoWk

/-!
# epsW display lemmas: the `wk` re-frame vs `AssumpCut`

Two facts about `wkInnerDisp`, the display where `epsW`'s `wk` arm runs the
inner erasure:

* **The `AssumpCut` bridge** (`wkInnerDisp_eq_removeAt_of_shape`): when the
  display is shaped for the `wk`'s context and `AssumpCut Γ c` holds (the
  first `c` entries are `.assumption`s — exactly what `TyP.ClosedWf` demands
  of every `wk`), there is **no** inline entry at any `j < c`, so the
  re-frame pass changes nothing: `wkInnerDisp ρ c = removeAt ρ c`. Under the
  closed regime the repair is literally the identity; the re-frame only
  bites at non-`ClosedWf` displays (the canonical Entry dispositions of
  let-binding contexts, where the wedge lives).
* **Congruence** (`DispLvlEq.wkInnerDisp`): `wkInnerDisp` is `DispLvlEq`-
  congruent — the re-frame applies `ETm.inst r .star` to inline values, and
  `LvlEq.inst'` carries `LvlEq` through it pointwise. This is what the `wk`
  arm of `lvlEq_epsW` needs. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- `wkInnerGo` passes over entries with no `.inline` before the cutoff
    unchanged: it is exactly `removeAt`. -/
theorem wkInnerGo_eq_removeAt_of_keepOrDrop (k : Nat) {ρ : List Disp}
    (h : ∀ (j : Nat), j < k → ρ[j]? = some .keep ∨ ρ[j]? = some .drop) :
    ∀ (r : Nat), wkInnerGo r k ρ = removeAt ρ k := by
  induction k generalizing ρ with
  | zero => intro _; cases ρ <;> rfl
  | succ k ih =>
      intro r
      have h' : ∀ (j : Nat), j < k →
          ρ[j + 1]? = some .keep ∨ ρ[j + 1]? = some .drop :=
        fun j hj => h (j + 1) (Nat.succ_lt_succ hj)
      cases ρ with
      | nil => rfl
      | cons d ρ' =>
          have hd0 := h 0 (Nat.zero_lt_succ k)
          simp only [List.getElem?_cons_zero] at hd0
          cases hd0 with
          | inl hk =>
              injection hk with hk
              subst hk
              simp only [wkInnerGo, removeAt]
              have h'' : ∀ (j : Nat), j < k → ρ'[j]? = some .keep ∨ ρ'[j]? = some .drop := by
                intro j hj
                simpa only [List.getElem?_cons_succ] using h' j hj
              rw [ih h'' (r - 1)]
          | inr hd =>
              injection hd with hd
              subst hd
              simp only [wkInnerGo, removeAt]
              have h'' : ∀ (j : Nat), j < k → ρ'[j]? = some .keep ∨ ρ'[j]? = some .drop := by
                intro j hj
                simpa only [List.getElem?_cons_succ] using h' j hj
              rw [ih h'' r]

/-- Under `AssumpCut Γ c` every entry before `c` is an `.assumption`, so a
    shaped display (for `insertAt d c Γ`, the `wk` node's own context) has
    only `.keep`/`.drop` before `c` — never `.inline`. -/
theorem assumpCut_noInlineBefore {Γ : LCtx} {c : Nat} (ha : AssumpCut Γ c) (d : LocalDecl)
    {ρ : List Disp} (hs : DispShape (insertAt d c Γ) ρ) :
    ∀ (j : Nat) (v : ETm), j < c → ρ[j]? ≠ some (.inline v) := by
  induction ha generalizing ρ with
  | zero Γ =>
      intro j v hj
      exact absurd hj (Nat.not_lt_zero _)
  | succ A _ ih =>
      intro j v hj
      rw [insertAt_succ_cons] at hs
      cases hs with
      | assumptionKeep hs₀ =>
          cases j with
          | zero => simp
          | succ j =>
              simp only [List.getElem?_cons_succ]
              exact ih hs₀ j v (Nat.lt_of_succ_lt_succ hj)
      | assumptionDrop hs₀ =>
          cases j with
          | zero => simp
          | succ j =>
              simp only [List.getElem?_cons_succ]
              exact ih hs₀ j v (Nat.lt_of_succ_lt_succ hj)
      | _ => nomatch hs

/-- **The `AssumpCut` bridge:** at a shaped display over the `wk` node's own
    context (`insertAt d c Γ`) with `AssumpCut Γ c` (what `TyP.ClosedWf`
    demands of every `wk`), the re-frame pass is the identity —
    `wkInnerDisp ρ c = removeAt ρ c`. -/
theorem wkInnerDisp_eq_removeAt_of_shape {Γ : LCtx} {c : Nat} (ha : AssumpCut Γ c) (d : LocalDecl)
    {ρ : List Disp} (hs : DispShape (insertAt d c Γ) ρ) :
    wkInnerDisp ρ c = removeAt ρ c := by
  unfold wkInnerDisp
  cases hc : ρ[c]? with
  | none => rfl
  | some d =>
      cases d with
      | keep =>
          have hcl : c < ρ.length :=
            if h : c < ρ.length then h
            else by
              have hn : ρ[c]? = none :=
                List.getElem?_eq_none_iff.mpr (Nat.not_lt.mp h)
              rw [hn] at hc
              exact Option.noConfusion hc
          have h : ∀ (j : Nat), j < c → ρ[j]? = some .keep ∨ ρ[j]? = some .drop := by
            intro j hj
            cases hj' : ρ[j]? with
            | none =>
                rw [List.getElem?_eq_none_iff] at hj'
                omega
            | some d' =>
                cases d' with
                | keep => exact Or.inl rfl
                | drop => exact Or.inr rfl
                | inline v =>
                    exact absurd hj' (assumpCut_noInlineBefore ha d hs j v hj)
          exact wkInnerGo_eq_removeAt_of_keepOrDrop c h _
      | drop => rfl
      | inline v => rfl

/-! ## The `DispLvlEq` congruence of the re-frame -/

/-- The re-frame pass is `DispLvlEq`-congruent: aligned entries stay aligned
    (`keep`/`drop` literally, `.inline` values through `LvlEq.inst'` with the
    same slot and `★`), and the `r` counters stay in lockstep because the
    keep/drop pattern is shared. -/
theorem DispLvlEq.wkInnerGo {ρ₁ ρ₂ : List Disp} (h : DispLvlEq ρ₁ ρ₂) :
    ∀ (r k : Nat), DispLvlEq (wkInnerGo r k ρ₁) (wkInnerGo r k ρ₂) := by
  induction h with
  | nil =>
      intro r k
      cases k with
      | zero => exact .nil
      | succ k => exact .nil
  | @keep ρ₁ ρ₂ h' ih =>
      intro r k
      cases k with
      | zero => exact h'
      | succ k =>
          show DispLvlEq
            (Disp.keep :: Rcic.Syn.wkInnerGo (r - 1) k ρ₁)
            (Disp.keep :: Rcic.Syn.wkInnerGo (r - 1) k ρ₂)
          exact .keep (ih (r - 1) k)
  | @drop ρ₁ ρ₂ h' ih =>
      intro r k
      cases k with
      | zero => exact h'
      | succ k =>
          show DispLvlEq
            (Disp.drop :: Rcic.Syn.wkInnerGo r k ρ₁)
            (Disp.drop :: Rcic.Syn.wkInnerGo r k ρ₂)
          exact .drop (ih r k)
  | @inline v₁ v₂ ρ₁ ρ₂ hv h' ih =>
      intro r k
      cases k with
      | zero => exact h'
      | succ k =>
          show DispLvlEq
            (Disp.inline (ETm.inst r .star v₁) :: Rcic.Syn.wkInnerGo r k ρ₁)
            (Disp.inline (ETm.inst r .star v₂) :: Rcic.Syn.wkInnerGo r k ρ₂)
          exact .inline (LvlEq.inst' hv r LvlEq.star) (ih r k)

/-- `wkInnerDisp` is `DispLvlEq`-congruent: keep-aligned cutoffs re-frame in
    lockstep, every other alignment is `removeAt` on both sides. -/
theorem DispLvlEq.wkInnerDisp {ρ₁ ρ₂ : List Disp} (h : DispLvlEq ρ₁ ρ₂) (c : Nat) :
    DispLvlEq (Rcic.Syn.wkInnerDisp ρ₁ c) (Rcic.Syn.wkInnerDisp ρ₂ c) := by
  unfold Rcic.Syn.wkInnerDisp
  rcases h.getElem?_keep_cases c with ⟨hk₁, hk₂⟩ | ⟨hn₁, hn₂⟩
  · simp only [hk₁, hk₂]
    rw [h.countKeep_take_eq c]
    exact h.wkInnerGo _ c
  · cases h1 : ρ₁[c]? with
    | none =>
        cases h2 : ρ₂[c]? with
        | none => simp only [h1, h2]; exact h.removeAt c
        | some d2 =>
            cases d2 with
            | keep => exact absurd h2 hn₂
            | drop => simp only [h1, h2]; exact h.removeAt c
            | inline v => simp only [h1, h2]; exact h.removeAt c
    | some d1 =>
        cases d1 with
        | keep => exact absurd h1 hn₁
        | drop =>
            cases h2 : ρ₂[c]? with
            | none => simp only [h1, h2]; exact h.removeAt c
            | some d2 =>
                cases d2 with
                | keep => exact absurd h2 hn₂
                | drop => simp only [h1, h2]; exact h.removeAt c
                | inline v => simp only [h1, h2]; exact h.removeAt c
        | inline v =>
            cases h2 : ρ₂[c]? with
            | none => simp only [h1, h2]; exact h.removeAt c
            | some d2 =>
                cases d2 with
                | keep => exact absurd h2 hn₂
                | drop => simp only [h1, h2]; exact h.removeAt c
                | inline v' => simp only [h1, h2]; exact h.removeAt c

end Rcic.Syn

#print axioms Rcic.Syn.wkInnerGo_eq_removeAt_of_keepOrDrop
#print axioms Rcic.Syn.assumpCut_noInlineBefore
#print axioms Rcic.Syn.wkInnerDisp_eq_removeAt_of_shape
#print axioms Rcic.Syn.DispLvlEq.wkInnerGo
#print axioms Rcic.Syn.DispLvlEq.wkInnerDisp

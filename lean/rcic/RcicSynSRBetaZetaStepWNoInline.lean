import rcic.RcicSynSRBetaZetaStepWCore
import rcic.RcicSynSRBetaZetaZlTooth

/-!
# In-class `wk` displays never reframe (`wkInnerDisp ρ c = removeAt ρ c`)

The `es_wk_keep_reframe` row of `StepSuppliersW` fires only when
`wkInnerDisp ρ c ≠ removeAt ρ c` at a demanded `wk`-keep query — an
`.inline` entry at a position `j < c` whose value the keep-lift would
re-frame. On the demand cone that cannot happen for any in-range cutoff:

* `routedDisp_inline_letBinding` — every routed display's `.inline` entries
  sit exactly at `.letBinding` positions of their context (or at positions
  at-or-beyond the context, the out-of-range-`wk` padding corner).
* `wkInnerDisp_eq_removeAt_of_demand` — at a demanded `wk` node with
  `c ≤ Γ.length`, `AssumpPref` (which pins `AssumptionPrefix Γ c`) plus the
  routed-display alignment kill every `.inline` below `c`, so
  `wkInnerDisp ρ c = removeAt ρ c` and the closer reads the child straight
  off the `Issues.wk_es` edge (`esW_wk_keep`).

The residue is exactly the out-of-range cutoff corner (`Γ.length < c`):
there the inserted decl lands inside the prefix and the display may carry
padding keeps; see the `StepSuppliersW.es_wk_keep_reframe` docstring.
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 canonical dispositions: inline only at letBinding positions -/

/-- `CtxP.disp` puts `.inline` entries only at `.letBinding` positions. -/
theorem ctxP_disp_inline_letBinding {σ : Level → Level} {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → (C : CtxP E n Γ) → ∀ (j : Nat) (v : ETm),
      (C.disp σ)[j]? = some (.inline v) → ∃ A w, Γ[j]? = some (.letBinding A w)
  | _, .nil _ _ => by
      intro j v h
      simp only [CtxP.disp] at h
      cases j <;> simp at h
  | _, .assumption _ _ _ _ u hC _ => by
      intro j v h
      simp only [CtxP.disp] at h
      cases j with
      | zero =>
          cases hb : levelIsZero (σ u) <;> simp [hb] at h
      | succ j =>
          cases hb : levelIsZero (σ u) <;>
            simp only [CtxP.disp, hb, List.getElem?_cons_succ] at h
          all_goals
            simpa only [List.getElem?_cons_succ] using
              ctxP_disp_inline_letBinding hC j v h
  | _, .letBinding _ _ _ A _ v hC _ _ => by
      intro j v' h
      simp only [CtxP.disp] at h
      cases j with
      | zero => exact ⟨A, v, by simp⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at h
          simpa only [List.getElem?_cons_succ] using
            ctxP_disp_inline_letBinding hC j v' h

/-! ## §2 context-side inverses (kind preservation, both directions) -/

/-- `binderDisp` is never `.inline`. -/
theorem binderDisp_ne_inline (b : Bool) (v : ETm) : binderDisp b ≠ .inline v := by
  cases b with
  | true => simp [binderDisp]
  | false => simp [binderDisp]

/-- Below an insertion point, an `.letBinding` entry of `insertAt d c Γ`
    comes from a `.letBinding` of `Γ` (or the position is at-or-beyond `Γ`). -/
theorem insertAt_letBinding_inv_lo {d : LocalDecl} :
    ∀ (c j : Nat) (Γ : LCtx) (A v : Expr Nat), j < c →
      (insertAt d c Γ)[j]? = some (.letBinding A v) →
      (∃ A' v', Γ[j]? = some (.letBinding A' v')) ∨ Γ.length ≤ j
  | 0, _, _, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | _ + 1, 0, [], _, _, _, _ => Or.inr (Nat.zero_le _)
  | _ + 1, _ + 1, [], _, _, _, hget => by simp [insertAt] at hget
  | _ + 1, 0, x :: Γ, A, v, _, hget => by
      simp only [insertAt, List.getElem?_cons_zero, Option.some.injEq] at hget
      cases x with
      | assumption A' => simp [liftDecl] at hget
      | letBinding A' v' => exact Or.inl ⟨A', v', by simp⟩
  | c + 1, j + 1, x :: Γ, A, v, hj, hget => by
      simp only [insertAt_succ_cons, List.getElem?_cons_succ] at hget
      rcases insertAt_letBinding_inv_lo c j Γ A v (Nat.lt_of_succ_lt_succ hj) hget with
        ⟨A', v', hG⟩ | hlen
      · exact Or.inl ⟨A', v', by simpa only [List.getElem?_cons_succ] using hG⟩
      · exact Or.inr (by simp only [List.length_cons]; omega)

/-- Strictly above an insertion point, an `.letBinding` entry of
    `insertAt d c Γ` comes from a `.letBinding` of `Γ` one index up (or the
    position is at-or-beyond `Γ`). -/
theorem insertAt_letBinding_inv_hi {d : LocalDecl} :
    ∀ (c j : Nat) (Γ : LCtx) (A v : Expr Nat), c ≤ j →
      (insertAt d c Γ)[j + 1]? = some (.letBinding A v) →
      (∃ A' v', Γ[j]? = some (.letBinding A' v')) ∨ Γ.length ≤ j
  | 0, _, [], _, _, _, hget => by simp [insertAt] at hget
  | 0, j, x :: Γ, A, v, _, hget => by
      simp only [insertAt_zero, List.getElem?_cons_succ] at hget
      exact Or.inl ⟨A, v, hget⟩
  | _ + 1, _, [], _, _, _, hget => by simp [insertAt] at hget
  | _ + 1, 0, x :: Γ, _, _, hj, _ => absurd hj (Nat.not_succ_le_zero _)
  | c + 1, j + 1, x :: Γ, A, v, hj, hget => by
      simp only [insertAt_succ_cons, List.getElem?_cons_succ] at hget
      rcases insertAt_letBinding_inv_hi c j Γ A v (Nat.le_of_succ_le_succ hj) hget with
        ⟨A', v', hG⟩ | hlen
      · exact Or.inl ⟨A', v', by simpa only [List.getElem?_cons_succ] using hG⟩
      · exact Or.inr (by simp only [List.length_cons]; omega)

/-- Below a removal point, an `.letBinding` entry of `substRemove v j Γ`
    comes from a `.letBinding` of `Γ` at the same index. -/
theorem substRemove_letBinding_inv_lo {v' : Expr Nat} :
    ∀ (j k : Nat) (Γ : LCtx) (A v : Expr Nat), k < j →
      (substRemove v' j Γ)[k]? = some (.letBinding A v) →
      ∃ A' v'', Γ[k]? = some (.letBinding A' v'')
  | j, _, [], _, _, _, hget => by cases j <;> simp [substRemove] at hget
  | 0, _, _, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | _ + 1, 0, x :: Γ, A, v, _, hget => by
      simp only [substRemove, List.getElem?_cons_zero, Option.some.injEq] at hget
      cases x with
      | assumption A' => simp [instDecl] at hget
      | letBinding A' v'' => exact ⟨A', v'', by simp⟩
  | j + 1, k + 1, x :: Γ, A, v, hk, hget => by
      simp only [substRemove_succ_cons, List.getElem?_cons_succ] at hget
      obtain ⟨A', v'', hG⟩ :=
        substRemove_letBinding_inv_lo j k Γ A v (Nat.lt_of_succ_lt_succ hk) hget
      exact ⟨A', v'', by simpa only [List.getElem?_cons_succ] using hG⟩

/-- At-or-above a removal point, `substRemove v j Γ` reads `Γ` one index
    up, verbatim. -/
theorem substRemove_getElem?_ge {v : Expr Nat} :
    ∀ (j k : Nat) (Γ : LCtx), j ≤ k → (substRemove v j Γ)[k]? = Γ[k + 1]?
  | j, _, [], _ => by cases j <;> simp [substRemove]
  | 0, k, x :: Γ, _ => by
      show Γ[k]? = (x :: Γ)[k + 1]?
      simp only [List.getElem?_cons_succ]
  | j + 1, 0, _, hj => absurd hj (Nat.not_succ_le_zero _)
  | j + 1, k + 1, x :: Γ, hj => by
      show (instDecl j v x :: substRemove v j Γ)[k + 1]? = (x :: Γ)[k + 1 + 1]?
      simp only [List.getElem?_cons_succ, Nat.add_assoc]
      exact substRemove_getElem?_ge j k Γ (Nat.le_of_succ_le_succ hj)

/-- `instLvlsDecl` maps `.letBinding` entries to `.letBinding` entries only. -/
theorem instLvlsDecl_letBinding_inv {ls : List Level} {A v : Expr Nat} {d : LocalDecl}
    (h : instLvlsDecl ls d = .letBinding A v) : ∃ A' v', d = .letBinding A' v' := by
  cases d with
  | assumption A' => simp [instLvlsDecl] at h
  | letBinding A' v' => exact ⟨A', v', rfl⟩

/-- Below the insertion point, an `.inline` entry of `insertDisp d j ρ` is an
    original entry of `ρ` at the same index (the insert itself is `d`, never
    an `.inline`). -/
theorem insertDisp_inline_lt {d : Disp} (hd : ∀ v, ¬ d = .inline v) :
    ∀ (ρ : List Disp) (j k : Nat) (v : ETm), k < j →
      (insertDisp d j ρ)[k]? = some (.inline v) → ρ[k]? = some (.inline v)
  | [], 0, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | [], _ + 1, 0, v, _, h => by
      simp only [insertDisp, List.getElem?_cons_zero, Option.some.injEq] at h
      exact absurd h (hd v)
  | [], _ + 1, _ + 1, _, _, h => by simp [insertDisp] at h
  | _ :: _, 0, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | _ :: _, _ + 1, 0, _, _, h => by
      simp only [insertDisp, List.getElem?_cons_zero] at h ⊢
      exact h
  | _ :: _, j + 1, k + 1, v, hk, h => by
      simp only [insertDisp, List.getElem?_cons_succ] at h ⊢
      exact insertDisp_inline_lt hd _ j k v (Nat.lt_of_succ_lt_succ hk) h

/-- The entry `insertDisp d j ρ` puts at its own position is never an
    `.inline` (it is the inserted `d` itself, or nothing past the end). -/
theorem insertDisp_self_ne_inline {d : Disp} (hd : ∀ v, ¬ d = .inline v) :
    ∀ (ρ : List Disp) (j : Nat) (v : ETm), (insertDisp d j ρ)[j]? ≠ some (.inline v)
  | [], 0, v => by
      intro hh
      simp only [insertDisp, List.getElem?_cons_zero, Option.some.injEq] at hh
      exact absurd hh (hd v)
  | [], _ + 1, v => by simp [insertDisp]
  | _ :: _, 0, v => by
      intro hh
      simp only [insertDisp, List.getElem?_cons_zero, Option.some.injEq] at hh
      exact absurd hh (hd v)
  | _ :: _, _ + 1, v => by
      simp only [insertDisp, List.getElem?_cons_succ]
      exact insertDisp_self_ne_inline hd _ _ v

/-! ## §3 the routed-display alignment -/

/-- Every routed display's `.inline` entries sit at `.letBinding` positions
    of their context — or at-or-beyond the context's end (the padding corner
    only reachable through out-of-range `wk` cutoffs). -/
theorem routedDisp_inline_letBinding {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} (h : RoutedDisp σ E n Γ ρ) :
    ∀ (j : Nat) (v : ETm), ρ[j]? = some (.inline v) →
      (∃ A w, Γ[j]? = some (.letBinding A w)) ∨ Γ.length ≤ j := by
  induction h with
  | @canon σ _ _ Γ C =>
      intro j v hρ
      exact Or.inl (ctxP_disp_inline_letBinding C j v hρ)
  | @assumption σ _ _ _ _ _ u _ _ ih =>
      intro j v hρ
      cases j with
      | zero =>
          cases hb : levelIsZero (σ u) <;> simp [hb, binderDisp] at hρ
      | succ j =>
          simp only [List.getElem?_cons_succ] at hρ
          rcases ih j v hρ with ⟨A, w, hG⟩ | hlen
          · exact Or.inl ⟨A, w, by simpa only [List.getElem?_cons_succ] using hG⟩
          · exact Or.inr (by simp only [List.length_cons]; omega)
  | letDrop _ _ _ _ ih =>
      intro j v hρ
      cases j with
      | zero => simp at hρ
      | succ j =>
          simp only [List.getElem?_cons_succ] at hρ
          rcases ih j v hρ with ⟨A, w, hG⟩ | hlen
          · exact Or.inl ⟨A, w, by simpa only [List.getElem?_cons_succ] using hG⟩
          · exact Or.inr (by simp only [List.length_cons]; omega)
  | @letInline σ _ _ _ _ A v0 _ _ _ _ ih =>
      intro j v hρ
      cases j with
      | zero => exact Or.inl ⟨A, v0, by simp⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at hρ
          rcases ih j v hρ with ⟨A, w, hG⟩ | hlen
          · exact Or.inl ⟨A, w, by simpa only [List.getElem?_cons_succ] using hG⟩
          · exact Or.inr (by simp only [List.length_cons]; omega)
  | @wk σ _ _ Γ ρ d c _ ih =>
      intro j v hρ
      rcases Nat.lt_or_ge j c with hjl | hjg
      · rw [removeAt_getElem?_lt c ρ j hjl] at hρ
        rcases ih j v hρ with ⟨A, w, hG⟩ | hlen
        · rcases insertAt_letBinding_inv_lo c j Γ A w hjl hG with ⟨A', w', hG'⟩ | hlen2
          · exact Or.inl ⟨A', w', hG'⟩
          · exact Or.inr hlen2
        · exact Or.inr (by have h1 := insertAt_length d c Γ; omega)
      · rw [removeAt_getElem?_ge c ρ j hjg] at hρ
        rcases ih (j + 1) v hρ with ⟨A, w, hG⟩ | hlen
        · rcases insertAt_letBinding_inv_hi c j Γ A w hjg hG with ⟨A', w', hG'⟩ | hlen2
          · exact Or.inl ⟨A', w', hG'⟩
          · exact Or.inr hlen2
        · exact Or.inr (by have h1 := insertAt_length d c Γ; omega)
  | @esub σ _ _ Γ ρl t v j u hget _ _ _ ih =>
      intro k v' hρ
      have hd' : ∀ w, ¬ binderDisp (levelIsZero (σ u)) = .inline w :=
        fun w hw => binderDisp_ne_inline _ w hw
      rcases Nat.lt_trichotomy k j with hlt | heq | hgt
      · have hρl : ρl[k]? = some (.inline v') :=
          insertDisp_inline_lt hd' ρl j k v' hlt hρ
        rcases ih k v' hρl with ⟨A, w, hG⟩ | hlen2
        · obtain ⟨A', w'', hG'⟩ := substRemove_letBinding_inv_lo j k Γ A w hlt hG
          exact Or.inl ⟨A', w'', hG'⟩
        · exact absurd hlen2 (by
            have hjlen := (List.getElem?_eq_some_iff.mp hget).1
            have h1 := substRemove_length_lt (v := v) (j := j) (Γ := Γ) hjlen
            omega)
      · subst heq
        exact absurd hρ (insertDisp_self_ne_inline hd' ρl k v')
      · have hjlt : j < ρl.length :=
          Nat.lt_of_not_ge (fun hcon => by
            have hnone : (insertDisp (binderDisp (levelIsZero (σ u))) j ρl)[k]? = none :=
              List.getElem?_eq_none_iff.mpr (by
                rw [insertDisp_length]
                omega)
            rw [hnone] at hρ
            exact absurd hρ (by simp))
        have hk1 : k - 1 + 1 = k := by omega
        have hρge : (insertDisp (binderDisp (levelIsZero (σ u))) j ρl)[(k - 1) + 1]? =
            some (.inline v') := by
          rw [hk1]
          exact hρ
        rw [insertDisp_getElem?_ge ρl j (k - 1) (by omega) hjlt] at hρge
        rcases ih (k - 1) v' hρge with ⟨A, w, hG⟩ | hlen
        · have hG2 : (substRemove v j Γ)[k - 1]? = some (.letBinding A w) := hG
          rw [substRemove_getElem?_ge j (k - 1) Γ (by omega)] at hG2
          refine Or.inl ⟨A, w, ?_⟩
          rw [hk1] at hG2
          exact hG2
        · exact Or.inr (by
            have h1 := substRemove_length_lt (v := v) (j := j) (Γ := Γ)
              (List.getElem?_eq_some_iff.mp hget).1
            omega)
  | @linst σ E a' n Γ ρ ls _ _ _ ih =>
      intro j v hρ
      rcases ih j v hρ with ⟨A, w, hG⟩ | hlen
      · have hG' : (Γ.map (instLvlsDecl ls))[j]? = some (.letBinding A w) := hG
        rw [List.getElem?_map] at hG'
        cases hd : Γ[j]? with
        | none => rw [hd] at hG'; simp at hG'
        | some d =>
          rw [hd] at hG'
          simp only [Option.map_some', Option.some.injEq] at hG'
          obtain ⟨A', w', hA'⟩ := instLvlsDecl_letBinding_inv hG'
          refine Or.inl ⟨A', w', ?_⟩
          rw [hA']
      · exact Or.inr (by
          have hmaplen : (instLvlsCtx ls Γ).length = Γ.length := by
            unfold instLvlsCtx
            simp
          omega)
  | ewk _ _ ih =>
      intro j v hρ
      exact ih j v hρ
  | cctx _ _ ih =>
      intro j v hρ
      cases j with
      | zero =>
          rcases ih 0 v hρ with ⟨A, w, hG⟩ | hlen
          · simp only [List.getElem?_cons_zero, Option.some.injEq] at hG
            simp at hG
          · exact absurd hlen (by simp)
      | succ j =>
          rcases ih (j + 1) v hρ with ⟨A, w, hG⟩ | hlen
          · exact Or.inl ⟨A, w, by simpa only [List.getElem?_cons_succ] using hG⟩
          · exact Or.inr hlen

/-! ## §4 the in-range cutoff discharge -/

/-- With no `.inline` entry below `c`, the `wk` prefix pass changes nothing:
    `wkInnerGo r c ρ` is exactly `removeAt ρ c` (each entry it would re-frame
    is absent). -/
theorem wkInnerGo_eq_removeAt_noInlineBelow :
    ∀ (c r : Nat) (ρ : List Disp), (∀ j v, j < c → ρ[j]? ≠ some (.inline v)) →
      wkInnerGo r c ρ = removeAt ρ c
  | 0, _, ρ, _ => by cases ρ <;> rfl
  | _ + 1, _, [], _ => rfl
  | c + 1, r, x :: ρ', h => by
      have hx : ∀ v, x ≠ .inline v := by
        intro v hv
        exact h 0 v (Nat.zero_lt_succ c) (by simp [hv])
      cases x with
      | keep =>
          show Disp.keep :: wkInnerGo (r - 1) c ρ' = Disp.keep :: removeAt ρ' c
          rw [wkInnerGo_eq_removeAt_noInlineBelow c (r - 1) ρ'
            (fun j v hj => by
              simpa only [List.getElem?_cons_succ] using h (j + 1) v (Nat.succ_lt_succ hj))]
      | drop =>
          show Disp.drop :: wkInnerGo r c ρ' = Disp.drop :: removeAt ρ' c
          rw [wkInnerGo_eq_removeAt_noInlineBelow c r ρ'
            (fun j v hj => by
              simpa only [List.getElem?_cons_succ] using h (j + 1) v (Nat.succ_lt_succ hj))]
      | inline v => exact absurd rfl (hx v)

/-- At a routed display over `insertAt d c Γ` whose inner context is an
    `AssumptionPrefix` at an in-range `c`, no `.inline` sits below `c`. -/
theorem routedDisp_noInlineBelow_of_ap {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} {d : LocalDecl} {c : Nat}
    (hr : RoutedDisp σ E n (insertAt d c Γ) ρ) (hap : AssumptionPrefix Γ c)
    (hc : c ≤ Γ.length) :
    ∀ (j : Nat) (v : ETm), j < c → ρ[j]? ≠ some (.inline v) := by
  intro j v hj hρj
  rcases routedDisp_inline_letBinding hr j v hρj with ⟨A, w, hΓ⟩ | hlen
  · rcases insertAt_letBinding_inv_lo c j Γ A w hj hΓ with ⟨A', w', hG⟩ | hlen2
    · have hjlen := (List.getElem?_eq_some_iff.mp hG).1
      have hmem : (.letBinding A' w') ∈ Γ.take c := by
        have h1 : (Γ.take c)[j]? = some (.letBinding A' w') := by
          rw [List.getElem?_take, if_pos hj]
          exact hG
        exact List.getElem?_mem h1
      obtain ⟨A'', hA''⟩ := hap _ hmem
      simp at hA''
    · exact absurd hlen2 (by omega)
  · exact absurd hlen (by have h1 := insertAt_length d c Γ; omega)

/-- The `wk` inner display of an in-range cutoff is exactly `removeAt`. -/
theorem wkInnerDisp_eq_removeAt_of_ap {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} {d : LocalDecl} {c : Nat}
    (hr : RoutedDisp σ E n (insertAt d c Γ) ρ) (hap : AssumptionPrefix Γ c)
    (hc : c ≤ Γ.length) : wkInnerDisp ρ c = removeAt ρ c := by
  unfold wkInnerDisp
  cases hρc : ρ[c]? with
  | none => rfl
  | some dv => cases dv with
    | keep =>
        exact wkInnerGo_eq_removeAt_noInlineBelow c (countKeep (ρ.take c)) ρ
          (routedDisp_noInlineBelow_of_ap hr hap hc)
    | drop => rfl
    | inline v => rfl

/-- **The in-range `es_wk_keep_reframe` discharge.** At every demanded `wk`
    query with an in-range cutoff, `wkInnerDisp ρ c = removeAt ρ c`: the
    `AssumpPref` the demand carries pins `AssumptionPrefix Γ c`, the routed
    display keeps `.inline` entries at `.letBinding` positions, and an
    in-range prefix is all assumptions. The closer then reads the child
    straight off the `Issues.wk_es` edge. -/
theorem wkInnerDisp_eq_removeAt_of_demand {Eₐ : ResolvedEnv}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    {d : LocalDecl} {c : Nat} (h : CvP E n Γ a b T)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
    {σ : Level → Level} {ρ : List Disp}
    (hq : Demand (.es (CvP.wk E n Γ a b T d c h) S σ ρ))
    (hc : c ≤ Γ.length) : wkInnerDisp ρ c = removeAt ρ c := by
  have hap' : (CvP.wk E n Γ a b T d c h).AssumpPref := Demand.ap hq
  have hap : AssumptionPrefix Γ c := hap'.1
  have hr : RoutedDisp σ E n (insertAt d c Γ) ρ := Demand.routed hq
  exact wkInnerDisp_eq_removeAt_of_ap hr hap hc

end Rcic.Syn

#print axioms Rcic.Syn.ctxP_disp_inline_letBinding
#print axioms Rcic.Syn.binderDisp_ne_inline
#print axioms Rcic.Syn.insertAt_letBinding_inv_lo
#print axioms Rcic.Syn.insertAt_letBinding_inv_hi
#print axioms Rcic.Syn.substRemove_letBinding_inv_lo
#print axioms Rcic.Syn.substRemove_getElem?_ge
#print axioms Rcic.Syn.instLvlsDecl_letBinding_inv
#print axioms Rcic.Syn.insertDisp_inline_lt
#print axioms Rcic.Syn.insertDisp_self_ne_inline
#print axioms Rcic.Syn.routedDisp_inline_letBinding
#print axioms Rcic.Syn.wkInnerGo_eq_removeAt_noInlineBelow
#print axioms Rcic.Syn.routedDisp_noInlineBelow_of_ap
#print axioms Rcic.Syn.wkInnerDisp_eq_removeAt_of_ap
#print axioms Rcic.Syn.wkInnerDisp_eq_removeAt_of_demand

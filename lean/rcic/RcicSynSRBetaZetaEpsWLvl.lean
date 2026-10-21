import rcic.RcicSynSRBetaZetaEpsWDisp

/-!
# epsW arm equations + the `lvlEq_epsW` congruence

The per-constructor unfolding lemmas of `TyP.epsW` (mirrors of the landed
`eps_*` arm lemmas; every arm except `wk` is verbatim `eps`, and `wk` runs at
`wkInnerDisp`), and the mother congruence:

* `lvlEq_epsW` — `epsW` is `LvlEq`-congruent in `σ` (pointwise `eqN`) and `ρ`
  (`DispLvlEq`) for **every** derivation, zero extra hypotheses. The `wk`
  arm goes through `DispLvlEq.wkInnerDisp` and `countKeep_take_eq`.
* `lvlEq_epsW_instLevel(_nil)` — the `linst` commutation corollaries,
  mirroring `lvlEq_eps_instLevel(_nil)`. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## `wk` arm equations (the only arm where `epsW` differs) -/

theorem epsW_wk_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat} {d : LocalDecl}
    {c : Nat} {D : TyP E n Γ e A} {σ : Level → Level} {ρ : List Disp}
    (hk : ρ[c]? = some .keep) :
    (TyP.wk E n Γ e A d c D).epsW σ ρ =
      (D.epsW σ (wkInnerDisp ρ c)).lift (countKeep (ρ.take c)) 1 := by
  simp only [TyP.epsW, hk]

theorem epsW_wk_not_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat} {d : LocalDecl}
    {c : Nat} {D : TyP E n Γ e A} {σ : Level → Level} {ρ : List Disp}
    (hk : ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v)) :
    (TyP.wk E n Γ e A d c D).epsW σ ρ = D.epsW σ (removeAt ρ c) := by
  rcases hk with hk | hk | ⟨v, hk⟩
  · have hd : wkInnerDisp ρ c = removeAt ρ c := by simp only [wkInnerDisp, hk]
    simp only [TyP.epsW, hk, hd]
  · have hd : wkInnerDisp ρ c = removeAt ρ c := by simp only [wkInnerDisp, hk]
    simp only [TyP.epsW, hk, hd]
  · have hd : wkInnerDisp ρ c = removeAt ρ c := by simp only [wkInnerDisp, hk]
    simp only [TyP.epsW, hk, hd]

theorem epsW_wk_not_keep_of_ne {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    {d : LocalDecl} {c : Nat} {D : TyP E n Γ e A} {σ : Level → Level} {ρ : List Disp}
    (hk : ρ[c]? ≠ some .keep) :
    (TyP.wk E n Γ e A d c D).epsW σ ρ = D.epsW σ (removeAt ρ c) := by
  cases hget : ρ[c]? with
  | none => exact epsW_wk_not_keep (.inl hget)
  | some disp =>
      cases disp with
      | keep => exact absurd hget hk
      | drop => exact epsW_wk_not_keep (.inr (.inl hget))
      | inline v => exact epsW_wk_not_keep (.inr (.inr ⟨v, hget⟩))

theorem wkInnerDisp_eq_removeAt_of_ne {ρ : List Disp} {c : Nat} (hk : ρ[c]? ≠ some .keep) :
    wkInnerDisp ρ c = removeAt ρ c := by
  cases hget : ρ[c]? with
  | none => simp only [wkInnerDisp, hget]
  | some disp =>
      cases disp with
      | keep => exact absurd hget hk
      | drop => simp only [wkInnerDisp, hget]
      | inline v => simp only [wkInnerDisp, hget]

/-! ## verbatim-arm equations (`lam`/`app`/`letE`/`lsub`) -/

theorem epsW_lam_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    {body B : Expr Nat} {v : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    {σ : Level → Level} {ρ : List Disp} (hu : levelIsZero (σ u) = true) :
    (TyP.lam E n Γ A u body B v hA hbody hB).epsW σ ρ = hbody.epsW σ (.drop :: ρ) := by
  simp only [TyP.epsW, hu]

theorem epsW_lam_keep_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} {body B : Expr Nat} {v : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    {σ : Level → Level} (ρ : List Disp) (hu : levelIsZero (σ u) = false) :
    (TyP.lam E n Γ A u body B v hA hbody hB).epsW σ ρ =
      lamOut (hbody.epsW σ (.keep :: ρ)) := by
  simp only [TyP.epsW, hu]
  cases hbody.epsW σ (.keep :: ρ) <;> rfl

theorem epsW_app_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a A B : Expr Nat} {w : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.app E n Γ f a A B w hf ha hT).epsW σ ρ =
      appOut (hf.epsW σ ρ) (ha.epsW σ ρ) := rfl

theorem let_epsW_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} {value B body : Expr Nat} {w : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (hT : TyP E n Γ (instantiate0 value B) (.sort w))
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.letE E n Γ A u value B body w hA hv hb hT).epsW σ ρ =
      hb.epsW σ (letDisp (hv.epsW σ ρ) :: ρ) := by
  simp only [TyP.epsW]
  cases hv.epsW σ ρ <;> rfl

theorem lsub_epsW_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat}
    {j : Nat} {u : Level} (D : TyP E n Γ e A) (hget : Γ[j]? = some (.letBinding t v))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.lsub E n Γ e A t v j u D hget hv hvT).epsW σ ρ =
      D.epsW σ (insertDisp (lsubDisp (countKeep (ρ.take j)) (hv.epsW σ ρ)) j ρ) := by
  simp only [TyP.epsW]
  cases hv.epsW σ ρ <;> rfl

/-! ## the mother congruence -/

/-- `TyP.epsW` is `LvlEq`-congruent in both the level map `σ` and the
    disposition list `ρ`, for **every** `D : TyP E n Γ e T` (all 15
    constructors, zero extra hypotheses) — the `epsW` mirror of `lvlEq_eps`.
    The `wk` arm runs at `wkInnerDisp` on both sides
    (`DispLvlEq.wkInnerDisp` + `countKeep_take_eq`). -/
theorem lvlEq_epsW :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → {σ₁ σ₂ : Level → Level} →
    (∀ l, eqN (σ₁ l) (σ₂ l)) → {ρ₁ ρ₂ : List Disp} →
    DispLvlEq ρ₁ ρ₂ → LvlEq (D.epsW σ₁ ρ₁) (D.epsW σ₂ ρ₂)
  | _, _, _, _, _, .sort _ _ _ l _ _, _, _, hσ, _, _, _ =>
      .sort (hσ l)
  | _, _, _, _, _, .bvar _ _ _ i _ u _ _, σ₁, σ₂, hσ, _, _, hρ => by
      have hbit : levelIsZero (σ₁ u) = levelIsZero (σ₂ u) := levelIsZero_congr (hσ u)
      simp only [TyP.epsW, hbit]
      cases levelIsZero (σ₂ u) with
      | true => exact .star
      | false => exact lvlEq_resolve hρ i
  | _, _, _, _, _, .const _ _ _ r ls _ _ u _ _ _ _ _, σ₁, σ₂, hσ, _, _, _ => by
      have hbit : levelIsZero (σ₁ u) = levelIsZero (σ₂ u) := levelIsZero_congr (hσ u)
      simp only [TyP.epsW, hbit]
      cases levelIsZero (σ₂ u) with
      | true => exact .star
      | false => exact .const r (eqNList_map_of_pointwise hσ ls)
  | _, _, _, _, _, .pi _ _ _ _ u _ _ hA hB, σ₁, σ₂, hσ, _, _, hρ => by
      have hbit : levelIsZero (σ₁ u) = levelIsZero (σ₂ u) := levelIsZero_congr (hσ u)
      simp only [TyP.epsW, hbit]
      cases levelIsZero (σ₂ u) with
      | true =>
          exact .pi (lvlEq_epsW hA hσ hρ) ((lvlEq_epsW hB hσ (.drop hρ)).lift' 0 1)
      | false =>
          exact .pi (lvlEq_epsW hA hσ hρ) (lvlEq_epsW hB hσ (.keep hρ))
  | _, _, _, _, _, .lam _ _ _ _ u _ _ _ hA hbody hB, σ₁, σ₂, hσ, ρ₁, ρ₂, hρ => by
      have hbit : levelIsZero (σ₁ u) = levelIsZero (σ₂ u) := levelIsZero_congr (hσ u)
      cases hzu : levelIsZero (σ₂ u) with
      | true =>
          rw [epsW_lam_drop hA hbody hB (hbit.trans hzu), epsW_lam_drop hA hbody hB hzu]
          exact lvlEq_epsW hbody hσ (.drop hρ)
      | false =>
          rw [epsW_lam_keep_eq hA hbody hB ρ₁ (hbit.trans hzu),
              epsW_lam_keep_eq hA hbody hB ρ₂ hzu]
          exact lvlEq_lam_match (lvlEq_epsW hbody hσ (.keep hρ))
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha hT, _, _, hσ, _, _, hρ => by
      rw [epsW_app_eq hf ha hT, epsW_app_eq hf ha hT]
      exact lvlEq_app_match (lvlEq_epsW hf hσ hρ) (lvlEq_epsW ha hσ hρ)
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb hT, _, _, hσ, _, _, hρ => by
      rw [let_epsW_eq hA hv hb hT, let_epsW_eq hA hv hb hT]
      exact lvlEq_epsW hb hσ (dispLvlEq_let_match (lvlEq_epsW hv hσ hρ) hρ)
  | _, _, _, _, _, .lit _ _ _ _ _ hexp, _, _, hσ, _, _, hρ =>
      lvlEq_epsW hexp hσ hρ
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h _, _, _, hσ, _, _, hρ =>
      lvlEq_epsW h hσ hρ
  | _, _, _, _, _, .wk _ _ _ _ _ _ c D, _, _, hσ, _, ρ₂, hρ => by
      have ih := lvlEq_epsW D hσ (hρ.wkInnerDisp c)
      rcases hρ.getElem?_keep_cases c with ⟨hk₁, hk₂⟩ | ⟨hn₁, hn₂⟩
      · rw [epsW_wk_keep hk₁, epsW_wk_keep hk₂, hρ.countKeep_take_eq c]
        exact ih.lift' (countKeep (ρ₂.take c)) 1
      · rw [epsW_wk_not_keep_of_ne hn₁, epsW_wk_not_keep_of_ne hn₂]
        rw [wkInnerDisp_eq_removeAt_of_ne hn₁, wkInnerDisp_eq_removeAt_of_ne hn₂] at ih
        exact ih
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ j u D _ hv _, σ₁, σ₂, hσ, _, ρ₂, hρ => by
      have hbit : levelIsZero (σ₁ u) = levelIsZero (σ₂ u) := levelIsZero_congr (hσ u)
      simp only [TyP.epsW, hbit]
      cases levelIsZero (σ₂ u) with
      | true => exact lvlEq_epsW D hσ (hρ.insertDisp_drop j)
      | false =>
          rw [hρ.countKeep_take_eq j]
          exact (lvlEq_epsW D hσ (hρ.insertDisp_keep j)).inst'
            (countKeep (ρ₂.take j)) (lvlEq_epsW hv hσ hρ)
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ j _ D hget hv hvT, _, _, hσ, _, _, hρ => by
      rw [lsub_epsW_eq D hget hv hvT, lsub_epsW_eq D hget hv hvT]
      exact lvlEq_epsW D hσ (dispLvlEq_lsub_match (lvlEq_epsW hv hσ hρ) hρ j)
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D, _, _, hσ, _, _, hρ =>
      lvlEq_epsW D (fun l => hσ (instLevel ls l)) hρ
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D, _, _, hσ, _, _, hρ =>
      lvlEq_epsW D hσ hρ
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _, _, _, hσ, _, _, hρ =>
      lvlEq_epsW D hσ hρ

/-- The `linst` commutation corollary: instantiating the levels of `epsW` at
    two `eqNList` lists yields `LvlEq` erasures (mirror of
    `lvlEq_eps_instLevel`). -/
theorem lvlEq_epsW_instLevel {E : ResolvedEnv} {a : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E a Γ e T) {ls₁ ls₂ : List Level} (hls : eqNList ls₁ ls₂)
    {ρ₁ ρ₂ : List Disp} (hρ : DispLvlEq ρ₁ ρ₂) :
    LvlEq (D.epsW (instLevel ls₁) ρ₁) (D.epsW (instLevel ls₂) ρ₂) :=
  lvlEq_epsW D (instLevel_eqNList hls) hρ

/-- `Γ = []`, `ρ₁ = ρ₂ = []` specialization (mirror of `lvlEq_eps_instLevel_nil`). -/
theorem lvlEq_epsW_instLevel_nil {E : ResolvedEnv} {a : Nat} {e T : Expr Nat}
    (D : TyP E a [] e T) {ls₁ ls₂ : List Level} (hls : eqNList ls₁ ls₂) :
    LvlEq (D.epsW (instLevel ls₁) []) (D.epsW (instLevel ls₂) []) :=
  lvlEq_epsW_instLevel D hls .nil

end Rcic.Syn

#print axioms Rcic.Syn.epsW_wk_keep
#print axioms Rcic.Syn.epsW_wk_not_keep
#print axioms Rcic.Syn.epsW_wk_not_keep_of_ne
#print axioms Rcic.Syn.epsW_lam_drop
#print axioms Rcic.Syn.epsW_lam_keep_eq
#print axioms Rcic.Syn.epsW_app_eq
#print axioms Rcic.Syn.let_epsW_eq
#print axioms Rcic.Syn.lsub_epsW_eq
#print axioms Rcic.Syn.lvlEq_epsW
#print axioms Rcic.Syn.lvlEq_epsW_instLevel
#print axioms Rcic.Syn.lvlEq_epsW_instLevel_nil

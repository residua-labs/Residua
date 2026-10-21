import rcic.RcicSynTagCoh

/-!
# S20 §2–4 / A7 — `RcicSynTagCohDerived`: erased-term star reflections and the
view-stripping `TagCoh` compositions

`research/rcic/sortrow/S20_TAGCOH_STEP.md` (ChatGPT, PR #7415), additive over
main's `RcicSynTagCoh`. Nothing here is projected from `CL` or `EUT`: every
`TagCoh` conclusion is derived structurally from the erased `eps` equations and
the landed row compositions.

- **§1 `ETm` reflections.** `lift` preserves and reflects `★`;
  `inst_star_iff_of_ne` is the non-star instantiation reflection; the full
  diagnostic `inst_star_iff` is proved by `ETm` induction — a `★` instantiation
  is either a `★` body or exactly `bvar j ↦ ★`.
- **§2 per-node `eps` star-iffs.** The non-`rfl` cases: `wk` (the `keep`
  disposition lifts the child's image, and `lift` never manufactures `★`) and
  `esub` (a proof-typed replacement drops the slot; a relevant replacement is
  `ETm.inst`, whose `★`-ness is the body's once `PB[V,W]` supplies `r ≠ ★`).
- **§3 `TagCoh` compositions.** `conv`/`ewk`/`cctx` keep the subject, so they
  return `TagCoh` directly; `wk`/`linst`/`esub` change the displayed subject
  (`lift`/`instantiateLevels`/`instantiate`), so — as with main's
  `tagCoh_lsub` — they return the raw star-status iff, re-presentable as
  `TagCoh` through `TagCoh.of_subject_eq` when the subjects coincide.
  `tagCoh_lam_local` is the per-side λ row: each body is taken under ITS OWN
  binder disposition `binderDisp (levelIsZero (σᵢ uᵢ))`, with no common bit `b`
  to align.
- **§4 controls.** `a7ctrl_app_coh_arg_status_differs` pins the §7 control: the
  same application under two displays whose ARGUMENT star-statuses differ
  (`keep` resolves to `bvar 0`, `drop` resolves to `★`) still coheres, because
  `app` star-status is exactly the function's (`eps_app_star_iff`).
  `inst_star_needs_ne` is the negative control: with `r = ★` the naïve
  reflection `inst = ★ → t = ★` fails (`bvar 0 ↦ ★` is `★` while `bvar 0` is
  not), which is exactly why `inst_star_iff_of_ne` takes `hr` and why the esub
  row consumes a `PB[V,W]` answer before reflecting.

The `PB[V,W]` answer is taken as an explicit `hr : hv.eps σ ρ ≠ .star`
hypothesis — the producer that DISCHARGES it is upstream of A7 and stays open.
`closure_claim = 0`. Axioms ⊆ [propext, Quot.sound].
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `ETm` reflections -/

/-- `lift` preserves and reflects `★` (it never manufactures `★` out of a
    non-`★` term, and `★`'s lift is `★`). -/
theorem lift_star_iff {c k : Nat} {t : ETm} : t.lift c k = .star ↔ t = .star :=
  ⟨lift_eq_star, fun h => by cases h; rfl⟩

/-- Non-star instantiation reflection (S20 §2): substituting a non-`★`
    replacement can only produce `★` from a `★` body. -/
theorem inst_star_iff_of_ne {j : Nat} {r t : ETm} (hr : r ≠ .star) :
    ETm.inst j r t = .star ↔ t = .star :=
  ⟨inst_eq_star hr, fun h => by cases h; rfl⟩

/-- The full diagnostic (S20 §2), by `ETm` induction: an instantiation is `★`
    iff the body is `★`, or it is exactly `bvar j` hitting a `★` replacement. -/
theorem inst_star_iff {j : Nat} {r t : ETm} :
    ETm.inst j r t = .star ↔ t = .star ∨ (t = .bvar j ∧ r = .star) := by
  induction t with
  | bvar i =>
    by_cases hij : i = j
    · subst hij
      simp only [ETm.inst, if_pos rfl]
      refine ⟨fun h => .inr ⟨trivial, h⟩, fun h => ?_⟩
      rcases h with h | ⟨-, h⟩
      · nomatch h
      · exact h
    · have hne : ETm.inst j r (.bvar i) ≠ .star := by
        simp only [ETm.inst, if_neg hij]
        by_cases hlt : j < i
        · rw [if_pos hlt]; exact fun h => nomatch h
        · rw [if_neg hlt]; exact fun h => nomatch h
      refine ⟨fun h => absurd h hne, fun h => ?_⟩
      rcases h with h | ⟨h, -⟩
      · nomatch h
      · cases h; exact absurd rfl hij
  | star =>
    simp only [ETm.inst]
    exact ⟨fun _ => .inl trivial, fun _ => trivial⟩
  | sort l =>
    simp only [ETm.inst]
    exact ⟨fun h => ETm.noConfusion h,
      fun h => h.elim (fun h => ETm.noConfusion h) (fun h => ETm.noConfusion h.1)⟩
  | const r' ls =>
    simp only [ETm.inst]
    exact ⟨fun h => ETm.noConfusion h,
      fun h => h.elim (fun h => ETm.noConfusion h) (fun h => ETm.noConfusion h.1)⟩
  | app f a _ _ =>
    simp only [ETm.inst]
    exact ⟨fun h => ETm.noConfusion h,
      fun h => h.elim (fun h => ETm.noConfusion h) (fun h => ETm.noConfusion h.1)⟩
  | lam b _ =>
    simp only [ETm.inst]
    exact ⟨fun h => ETm.noConfusion h,
      fun h => h.elim (fun h => ETm.noConfusion h) (fun h => ETm.noConfusion h.1)⟩
  | pi a b _ _ =>
    simp only [ETm.inst]
    exact ⟨fun h => ETm.noConfusion h,
      fun h => h.elim (fun h => ETm.noConfusion h) (fun h => ETm.noConfusion h.1)⟩

/-! ## §2 per-node `eps` star-iffs -/

/-- `wk` star-status is the child's under the real `removeAt` display. The
    `keep` case lifts the child's image, which preserves `★`-ness both ways;
    every other disposition erases to the child's image unchanged. -/
theorem eps_wk_star_iff {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    {d : LocalDecl} {c : Nat} {D : TyP E n Γ e A} {σ : Level → Level} {ρ : List Disp} :
    (TyP.wk E n Γ e A d c D).eps σ ρ = .star ↔ D.eps σ (removeAt ρ c) = .star := by
  cases hρ : ρ[c]? with
  | none => rw [eps_wk_not_keep (Or.inl hρ)]
  | some disp =>
    cases disp with
    | keep =>
      rw [eps_wk_keep hρ]
      exact lift_star_iff
    | drop => rw [eps_wk_not_keep (Or.inr (Or.inl hρ))]
    | inline v => rw [eps_wk_not_keep (Or.inr (Or.inr ⟨v, hρ⟩))]

/-- `esub` at a proof-typed replacement (`levelIsZero (σ u)`): the slot drops
    and the node's star-status is the child's under the real `insertDisp .drop`
    display — the current erased action is `id`. -/
theorem eps_esub_star_drop_iff {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp} (hu : levelIsZero (σ u) = true) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).eps σ ρ = .star ↔
      D.eps σ (insertDisp .drop j ρ) = .star := by
  rw [eps_esub_drop hu]

/-- `esub` at a relevant replacement (`levelIsZero (σ u) = false`): the erased
    action is `ETm.inst (countKeep (ρ.take j)) (hv.eps σ ρ)`. The `PB[V,W]`
    answer `hr : hv.eps σ ρ ≠ .star` is taken as an explicit hypothesis —
    non-star evidence is NEVER read off the `TagCoh` being proved — and under
    it `inst_star_iff_of_ne` reduces the node's star-status to the child's
    under the real `insertDisp .keep` display. -/
theorem eps_esub_star_keep_iff_of_pb {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = false) (hr : hv.eps σ ρ ≠ .star) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).eps σ ρ = .star ↔
      D.eps σ (insertDisp .keep j ρ) = .star := by
  rw [eps_esub_keep hu]
  exact inst_star_iff_of_ne hr

/-! ## §3 the `TagCoh` compositions -/

/-- Per-side λ `TagCoh` (S20 §3): the two bodies may sit under DIFFERENT binder
    dispositions — each side's own `binderDisp (levelIsZero (σᵢ uᵢ))` — and no
    common bit `b` is imposed. `eps_lam_star_iff` reduces each λ to its body
    under its own disposition; the child's `TagCoh` transports. -/
theorem tagCoh_lam_local {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx}
    {A body : Expr Nat} {u₁ v₁ : Level} {B₁ : Expr Nat}
    {hA₁ : TyP E₁ n₁ Γ₁ A (.sort u₁)}
    {hbody₁ : TyP E₁ n₁ (.assumption A :: Γ₁) body B₁}
    {hB₁ : TyP E₁ n₁ (.assumption A :: Γ₁) B₁ (.sort v₁)}
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {u₂ v₂ : Level} {B₂ : Expr Nat}
    {hA₂ : TyP E₂ n₂ Γ₂ A (.sort u₂)}
    {hbody₂ : TyP E₂ n₂ (.assumption A :: Γ₂) body B₂}
    {hB₂ : TyP E₂ n₂ (.assumption A :: Γ₂) B₂ (.sort v₂)}
    {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp}
    (ht : TagCoh σ₁ (binderDisp (levelIsZero (σ₁ u₁)) :: ρ₁)
      σ₂ (binderDisp (levelIsZero (σ₂ u₂)) :: ρ₂) hbody₁ hbody₂) :
    TagCoh σ₁ ρ₁ σ₂ ρ₂
      (TyP.lam E₁ n₁ Γ₁ A u₁ body B₁ v₁ hA₁ hbody₁ hB₁)
      (TyP.lam E₂ n₂ Γ₂ A u₂ body B₂ v₂ hA₂ hbody₂ hB₂) :=
  eps_lam_star_iff.trans (ht.trans eps_lam_star_iff.symm)

/-- `conv` strips to the original typing child on both sides — erased `eps`
    does not inspect conversion. -/
theorem tagCoh_conv {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx} {e A₁ B₁ : Expr Nat}
    {u₁ : Level} {D₁ : TyP E₁ n₁ Γ₁ e A₁} {hc₁ : CvP E₁ n₁ Γ₁ A₁ B₁ (.sort u₁)}
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {A₂ B₂ : Expr Nat} {u₂ : Level}
    {D₂ : TyP E₂ n₂ Γ₂ e A₂} {hc₂ : CvP E₂ n₂ Γ₂ A₂ B₂ (.sort u₂)}
    {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp}
    (ht : TagCoh σ₁ ρ₁ σ₂ ρ₂ D₁ D₂) :
    TagCoh σ₁ ρ₁ σ₂ ρ₂
      (TyP.conv E₁ n₁ Γ₁ e A₁ B₁ u₁ D₁ hc₁)
      (TyP.conv E₂ n₂ Γ₂ e A₂ B₂ u₂ D₂ hc₂) :=
  ht

/-- `conv` on the left only. -/
theorem tagCoh_conv_left {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx}
    {e A₁ B₁ : Expr Nat} {u₁ : Level} {D₁ : TyP E₁ n₁ Γ₁ e A₁}
    {hc₁ : CvP E₁ n₁ Γ₁ A₁ B₁ (.sort u₁)}
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {T₂ : Expr Nat}
    {D₂ : TyP E₂ n₂ Γ₂ e T₂} {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp}
    (ht : TagCoh σ₁ ρ₁ σ₂ ρ₂ D₁ D₂) :
    TagCoh σ₁ ρ₁ σ₂ ρ₂ (TyP.conv E₁ n₁ Γ₁ e A₁ B₁ u₁ D₁ hc₁) D₂ :=
  ht

/-- `conv` on the right only. -/
theorem tagCoh_conv_right {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx}
    {e T₁ : Expr Nat} {D₁ : TyP E₁ n₁ Γ₁ e T₁}
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {A₂ B₂ : Expr Nat} {u₂ : Level}
    {D₂ : TyP E₂ n₂ Γ₂ e A₂} {hc₂ : CvP E₂ n₂ Γ₂ A₂ B₂ (.sort u₂)}
    {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp}
    (ht : TagCoh σ₁ ρ₁ σ₂ ρ₂ D₁ D₂) :
    TagCoh σ₁ ρ₁ σ₂ ρ₂ D₁ (TyP.conv E₂ n₂ Γ₂ e A₂ B₂ u₂ D₂ hc₂) :=
  ht

/-- `ewk` strips to the original typing child — the environment extension is
    erased-invisible. -/
theorem tagCoh_ewk {E₁ E₁' : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx}
    {e T₁ : Expr Nat} {hext₁ : EnvExt E₁ E₁'} {D₁ : TyP E₁ n₁ Γ₁ e T₁}
    {E₂ E₂' : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {T₂ : Expr Nat}
    {hext₂ : EnvExt E₂ E₂'} {D₂ : TyP E₂ n₂ Γ₂ e T₂}
    {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp}
    (ht : TagCoh σ₁ ρ₁ σ₂ ρ₂ D₁ D₂) :
    TagCoh σ₁ ρ₁ σ₂ ρ₂
      (TyP.ewk E₁ E₁' n₁ Γ₁ e T₁ hext₁ D₁)
      (TyP.ewk E₂ E₂' n₂ Γ₂ e T₂ hext₂ D₂) :=
  ht

/-- `cctx` strips to the original typing child with the same `ρ` — the
    innermost binder's conversion is erased-invisible. -/
theorem tagCoh_cctx {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx}
    {e T₁ A₁ A₁' : Expr Nat} {u₁ : Level}
    {D₁ : TyP E₁ n₁ (.assumption A₁ :: Γ₁) e T₁}
    {hA₁ : CvP E₁ n₁ Γ₁ A₁ A₁' (.sort u₁)}
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {T₂ A₂ A₂' : Expr Nat} {u₂ : Level}
    {D₂ : TyP E₂ n₂ (.assumption A₂ :: Γ₂) e T₂}
    {hA₂ : CvP E₂ n₂ Γ₂ A₂ A₂' (.sort u₂)}
    {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp}
    (ht : TagCoh σ₁ ρ₁ σ₂ ρ₂ D₁ D₂) :
    TagCoh σ₁ ρ₁ σ₂ ρ₂
      (TyP.cctx E₁ n₁ Γ₁ e T₁ A₁ A₁' u₁ D₁ hA₁)
      (TyP.cctx E₂ n₂ Γ₂ e T₂ A₂ A₂' u₂ D₂ hA₂) :=
  ht

/-- `wk`: each side's subject is lifted (`lift cᵢ 1 e`), so the result is the
    raw star-status iff (as `tagCoh_lsub`); `TagCoh.of_subject_eq` re-presents
    it when the lifted subjects coincide. The child's `TagCoh` runs under each
    side's own `removeAt ρᵢ cᵢ` display. -/
theorem tagCoh_wk {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx} {e A₁ : Expr Nat}
    {d₁ : LocalDecl} {c₁ : Nat} {D₁ : TyP E₁ n₁ Γ₁ e A₁}
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {A₂ : Expr Nat}
    {d₂ : LocalDecl} {c₂ : Nat} {D₂ : TyP E₂ n₂ Γ₂ e A₂}
    {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp}
    (ht : TagCoh σ₁ (removeAt ρ₁ c₁) σ₂ (removeAt ρ₂ c₂) D₁ D₂) :
    (TyP.wk E₁ n₁ Γ₁ e A₁ d₁ c₁ D₁).eps σ₁ ρ₁ = .star ↔
      (TyP.wk E₂ n₂ Γ₂ e A₂ d₂ c₂ D₂).eps σ₂ ρ₂ = .star :=
  eps_wk_star_iff.trans (ht.trans eps_wk_star_iff.symm)

/-- `linst`: each side's subject is level-instantiated, so the result is the
    raw star-status iff. The child's `TagCoh` runs under each side's own
    recomposed level map `σᵢ ∘ instLevel lsᵢ` with the display unchanged. -/
theorem tagCoh_linst {E₁ : ResolvedEnv} {a₁ n₁ : Nat} {Γ₁ : LCtx}
    {e A₁ : Expr Nat} {ls₁ : List Level}
    {hls₁ : levelsBounded n₁ ls₁ = true} {hlen₁ : ls₁.length = a₁}
    {D₁ : TyP E₁ a₁ Γ₁ e A₁}
    {E₂ : ResolvedEnv} {a₂ n₂ : Nat} {Γ₂ : LCtx} {A₂ : Expr Nat}
    {ls₂ : List Level}
    {hls₂ : levelsBounded n₂ ls₂ = true} {hlen₂ : ls₂.length = a₂}
    {D₂ : TyP E₂ a₂ Γ₂ e A₂}
    {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp}
    (ht : TagCoh (fun l => σ₁ (instLevel ls₁ l)) ρ₁
      (fun l => σ₂ (instLevel ls₂ l)) ρ₂ D₁ D₂) :
    (TyP.linst E₁ a₁ n₁ Γ₁ e A₁ ls₁ hls₁ hlen₁ D₁).eps σ₁ ρ₁ = .star ↔
      (TyP.linst E₂ a₂ n₂ Γ₂ e A₂ ls₂ hls₂ hlen₂ D₂).eps σ₂ ρ₂ = .star := by
  rw [eps_linst, eps_linst]
  exact ht

/-- `esub`, proof-typed replacement on both sides: the child's `TagCoh` under
    each side's real `insertDisp .drop jᵢ` display gives the nodes'
    star-status iff. -/
theorem tagCoh_esub_drop {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx}
    {e A₁ t₁ v₁ : Expr Nat} {j₁ : Nat} {u₁ : Level} {D₁ : TyP E₁ n₁ Γ₁ e A₁}
    {hget₁ : Γ₁[j₁]? = some (.assumption t₁)}
    {hv₁ : TyP E₁ n₁ (substRemove v₁ j₁ Γ₁) (lift 0 j₁ v₁) (lift 0 j₁ t₁)}
    {hvT₁ : TyP E₁ n₁ (substRemove v₁ j₁ Γ₁) (lift 0 j₁ t₁) (.sort u₁)}
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {A₂ t₂ v₂ : Expr Nat}
    {j₂ : Nat} {u₂ : Level} {D₂ : TyP E₂ n₂ Γ₂ e A₂}
    {hget₂ : Γ₂[j₂]? = some (.assumption t₂)}
    {hv₂ : TyP E₂ n₂ (substRemove v₂ j₂ Γ₂) (lift 0 j₂ v₂) (lift 0 j₂ t₂)}
    {hvT₂ : TyP E₂ n₂ (substRemove v₂ j₂ Γ₂) (lift 0 j₂ t₂) (.sort u₂)}
    {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp}
    (hu₁ : levelIsZero (σ₁ u₁) = true) (hu₂ : levelIsZero (σ₂ u₂) = true)
    (ht : TagCoh σ₁ (insertDisp .drop j₁ ρ₁) σ₂ (insertDisp .drop j₂ ρ₂) D₁ D₂) :
    (TyP.esub E₁ n₁ Γ₁ e A₁ t₁ v₁ j₁ u₁ D₁ hget₁ hv₁ hvT₁).eps σ₁ ρ₁ = .star ↔
      (TyP.esub E₂ n₂ Γ₂ e A₂ t₂ v₂ j₂ u₂ D₂ hget₂ hv₂ hvT₂).eps σ₂ ρ₂ = .star :=
  (eps_esub_star_drop_iff hu₁).trans
    (ht.trans (eps_esub_star_drop_iff hu₂).symm)

/-- `esub`, relevant replacement on both sides — the PB-gated case (S20 §4).
    Each side's `PB[V,W]` answer `hrᵢ : hvᵢ.eps σᵢ ρᵢ ≠ .star` is an explicit
    hypothesis, consumed by `inst_star_iff_of_ne` BEFORE the child's `TagCoh`
    under the real `insertDisp .keep jᵢ` displays is applied. -/
theorem tagCoh_esub_of_pb {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx}
    {e A₁ t₁ v₁ : Expr Nat} {j₁ : Nat} {u₁ : Level} {D₁ : TyP E₁ n₁ Γ₁ e A₁}
    {hget₁ : Γ₁[j₁]? = some (.assumption t₁)}
    {hv₁ : TyP E₁ n₁ (substRemove v₁ j₁ Γ₁) (lift 0 j₁ v₁) (lift 0 j₁ t₁)}
    {hvT₁ : TyP E₁ n₁ (substRemove v₁ j₁ Γ₁) (lift 0 j₁ t₁) (.sort u₁)}
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {A₂ t₂ v₂ : Expr Nat}
    {j₂ : Nat} {u₂ : Level} {D₂ : TyP E₂ n₂ Γ₂ e A₂}
    {hget₂ : Γ₂[j₂]? = some (.assumption t₂)}
    {hv₂ : TyP E₂ n₂ (substRemove v₂ j₂ Γ₂) (lift 0 j₂ v₂) (lift 0 j₂ t₂)}
    {hvT₂ : TyP E₂ n₂ (substRemove v₂ j₂ Γ₂) (lift 0 j₂ t₂) (.sort u₂)}
    {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp}
    (hu₁ : levelIsZero (σ₁ u₁) = false) (hu₂ : levelIsZero (σ₂ u₂) = false)
    (hr₁ : hv₁.eps σ₁ ρ₁ ≠ .star) (hr₂ : hv₂.eps σ₂ ρ₂ ≠ .star)
    (ht : TagCoh σ₁ (insertDisp .keep j₁ ρ₁) σ₂ (insertDisp .keep j₂ ρ₂) D₁ D₂) :
    (TyP.esub E₁ n₁ Γ₁ e A₁ t₁ v₁ j₁ u₁ D₁ hget₁ hv₁ hvT₁).eps σ₁ ρ₁ = .star ↔
      (TyP.esub E₂ n₂ Γ₂ e A₂ t₂ v₂ j₂ u₂ D₂ hget₂ hv₂ hvT₂).eps σ₂ ρ₂ = .star :=
  (eps_esub_star_keep_iff_of_pb hu₁ hr₁).trans
    (ht.trans (eps_esub_star_keep_iff_of_pb hu₂ hr₂).symm)

/-! ## §4 controls (S20 §7) -/

/-- Control context: one relevant `Prop`-level assumption — `Γ = [x : sort 0]`
    (`sort 0 : sort 1`, a TYPE, not a proof). -/
def a7CtrlΓ : LCtx := [.assumption (.sort .zero)]

/-- `sort 0 : sort 1` inside `a7CtrlΓ`. -/
def a7CtrlS0 : TyP emptyEnv 0 a7CtrlΓ (.sort .zero) (.sort (.succ .zero)) :=
  .sort _ _ _ _ _ (eqN_refl _)

/-- `sort 0 : sort 1` under the lam's own binder context. -/
def a7CtrlBody : TyP emptyEnv 0 (.assumption (.sort .zero) :: a7CtrlΓ)
    (.sort .zero) (.sort (.succ .zero)) :=
  .sort _ _ _ _ _ (eqN_refl _)

/-- `λ (_ : sort 0). sort 0 : ∀ _ : sort 0, sort 1` in `a7CtrlΓ`. -/
def a7CtrlLam : TyP emptyEnv 0 a7CtrlΓ
    (.lam (.sort .zero) (.sort .zero)) (.pi (.sort .zero) (.sort (.succ .zero))) :=
  .lam _ _ _ (.sort .zero) (.succ .zero) (.sort .zero) (.sort (.succ .zero))
    (.succ (.succ .zero)) a7CtrlS0 a7CtrlBody
    (.sort _ _ _ _ _ (eqN_refl _))

/-- The context variable `#0 : sort 0` — a TYPE-level argument: `eps_bvar_rel`
    resolves it through the display, so `keep` gives `bvar 0` and `drop` gives
    `★`. -/
def a7CtrlArg : TyP emptyEnv 0 a7CtrlΓ (.bvar 0) (.sort .zero) :=
  .bvar _ _ _ 0 (.sort .zero) (.succ .zero) rfl a7CtrlS0

/-- `(λ (_ : sort 0). sort 0) #0 : sort 1`. -/
def a7CtrlApp : TyP emptyEnv 0 a7CtrlΓ
    (.app (.lam (.sort .zero) (.sort .zero)) (.bvar 0)) (.sort (.succ .zero)) :=
  .app _ _ _ (.lam (.sort .zero) (.sort .zero)) (.bvar 0) (.sort .zero)
    (.sort (.succ .zero)) (.succ (.succ .zero)) a7CtrlLam a7CtrlArg
    (.sort _ _ _ _ _ (eqN_refl _))

/-- The lam's erasure is `.lam (.sort .zero)` under either display — the binder
    is kept (a `sort 1` domain bit is nonzero) and the body is `sort 0`. -/
theorem a7CtrlLam_keep_eps : a7CtrlLam.eps id [.keep] = .lam (.sort .zero) := rfl

theorem a7CtrlLam_drop_eps : a7CtrlLam.eps id [.drop] = .lam (.sort .zero) := rfl

/-- §7 control (a): the same application under displays whose ARGUMENT
    star-statuses differ — `bvar 0` under `[.keep]`, `★` under `[.drop]` —
    still coheres, because `app` star-status is exactly the function's
    (`eps_app_star_iff`). Kernel values pinned below. -/
theorem a7Ctrl_arg_status_differs :
    a7CtrlArg.eps id [.keep] = .bvar 0 ∧ a7CtrlArg.eps id [.drop] = .star :=
  ⟨rfl, rfl⟩

theorem a7CtrlApp_keep_eps :
    a7CtrlApp.eps id [.keep] = .app (.lam (.sort .zero)) (.bvar 0) := rfl

theorem a7CtrlApp_drop_eps : a7CtrlApp.eps id [.drop] = .lam (.sort .zero) := rfl

/-- §7 control (b): `TagCoh` of the two displayed applications despite the
    differing argument star-statuses — `tagCoh_app` consumes only the
    function's correspondence. -/
theorem a7Ctrl_app_coh_arg_status_differs :
    TagCoh id [.keep] id [.drop] a7CtrlApp a7CtrlApp :=
  tagCoh_app (show a7CtrlLam.eps id [.keep] = .star ↔ a7CtrlLam.eps id [.drop] = .star
    from by rw [a7CtrlLam_keep_eps, a7CtrlLam_drop_eps])

/-- §7 negative control: `inst` with `r = ★` produces `★` at the substituted
    index even though the body is NOT `★` — the premise of
    `inst_star_iff_of_ne` is load-bearing and a `★` replacement must never be
    presented as satisfying it. -/
theorem inst_star_needs_ne :
    ETm.inst 0 .star (.bvar 0) = .star ∧ ETm.bvar 0 ≠ .star :=
  ⟨rfl, ETm.noConfusion⟩

end Rcic.Syn

#print axioms Rcic.Syn.lift_star_iff
#print axioms Rcic.Syn.inst_star_iff_of_ne
#print axioms Rcic.Syn.inst_star_iff
#print axioms Rcic.Syn.eps_wk_star_iff
#print axioms Rcic.Syn.eps_esub_star_drop_iff
#print axioms Rcic.Syn.eps_esub_star_keep_iff_of_pb
#print axioms Rcic.Syn.tagCoh_lam_local
#print axioms Rcic.Syn.tagCoh_conv
#print axioms Rcic.Syn.tagCoh_conv_left
#print axioms Rcic.Syn.tagCoh_conv_right
#print axioms Rcic.Syn.tagCoh_ewk
#print axioms Rcic.Syn.tagCoh_cctx
#print axioms Rcic.Syn.tagCoh_wk
#print axioms Rcic.Syn.tagCoh_linst
#print axioms Rcic.Syn.tagCoh_esub_drop
#print axioms Rcic.Syn.tagCoh_esub_of_pb
#print axioms Rcic.Syn.a7CtrlΓ
#print axioms Rcic.Syn.a7CtrlS0
#print axioms Rcic.Syn.a7CtrlBody
#print axioms Rcic.Syn.a7CtrlLam
#print axioms Rcic.Syn.a7CtrlArg
#print axioms Rcic.Syn.a7CtrlApp
#print axioms Rcic.Syn.a7CtrlLam_keep_eps
#print axioms Rcic.Syn.a7CtrlLam_drop_eps
#print axioms Rcic.Syn.a7Ctrl_arg_status_differs
#print axioms Rcic.Syn.a7CtrlApp_keep_eps
#print axioms Rcic.Syn.a7CtrlApp_drop_eps
#print axioms Rcic.Syn.a7Ctrl_app_coh_arg_status_differs
#print axioms Rcic.Syn.inst_star_needs_ne

import rcic.RcicSynSRClEutApp

/-!
# RcicSynSRClEutOther — row 15's `eutOther` residual cell (cc 03:15Z)

The `es_eut_field` residual premise covers non-`.conv` cells with a
transport-headed operand (`wk`/`esub`/`lsub`/`linst`/`ewk`/`cctx`).
Measured, none is an erasure fact about two typings of ONE smaller
subject at a routed display:

* `wk`/`esub`/`lsub`/`linst` retype at a DIFFERENT context AND a
  transported subject (`lift c 1 e`, `instantiate j … e`,
  `instantiateLevels ls e`) — the dispatch's same-subject cast is
  genuinely stuck, so no `.cl`/`.eut` pairing exists;
* `wk` additionally SPLITS the display: the payload's erasure runs at
  `removeAt ρ c` while the co-operand's runs at `ρ`
  (`reg2_eps_wk_not_keep`/`_keep`) — no query kind pairs two displays;
* `esub`/`lsub` shift by `insertDisp` (and wrap `ETm.inst`/`inline` on
  the keep branch) — same split, plus a wrapper;
* `linst` moves the level map (`σ ∘ instLevel ls`);
* `ewk`/`cctx` keep subject, display and map but move the ENV / the
  binder's type (`goal_eut_ewk_is_cross_env_payload`, `rfl`): the goal
  is the payload pair's EUT goal verbatim — unstateable, since the
  kinds unify the environment / the context.

Named wall: `eutOtherP_tableOfI` (the exact residual premise shape at
`tableOfI`); not refuted, not claimed; nonvacuous at the identical
instance (`eutOtherP_ident_sat`). `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- The generic residual-cell unfold (`rfl`): every `eutOther` goal is
    the conversion of the two operands' TYPE-erasures through `reg.2` —
    the measurement base for each transport arm. -/
theorem goal_eut_residual_unfold {tbl : List CRule}
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Goal tbl (.eut D₁ D₂ S σ ρ) =
      ConvMod (EStep tbl) LvlEq (D₁.reg.2.eps σ ρ) (D₂.reg.2.eps σ ρ) := rfl

/-- The `wk` arm's display split (not-keep branch): the wk operand's
    type-erasure runs at `removeAt ρ c` — a DIFFERENT display from the
    co-operand's `ρ`. No query kind pairs two typings at two displays,
    and the payload sits at `insertAt d c Γ` under `lift c 1 e`. -/
theorem reg2_eps_wk_not_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} {d : LocalDecl} {c : Nat} {D : TyP E n Γ e A}
    {σ : Level → Level} {ρ : List Disp}
    (hk : ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v)) :
    (TyP.wk E n Γ e A d c D).reg.2.eps σ ρ
      = D.reg.2.eps σ (removeAt ρ c) := by
  show (TyP.wk E n Γ A _ d c D.reg.2).eps σ ρ = _
  exact eps_wk_not_keep hk

/-- The `wk` arm's display split (keep branch): additionally a de Bruijn
    `lift` by the kept prefix — a THIRD display discipline no kind
    states. -/
theorem reg2_eps_wk_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} {d : LocalDecl} {c : Nat} {D : TyP E n Γ e A}
    {σ : Level → Level} {ρ : List Disp} (hk : ρ[c]? = some .keep) :
    (TyP.wk E n Γ e A d c D).reg.2.eps σ ρ
      = (D.reg.2.eps σ (removeAt ρ c)).lift (countKeep (ρ.take c)) 1 := by
  show (TyP.wk E n Γ A _ d c D.reg.2).eps σ ρ = _
  exact eps_wk_keep hk

/-- The `ewk` arm (`rfl`): the residual goal IS the payload pair's EUT
    goal verbatim — same subject, display, and level map; the ONLY move
    is the environment (`D₁ : TyP E₀ …`, `D₂ : TyP E …`), and the query
    kinds unify the environment, so no `.eut`/`.cl` can state the pair.
    `cctx` is the same shape with the binder's type moved. -/
theorem goal_eut_ewk_is_cross_env_payload {tbl : List CRule}
    {Eₐ E₀' E₀ E : ResolvedEnv} {n₀' n : Nat} {Γ₀' Γ : LCtx}
    {e A T₂ : Expr Nat} {hext : EnvExt E₀ E}
    (D₁ : TyP E₀ n Γ e A) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (ρ : List Disp) :
    Goal tbl (.eut (TyP.ewk E₀ E n Γ e A hext D₁) D₂ S σ ρ) =
      ConvMod (EStep tbl) LvlEq (D₁.reg.2.eps σ ρ) (D₂.reg.2.eps σ ρ) := rfl

/-! ## cc 05:45Z ask 2: per-arm reductions (the `esW_*` transport
pattern at the `TyP` cell layer). Each transport/transport residual
goal reduces, by the LANDED `eps_*` commutations applied to both sides,
to the payload pair's EUT goal at the moved `(σ, ρ)` — plus, on keep
branches, a congruence closure. The payload edge itself is NOT issuable:
the stuck cast node is `occ_eut`/`occ_cl`'s same-site cast
(`Dᵢ : TyP q.site.E q.site.n q.site.Γ e Tᵢ` — one context, one subject),
while transport payloads sit at their own context/subject; the ES layer
has the precedent rows (`wk_es`, `esub_es`, `linst_es`, `ewk_es`,
`cctx_es`), the EUT/CL layer has none. -/

/-- `esub` reg-commutation, drop branch. -/
theorem reg2_eps_esub_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level}
    {D : TyP E n Γ e A} {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp} (hu : levelIsZero (σ u) = true) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).reg.2.eps σ ρ
      = D.reg.2.eps σ (insertDisp .drop j ρ) := by
  show (TyP.esub E n Γ A _ t v j u D.reg.2 hget hv hvT).eps σ ρ = _
  exact eps_esub_drop hu

/-- `esub` reg-commutation, keep branch (the `ETm.inst` wrapper). -/
theorem reg2_eps_esub_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level}
    {D : TyP E n Γ e A} {hget : Γ[j]? = some (.assumption t)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp} (hu : levelIsZero (σ u) = false) :
    (TyP.esub E n Γ e A t v j u D hget hv hvT).reg.2.eps σ ρ
      = ETm.inst (countKeep (ρ.take j)) (hv.eps σ ρ)
          (D.reg.2.eps σ (insertDisp .keep j ρ)) := by
  show (TyP.esub E n Γ A _ t v j u D.reg.2 hget hv hvT).eps σ ρ = _
  exact eps_esub_keep hu

/-- `lsub` reg-commutation at the star/drop arm. -/
theorem reg2_eps_lsub_star {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level}
    {D : TyP E n Γ e A} {hget : Γ[j]? = some (.letBinding t v)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp} (hstar : hv.eps σ ρ = .star) :
    (TyP.lsub E n Γ e A t v j u D hget hv hvT).reg.2.eps σ ρ
      = D.reg.2.eps σ (insertDisp .drop j ρ) := by
  show (TyP.lsub E n Γ A _ t v j u D.reg.2 hget hv hvT).eps σ ρ = _
  rw [eps_lsub, hstar]

/-- `linst` reg-commutation (the composite level map). -/
theorem reg2_eps_linst {E : ResolvedEnv} {a n : Nat} {Γ : LCtx} {e A : Expr Nat}
    {ls : List Level} {hls : levelsBounded n ls = true} {hlen : ls.length = a}
    {D : TyP E a Γ e A} {σ : Level → Level} {ρ : List Disp} :
    (TyP.linst E a n Γ e A ls hls hlen D).reg.2.eps σ ρ
      = D.reg.2.eps (fun l => σ (instLevel ls l)) ρ := by
  show (TyP.linst E a n Γ A _ ls hls hlen D.reg.2).eps σ ρ = _
  exact eps_linst σ ρ

/-- `ewk` reg-commutation (verbatim). -/
theorem reg2_eps_ewk {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    {hext : EnvExt E₀ E} {D : TyP E₀ n Γ e A} {σ : Level → Level} {ρ : List Disp} :
    (TyP.ewk E₀ E n Γ e A hext D).reg.2.eps σ ρ = D.reg.2.eps σ ρ := by
  show (TyP.ewk E₀ E n Γ A _ hext D.reg.2).eps σ ρ = _
  exact eps_ewk σ ρ

/-- `wk`/`wk` (same `c`), not-keep: the residual goal IS the payload
    pair's EUT goal at `removeAt ρ c` — the `wk_es` display move, at the
    TyP layer. Stuck cast node: `occ_eut`'s same-site cast (payloads at
    `Γ` typing `e`, the cell site `insertAt d c Γ` typing
    `lift c 1 e`); no `wk_eut` Issues row exists. -/
theorem goal_eut_wk_wk_not_keep {tbl : List CRule}
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e A₁ A₂ : Expr Nat} {d : LocalDecl} {c : Nat}
    (D₁ : TyP E n Γ e A₁) (D₂ : TyP E n Γ e A₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v)) :
    Goal tbl (.eut (TyP.wk E n Γ e A₁ d c D₁) (TyP.wk E n Γ e A₂ d c D₂) S σ ρ)
      = Goal tbl (.eut D₁ D₂ S σ (removeAt ρ c)) := by
  simp only [goal_eut_residual_unfold, reg2_eps_wk_not_keep hk]

/-- `wk`/`wk`, keep: commutation to `removeAt ρ c` PLUS a de Bruijn
    `lift (countKeep (ρ.take c)) 1` on each side (the `esW_wk_keep`
    closure is `convMod_lift`, TableClosed; the epsW regime reads the
    child at `wkInnerDisp ρ c`, which refines `removeAt` exactly here).
    Stuck cast node: the site cast as above, plus the lift congruence. -/
theorem goal_eut_wk_wk_keep {tbl : List CRule}
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e A₁ A₂ : Expr Nat} {d : LocalDecl} {c : Nat}
    (D₁ : TyP E n Γ e A₁) (D₂ : TyP E n Γ e A₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = some .keep) :
    Goal tbl (.eut (TyP.wk E n Γ e A₁ d c D₁) (TyP.wk E n Γ e A₂ d c D₂) S σ ρ)
      = ConvMod (EStep tbl) LvlEq
          ((D₁.reg.2.eps σ (removeAt ρ c)).lift (countKeep (ρ.take c)) 1)
          ((D₂.reg.2.eps σ (removeAt ρ c)).lift (countKeep (ρ.take c)) 1) := by
  simp only [goal_eut_residual_unfold, reg2_eps_wk_keep hk]

/-- `esub`/`esub` (same `Γ j v`), drop: the goal IS the payload pair's
    EUT goal at `insertDisp .drop j ρ` (the `esub_es` display move).
    Stuck cast node: `occ_eut`'s same-site cast (payloads at `Γ` typing
    `e`, the cell site `substRemove v j Γ` typing
    `instantiate j (lift 0 j v) e`). -/
theorem goal_eut_esub_esub_drop {tbl : List CRule}
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.assumption t)}
    {hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    (D₁ : TyP E n Γ e A₁) (D₂ : TyP E n Γ e A₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ u) = true) :
    Goal tbl (.eut (TyP.esub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.esub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ)
      = Goal tbl (.eut D₁ D₂ S σ (insertDisp .drop j ρ)) := by
  simp only [goal_eut_residual_unfold, reg2_eps_esub_drop hu]

/-- `esub`/`esub`, keep: the goal reduces to the `ETm.inst` composite —
    payload EUT at `insertDisp .keep j ρ` under the wrapper, closed (over
    a `TableClosed` table) by `convMod_inst_body` ∘ `convMod_inst_repl`
    with the VALUE pair — `eut_app_nodes_keep`'s `hmid` pattern verbatim.
    Stuck cast node: the value typings `hv₁ hv₂` sit at
    `substRemove v j Γ`, off the cell's site — the same off-site cast. -/
theorem goal_eut_esub_esub_keep {tbl : List CRule}
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.assumption t)}
    {hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    (D₁ : TyP E n Γ e A₁) (D₂ : TyP E n Γ e A₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ u) = false) :
    Goal tbl (.eut (TyP.esub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.esub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ)
      = ConvMod (EStep tbl) LvlEq
          (ETm.inst (countKeep (ρ.take j)) (hv₁.eps σ ρ)
            (D₁.reg.2.eps σ (insertDisp .keep j ρ)))
          (ETm.inst (countKeep (ρ.take j)) (hv₂.eps σ ρ)
            (D₂.reg.2.eps σ (insertDisp .keep j ρ))) := by
  simp only [goal_eut_residual_unfold, reg2_eps_esub_keep hu]

/-- `lsub`/`lsub`, star arm (both values erase to `★`): the goal IS the
    payload pair's EUT goal at `insertDisp .drop j ρ`. The inline arm
    additionally wraps `localize (countKeep (ρ.take j)) ev` — the third
    display discipline (measured M6). Stuck cast node: the site cast,
    as `esub`. -/
theorem goal_eut_lsub_lsub_star {tbl : List CRule}
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.letBinding t v)}
    {hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    (D₁ : TyP E n Γ e A₁) (D₂ : TyP E n Γ e A₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hstar₁ : hv₁.eps σ ρ = .star) (hstar₂ : hv₂.eps σ ρ = .star) :
    Goal tbl (.eut (TyP.lsub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.lsub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ)
      = Goal tbl (.eut D₁ D₂ S σ (insertDisp .drop j ρ)) := by
  simp only [goal_eut_residual_unfold, reg2_eps_lsub_star hstar₁,
    reg2_eps_lsub_star hstar₂]

/-- `linst`/`linst` (same `ls`): the goal IS the payload pair's EUT
    goal at the COMPOSITE map `σ ∘ instLevel ls` (the `linst_es` move).
    Stuck cast node: the issued query's level map is the cell's own `σ`
    (`occ_eut` does not reparameterize it), and the payloads sit at
    `instLvlsCtx ls Γ`/`a` — off the cell site on both context and
    level-map. -/
theorem goal_eut_linst_linst {tbl : List CRule}
    {Eₐ E₀ E : ResolvedEnv} {n₀ a n : Nat} {Γ₀ Γ : LCtx}
    {e A₁ A₂ : Expr Nat} {ls : List Level}
    {hls : levelsBounded n ls = true} {hlen : ls.length = a}
    (D₁ : TyP E a Γ e A₁) (D₂ : TyP E a Γ e A₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Goal tbl (.eut (TyP.linst E a n Γ e A₁ ls hls hlen D₁)
        (TyP.linst E a n Γ e A₂ ls hls hlen D₂) S σ ρ)
      = Goal tbl (.eut D₁ D₂ S (fun l => σ (instLevel ls l)) ρ) := by
  simp only [goal_eut_residual_unfold, reg2_eps_linst]

/-- `ewk`/`ewk`: the goal IS the payload pair's EUT goal VERBATIM (same
    `σ ρ`) — pure env move (`ewk_es` precedent). Stuck cast node: the
    payloads sit at `E₀`, the cell site at `E` — `occ_eut`'s same-site
    cast again; this is the identical-instance shape of M6's
    cross-env measurement, now on the reducible diagonal. -/
theorem goal_eut_ewk_ewk {tbl : List CRule}
    {Eₐ E₀' E₀ E : ResolvedEnv} {n₀' n : Nat} {Γ₀' Γ : LCtx}
    {e A₁ A₂ : Expr Nat} {hext : EnvExt E₀ E}
    (D₁ : TyP E₀ n Γ e A₁) (D₂ : TyP E₀ n Γ e A₂)
    (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (ρ : List Disp) :
    Goal tbl (.eut (TyP.ewk E₀ E n Γ e A₁ hext D₁)
        (TyP.ewk E₀ E n Γ e A₂ hext D₂) S σ ρ)
      = Goal tbl (.eut D₁ D₂ S σ ρ) := by
  simp only [goal_eut_residual_unfold, reg2_eps_ewk]

/-! ## The named wall, and its nonvacuity -/

/-- The row-15 `eutOther` premise, exact, at `tbl := tableOfI hW` — the
    ONE named Prop the residual cell retains. NOT claimed, NOT refuted:
    the six transport arms are measured above (context/subject/env moves,
    display splits); no on-cone falsity route is claimed. -/
def eutOtherP_tableOfI {Eₐ E : ResolvedEnv} (hW : EnvWfT E) : Prop :=
  ∀ (Aw : Nat → Nat) {E' : ResolvedEnv} {n : Nat}
    {Γ Γ₁ Γ₂ : LCtx} {e e₁ e₂ T₁ T₂ : Expr Nat}
    {E₀' : ResolvedEnv} {n₀' : Nat} {Γ₀' : LCtx}
    (D₁ : TyP E' n Γ₁ e₁ T₁) (D₂ : TyP E' n Γ₂ e₂ T₂)
    (hΓ₁ : Γ₁ = Γ) (he₁ : e₁ = e) (hΓ₂ : Γ₂ = Γ) (he₂ : e₂ = e)
    (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (ρ : List Disp),
    eutResidualTag D₁.headTag D₂.headTag = true →
    CaseStep Aw (tableOfI hW)
      (.eut (hΓ₁ ▸ he₁ ▸ D₁) (hΓ₂ ▸ he₂ ▸ D₂) S σ ρ)

/-- The named wall is not vacuous: at the identical instance — the SAME
    `ewk`-transported derivation on both sides — the residual premise's
    conclusion is inhabited (the goal is reflexive), and the tag fires. -/
theorem eutOtherP_ident_sat {tbl : List CRule} {Eₐ E₀' E₀ E : ResolvedEnv}
    {n₀' n : Nat} {Γ₀' Γ : LCtx} {e A : Expr Nat} {hext : EnvExt E₀ E}
    (D : TyP E₀ n Γ e A) (S : ScopedCtx Eₐ E₀' n₀' Γ₀')
    (σ : Level → Level) (ρ : List Disp) (Aw : Nat → Nat) :
    eutResidualTag (TyP.ewk E₀ E n Γ e A hext D).headTag
        (TyP.ewk E₀ E n Γ e A hext D).headTag = true ∧
      CaseStep Aw tbl (.eut (TyP.ewk E₀ E n Γ e A hext D)
        (TyP.ewk E₀ E n Γ e A hext D) S σ ρ) :=
  ⟨rfl, fun _ _ => ConvMod.refl _⟩

#print axioms Rcic.Syn.goal_eut_residual_unfold
#print axioms Rcic.Syn.reg2_eps_wk_not_keep
#print axioms Rcic.Syn.reg2_eps_wk_keep
#print axioms Rcic.Syn.goal_eut_ewk_is_cross_env_payload
#print axioms Rcic.Syn.eutOtherP_tableOfI
#print axioms Rcic.Syn.eutOtherP_ident_sat
#print axioms Rcic.Syn.reg2_eps_esub_drop
#print axioms Rcic.Syn.reg2_eps_esub_keep
#print axioms Rcic.Syn.reg2_eps_lsub_star
#print axioms Rcic.Syn.reg2_eps_linst
#print axioms Rcic.Syn.reg2_eps_ewk
#print axioms Rcic.Syn.goal_eut_wk_wk_not_keep
#print axioms Rcic.Syn.goal_eut_wk_wk_keep
#print axioms Rcic.Syn.goal_eut_esub_esub_drop
#print axioms Rcic.Syn.goal_eut_esub_esub_keep
#print axioms Rcic.Syn.goal_eut_lsub_lsub_star
#print axioms Rcic.Syn.goal_eut_linst_linst
#print axioms Rcic.Syn.goal_eut_ewk_ewk

end Rcic.Syn

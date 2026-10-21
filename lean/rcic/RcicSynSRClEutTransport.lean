import rcic.RcicSynSRClEutOther
import rcic.RcicSynES

/-!
# RcicSynSRClEutTransport — the EUT/CL transport issue rows (cc 06:05Z)

The ES layer has transport issue rows (`Issues.wk_es`, `esub_es`, `linst_es`,
`ewk_es`, `cctx_es`); the EUT/CL layer had none (M6/M7's measured gap —
`occ_eut`/`occ_cl`'s same-site cast cannot reparameterize). This module adds
them: `IssuesCT` = `IssuesC` plus one row per transport arm, issuing the EUT
(resp. CL) query on the PAYLOAD pair at the moved `(σ, ρ)`, plus the value-pair
CL row the `esub` keep arm's `ETm.inst` wrapper consumes:

* `wk` → payload at `removeAt ρ c` (keep arm: + `convMod_lift` congruence);
* `ewk` → payload verbatim (`eps_ewk` is `rfl`, pure env move);
* `esub` → payload at `insertDisp (binderDisp (levelIsZero (σ u))) j ρ` —
  the landed `esub_es` display move; the keep arm's `ETm.inst` wrapper closes
  by `convMod_inst` with the issued VALUE-pair CL (`*_esub_clv`),
  `eut_app_nodes_keep`'s `hmid` pattern;
* `lsub` (star arm) → payload at `insertDisp .drop j ρ`; the target's
  routedness is a ROW PREMISE (`RoutedDisp` has no lsub constructor — the
  row carries it instead of assuming it). The inline arm stays in the wall;
* `linst` → payload at `σ ∘ instLevel ls` (`LevelHom.linst` preserves Hom);
* `cctx` → payload verbatim at the source binder (`RoutedDisp.cctx`,
  `eps_cctx` `rfl`), `cctx_es`'s analogue. Included: `StepHeadTag.isTransport`
  counts six arms and the row's site needs a shared source binder to be
  well-formed — exactly the reducible diagonal.

Answer transports: the M6/M7 EUT diagonals (`goal_eut_*`,
`RcicSynSRClEutOther`) and the CL analogues (`goal_cl_*` here, the `eps_*`
commutations verbatim) reduce each cell's goal to the payload goal at the
moved parameters; keep branches add `convMod_lift`/`convMod_inst`
(`TableClosed`). Ranks: `wk`/`ewk`/`linst` keep the atoms and drop one weight
(`lexDM_cvMeas_wk`'s pattern at the pair measure); `esub`/`lsub`/`cctx` and
the value rows drop the child atoms as a strict sub-multiset
(`dmStep_perm_right` ∘ `dmStep_drop` over `perm_transport_*`). No answer
transport is false; no on-cone instance against one. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative
open DispForPathPins

/-! ## §1 `IssuesCT` — `IssuesC` plus the transport payload rows -/

/-- The transport issue rows: `IssuesC` plus, for each transport arm, the EUT
    (resp. CL) query on the PAYLOAD pair at the moved `(σ, ρ)` — `wk_es` /
    `esub_es` / `linst_es` / `ewk_es` / `cctx_es` verbatim at the TyP-pair
    kinds. `lsub` has no `RoutedDisp` constructor, so its rows carry the
    target's routedness; `esub`'s value pair (`*_esub_clv`) stays at the site
    (same context `substRemove v j Γ`, same display `ρ`). -/
inductive IssuesCT {Eₐ : ResolvedEnv} : P2Query Eₐ → P2Query Eₐ → Prop where
  | old {q q' : P2Query Eₐ} (h : IssuesC q q') : IssuesCT q q'
  -- wk (cc order 1): the payload pair at `removeAt ρ c`.
  | eut_wk_eut {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {e A₁ A₂ : Expr Nat}
      {d : LocalDecl} {c : Nat}
      (D₁ : TyP E n Γ e A₁) (D₂ : TyP E n Γ e A₂)
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
      IssuesCT (P2Query.eut (TyP.wk E n Γ e A₁ d c D₁) (TyP.wk E n Γ e A₂ d c D₂) S σ ρ)
        (P2Query.eut D₁ D₂ S σ (removeAt ρ c))
  | cl_wk_cl {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {e A₁ A₂ : Expr Nat}
      {d : LocalDecl} {c : Nat}
      (D₁ : TyP E n Γ e A₁) (D₂ : TyP E n Γ e A₂)
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
      IssuesCT (P2Query.cl (TyP.wk E n Γ e A₁ d c D₁) (TyP.wk E n Γ e A₂ d c D₂) S σ ρ)
        (P2Query.cl D₁ D₂ S σ (removeAt ρ c))
  -- ewk (cc order 2): the payload pair verbatim at the source env.
  | eut_ewk_eut {E₀ E₀' E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {e A₁ A₂ : Expr Nat}
      {hext : EnvExt E₀ E}
      (D₁ : TyP E₀ n Γ e A₁) (D₂ : TyP E₀ n Γ e A₂)
      (S : ScopedCtx Eₐ E₀' n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
      IssuesCT (P2Query.eut (TyP.ewk E₀ E n Γ e A₁ hext D₁) (TyP.ewk E₀ E n Γ e A₂ hext D₂) S σ ρ)
        (P2Query.eut D₁ D₂ S σ ρ)
  | cl_ewk_cl {E₀ E₀' E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {e A₁ A₂ : Expr Nat}
      {hext : EnvExt E₀ E}
      (D₁ : TyP E₀ n Γ e A₁) (D₂ : TyP E₀ n Γ e A₂)
      (S : ScopedCtx Eₐ E₀' n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
      IssuesCT (P2Query.cl (TyP.ewk E₀ E n Γ e A₁ hext D₁) (TyP.ewk E₀ E n Γ e A₂ hext D₂) S σ ρ)
        (P2Query.cl D₁ D₂ S σ ρ)
  -- esub (cc order 3): the payload pair at the `esub_es` display, plus the
  -- value-pair CL at the site (the keep arm's `inst` wrapper).
  | eut_esub_eut {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
      {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level} {hget : Γ[j]? = some (.assumption t)}
      (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
      IssuesCT (P2Query.eut (TyP.esub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.esub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ)
        (P2Query.eut D₁ D₂ S σ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ))
  | cl_esub_cl {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
      {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level} {hget : Γ[j]? = some (.assumption t)}
      (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
      IssuesCT (P2Query.cl (TyP.esub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.esub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ)
        (P2Query.cl D₁ D₂ S σ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ))
  | eut_esub_clv {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
      {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level} {hget : Γ[j]? = some (.assumption t)}
      (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
      IssuesCT (P2Query.eut (TyP.esub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.esub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ)
        (P2Query.cl hv₁ hv₂ S σ ρ)
  | cl_esub_clv {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
      {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level} {hget : Γ[j]? = some (.assumption t)}
      (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
      IssuesCT (P2Query.cl (TyP.esub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.esub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ)
        (P2Query.cl hv₁ hv₂ S σ ρ)
  -- lsub (cc order 4): the payload pair at `insertDisp .drop j ρ`; the
  -- target's routedness is a row premise (no `RoutedDisp.lsub` exists).
  | eut_lsub_eut {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
      {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level} {hget : Γ[j]? = some (.letBinding t v)}
      (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
      (hr : RoutedDisp σ E n Γ (insertDisp .drop j ρ)) :
      IssuesCT (P2Query.eut (TyP.lsub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.lsub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ)
        (P2Query.eut D₁ D₂ S σ (insertDisp .drop j ρ))
  | cl_lsub_cl {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
      {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level} {hget : Γ[j]? = some (.letBinding t v)}
      (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
      (hr : RoutedDisp σ E n Γ (insertDisp .drop j ρ)) :
      IssuesCT (P2Query.cl (TyP.lsub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.lsub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ)
        (P2Query.cl D₁ D₂ S σ (insertDisp .drop j ρ))
  -- linst (cc order 5): the payload pair at the composite level map.
  | eut_linst_eut {E₀ E : ResolvedEnv} {n₀ a n : Nat} {Γ₀ Γ : LCtx} {e A₁ A₂ : Expr Nat}
      {ls : List Level} {hls : levelsBounded n ls = true} {hlen : ls.length = a}
      (D₁ : TyP E a Γ e A₁) (D₂ : TyP E a Γ e A₂)
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
      IssuesCT (P2Query.eut (TyP.linst E a n Γ e A₁ ls hls hlen D₁)
        (TyP.linst E a n Γ e A₂ ls hls hlen D₂) S σ ρ)
        (P2Query.eut D₁ D₂ S (fun l => σ (instLevel ls l)) ρ)
  | cl_linst_cl {E₀ E : ResolvedEnv} {n₀ a n : Nat} {Γ₀ Γ : LCtx} {e A₁ A₂ : Expr Nat}
      {ls : List Level} {hls : levelsBounded n ls = true} {hlen : ls.length = a}
      (D₁ : TyP E a Γ e A₁) (D₂ : TyP E a Γ e A₂)
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
      IssuesCT (P2Query.cl (TyP.linst E a n Γ e A₁ ls hls hlen D₁)
        (TyP.linst E a n Γ e A₂ ls hls hlen D₂) S σ ρ)
        (P2Query.cl D₁ D₂ S (fun l => σ (instLevel ls l)) ρ)
  -- cctx (the sixth transport): the payload pair verbatim at the source binder.
  | eut_cctx_eut {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
      {e T₁ T₂ A A' : Expr Nat} {u₁ u₂ : Level}
      (D₁ : TyP E n (.assumption A :: Γ) e T₁) (hA₁ : CvP E n Γ A A' (.sort u₁))
      (D₂ : TyP E n (.assumption A :: Γ) e T₂) (hA₂ : CvP E n Γ A A' (.sort u₂))
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
      IssuesCT (P2Query.eut (TyP.cctx E n Γ e T₁ A A' u₁ D₁ hA₁)
        (TyP.cctx E n Γ e T₂ A A' u₂ D₂ hA₂) S σ ρ)
        (P2Query.eut D₁ D₂ S σ ρ)
  | cl_cctx_cl {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
      {e T₁ T₂ A A' : Expr Nat} {u₁ u₂ : Level}
      (D₁ : TyP E n (.assumption A :: Γ) e T₁) (hA₁ : CvP E n Γ A A' (.sort u₁))
      (D₂ : TyP E n (.assumption A :: Γ) e T₂) (hA₂ : CvP E n Γ A A' (.sort u₂))
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
      IssuesCT (P2Query.cl (TyP.cctx E n Γ e T₁ A A' u₁ D₁ hA₁)
        (TyP.cctx E n Γ e T₂ A A' u₂ D₂ hA₂) S σ ρ)
        (P2Query.cl D₁ D₂ S σ ρ)

/-- The demand closure under `IssuesCT`: the `DemandC` rows, plus issuance.
    No root constructor mentions a transport pair — the issued edges are only
    ever demanded by issuance. -/
inductive DemandCT {Eₐ : ResolvedEnv} : P2Query Eₐ → Prop where
  | old {q : P2Query Eₐ} (h : DemandC q) : DemandCT q
  | issued (issuer target : P2Query Eₐ) :
      DemandCT issuer → IssuesCT issuer target → DemandCT target

/-- Every T-issued query's derivations are `AssumpPref` once the issuer's
    are: the transport rows expose the payload (or value) components of the
    node's own `AssumpPref`. -/
theorem IssuesCT.ap {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ} (hi : q.AP)
    (e : IssuesCT q q') : q'.AP := by
  cases e with
  | old h => exact IssuesC.ap hi h
  | eut_wk_eut _ _ _ _ _ | cl_wk_cl _ _ _ _ _ =>
      exact ⟨hi.1.2, hi.2.2⟩
  | eut_ewk_eut _ _ _ _ _ | cl_ewk_cl _ _ _ _ _ =>
      exact ⟨hi.1, hi.2⟩
  | eut_esub_eut _ _ _ _ _ _ _ _ _ | cl_esub_cl _ _ _ _ _ _ _ _ _
      | eut_lsub_eut _ _ _ _ _ _ _ _ _ _ | cl_lsub_cl _ _ _ _ _ _ _ _ _ _ =>
      exact ⟨hi.1.2.1, hi.2.2.1⟩
  | eut_esub_clv _ _ _ _ _ _ _ _ _ | cl_esub_clv _ _ _ _ _ _ _ _ _ =>
      exact ⟨hi.1.2.2.1, hi.2.2.2.1⟩
  | eut_linst_eut _ _ _ _ _ | cl_linst_cl _ _ _ _ _ =>
      exact ⟨hi.1, hi.2⟩
  | eut_cctx_eut _ _ _ _ _ _ _ | cl_cctx_cl _ _ _ _ _ _ _ =>
      exact ⟨hi.1.1, hi.2.1⟩

/-- Every T-issued query's level map is a `LevelHom` once the issuer's is
    (`linst` composes with `instLevel`, `LevelHom.linst`). -/
theorem IssuesCT.hom {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ} (hi : q.Hom)
    (e : IssuesCT q q') : q'.Hom := by
  cases e with
  | old h => exact IssuesC.hom hi h
  | eut_linst_eut _ _ _ _ _ | cl_linst_cl _ _ _ _ _ => exact LevelHom.linst hi _
  | _ => exact hi

/-- Every T-issued query's display is routed once the issuer's is: the
    `RoutedDisp` transport constructors move the site routedness across the
    transport; the `lsub` rows carry the target routedness as their premise;
    the value-pair rows keep the site's display verbatim. -/
theorem IssuesCT.routed {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ} (hr : q.Routed)
    (e : IssuesCT q q') : q'.Routed := by
  cases e with
  | old h => exact IssuesC.routed hr h
  | @eut_wk_eut _ _ _ _ _ _ _ _ _ d c _ _ _ _ _ | @cl_wk_cl _ _ _ _ _ _ _ _ _ d c _ _ _ _ _ =>
      exact RoutedDisp.wk d c hr
  | @eut_ewk_eut _ _ _ _ _ _ _ _ _ _ hext _ _ _ _ _
      | @cl_ewk_cl _ _ _ _ _ _ _ _ _ _ hext _ _ _ _ _ =>
      exact RoutedDisp.ewk hext hr
  | @eut_esub_eut _ _ _ _ _ _ _ _ _ _ _ _ _ hget _ hv₁ hvT₁ _ _ _ _ _ _
      | @cl_esub_cl _ _ _ _ _ _ _ _ _ _ _ _ _ hget _ hv₁ hvT₁ _ _ _ _ _ _ =>
      exact RoutedDisp.esub hget hv₁ hvT₁ hr
  | eut_esub_clv _ _ _ _ _ _ _ _ _ | cl_esub_clv _ _ _ _ _ _ _ _ _ => exact hr
  | eut_lsub_eut _ _ _ _ _ _ _ _ _ hrt | cl_lsub_cl _ _ _ _ _ _ _ _ _ hrt => exact hrt
  | @eut_linst_eut _ _ _ _ _ _ _ _ _ _ ls hls hlen _ _ _ _ _
      | @cl_linst_cl _ _ _ _ _ _ _ _ _ _ ls hls hlen _ _ _ _ _ =>
      exact RoutedDisp.linst ls hls hlen hr
  | eut_cctx_eut _ hA₁ _ _ _ _ _ | cl_cctx_cl _ hA₁ _ _ _ _ _ =>
      exact RoutedDisp.cctx hA₁ hr

/-- The CT closure preserves `AP`. -/
theorem DemandCT.ap {Eₐ : ResolvedEnv} {q : P2Query Eₐ} (hq : DemandCT q) : q.AP := by
  induction hq with
  | old h => exact DemandC.ap h
  | issued _ _ _ e ih => exact IssuesCT.ap ih e

/-- The CT closure preserves `LevelHom`. -/
theorem DemandCT.hom {Eₐ : ResolvedEnv} {q : P2Query Eₐ} (hq : DemandCT q) : q.Hom := by
  induction hq with
  | old h => exact DemandC.hom h
  | issued _ _ _ e ih => exact IssuesCT.hom ih e

/-- The CT closure preserves routedness. -/
theorem DemandCT.routed {Eₐ : ResolvedEnv} {q : P2Query Eₐ} (hq : DemandCT q) :
    q.Routed := by
  induction hq with
  | old h => exact DemandC.routed h
  | issued _ _ _ e ih => exact IssuesCT.routed ih e

/-! ## §2 the CT step obligation -/

/-- `StepIH` over the T demand closure. -/
abbrev StepIHCT (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (q : P2Query Eₐ) : Prop :=
  ∀ q' : P2Query Eₐ, DemandCT q' → Before Aw q' q → Goal tbl q'

/-- The per-case step obligation over the T closure (`CaseStep`'s shape). -/
abbrev CaseStepCT (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (q : P2Query Eₐ) : Prop :=
  DemandCT q → StepIHCT Aw tbl q → Goal tbl q

/-- The semantic answer of a T-issued strictly-smaller sub-request. -/
theorem ih_issueCT {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {q : P2Query Eₐ} (hq : DemandCT q) (ih : StepIHCT Aw tbl q)
    (q' : P2Query Eₐ) (e : IssuesCT q q') (hb : Before Aw q' q) : Goal tbl q' :=
  ih q' (.issued q q' hq e) hb

/-- An IH call on a T-issued sub-request in the **same frame** at a strictly
    smaller local key. -/
theorem ih_localCT {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {q : P2Query Eₐ} (hq : DemandCT q) (ih : StepIHCT Aw tbl q)
    (q' : P2Query Eₐ) (e : IssuesCT q q')
    (hp : q'.originalPrefixLength = q.originalPrefixLength)
    (hk : LexDM (q'.localKey Aw) (q.localKey Aw)) : Goal tbl q' :=
  ih_issueCT Aw tbl hq ih q' e (before_of_same_prefix Aw hp hk)

/-- The fixpoint lift over the T closure — `solve_of_step` verbatim over
    `DemandCT` and the LANDED rank. -/
theorem solve_of_stepCT {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (step : ∀ q : P2Query Eₐ, DemandCT q →
      (∀ q' : P2Query Eₐ, DemandCT q' → Before Aw q' q → Goal tbl q') →
      Goal tbl q) :
    ∀ q : P2Query Eₐ, DemandCT q → Goal tbl q := by
  have allAt : ∀ k : Key, ∀ q : P2Query Eₐ, q.rank Aw = k → DemandCT q → Goal tbl q :=
    keyLT_wf.fix (fun k ih q hkey hq =>
      step q hq (fun q' hq' hlt =>
        ih (q'.rank Aw) (by unfold Before at hlt; rwa [hkey] at hlt) q' rfl hq'))
  intro q hq
  exact allAt (q.rank Aw) q rfl hq

/-! ## §3 the permutations the sub-multiset drops ride on -/

/-- Two transport operands, four dropped children, two kept payloads:
    `(a++b) ++ (x++y)` is the dropped set prepended to the kept payloads;
    the parent atoms are the interleaved `(x++a) ++ (y++b)`. -/
theorem perm_drop_pairs (a b x y : List Nat) :
    ((a ++ b) ++ (x ++ y)).Perm ((x ++ a) ++ (y ++ b)) := by
  refine List.perm_append_comm.trans ?_
  rw [show (x ++ y) ++ (a ++ b) = x ++ ((y ++ a) ++ b) by simp only [List.append_assoc],
      show (x ++ a) ++ (y ++ b) = x ++ ((a ++ y) ++ b) by simp only [List.append_assoc]]
  exact List.Perm.append_left _ (List.Perm.append_right _ List.perm_append_comm)

/-- `esub`/`lsub` payload pair: the four value-typing atom lists come out as
    one dropped block, the two payload lists stay in order. -/
theorem perm_transport_pair (p q r s x y : List Nat) :
    ((p ++ q ++ r ++ s) ++ (x ++ y)).Perm ((x ++ p ++ q) ++ (y ++ r ++ s)) := by
  refine List.perm_append_comm.trans ?_
  rw [show (x ++ y) ++ (p ++ q ++ r ++ s) = x ++ ((y ++ (p ++ q)) ++ (r ++ s)) by
        simp only [List.append_assoc],
      show (x ++ p ++ q) ++ (y ++ r ++ s) = x ++ (((p ++ q) ++ y) ++ (r ++ s)) by
        simp only [List.append_assoc]]
  exact List.Perm.append_left _ (List.Perm.append_right _ List.perm_append_comm)

/-- `esub` value pair: the payloads and the kind sources drop, the two value
    typings keep their positions at the tail. -/
theorem perm_transport_vals (x q y s p r : List Nat) :
    ((x ++ q ++ y ++ s) ++ (p ++ r)).Perm ((x ++ p ++ q) ++ (y ++ r ++ s)) := by
  have h1 : ((x ++ p ++ q) ++ (y ++ r ++ s)).Perm (x ++ q ++ y ++ r ++ s ++ p) := by
    rw [show (x ++ p ++ q) ++ (y ++ r ++ s) = x ++ (p ++ (q ++ y ++ r ++ s)) by
          simp only [List.append_assoc],
        show x ++ q ++ y ++ r ++ s ++ p = x ++ ((q ++ y ++ r ++ s) ++ p) by
          simp only [List.append_assoc]]
    exact List.Perm.append_left _ List.perm_append_comm
  have h2 : (x ++ q ++ y ++ r ++ s ++ p).Perm ((x ++ q ++ y ++ s) ++ (p ++ r)) := by
    rw [show x ++ q ++ y ++ r ++ s ++ p = (x ++ q ++ y) ++ (r ++ (s ++ p)) by
          simp only [List.append_assoc],
        show (x ++ q ++ y ++ s) ++ (p ++ r) = (x ++ q ++ y) ++ ((s ++ p) ++ r) by
          simp only [List.append_assoc]]
    exact List.Perm.append_left _ List.perm_append_comm
  exact (h1.trans h2).symm

/-! ## §4 the rank edges (the LANDED key) -/

/-- `wk`: same atoms (`(wk Dᵢ).atoms = Dᵢ.atoms`), one less weight each. -/
theorem lexDM_tyPair_wk (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A₁ A₂ : Expr Nat} {d : LocalDecl} {c : Nat}
    (D₁ : TyP E n Γ e A₁) (D₂ : TyP E n Γ e A₂) :
    LexDM (tyPairMeas Aw D₁ D₂)
      (tyPairMeas Aw (TyP.wk E n Γ e A₁ d c D₁) (TyP.wk E n Γ e A₂ d c D₂)) := by
  simp only [tyPairMeas, TyP.atoms, TyP.wt]
  exact Prod.Lex.right _ (by omega)

/-- `ewk`: same atoms, one less weight each. -/
theorem lexDM_tyPair_ewk (Aw : Nat → Nat) {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A₁ A₂ : Expr Nat} {hext : EnvExt E₀ E}
    (D₁ : TyP E₀ n Γ e A₁) (D₂ : TyP E₀ n Γ e A₂) :
    LexDM (tyPairMeas Aw D₁ D₂)
      (tyPairMeas Aw (TyP.ewk E₀ E n Γ e A₁ hext D₁)
        (TyP.ewk E₀ E n Γ e A₂ hext D₂)) := by
  simp only [tyPairMeas, TyP.atoms, TyP.wt]
  exact Prod.Lex.right _ (by omega)

/-- `linst`: same atoms, one less weight each. -/
theorem lexDM_tyPair_linst (Aw : Nat → Nat) {E : ResolvedEnv} {a n : Nat} {Γ : LCtx}
    {e A₁ A₂ : Expr Nat} {ls : List Level}
    {hls : levelsBounded n ls = true} {hlen : ls.length = a}
    (D₁ : TyP E a Γ e A₁) (D₂ : TyP E a Γ e A₂) :
    LexDM (tyPairMeas Aw D₁ D₂)
      (tyPairMeas Aw (TyP.linst E a n Γ e A₁ ls hls hlen D₁)
        (TyP.linst E a n Γ e A₂ ls hls hlen D₂)) := by
  simp only [tyPairMeas, TyP.atoms, TyP.wt]
  exact Prod.Lex.right _ (by omega)

/-- `cctx`: the two bridge atoms are a strict dropped sub-multiset. -/
theorem lexDM_tyPair_cctx (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ A A' : Expr Nat} {u₁ u₂ : Level}
    (D₁ : TyP E n (.assumption A :: Γ) e T₁) (hA₁ : CvP E n Γ A A' (.sort u₁))
    (D₂ : TyP E n (.assumption A :: Γ) e T₂) (hA₂ : CvP E n Γ A A' (.sort u₂)) :
    LexDM (tyPairMeas Aw D₁ D₂)
      (tyPairMeas Aw (TyP.cctx E n Γ e T₁ A A' u₁ D₁ hA₁)
        (TyP.cctx E n Γ e T₂ A A' u₂ D₂ hA₂)) := by
  have hX : (hA₁.atoms Aw ++ hA₂.atoms Aw) ≠ [] :=
    fun h => CvP.atoms_ne_nil Aw hA₁ (List.append_eq_nil.mp h).1
  simp only [tyPairMeas, TyP.atoms]
  exact Prod.Lex.left _ _
    (dmStep_perm_right (perm_drop_pairs _ _ _ _) (dmStep_drop hX))

/-- `esub`/`lsub` payload pair: the four value-typing atom lists drop. -/
theorem lexDM_tyPair_subs (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.assumption t)}
    (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
    LexDM (tyPairMeas Aw D₁ D₂)
      (tyPairMeas Aw (TyP.esub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.esub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂)) := by
  have hX : (hv₁.atoms Aw ++ hvT₁.atoms Aw ++ hv₂.atoms Aw ++ hvT₂.atoms Aw) ≠ [] :=
    fun h => TyP.atoms_ne_nil Aw hv₁
      (List.append_eq_nil.mp (List.append_eq_nil.mp (List.append_eq_nil.mp h).1).1).1
  simp only [tyPairMeas, TyP.atoms]
  exact Prod.Lex.left _ _
    (dmStep_perm_right (perm_transport_pair _ _ _ _ _ _) (dmStep_drop hX))

/-- `esub` value pair: the payloads and the kind sources drop; the value
    typings stay. -/
theorem lexDM_tyPair_esub_vals (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.assumption t)}
    (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
    LexDM (tyPairMeas Aw hv₁ hv₂)
      (tyPairMeas Aw (TyP.esub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.esub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂)) := by
  have hX : (D₁.atoms Aw ++ hvT₁.atoms Aw ++ D₂.atoms Aw ++ hvT₂.atoms Aw) ≠ [] :=
    fun h => TyP.atoms_ne_nil Aw D₁
      (List.append_eq_nil.mp (List.append_eq_nil.mp (List.append_eq_nil.mp h).1).1).1
  simp only [tyPairMeas, TyP.atoms]
  exact Prod.Lex.left _ _
    (dmStep_perm_right (perm_transport_vals _ _ _ _ _ _) (dmStep_drop hX))

/-- `lsub` payload pair: same shape (atoms of `lsub` = atoms of `esub`). -/
theorem lexDM_tyPair_lsub (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.letBinding t v)}
    (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
    LexDM (tyPairMeas Aw D₁ D₂)
      (tyPairMeas Aw (TyP.lsub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.lsub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂)) := by
  have hX : (hv₁.atoms Aw ++ hvT₁.atoms Aw ++ hv₂.atoms Aw ++ hvT₂.atoms Aw) ≠ [] :=
    fun h => TyP.atoms_ne_nil Aw hv₁
      (List.append_eq_nil.mp (List.append_eq_nil.mp (List.append_eq_nil.mp h).1).1).1
  simp only [tyPairMeas, TyP.atoms]
  exact Prod.Lex.left _ _
    (dmStep_perm_right (perm_transport_pair _ _ _ _ _ _) (dmStep_drop hX))

/-- The issued rows' local keys strictly decrease (same frame, so
    `originalPrefixLength` is `rfl` at every use site). -/
theorem lexKeyT_eut_wk_eut (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e A₁ A₂ : Expr Nat} {d : LocalDecl} {c : Nat}
    (D₁ : TyP E n Γ e A₁) (D₂ : TyP E n Γ e A₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    LexDM ((P2Query.eut D₁ D₂ S σ (removeAt ρ c)).localKey Aw)
      ((P2Query.eut (TyP.wk E n Γ e A₁ d c D₁) (TyP.wk E n Γ e A₂ d c D₂) S σ ρ).localKey Aw) :=
  lexDM_combMeas_mono Aw _ (lexDM_tyPair_wk Aw D₁ D₂)

theorem lexKeyT_cl_wk_cl (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e A₁ A₂ : Expr Nat} {d : LocalDecl} {c : Nat}
    (D₁ : TyP E n Γ e A₁) (D₂ : TyP E n Γ e A₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    LexDM ((P2Query.cl D₁ D₂ S σ (removeAt ρ c)).localKey Aw)
      ((P2Query.cl (TyP.wk E n Γ e A₁ d c D₁) (TyP.wk E n Γ e A₂ d c D₂) S σ ρ).localKey Aw) :=
  lexDM_combMeas_mono Aw _ (lexDM_tyPair_wk Aw D₁ D₂)

theorem lexKeyT_eut_ewk_eut (Aw : Nat → Nat) {Eₐ E₀ E₀' E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e A₁ A₂ : Expr Nat} {hext : EnvExt E₀ E}
    (D₁ : TyP E₀ n Γ e A₁) (D₂ : TyP E₀ n Γ e A₂)
    (S : ScopedCtx Eₐ E₀' n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    LexDM ((P2Query.eut D₁ D₂ S σ ρ).localKey Aw)
      ((P2Query.eut (TyP.ewk E₀ E n Γ e A₁ hext D₁)
        (TyP.ewk E₀ E n Γ e A₂ hext D₂) S σ ρ).localKey Aw) :=
  lexDM_combMeas_mono Aw _ (lexDM_tyPair_ewk Aw D₁ D₂)

theorem lexKeyT_cl_ewk_cl (Aw : Nat → Nat) {Eₐ E₀ E₀' E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e A₁ A₂ : Expr Nat} {hext : EnvExt E₀ E}
    (D₁ : TyP E₀ n Γ e A₁) (D₂ : TyP E₀ n Γ e A₂)
    (S : ScopedCtx Eₐ E₀' n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    LexDM ((P2Query.cl D₁ D₂ S σ ρ).localKey Aw)
      ((P2Query.cl (TyP.ewk E₀ E n Γ e A₁ hext D₁)
        (TyP.ewk E₀ E n Γ e A₂ hext D₂) S σ ρ).localKey Aw) :=
  lexDM_combMeas_mono Aw _ (lexDM_tyPair_ewk Aw D₁ D₂)

theorem lexKeyT_eut_esub_eut (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.assumption t)}
    (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    LexDM ((P2Query.eut D₁ D₂ S σ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ)).localKey Aw)
      ((P2Query.eut (TyP.esub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.esub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ).localKey Aw) :=
  lexDM_combMeas_mono Aw _ (lexDM_tyPair_subs Aw D₁ hv₁ hvT₁ D₂ hv₂ hvT₂)

theorem lexKeyT_cl_esub_cl (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.assumption t)}
    (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    LexDM ((P2Query.cl D₁ D₂ S σ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ)).localKey Aw)
      ((P2Query.cl (TyP.esub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.esub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ).localKey Aw) :=
  lexDM_combMeas_mono Aw _ (lexDM_tyPair_subs Aw D₁ hv₁ hvT₁ D₂ hv₂ hvT₂)

theorem lexKeyT_eut_esub_clv (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.assumption t)}
    (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    LexDM ((P2Query.cl hv₁ hv₂ S σ ρ).localKey Aw)
      ((P2Query.eut (TyP.esub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.esub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ).localKey Aw) :=
  lexDM_combMeas_mono Aw _ (lexDM_tyPair_esub_vals Aw D₁ hv₁ hvT₁ D₂ hv₂ hvT₂)

theorem lexKeyT_cl_esub_clv (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.assumption t)}
    (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    LexDM ((P2Query.cl hv₁ hv₂ S σ ρ).localKey Aw)
      ((P2Query.cl (TyP.esub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.esub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ).localKey Aw) :=
  lexDM_combMeas_mono Aw _ (lexDM_tyPair_esub_vals Aw D₁ hv₁ hvT₁ D₂ hv₂ hvT₂)

theorem lexKeyT_eut_lsub_eut (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.letBinding t v)}
    (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    LexDM ((P2Query.eut D₁ D₂ S σ (insertDisp .drop j ρ)).localKey Aw)
      ((P2Query.eut (TyP.lsub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.lsub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ).localKey Aw) :=
  lexDM_combMeas_mono Aw _ (lexDM_tyPair_lsub Aw D₁ hv₁ hvT₁ D₂ hv₂ hvT₂)

theorem lexKeyT_cl_lsub_cl (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.letBinding t v)}
    (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    LexDM ((P2Query.cl D₁ D₂ S σ (insertDisp .drop j ρ)).localKey Aw)
      ((P2Query.cl (TyP.lsub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.lsub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ).localKey Aw) :=
  lexDM_combMeas_mono Aw _ (lexDM_tyPair_lsub Aw D₁ hv₁ hvT₁ D₂ hv₂ hvT₂)

theorem lexKeyT_eut_linst_eut (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv}
    {n₀ a n : Nat} {Γ₀ Γ : LCtx} {e A₁ A₂ : Expr Nat} {ls : List Level}
    {hls : levelsBounded n ls = true} {hlen : ls.length = a}
    (D₁ : TyP E a Γ e A₁) (D₂ : TyP E a Γ e A₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    LexDM ((P2Query.eut D₁ D₂ S (fun l => σ (instLevel ls l)) ρ).localKey Aw)
      ((P2Query.eut (TyP.linst E a n Γ e A₁ ls hls hlen D₁)
        (TyP.linst E a n Γ e A₂ ls hls hlen D₂) S σ ρ).localKey Aw) :=
  lexDM_combMeas_mono Aw _ (lexDM_tyPair_linst Aw D₁ D₂)

theorem lexKeyT_cl_linst_cl (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv}
    {n₀ a n : Nat} {Γ₀ Γ : LCtx} {e A₁ A₂ : Expr Nat} {ls : List Level}
    {hls : levelsBounded n ls = true} {hlen : ls.length = a}
    (D₁ : TyP E a Γ e A₁) (D₂ : TyP E a Γ e A₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    LexDM ((P2Query.cl D₁ D₂ S (fun l => σ (instLevel ls l)) ρ).localKey Aw)
      ((P2Query.cl (TyP.linst E a n Γ e A₁ ls hls hlen D₁)
        (TyP.linst E a n Γ e A₂ ls hls hlen D₂) S σ ρ).localKey Aw) :=
  lexDM_combMeas_mono Aw _ (lexDM_tyPair_linst Aw D₁ D₂)

theorem lexKeyT_eut_cctx_eut (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ A A' : Expr Nat} {u₁ u₂ : Level}
    (D₁ : TyP E n (.assumption A :: Γ) e T₁) (hA₁ : CvP E n Γ A A' (.sort u₁))
    (D₂ : TyP E n (.assumption A :: Γ) e T₂) (hA₂ : CvP E n Γ A A' (.sort u₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    LexDM ((P2Query.eut D₁ D₂ S σ ρ).localKey Aw)
      ((P2Query.eut (TyP.cctx E n Γ e T₁ A A' u₁ D₁ hA₁)
        (TyP.cctx E n Γ e T₂ A A' u₂ D₂ hA₂) S σ ρ).localKey Aw) :=
  lexDM_combMeas_mono Aw _ (lexDM_tyPair_cctx Aw D₁ hA₁ D₂ hA₂)

theorem lexKeyT_cl_cctx_cl (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ A A' : Expr Nat} {u₁ u₂ : Level}
    (D₁ : TyP E n (.assumption A :: Γ) e T₁) (hA₁ : CvP E n Γ A A' (.sort u₁))
    (D₂ : TyP E n (.assumption A :: Γ) e T₂) (hA₂ : CvP E n Γ A A' (.sort u₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    LexDM ((P2Query.cl D₁ D₂ S σ ρ).localKey Aw)
      ((P2Query.cl (TyP.cctx E n Γ e T₁ A A' u₁ D₁ hA₁)
        (TyP.cctx E n Γ e T₂ A A' u₂ D₂ hA₂) S σ ρ).localKey Aw) :=
  lexDM_combMeas_mono Aw _ (lexDM_tyPair_cctx Aw D₁ hA₁ D₂ hA₂)

/-! ## §5 the CL answer transports (the `eps_*` commutations verbatim) -/

/-- The generic `.cl` residual-cell unfold (`rfl`): the goal is the
    conversion of the two operands' SUBJECT-erasures. -/
theorem goal_cl_residual_unfold {tbl : List CRule}
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Goal tbl (P2Query.cl D₁ D₂ S σ ρ) =
      ConvMod (EStep tbl) LvlEq (D₁.eps σ ρ) (D₂.eps σ ρ) := rfl

/-- `wk`/`wk`, not-keep: the CL goal IS the payload pair's CL goal at
    `removeAt ρ c` (`eps_wk_not_keep` both sides). -/
theorem goal_cl_wk_wk_not_keep {tbl : List CRule}
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e A₁ A₂ : Expr Nat} {d : LocalDecl} {c : Nat}
    (D₁ : TyP E n Γ e A₁) (D₂ : TyP E n Γ e A₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v)) :
    Goal tbl (P2Query.cl (TyP.wk E n Γ e A₁ d c D₁) (TyP.wk E n Γ e A₂ d c D₂) S σ ρ)
      = Goal tbl (P2Query.cl D₁ D₂ S σ (removeAt ρ c)) := by
  simp only [goal_cl_residual_unfold, eps_wk_not_keep hk]

/-- `wk`/`wk`, keep: `eps_wk_keep` both sides — a de Bruijn `lift` on the
    payload pair's erasures (`convMod_lift` closes it, `TableClosed`). -/
theorem goal_cl_wk_wk_keep {tbl : List CRule}
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e A₁ A₂ : Expr Nat} {d : LocalDecl} {c : Nat}
    (D₁ : TyP E n Γ e A₁) (D₂ : TyP E n Γ e A₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = some .keep) :
    Goal tbl (P2Query.cl (TyP.wk E n Γ e A₁ d c D₁) (TyP.wk E n Γ e A₂ d c D₂) S σ ρ)
      = ConvMod (EStep tbl) LvlEq
          ((D₁.eps σ (removeAt ρ c)).lift (countKeep (ρ.take c)) 1)
          ((D₂.eps σ (removeAt ρ c)).lift (countKeep (ρ.take c)) 1) := by
  simp only [goal_cl_residual_unfold, eps_wk_keep hk]

/-- `esub`/`esub`, drop: the CL goal IS the payload pair's CL goal at
    `insertDisp .drop j ρ` (`eps_esub_drop` both sides). -/
theorem goal_cl_esub_esub_drop {tbl : List CRule}
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
    Goal tbl (P2Query.cl (TyP.esub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.esub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ)
      = Goal tbl (P2Query.cl D₁ D₂ S σ (insertDisp .drop j ρ)) := by
  simp only [goal_cl_residual_unfold, eps_esub_drop hu]

/-- `esub`/`esub`, keep: the goal reduces to the `ETm.inst` composite —
    `convMod_inst` with the payload CL at `insertDisp .keep j ρ` and the
    value-pair CL at `ρ` (`TableClosed`). -/
theorem goal_cl_esub_esub_keep {tbl : List CRule}
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
    Goal tbl (P2Query.cl (TyP.esub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.esub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ)
      = ConvMod (EStep tbl) LvlEq
          (ETm.inst (countKeep (ρ.take j)) (hv₁.eps σ ρ)
            (D₁.eps σ (insertDisp .keep j ρ)))
          (ETm.inst (countKeep (ρ.take j)) (hv₂.eps σ ρ)
            (D₂.eps σ (insertDisp .keep j ρ))) := by
  simp only [goal_cl_residual_unfold, eps_esub_keep hu]

/-- `lsub`/`lsub`, star arm (both values erase to `★`): the CL goal IS the
    payload pair's CL goal at `insertDisp .drop j ρ`. -/
theorem goal_cl_lsub_lsub_star {tbl : List CRule}
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
    Goal tbl (P2Query.cl (TyP.lsub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.lsub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ)
      = Goal tbl (P2Query.cl D₁ D₂ S σ (insertDisp .drop j ρ)) := by
  simp only [goal_cl_residual_unfold, eps_lsub, hstar₁, hstar₂]

/-- `linst`/`linst`: the CL goal IS the payload pair's CL goal at the
    composite map `σ ∘ instLevel ls` (`eps_linst` both sides). -/
theorem goal_cl_linst_linst {tbl : List CRule}
    {Eₐ E₀ E : ResolvedEnv} {n₀ a n : Nat} {Γ₀ Γ : LCtx}
    {e A₁ A₂ : Expr Nat} {ls : List Level}
    {hls : levelsBounded n ls = true} {hlen : ls.length = a}
    (D₁ : TyP E a Γ e A₁) (D₂ : TyP E a Γ e A₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Goal tbl (P2Query.cl (TyP.linst E a n Γ e A₁ ls hls hlen D₁)
        (TyP.linst E a n Γ e A₂ ls hls hlen D₂) S σ ρ)
      = Goal tbl (P2Query.cl D₁ D₂ S (fun l => σ (instLevel ls l)) ρ) := by
  simp only [goal_cl_residual_unfold, eps_linst]

/-- `ewk`/`ewk`: the CL goal IS the payload pair's CL goal VERBATIM
    (`eps_ewk` is `rfl`). -/
theorem goal_cl_ewk_ewk {tbl : List CRule}
    {Eₐ E₀' E₀ E : ResolvedEnv} {n₀' n : Nat} {Γ₀' Γ : LCtx}
    {e A₁ A₂ : Expr Nat} {hext : EnvExt E₀ E}
    (D₁ : TyP E₀ n Γ e A₁) (D₂ : TyP E₀ n Γ e A₂)
    (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (ρ : List Disp) :
    Goal tbl (P2Query.cl (TyP.ewk E₀ E n Γ e A₁ hext D₁)
        (TyP.ewk E₀ E n Γ e A₂ hext D₂) S σ ρ)
      = Goal tbl (P2Query.cl D₁ D₂ S σ ρ) := by
  simp only [goal_cl_residual_unfold, eps_ewk]

/-- `cctx`/`cctx`: the CL goal IS the payload pair's CL goal VERBATIM
    (`eps_cctx` is `rfl`). -/
theorem goal_cl_cctx_cctx {tbl : List CRule}
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e T₁ T₂ A A' : Expr Nat} {u₁ u₂ : Level}
    (D₁ : TyP E n (.assumption A :: Γ) e T₁) (hA₁ : CvP E n Γ A A' (.sort u₁))
    (D₂ : TyP E n (.assumption A :: Γ) e T₂) (hA₂ : CvP E n Γ A A' (.sort u₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Goal tbl (P2Query.cl (TyP.cctx E n Γ e T₁ A A' u₁ D₁ hA₁)
        (TyP.cctx E n Γ e T₂ A A' u₂ D₂ hA₂) S σ ρ)
      = Goal tbl (P2Query.cl D₁ D₂ S σ ρ) := by
  simp only [goal_cl_residual_unfold, eps_cctx]

/-- `cctx` reg-commutation (`rfl` through `eps_cctx`). -/
theorem reg2_eps_cctx {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T A A' : Expr Nat} {u : Level}
    {D : TyP E n (.assumption A :: Γ) e T} {hA : CvP E n Γ A A' (.sort u)}
    {σ : Level → Level} {ρ : List Disp} :
    (TyP.cctx E n Γ e T A A' u D hA).reg.2.eps σ ρ = D.reg.2.eps σ ρ := by
  show (TyP.cctx E n Γ T _ A A' u D.reg.2 hA).eps σ ρ = _
  exact eps_cctx σ ρ

/-- `cctx`/`cctx`: the EUT goal IS the payload pair's EUT goal VERBATIM. -/
theorem goal_eut_cctx_cctx {tbl : List CRule}
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e T₁ T₂ A A' : Expr Nat} {u₁ u₂ : Level}
    (D₁ : TyP E n (.assumption A :: Γ) e T₁) (hA₁ : CvP E n Γ A A' (.sort u₁))
    (D₂ : TyP E n (.assumption A :: Γ) e T₂) (hA₂ : CvP E n Γ A A' (.sort u₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Goal tbl (P2Query.eut (TyP.cctx E n Γ e T₁ A A' u₁ D₁ hA₁)
        (TyP.cctx E n Γ e T₂ A A' u₂ D₂ hA₂) S σ ρ)
      = Goal tbl (P2Query.eut D₁ D₂ S σ ρ) := by
  simp only [goal_eut_residual_unfold, reg2_eps_cctx]

/-! ## §6 the diagonal cells discharged -/

/-- `eut` `wk`/`wk`: the payload EUT at `removeAt ρ c` answers the cell —
    verbatim not-keep, under `convMod_lift` keep. -/
theorem eut_wk_wk_caseStepT (Aw : Nat → Nat) (tbl : List CRule) (hTC : TableClosed tbl)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e A₁ A₂ : Expr Nat} {d : LocalDecl} {c : Nat}
    (D₁ : TyP E n Γ e A₁) (D₂ : TyP E n Γ e A₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStepCT Aw tbl
      (P2Query.eut (TyP.wk E n Γ e A₁ d c D₁) (TyP.wk E n Γ e A₂ d c D₂) S σ ρ) := by
  intro hq ih
  have hchild := ih_localCT Aw tbl hq ih (P2Query.eut D₁ D₂ S σ (removeAt ρ c))
    (IssuesCT.eut_wk_eut D₁ D₂ S σ ρ) rfl (lexKeyT_eut_wk_eut Aw D₁ D₂ S σ ρ)
  rcases getElem?_keep_or_not_keep ρ c with hk | hk
  · rw [goal_eut_wk_wk_keep (hk := hk)]
    exact convMod_lift hTC hchild _ _
  · rw [goal_eut_wk_wk_not_keep (hk := hk)]
    exact hchild

/-- `cl` `wk`/`wk`: the payload CL at `removeAt ρ c` answers the cell. -/
theorem cl_wk_wk_caseStepT (Aw : Nat → Nat) (tbl : List CRule) (hTC : TableClosed tbl)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e A₁ A₂ : Expr Nat} {d : LocalDecl} {c : Nat}
    (D₁ : TyP E n Γ e A₁) (D₂ : TyP E n Γ e A₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStepCT Aw tbl
      (P2Query.cl (TyP.wk E n Γ e A₁ d c D₁) (TyP.wk E n Γ e A₂ d c D₂) S σ ρ) := by
  intro hq ih
  have hchild := ih_localCT Aw tbl hq ih (P2Query.cl D₁ D₂ S σ (removeAt ρ c))
    (IssuesCT.cl_wk_cl D₁ D₂ S σ ρ) rfl (lexKeyT_cl_wk_cl Aw D₁ D₂ S σ ρ)
  rcases getElem?_keep_or_not_keep ρ c with hk | hk
  · rw [goal_cl_wk_wk_keep (hk := hk)]
    exact convMod_lift hTC hchild _ _
  · rw [goal_cl_wk_wk_not_keep (hk := hk)]
    exact hchild

/-- `eut` `ewk`/`ewk`: the payload EUT answers verbatim (`rfl` transport). -/
theorem eut_ewk_ewk_caseStepT (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀' E₀ E : ResolvedEnv} {n₀' n : Nat} {Γ₀' Γ : LCtx}
    {e A₁ A₂ : Expr Nat} {hext : EnvExt E₀ E}
    (D₁ : TyP E₀ n Γ e A₁) (D₂ : TyP E₀ n Γ e A₂)
    (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (ρ : List Disp) :
    CaseStepCT Aw tbl
      (P2Query.eut (TyP.ewk E₀ E n Γ e A₁ hext D₁) (TyP.ewk E₀ E n Γ e A₂ hext D₂) S σ ρ) := by
  intro hq ih
  have hchild := ih_localCT Aw tbl hq ih (P2Query.eut D₁ D₂ S σ ρ)
    (IssuesCT.eut_ewk_eut D₁ D₂ S σ ρ) rfl (lexKeyT_eut_ewk_eut Aw D₁ D₂ S σ ρ)
  rw [goal_eut_ewk_ewk]
  exact hchild

/-- `cl` `ewk`/`ewk`: the payload CL answers verbatim. -/
theorem cl_ewk_ewk_caseStepT (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀' E₀ E : ResolvedEnv} {n₀' n : Nat} {Γ₀' Γ : LCtx}
    {e A₁ A₂ : Expr Nat} {hext : EnvExt E₀ E}
    (D₁ : TyP E₀ n Γ e A₁) (D₂ : TyP E₀ n Γ e A₂)
    (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (ρ : List Disp) :
    CaseStepCT Aw tbl
      (P2Query.cl (TyP.ewk E₀ E n Γ e A₁ hext D₁) (TyP.ewk E₀ E n Γ e A₂ hext D₂) S σ ρ) := by
  intro hq ih
  have hchild := ih_localCT Aw tbl hq ih (P2Query.cl D₁ D₂ S σ ρ)
    (IssuesCT.cl_ewk_cl D₁ D₂ S σ ρ) rfl (lexKeyT_cl_ewk_cl Aw D₁ D₂ S σ ρ)
  rw [goal_cl_ewk_ewk]
  exact hchild

/-- `eut` `esub`/`esub`: the payload EUT at the `binderDisp`-moved display
    answers drop; keep closes the `ETm.inst` wrapper by `convMod_inst` with
    the issued value-pair CL. -/
theorem eut_esub_esub_caseStepT (Aw : Nat → Nat) (tbl : List CRule) (hTC : TableClosed tbl)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.assumption t)}
    (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStepCT Aw tbl
      (P2Query.eut (TyP.esub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.esub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ) := by
  intro hq ih
  have hchild := ih_localCT Aw tbl hq ih
    (P2Query.eut D₁ D₂ S σ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ))
    (IssuesCT.eut_esub_eut D₁ hv₁ hvT₁ D₂ hv₂ hvT₂ S σ ρ) rfl
    (lexKeyT_eut_esub_eut Aw D₁ hv₁ hvT₁ D₂ hv₂ hvT₂ S σ ρ)
  cases hu : levelIsZero (σ u) with
  | true =>
      rw [hu] at hchild
      rw [goal_eut_esub_esub_drop (hu := hu)]
      exact hchild
  | false =>
      rw [hu] at hchild
      rw [goal_eut_esub_esub_keep (hu := hu)]
      have hclv := ih_localCT Aw tbl hq ih (P2Query.cl hv₁ hv₂ S σ ρ)
        (IssuesCT.eut_esub_clv D₁ hv₁ hvT₁ D₂ hv₂ hvT₂ S σ ρ) rfl
        (lexKeyT_eut_esub_clv Aw D₁ hv₁ hvT₁ D₂ hv₂ hvT₂ S σ ρ)
      exact convMod_inst hTC hchild hclv _

/-- `cl` `esub`/`esub`: the same shape at the subject-erasure kind. -/
theorem cl_esub_esub_caseStepT (Aw : Nat → Nat) (tbl : List CRule) (hTC : TableClosed tbl)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.assumption t)}
    (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStepCT Aw tbl
      (P2Query.cl (TyP.esub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.esub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ) := by
  intro hq ih
  have hchild := ih_localCT Aw tbl hq ih
    (P2Query.cl D₁ D₂ S σ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ))
    (IssuesCT.cl_esub_cl D₁ hv₁ hvT₁ D₂ hv₂ hvT₂ S σ ρ) rfl
    (lexKeyT_cl_esub_cl Aw D₁ hv₁ hvT₁ D₂ hv₂ hvT₂ S σ ρ)
  cases hu : levelIsZero (σ u) with
  | true =>
      rw [hu] at hchild
      rw [goal_cl_esub_esub_drop (hu := hu)]
      exact hchild
  | false =>
      rw [hu] at hchild
      rw [goal_cl_esub_esub_keep (hu := hu)]
      have hclv := ih_localCT Aw tbl hq ih (P2Query.cl hv₁ hv₂ S σ ρ)
        (IssuesCT.cl_esub_clv D₁ hv₁ hvT₁ D₂ hv₂ hvT₂ S σ ρ) rfl
        (lexKeyT_cl_esub_clv Aw D₁ hv₁ hvT₁ D₂ hv₂ hvT₂ S σ ρ)
      exact convMod_inst hTC hchild hclv _

/-- `eut` `lsub`/`lsub`, the star arm: both values erase to `★`, so both
    operands' erasures run at `insertDisp .drop j ρ`, and the payload EUT
    answers verbatim. The row supplies the target's routedness (`hr`); the
    inline arm stays in the residual wall. -/
theorem eut_lsub_lsub_star_caseStepT (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.letBinding t v)}
    (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hr : RoutedDisp σ E n Γ (insertDisp .drop j ρ))
    (hstar₁ : hv₁.eps σ ρ = .star) (hstar₂ : hv₂.eps σ ρ = .star) :
    CaseStepCT Aw tbl
      (P2Query.eut (TyP.lsub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.lsub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ) := by
  intro hq ih
  have hchild := ih_localCT Aw tbl hq ih
    (P2Query.eut D₁ D₂ S σ (insertDisp .drop j ρ))
    (IssuesCT.eut_lsub_eut D₁ hv₁ hvT₁ D₂ hv₂ hvT₂ S σ ρ hr) rfl
    (lexKeyT_eut_lsub_eut Aw D₁ hv₁ hvT₁ D₂ hv₂ hvT₂ S σ ρ)
  rw [goal_eut_lsub_lsub_star (hstar₁ := hstar₁) (hstar₂ := hstar₂)]
  exact hchild

/-- `cl` `lsub`/`lsub`, the star arm. -/
theorem cl_lsub_lsub_star_caseStepT (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e A₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.letBinding t v)}
    (D₁ : TyP E n Γ e A₁) (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (D₂ : TyP E n Γ e A₂) (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hr : RoutedDisp σ E n Γ (insertDisp .drop j ρ))
    (hstar₁ : hv₁.eps σ ρ = .star) (hstar₂ : hv₂.eps σ ρ = .star) :
    CaseStepCT Aw tbl
      (P2Query.cl (TyP.lsub E n Γ e A₁ t v j u D₁ hget hv₁ hvT₁)
        (TyP.lsub E n Γ e A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ) := by
  intro hq ih
  have hchild := ih_localCT Aw tbl hq ih
    (P2Query.cl D₁ D₂ S σ (insertDisp .drop j ρ))
    (IssuesCT.cl_lsub_cl D₁ hv₁ hvT₁ D₂ hv₂ hvT₂ S σ ρ hr) rfl
    (lexKeyT_cl_lsub_cl Aw D₁ hv₁ hvT₁ D₂ hv₂ hvT₂ S σ ρ)
  rw [goal_cl_lsub_lsub_star (hstar₁ := hstar₁) (hstar₂ := hstar₂)]
  exact hchild

/-- `eut` `linst`/`linst`: the payload EUT at the composite level map
    answers verbatim (`eps_linst`). -/
theorem eut_linst_linst_caseStepT (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ a n : Nat} {Γ₀ Γ : LCtx}
    {e A₁ A₂ : Expr Nat} {ls : List Level}
    {hls : levelsBounded n ls = true} {hlen : ls.length = a}
    (D₁ : TyP E a Γ e A₁) (D₂ : TyP E a Γ e A₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStepCT Aw tbl
      (P2Query.eut (TyP.linst E a n Γ e A₁ ls hls hlen D₁)
        (TyP.linst E a n Γ e A₂ ls hls hlen D₂) S σ ρ) := by
  intro hq ih
  have hchild := ih_localCT Aw tbl hq ih
    (P2Query.eut D₁ D₂ S (fun l => σ (instLevel ls l)) ρ)
    (IssuesCT.eut_linst_eut D₁ D₂ S σ ρ) rfl
    (lexKeyT_eut_linst_eut Aw D₁ D₂ S σ ρ)
  rw [goal_eut_linst_linst]
  exact hchild

/-- `cl` `linst`/`linst`: the payload CL at the composite level map. -/
theorem cl_linst_linst_caseStepT (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ a n : Nat} {Γ₀ Γ : LCtx}
    {e A₁ A₂ : Expr Nat} {ls : List Level}
    {hls : levelsBounded n ls = true} {hlen : ls.length = a}
    (D₁ : TyP E a Γ e A₁) (D₂ : TyP E a Γ e A₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStepCT Aw tbl
      (P2Query.cl (TyP.linst E a n Γ e A₁ ls hls hlen D₁)
        (TyP.linst E a n Γ e A₂ ls hls hlen D₂) S σ ρ) := by
  intro hq ih
  have hchild := ih_localCT Aw tbl hq ih
    (P2Query.cl D₁ D₂ S (fun l => σ (instLevel ls l)) ρ)
    (IssuesCT.cl_linst_cl D₁ D₂ S σ ρ) rfl
    (lexKeyT_cl_linst_cl Aw D₁ D₂ S σ ρ)
  rw [goal_cl_linst_linst]
  exact hchild

/-- `eut` `cctx`/`cctx`: the payload EUT answers verbatim (`eps_cctx`
    `rfl`); `RoutedDisp.cctx` moves the routedness across the binder. -/
theorem eut_cctx_cctx_caseStepT (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e T₁ T₂ A A' : Expr Nat} {u₁ u₂ : Level}
    (D₁ : TyP E n (.assumption A :: Γ) e T₁) (hA₁ : CvP E n Γ A A' (.sort u₁))
    (D₂ : TyP E n (.assumption A :: Γ) e T₂) (hA₂ : CvP E n Γ A A' (.sort u₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStepCT Aw tbl
      (P2Query.eut (TyP.cctx E n Γ e T₁ A A' u₁ D₁ hA₁)
        (TyP.cctx E n Γ e T₂ A A' u₂ D₂ hA₂) S σ ρ) := by
  intro hq ih
  have hchild := ih_localCT Aw tbl hq ih (P2Query.eut D₁ D₂ S σ ρ)
    (IssuesCT.eut_cctx_eut D₁ hA₁ D₂ hA₂ S σ ρ) rfl
    (lexKeyT_eut_cctx_eut Aw D₁ hA₁ D₂ hA₂ S σ ρ)
  rw [goal_eut_cctx_cctx]
  exact hchild

/-- `cl` `cctx`/`cctx`: the payload CL answers verbatim. -/
theorem cl_cctx_cctx_caseStepT (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e T₁ T₂ A A' : Expr Nat} {u₁ u₂ : Level}
    (D₁ : TyP E n (.assumption A :: Γ) e T₁) (hA₁ : CvP E n Γ A A' (.sort u₁))
    (D₂ : TyP E n (.assumption A :: Γ) e T₂) (hA₂ : CvP E n Γ A A' (.sort u₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStepCT Aw tbl
      (P2Query.cl (TyP.cctx E n Γ e T₁ A A' u₁ D₁ hA₁)
        (TyP.cctx E n Γ e T₂ A A' u₂ D₂ hA₂) S σ ρ) := by
  intro hq ih
  have hchild := ih_localCT Aw tbl hq ih (P2Query.cl D₁ D₂ S σ ρ)
    (IssuesCT.cl_cctx_cl D₁ hA₁ D₂ hA₂ S σ ρ) rfl
    (lexKeyT_cl_cctx_cl Aw D₁ hA₁ D₂ hA₂ S σ ρ)
  rw [goal_cl_cctx_cctx]
  exact hchild

#print axioms Rcic.Syn.IssuesCT
#print axioms Rcic.Syn.DemandCT
#print axioms Rcic.Syn.IssuesCT.ap
#print axioms Rcic.Syn.IssuesCT.hom
#print axioms Rcic.Syn.IssuesCT.routed
#print axioms Rcic.Syn.DemandCT.ap
#print axioms Rcic.Syn.DemandCT.hom
#print axioms Rcic.Syn.DemandCT.routed
#print axioms Rcic.Syn.ih_issueCT
#print axioms Rcic.Syn.ih_localCT
#print axioms Rcic.Syn.solve_of_stepCT
#print axioms Rcic.Syn.perm_drop_pairs
#print axioms Rcic.Syn.perm_transport_pair
#print axioms Rcic.Syn.perm_transport_vals
#print axioms Rcic.Syn.lexDM_tyPair_wk
#print axioms Rcic.Syn.lexDM_tyPair_ewk
#print axioms Rcic.Syn.lexDM_tyPair_linst
#print axioms Rcic.Syn.lexDM_tyPair_cctx
#print axioms Rcic.Syn.lexDM_tyPair_subs
#print axioms Rcic.Syn.lexDM_tyPair_esub_vals
#print axioms Rcic.Syn.lexDM_tyPair_lsub
#print axioms Rcic.Syn.lexKeyT_eut_wk_eut
#print axioms Rcic.Syn.lexKeyT_cl_wk_cl
#print axioms Rcic.Syn.lexKeyT_eut_ewk_eut
#print axioms Rcic.Syn.lexKeyT_cl_ewk_cl
#print axioms Rcic.Syn.lexKeyT_eut_esub_eut
#print axioms Rcic.Syn.lexKeyT_cl_esub_cl
#print axioms Rcic.Syn.lexKeyT_eut_esub_clv
#print axioms Rcic.Syn.lexKeyT_cl_esub_clv
#print axioms Rcic.Syn.lexKeyT_eut_lsub_eut
#print axioms Rcic.Syn.lexKeyT_cl_lsub_cl
#print axioms Rcic.Syn.lexKeyT_eut_linst_eut
#print axioms Rcic.Syn.lexKeyT_cl_linst_cl
#print axioms Rcic.Syn.lexKeyT_eut_cctx_eut
#print axioms Rcic.Syn.lexKeyT_cl_cctx_cl
#print axioms Rcic.Syn.goal_cl_residual_unfold
#print axioms Rcic.Syn.goal_cl_wk_wk_not_keep
#print axioms Rcic.Syn.goal_cl_wk_wk_keep
#print axioms Rcic.Syn.goal_cl_esub_esub_drop
#print axioms Rcic.Syn.goal_cl_esub_esub_keep
#print axioms Rcic.Syn.goal_cl_lsub_lsub_star
#print axioms Rcic.Syn.goal_cl_linst_linst
#print axioms Rcic.Syn.goal_cl_ewk_ewk
#print axioms Rcic.Syn.goal_cl_cctx_cctx
#print axioms Rcic.Syn.reg2_eps_cctx
#print axioms Rcic.Syn.goal_eut_cctx_cctx
#print axioms Rcic.Syn.eut_wk_wk_caseStepT
#print axioms Rcic.Syn.cl_wk_wk_caseStepT
#print axioms Rcic.Syn.eut_ewk_ewk_caseStepT
#print axioms Rcic.Syn.cl_ewk_ewk_caseStepT
#print axioms Rcic.Syn.eut_esub_esub_caseStepT
#print axioms Rcic.Syn.cl_esub_esub_caseStepT
#print axioms Rcic.Syn.eut_lsub_lsub_star_caseStepT
#print axioms Rcic.Syn.cl_lsub_lsub_star_caseStepT
#print axioms Rcic.Syn.eut_linst_linst_caseStepT
#print axioms Rcic.Syn.cl_linst_linst_caseStepT
#print axioms Rcic.Syn.eut_cctx_cctx_caseStepT
#print axioms Rcic.Syn.cl_cctx_cctx_caseStepT

end Rcic.Syn

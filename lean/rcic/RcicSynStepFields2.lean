import rcic.RcicSynStepSkeleton

/-!
# `es_app` / `es_pi` step-field work (STEP_SUPPLIERS, `RcicSynStepFields2`)

Two of the seventeen `StepSuppliers` fields of `RcicSynStepSkeleton`. This module
proves, unconditionally and from the actual `Demand`/`Issues`/`StepIH` machinery,
the **issued-row half** of each field, and pins the **remaining obligation** in
the form of assembly lemmas whose premises are exactly the spec's ports.

## What is proved

* `es_app_ih_fun`, `es_app_ih_arg`: under the `es_app` field's binders, the IH
  delivers `ES tbl σ ρ h1` and `ES tbl σ ρ h2` — `Issues.app_es1`/`app_es2` issue
  the sub-conversions in the parent frame at the parent display, and
  `rule_sub_before` gives the strict local-key drop (`h1.wt < node.wt`).

* `es_pi_ih_dom`, `es_pi_ih_body`: under the `es_pi` field's binders, the IH
  delivers `ES tbl σ ρ hA` (`pi_esA`, `rule_sub_before`) and
  `ES tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) hB` (`pi_esB`,
  `binder_body_before` — the body one binder up at the real binder display).

## What remains, exactly

The `CaseStep` conclusions themselves are NOT closed here — they reduce to
`es_app`/`es_app_star`/`es_pi` hypotheses that are the obligations the step
cannot yet discharge on landed APIs:

* `es_app` (spec `BELOWC_FAILED_READERS_AND_LET_BODY` §3.3, §4.1): needs
  `R := appSource dr rfl` and the bounded `leftSurface` of `dl`, then
  `CL[dl, leftSurface]`, `CL/Tag[hᵢ.dr, R.hf/R.ha]`, the four `PB` ports, and the
  app-clause worker `D.eps = appClause (R.hf.eps) (R.ha.eps)`. The decoder has
  landed — `RcicSynDomainSource` (#7475) supplies `appSource`/`appDomain`/
  `appSource_ap`/`appSource_*_wt` — and `RcicSynStepFields5` assembles the
  `CaseStep` (`es_app_field`) over `AppPorts`: the `CL[hᵢ.dr, R.·]` pairs are
  `occ_cl`-issuable via the port-carried `subAt` receipts, the `PB`s/`Tag`s/
  `leftCl`/`drClause` stay named ports.
* `es_pi` (spec §3.5): needs `HR := piDomain dr` — landed with
  `piDomSrc_subject`/`piDomain_wt_lt`/`piDomain_ap`; `RcicSynStepFields5`
  assembles `es_pi_field` over `PiPorts`: the domain `CL[hA.dr, he' ▸ HR.H]`
  and the sort-gate `BIT[hA.dr, hT ▸ he' ▸ HR.H]` are `occ_cl`/`occ_bitCoh`-
  issuable via the port-carried `subAt` receipts `occHA`/`occHR`, and the
  issued bit re-gates the `piSlot` binder. The codomain/body source is still
  not a generic projection (spec: "a generic source is not enough to
  reconstruct arbitrary deeper body clauses") — that deeper body route is the
  residual `PiPorts.rightCl`, now the decoded comparison against
  `piRightSurface hA hB dr` rather than the whole right side.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `es_app`: the issued `ES` rows -/

/-- `es_app`, function leg. `app_es1` issues `h1`'s `ES` request in the parent
    frame at the parent display; `rule_sub_before` drops the rank. -/
theorem es_app_ih_fun {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)) :
    ES tbl σ ρ h1 :=
  ih_issue Aw tbl hq ih (.es h1 S σ ρ) .app_es1
    (rule_sub_before Aw (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl h1
    (by simp only [CvP.wt]; omega) S σ ρ ρ)

/-- `es_app`, argument leg. `app_es2` issues `h2`'s `ES` request. -/
theorem es_app_ih_arg {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)) :
    ES tbl σ ρ h2 :=
  ih_issue Aw tbl hq ih (.es h2 S σ ρ) .app_es2
    (rule_sub_before Aw (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl h2
    (by simp only [CvP.wt]; omega) S σ ρ ρ)

/-! ## §2 `es_pi`: the issued `ES` rows -/

/-- `es_pi`, domain leg. `pi_esA` issues `hA`'s `ES` request in the parent frame. -/
theorem es_pi_ih_dom {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ)) :
    ES tbl σ ρ hA :=
  ih_issue Aw tbl hq ih (.es hA S σ ρ) .pi_esA
    (rule_sub_before Aw (CvP.pi E n Γ A A' B B' u v hA hB dl dr) rfl hA
    (by simp only [CvP.wt]; omega) S σ ρ ρ)

/-- `es_pi`, body leg. `pi_esB` issues `hB`'s `ES` request one binder up, at the
    real binder display — `binder_body_before` (S15 §6, the repaired edge). -/
theorem es_pi_ih_body {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ)) :
    ES tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) hB :=
  ih_issue Aw tbl hq ih (.es hB S σ (binderDisp (levelIsZero (σ u)) :: ρ)) .pi_esB
    (binder_body_before Aw hA hB dl dr S σ ρ)

end Rcic.Syn

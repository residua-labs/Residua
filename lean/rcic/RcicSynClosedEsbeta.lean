import rcic.RcicSynStepFieldsEsBeta
import rcic.RcicSynStepFields5
import rcic.RcicSynDomainSource

/-!
# `es_beta_closed` — `StepSuppliers.es_beta` after the `DomainSource` re-measure

Continuation of `RcicSynStepFieldsEsBeta.es_beta_field` (swe-esbeta lane;
sortRow ports assignment).  `closure_claim = 0`.

`RcicSynStepFieldsEsBeta` was measured **before** `RcicSynDomainSource`
landed: its docstring names `lamDomain`/`appSource` as unlanded and leaves
`domBit` and `argCl` as unconditional (d) ports.  Re-measuring against the
current tree moves two of the six always-open `BetaClPorts` fields and the
`star`-arm `PBit` pair to class (b) (answerable from `StepIH` through an
existing `Issues` row), gives `argTag` two `occ_pb` receipt disjuncts, and
discharges the reader-compatibility half of `domBit` outright (class (c)):

- **`domBit`** (`levelIsZero (σ g.u) = levelIsZero (σ u)`): the landed
  `readRedex_domain_u` discharges the reader-compat half —
  `(betaDomSrc dl).u = g.u` on every `.yes g` read (c).  What remains is
  `BIT[Hg, hA]` — bit coherence between `betaDomSrc dl`'s stored domain
  typing and `hA`.  Both typings share subject `A` at the site context,
  so whenever `betaDomTy dl` (the decoder's `H` re-indexed by its own
  `he'`/`hT`) sits at a `P2Query.subAt` occurrence path `pH`, `StepIH`
  supplies it through `es_issued_occ_bitCoh` (`Issues.occ_bitCoh`, the
  `subAt_wt_lt`/`dmStep_pair_below` `Before` discharged inside the landed
  lemma) — (b).  For a direct `TyP.app` left endpoint `pH = [3, 0, 0]`
  by `rfl` (§4 `domBit_occ_witness`).
- **`argCl`** (`CL[g.harg, harg]`): `readRedex` wraps its argument typing
  in `TyP.ewk` (`redexOfApp`), so `g.harg` is never a literal `subAt`
  occurrence — but `eps` peels `ewk` by `rfl`, so `g.harg`'s erasure *is*
  the inner argument's erasure.  Whenever `betaArgTy dl` (the `appSource`
  argument typing re-indexed to `arg`) sits at an occurrence path `pA`
  **and** `g.harg.eps σ ρ = (betaArgTy dl).eps σ ρ`, `es_issued_occ_cl`
  supplies `CL[betaArgTy dl, harg]` and the eps bridge rewrites the goal —
  (b).  For a direct `TyP.app`/`conv` chain the occurrence is `[3, 1]` /
  deeper and the bridge is `rfl` (§4 `argTy_occ_witness`); for
  `wk`/`esub`-`under`/`lsub`/`linst`/`ewk`/`cctx` heads the conjunction
  fails and the verbatim `CL` stays (d).
- **`argTag`** (`Tag[g.harg, harg]`): `Issues` has no tag row, but
  `occ_pb` issues the `PBit` chain — `PBit[harg, hA]` is *unconditionally*
  issuable (`harg` at `(0, [2])`, `hA` at `(0, [0])` by `rfl` —
  `beta_issued_harg_pb`), and the read-side leg closes in two receipt
  routes: (i) the `betaArgTy` occurrence `pA` plus
  `(appSource dl rfl).A = A` plus the eps bridge — `hAeq ▸
  (betaArgTy dl)` sits at `pA` by `dnode_ty_cast*`
  (`beta_issued_argCast_pb`, `beta_argTag_of_occ_eps`); (ii) the
  `betaArgTy`/`betaAppDomTy` occurrence pair plus the eps bridge plus
  `lZ (σ (appDomain dl rfl).u) = lZ (σ u)` (`beta_issued_appArg_pb`,
  `beta_argTag_of_appDom_occ`).  Either disjunct discharges `argTag` from
  `StepIH` alone (class (b)); with neither route's receipts it stays
  verbatim (d).
- **star arm**: `BetaFieldResid`'s unconditional `PBit` pair becomes the
  disjunction `(∃ pReg, subAt … = some (.ty dl.reg.2)) ∨ (PBit dl
  dl.reg.2 ∧ PBit dr dl.reg.2)` — the occurrence disjunct is discharged
  outright by the landed `beta_issued_*_reg_pb`/`es_beta_of_dl_star_reg_occ`
  (class (b); for a direct `TyP.app`, `pReg = [3, 2]` by `rfl`).

Still genuinely open — class (d), named exactly, verbatim fields:

- `argTag`'s fallback: when neither `occ_pb` receipt route above fires the
  verbatim `Tag[g.harg, harg]` stays (d).
- `bodyTag` (`Tag[g.hbody, hbody]`) and `bodyCl` (`CL[g.hbody, hbody]`):
  both live in `.assumption A :: Γ` at the `binderDisp … :: ρ` display;
  `occ_*` rows are same-site-`Γ` and same-site-`ρ` — no row can ever issue
  a binder-raised-context query.
- `reductCl` (`CL[instEnd hbody harg hA, dr]`): `instEnd` is a synthesized
  canonical node, never a `subAt` occurrence.
- `none` verdict: the whole `BetaPorts` stays residual — `got` needs a
  `lamBody`-style body decoder (only `lamDomain` landed), `eps` is
  semantic.
- `raw` verdict: the eps equation `dl.eps σ ρ = redexClauseOf g σ ρ`
  stays (d) verbatim.

`es_beta_closed` is the field theorem under `BetaFieldResidClosed`;
`BetaClPortsClosed.toBetaClPorts` converts the weakened ports to the
landed `BetaClPorts`, discharging both `∃`-disjuncts through `StepIH`.
§4 (`ClosedControls`) is the non-vacuity witness: a concrete direct
`TyP.app` fixture shows every receipt disjunct and every verbatim port is
satisfiable.  The skeleton, `RcicSynStepFields3`, `RcicSynStepFields5`,
`RcicSynStepFieldsEsBeta` and `RcicSynDomainSource` are untouched.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 decoder-anchored nodes -/

/-- The structural domain source of `dl`'s application function:
    `lamDomain (appSource dl rfl).hf (appSource dl rfl).feq` from the
    landed `RcicSynDomainSource` decoders.  `readRedex_domain_u` proves
    `(betaDomSrc dl).u = g.u` on every `.yes g` read. -/
abbrev betaDomSrc {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat}
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B)) :
    DomainSource E n Γ A :=
  lamDomain (appSource dl rfl).hf (appSource dl rfl).feq

/-- `betaDomSrc`'s stored typing re-indexed to
    `TyP E n Γ A (.sort (betaDomSrc dl).u)` by its own `he'`/`hT`.  For
    `app`/`conv`-headed `dl` the casts are `rfl` and the node is a literal
    `dl` descendant (`subAt`-reachable); for `wk`/`esub`/`lsub`/`linst`/
    `ewk`/`cctx` heads it is the decoder's re-wrapped transport, never an
    occurrence. -/
abbrev betaDomTy {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat}
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B)) :
    TyP E n Γ A (.sort (betaDomSrc dl).u) :=
  tyCast (betaDomSrc dl).he' (betaDomSrc dl).hT (betaDomSrc dl).H

/-- `appSource`'s argument typing re-indexed to `arg` by its own `aeq`.
    For `app`/`conv`-headed `dl` the cast is `rfl` and the node is a
    literal `dl` descendant; transported heads re-wrap it. -/
abbrev betaArgTy {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat}
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B)) :
    TyP E n Γ arg (appSource dl rfl).A :=
  tyCast (appSource dl rfl).aeq rfl (appSource dl rfl).ha

/-- `betaDomTy` inherits `dl`'s `AssumpPref` through the decoders and the
    re-indexing casts. -/
theorem betaDomTy_ap {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat}
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (hap : dl.AssumpPref) : (betaDomTy dl).AssumpPref := by
  have h := lamDomain_ap (appSource dl rfl).hf (appSource dl rfl).feq
    (appSource_ap dl rfl hap).1
  exact assumpPref_tyCast (betaDomSrc dl).he' (betaDomSrc dl).hT h

/-- `betaArgTy` inherits `dl`'s `AssumpPref` through `appSource` and the
    subject cast. -/
theorem betaArgTy_ap {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat}
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (hap : dl.AssumpPref) : (betaArgTy dl).AssumpPref := by
  have h := (appSource_ap dl rfl hap).2
  exact assumpPref_tyCast (appSource dl rfl).aeq rfl h

/-- `appDomain`'s stored typing re-indexed to `appSource`'s recorded domain
    by its own `he'`/`hT` — a sort typing of `(appSource dl rfl).A` at level
    `(appDomain dl rfl).u`.  For a direct `TyP.app` the casts are `rfl` and
    the node is `dl`'s `hf.reg.2` domain child (`subAt`-reachable). -/
abbrev betaAppDomTy {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat}
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B)) :
    TyP E n Γ (appSource dl rfl).A (.sort (appDomain dl rfl).u) :=
  tyCast (appDomain dl rfl).he' (appDomain dl rfl).hT (appDomain dl rfl).H

/-- `betaAppDomTy` inherits `dl`'s `AssumpPref` through `appDomain` and the
    re-indexing casts. -/
theorem betaAppDomTy_ap {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat}
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (hap : dl.AssumpPref) : (betaAppDomTy dl).AssumpPref :=
  assumpPref_tyCast (appDomain dl rfl).he' (appDomain dl rfl).hT
    (appDomain_ap dl rfl hap)

/-! ## §2 the `StepIH`-discharged ports (`Issues.occ_bitCoh`/`occ_cl`) -/

/-- `BIT[Hg, hA]` — `domBit` re-anchored on `betaDomSrc`.  Discharged by
    the landed `es_issued_occ_bitCoh` (`Issues.occ_bitCoh`, same site,
    subject `A` on both sides) whenever `betaDomTy dl` sits at an
    occurrence path — for a direct `TyP.app`, `pH = [3, 0, 0]` by `rfl`. -/
theorem beta_domBit_of_occ (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pH : List Nat)
    (hocc : P2Query.subAt
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) 0 pH =
        some (.ty (betaDomTy dl)))
    (hq : Demand
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ))
    (ih : StepIH Aw tbl
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)) :
    levelIsZero (σ (betaDomSrc dl).u) = levelIsZero (σ u) := by
  obtain ⟨hapA, _, _, hapdl, _⟩ := hq.ap
  exact es_issued_occ_bitCoh Aw tbl
    (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) rfl S σ ρ
    (betaDomTy dl) hA pH [0] hocc rfl (betaDomTy_ap dl hapdl) hapA hq ih

/-- `CL[betaArgTy, harg]` — the issued `.cl` leg, discharged by the landed
    `es_issued_occ_cl` whenever `betaArgTy dl` sits at an occurrence path
    (`[3, 1]` by `rfl` for a direct `TyP.app`). -/
theorem beta_argCl_of_occ (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pA : List Nat)
    (hocc : P2Query.subAt
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) 0 pA =
        some (.ty (betaArgTy dl)))
    (hq : Demand
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ))
    (ih : StepIH Aw tbl
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)) :
    CL tbl σ ρ (betaArgTy dl) harg := by
  obtain ⟨_, _, haparg, hapdl, _⟩ := hq.ap
  exact es_issued_occ_cl Aw tbl
    (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) rfl S σ ρ
    (betaArgTy dl) harg pA [2] hocc rfl (betaArgTy_ap dl hapdl) haparg hq ih

/-- `CL[g.harg, harg]` — `argCl` — from the `betaArgTy` occurrence plus the
    erasure bridge `g.harg.eps σ ρ = (betaArgTy dl).eps σ ρ` (`rfl` for
    `ewk`-wrapped reads). -/
theorem beta_argCl_of_occ_eps (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    {g : RedexGot Aw (dl.wt Aw) E n Γ A body arg}
    (pA : List Nat)
    (hocc : P2Query.subAt
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) 0 pA =
        some (.ty (betaArgTy dl)))
    (heps : g.harg.eps σ ρ = (betaArgTy dl).eps σ ρ)
    (hq : Demand
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ))
    (ih : StepIH Aw tbl
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)) :
    CL tbl σ ρ g.harg harg := by
  have hcl := beta_argCl_of_occ Aw tbl hA hbody harg dl dr S σ ρ pA hocc hq ih
  show ConvMod (EStep tbl) LvlEq (g.harg.eps σ ρ) (harg.eps σ ρ)
  rw [heps]
  exact hcl

/-- `domBit` (`levelIsZero (σ g.u) = levelIsZero (σ u)`) from the
    `Hg`-anchored bit — the reader compatibility is discharged by the
    landed `readRedex_domain_u`. -/
theorem beta_domBit_of_read (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (σ : Level → Level)
    {g : RedexGot Aw (dl.wt Aw) E n Γ A body arg}
    (hr : readRedex (envExt_refl E) Aw dl rfl = .yes g)
    (hbit : levelIsZero (σ (betaDomSrc dl).u) = levelIsZero (σ u)) :
    levelIsZero (σ g.u) = levelIsZero (σ u) := by
  have heq : (betaDomSrc dl).u = g.u :=
    readRedex_domain_u (envExt_refl E) Aw dl rfl hr
  rw [heq] at hbit
  exact hbit

/-! ## §2b `argTag`'s `occ_pb` discharge (`PBit` chains anchored on `hA`)

`argTag` (`Tag[g.harg, harg]`) has no `Issues` tag row, but its statement is
exactly a `PBit` chain: `PBit σ ρ harg hA` is *unconditionally* issuable —
`harg` sits at `(0, [2])` and `hA` at `(0, [0])` of the `CvP.beta` payload,
both by `rfl`.  The read-side leg is issuable once `betaArgTy dl` (or the
`(appSource.A)`-cast of it) sits at an occurrence path, chained through the
read's eps bridge.  Two receipt routes are provided: the `hA`-anchored
route needs `(appSource dl rfl).A = A` (the application's recorded domain is
the β domain); the `appDomain`-anchored route needs a receipt for
`betaAppDomTy dl` and the level-bit equality
`levelIsZero (σ (appDomain dl rfl).u) = levelIsZero (σ u)`. -/

/-- `PBit σ ρ harg hA` — unconditional `occ_pb` issue: `harg` sits at
    `(0, [2])` and `hA` at `(0, [0])` by `rfl`, with weight bounds by
    `simp only [CvP.wt]; omega` — the same route as the landed
    `beta_issued_dl_reg_pb`. -/
theorem beta_issued_harg_pb (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)) :
    PBit σ ρ harg hA := by
  obtain ⟨hapA, _, haparg, _, _⟩ := hq.ap
  exact ih_issue Aw tbl hq ih (.pb harg hA S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := [2]) (k₂ := 0) (p₂ := [0])
      rfl rfl haparg hapA)
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.beta E n Γ A body arg B u hA hbody harg dl dr)
        rfl harg hA
        (by simp only [CvP.wt]; omega) (by simp only [CvP.wt]; omega)))))

/-- `PBit σ ρ (hAeq ▸ betaArgTy dl) hA` — the `hA`-anchored
    read-side leg.  Whenever `betaArgTy dl` sits at occurrence path `pA` and
    the application's recorded domain is the β domain
    (`hAeq : (appSource dl rfl).A = A`), the type-cast node sits at the same
    `pA` (`dnode_ty_cast*`: `▸` leaves the forest node unchanged) and
    `occ_pb` at `(pA, [0])` issues the bit. -/
theorem beta_issued_argCast_pb (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pA : List Nat)
    (hAeq : (appSource dl rfl).A = A)
    (hocc : P2Query.subAt
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) 0 pA =
        some (.ty (betaArgTy dl)))
    (hq : Demand
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ))
    (ih : StepIH Aw tbl
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)) :
    PBit σ ρ (hAeq ▸ betaArgTy dl) hA := by
  obtain ⟨hapA, _, _, hapdl, _⟩ := hq.ap
  have hocc' : P2Query.subAt
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) 0 pA =
        some (.ty (hAeq ▸ betaArgTy dl)) := by
    rw [dnode_ty_castT hAeq (betaArgTy dl)]
    exact hocc
  have hpA : pA ≠ [] := by
    rintro rfl
    rw [P2Query.subAt] at hocc
    simp only [P2Query.payload, List.getElem?_cons_zero, Option.some_bind,
      DNode.subAt] at hocc
    exact DNode.noConfusion (Option.some.inj hocc)
  have hw₁ : (hAeq ▸ betaArgTy dl).wt Aw <
      (CvP.beta E n Γ A body arg B u hA hbody harg dl dr).wt Aw := by
    rw [TyP.wt_castT]
    exact DNode.subAt_wt_lt Aw pA hpA _ _ hocc
  exact ih_issue Aw tbl hq ih
    (.pb (hAeq ▸ betaArgTy dl) hA S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := pA) (k₂ := 0) (p₂ := [0])
      hocc' rfl
      (TyP.ap_castT hAeq (betaArgTy dl) ▸ betaArgTy_ap dl hapdl) hapA)
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.beta E n Γ A body arg B u hA hbody harg dl dr)
        rfl (hAeq ▸ betaArgTy dl) hA
        hw₁ (by simp only [CvP.wt]; omega)))))

/-- `PBit σ ρ (betaArgTy dl) (betaAppDomTy dl)` — the `appDomain`-anchored
    read-side leg: `occ_pb` at `(pA, pDom)` issues the bit between the
    argument typing and the recorded domain's sort typing whenever both sit
    at occurrence paths. -/
theorem beta_issued_appArg_pb (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pA pDom : List Nat)
    (hoccA : P2Query.subAt
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) 0 pA =
        some (.ty (betaArgTy dl)))
    (hoccD : P2Query.subAt
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) 0 pDom =
        some (.ty (betaAppDomTy dl)))
    (hq : Demand
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ))
    (ih : StepIH Aw tbl
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)) :
    PBit σ ρ (betaArgTy dl) (betaAppDomTy dl) := by
  obtain ⟨_, _, _, hapdl, _⟩ := hq.ap
  have hpA : pA ≠ [] := by
    rintro rfl
    rw [P2Query.subAt] at hoccA
    simp only [P2Query.payload, List.getElem?_cons_zero, Option.some_bind,
      DNode.subAt] at hoccA
    exact DNode.noConfusion (Option.some.inj hoccA)
  have hpD : pDom ≠ [] := by
    rintro rfl
    rw [P2Query.subAt] at hoccD
    simp only [P2Query.payload, List.getElem?_cons_zero, Option.some_bind,
      DNode.subAt] at hoccD
    exact DNode.noConfusion (Option.some.inj hoccD)
  have hwA : (betaArgTy dl).wt Aw <
      (CvP.beta E n Γ A body arg B u hA hbody harg dl dr).wt Aw :=
    DNode.subAt_wt_lt Aw pA hpA _ _ hoccA
  have hwD : (betaAppDomTy dl).wt Aw <
      (CvP.beta E n Γ A body arg B u hA hbody harg dl dr).wt Aw :=
    DNode.subAt_wt_lt Aw pDom hpD _ _ hoccD
  exact ih_issue Aw tbl hq ih
    (.pb (betaArgTy dl) (betaAppDomTy dl) S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := pA) (k₂ := 0) (p₂ := pDom)
      hoccA hoccD (betaArgTy_ap dl hapdl) (betaAppDomTy_ap dl hapdl))
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.beta E n Γ A body arg B u hA hbody harg dl dr)
        rfl (betaArgTy dl) (betaAppDomTy dl) hwA hwD))))

/-- `Tag[g.harg, harg]` — the `hA`-anchored route: `betaArgTy`'s occurrence
    plus `(appSource dl rfl).A = A` plus the eps bridge chains
    `PBit[cast, hA]` and `PBit[harg, hA]` to the tag. -/
theorem beta_argTag_of_occ_eps (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    {g : RedexGot Aw (dl.wt Aw) E n Γ A body arg}
    (pA : List Nat)
    (hAeq : (appSource dl rfl).A = A)
    (hocc : P2Query.subAt
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) 0 pA =
        some (.ty (betaArgTy dl)))
    (heps : g.harg.eps σ ρ = (betaArgTy dl).eps σ ρ)
    (hq : Demand
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ))
    (ih : StepIH Aw tbl
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)) :
    (g.harg.eps σ ρ = .star) ↔ (harg.eps σ ρ = .star) := by
  have hpbL : PBit σ ρ (hAeq ▸ betaArgTy dl) hA :=
    beta_issued_argCast_pb Aw tbl hA hbody harg dl dr S σ ρ pA hAeq hocc hq ih
  have hpbR : PBit σ ρ harg hA :=
    beta_issued_harg_pb Aw tbl hA hbody harg dl dr S σ ρ hq ih
  have heps' : (hAeq ▸ betaArgTy dl).eps σ ρ =
      (betaArgTy dl).eps σ ρ :=
    TyP.eps_castT hAeq (betaArgTy dl) σ ρ
  constructor
  · intro hstar
    exact hpbR.mpr (hpbL.mp (heps'.symm ▸ (heps ▸ hstar)))
  · intro hstar
    have h1 : (hAeq ▸ betaArgTy dl).eps σ ρ = .star :=
      hpbL.mpr (hpbR.mp hstar)
    have h2 : (betaArgTy dl).eps σ ρ = .star := heps' ▸ h1
    exact heps.symm ▸ h2

/-- `Tag[g.harg, harg]` — the `appDomain`-anchored route: the
    `betaArgTy`/`betaAppDomTy` occurrence pair plus the eps bridge plus the
    level-bit equality `lZ (σ (appDomain dl rfl).u) = lZ (σ u)` chains
    `PBit[betaArgTy, betaAppDomTy]` and `PBit[harg, hA]` to the tag. -/
theorem beta_argTag_of_appDom_occ (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    {g : RedexGot Aw (dl.wt Aw) E n Γ A body arg}
    (pA pDom : List Nat)
    (hoccA : P2Query.subAt
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) 0 pA =
        some (.ty (betaArgTy dl)))
    (hoccD : P2Query.subAt
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) 0 pDom =
        some (.ty (betaAppDomTy dl)))
    (heps : g.harg.eps σ ρ = (betaArgTy dl).eps σ ρ)
    (hbit : levelIsZero (σ (appDomain dl rfl).u) = levelIsZero (σ u))
    (hq : Demand
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ))
    (ih : StepIH Aw tbl
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)) :
    (g.harg.eps σ ρ = .star) ↔ (harg.eps σ ρ = .star) := by
  have hpbL : PBit σ ρ (betaArgTy dl) (betaAppDomTy dl) :=
    beta_issued_appArg_pb Aw tbl hA hbody harg dl dr S σ ρ pA pDom hoccA hoccD
      hq ih
  have hpbR : PBit σ ρ harg hA :=
    beta_issued_harg_pb Aw tbl hA hbody harg dl dr S σ ρ hq ih
  constructor
  · intro hstar
    exact hpbR.mpr (hbit ▸ hpbL.mp (heps ▸ hstar))
  · intro hstar
    have h1 : levelIsZero (σ (appDomain dl rfl).u) = true :=
      hbit.symm ▸ hpbR.mp hstar
    have h2 : (betaArgTy dl).eps σ ρ = .star := hpbL.mpr h1
    exact heps.symm ▸ h2

/-! ## §3 the closed residual and the field theorem -/

/-- `BetaClPorts` after the `DomainSource` re-measure: `domBit` and
    `argCl` gain an occurrence-receipt disjunct discharged by `StepIH`;
    the other four fields are the verbatim `BetaClPorts` ports — still
    (d), named in the module docstring. -/
structure BetaClPortsClosed (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg) : Type where
  /-- `BIT[Hg, hA]` ∘ `readRedex_domain_u` compat — the `∃`-receipt
      disjunct is discharged by `beta_domBit_of_occ`. -/
  domBit :
    (∃ pH, P2Query.subAt
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) 0 pH =
        some (.ty (betaDomTy dl)))
    ∨ levelIsZero (σ (betaDomSrc dl).u) = levelIsZero (σ u)
  /-- `Tag[g.harg, harg]` — `(routeA ∨ routeB) ∨ Tag`: the `hA`-anchored
      disjunct needs `betaArgTy`'s occurrence, `(appSource dl rfl).A = A`,
      and the eps bridge; the `appDomain`-anchored disjunct needs both
      occurrences, the bridge, and the level-bit equality.  Either is
      discharged by `StepIH`; the verbatim `Tag` is the (d) fallback. -/
  argTag :
    ((∃ pA, P2Query.subAt
        (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) 0 pA =
          some (.ty (betaArgTy dl)))
      ∧ (appSource dl rfl).A = A
      ∧ g.harg.eps σ ρ = (betaArgTy dl).eps σ ρ)
    ∨ (((∃ pA, P2Query.subAt
          (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) 0 pA =
            some (.ty (betaArgTy dl)))
        ∧ (∃ pDom, P2Query.subAt
          (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) 0 pDom =
            some (.ty (betaAppDomTy dl)))
        ∧ g.harg.eps σ ρ = (betaArgTy dl).eps σ ρ
        ∧ levelIsZero (σ (appDomain dl rfl).u) = levelIsZero (σ u))
      ∨ ((g.harg.eps σ ρ = .star) ↔ (harg.eps σ ρ = .star)))
  /-- `CL[g.harg, harg]` — `(∃ receipt ∧ eps-bridge) ∨ CL`. -/
  argCl :
    ((∃ pA, P2Query.subAt
        (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) 0 pA =
          some (.ty (betaArgTy dl)))
      ∧ g.harg.eps σ ρ = (betaArgTy dl).eps σ ρ)
    ∨ CL tbl σ ρ g.harg harg
  /-- `Tag[g.hbody, hbody]` — (d), verbatim `BetaClPorts.bodyTag`. -/
  bodyTag : (g.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
    (hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star)
  /-- `CL[g.hbody, hbody]` — (d), verbatim `BetaClPorts.bodyCl`. -/
  bodyCl : CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) g.hbody hbody
  /-- `CL[instEnd, dr]` — (d), verbatim `BetaClPorts.reductCl`. -/
  reductCl : CL tbl σ ρ (instEnd hbody harg hA) dr

/-- `BetaFieldResid` after the `DomainSource` re-measure: `clause`/`raw`
    arms carry `BetaClPortsClosed`; the `star` arm's `PBit` pair gains the
    `dl.reg.2` occurrence disjunct discharged by the landed
    `beta_issued_*_reg_pb`; `none` keeps the verbatim `BetaPorts`. -/
def BetaFieldResidClosed (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    (r : RedexRead Aw (dl.wt Aw) E n Γ A body arg) →
    RedexVerdict dl σ ρ r → Type
  | .yes g, .clause _ => BetaClPortsClosed Aw tbl hA hbody harg dl dr S σ ρ g
  | .yes _, .star _ =>
      PLift ((∃ pReg, P2Query.subAt
          (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) 0 pReg =
            some (.ty dl.reg.2))
        ∨ (PBit σ ρ dl dl.reg.2 ∧ PBit σ ρ dr dl.reg.2))
  | .yes g, .raw =>
      PProd (dl.eps σ ρ = redexClauseOf g σ ρ)
        (BetaClPortsClosed Aw tbl hA hbody harg dl dr S σ ρ g)
  | .no, _ => BetaPorts Aw tbl hA hbody harg dl dr σ ρ

/-- Convert the weakened ports to the landed `BetaClPorts`: the
    `∃`-receipt disjuncts are discharged by `StepIH`; everything else is
    verbatim. -/
def BetaClPortsClosed.toBetaClPorts (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    {g : RedexGot Aw (dl.wt Aw) E n Γ A body arg}
    (ports : BetaClPortsClosed Aw tbl hA hbody harg dl dr S σ ρ g)
    (hr : readRedex (envExt_refl E) Aw dl rfl = .yes g)
    (hq : Demand
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ))
    (ih : StepIH Aw tbl
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)) :
    BetaClPorts Aw tbl hA hbody harg dl dr σ ρ g := by
  refine ⟨?_, ?_, ?_, ports.bodyTag, ports.bodyCl, ports.reductCl⟩
  · rcases ports.domBit with ⟨pH, hocc⟩ | hbit
    · exact beta_domBit_of_read Aw dl σ hr
        (beta_domBit_of_occ Aw tbl hA hbody harg dl dr S σ ρ pH hocc hq ih)
    · exact beta_domBit_of_read Aw dl σ hr hbit
  · rcases ports.argTag with ⟨⟨pA, hocc⟩, hAeq, heps⟩ |
        ⟨⟨pA, hoccA⟩, ⟨pDom, hoccD⟩, heps, hbit⟩ | htag
    · exact beta_argTag_of_occ_eps Aw tbl hA hbody harg dl dr S σ ρ
        pA hAeq hocc heps hq ih
    · exact beta_argTag_of_appDom_occ Aw tbl hA hbody harg dl dr S σ ρ
        pA pDom hoccA hoccD heps hbit hq ih
    · exact htag
  · rcases ports.argCl with ⟨⟨pA, hocc⟩, heps⟩ | hcl
    · exact beta_argCl_of_occ_eps Aw tbl hA hbody harg dl dr S σ ρ pA hocc heps
        hq ih
    · exact hcl

/-- `StepSuppliers.es_beta` after the `DomainSource` re-measure: the same
    telescope plus `BetaFieldResidClosed`.  `clause`/`raw`/`none` finish by
    the landed `es_beta` through `toBetaClPorts`; `star` finishes by the
    landed `es_beta_of_dl_star_reg_occ` on the occurrence disjunct and by
    `ConvMod.refl` on the `PBit` pair, exactly as `es_beta_field`. -/
theorem es_beta_closed (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (resid : BetaFieldResidClosed Aw tbl hA hbody harg dl dr S σ ρ
      (readRedex (envExt_refl E) Aw dl rfl)
      (epsReadRedex (envExt_refl E) Aw σ dl rfl ρ)) :
    CaseStep Aw tbl
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) := by
  intro hq ih
  have key : PSigma fun (r : RedexRead Aw (dl.wt Aw) E n Γ A body arg) =>
      PSigma fun (v : RedexVerdict dl σ ρ r) =>
        PProd (readRedex (envExt_refl E) Aw dl rfl = r)
          (BetaFieldResidClosed Aw tbl hA hbody harg dl dr S σ ρ r v) :=
    ⟨_, _, rfl, resid⟩
  obtain ⟨r, v, hr, res⟩ := key
  cases v with
  | clause heps =>
      exact es_beta Aw tbl hA hbody harg dl dr S σ ρ
        (BetaClPorts.toBetaPorts heps
          (BetaClPortsClosed.toBetaClPorts Aw tbl hA hbody harg dl dr S σ ρ
            res hr hq ih)) hq ih
  | star heps =>
      rcases res.down with ⟨pReg, hocc⟩ | hpb
      · exact es_beta_of_dl_star_reg_occ Aw tbl hA hbody harg dl dr S σ ρ
          heps pReg hocc hq ih
      · show ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)
        rw [heps, hpb.2.mpr (hpb.1.mp heps)]
        exact ConvMod.refl _
  | raw =>
      exact es_beta Aw tbl hA hbody harg dl dr S σ ρ
        (BetaClPorts.toBetaPorts res.1
          (BetaClPortsClosed.toBetaClPorts Aw tbl hA hbody harg dl dr S σ ρ
            res.2 hr hq ih)) hq ih
  | none =>
      exact es_beta Aw tbl hA hbody harg dl dr S σ ρ res hq ih

/-! ## §4 non-vacuity: a concrete direct-`TyP.app` fixture

`A := .sort l1` (sorted at `l2`), `body := .sort l0`, `arg := .sort l0`,
`B := .sort l1`, `u := l2`, at `emptyEnv`, `n = 0`, `Γ = []`.  `dr` is
`instEnd` itself, so `reductCl` is `ConvMod.refl`.  Every receipt disjunct
of `BetaClPortsClosed`/`BetaFieldResidClosed`'s `star` arm and every
verbatim port is inhabited here — the residual is not vacuous. -/

namespace ClosedControls

private def l0 : Level := .zero
private def l1 : Level := .succ l0
private def l2 : Level := .succ l1
private def l3 : Level := .succ l2

private def sort0 (Γ : LCtx) : TyP emptyEnv 0 Γ (.sort l0) (.sort l1) :=
  TyP.sort _ _ _ _ _ (eqN_refl _)
private def sort1 (Γ : LCtx) : TyP emptyEnv 0 Γ (.sort l1) (.sort l2) :=
  TyP.sort _ _ _ _ _ (eqN_refl _)
private def sort2 (Γ : LCtx) : TyP emptyEnv 0 Γ (.sort l2) (.sort l3) :=
  TyP.sort _ _ _ _ _ (eqN_refl _)

/-- `A := .sort l1` typed at `.sort l2` (so `u = l2`). -/
def fixHA : TyP emptyEnv 0 [] (.sort l1) (.sort l2) := sort1 []
/-- `body := .sort l0` typed at `B := .sort l1` under the binder. -/
def fixHBody : TyP emptyEnv 0 [.assumption (.sort l1)] (.sort l0) (.sort l1) :=
  sort0 _
/-- `arg := .sort l0` typed at `A := .sort l1`. -/
def fixHArg : TyP emptyEnv 0 [] (.sort l0) (.sort l1) := sort0 []

/-- The function: `.lam (.sort l1) (.sort l0) : .pi (.sort l1) (.sort l1)`. -/
def fixHf : TyP emptyEnv 0 [] (.lam (.sort l1) (.sort l0))
    (.pi (.sort l1) (.sort l1)) :=
  TyP.lam emptyEnv 0 [] (.sort l1) l2 (.sort l0) (.sort l1) l2
    fixHA fixHBody (sort1 _)

/-- The left endpoint: `app (lam …) arg`. -/
def fixDl : TyP emptyEnv 0 [] (.app (.lam (.sort l1) (.sort l0)) (.sort l0))
    (instantiate0 (.sort l0) (.sort l1)) :=
  TyP.app emptyEnv 0 [] (.lam (.sort l1) (.sort l0)) (.sort l0)
    (.sort l1) (.sort l1) l2 fixHf fixHArg (sort1 _)

/-- The right endpoint — `instEnd` itself, so `reductCl` is `refl`. -/
def fixDr : TyP emptyEnv 0 [] (instantiate0 (.sort l0) (.sort l0))
    (instantiate0 (.sort l0) (.sort l1)) :=
  instEnd fixHBody fixHArg fixHA

/-- The β conversion node. -/
def fixBeta : CvP emptyEnv 0 [] (.app (.lam (.sort l1) (.sort l0)) (.sort l0))
    (instantiate0 (.sort l0) (.sort l0)) (instantiate0 (.sort l0) (.sort l1)) :=
  CvP.beta emptyEnv 0 [] (.sort l1) (.sort l0) (.sort l0) (.sort l1) l2
    fixHA fixHBody fixHArg fixDl fixDr

/-- The `LamGot` the read produces for `fixHf`. -/
def fixLamGot (Aw : Nat → Nat) :
    LamGot Aw (fixHf.wt Aw) emptyEnv 0 [] (.sort l1) (.sort l0) where
  B := .sort l1
  u := l2
  hbody := fixHBody
  lt := fun y hy => atoms_lt_of_wt_lt Aw fixHBody
    (by simp only [fixHf, fixHBody, sort0, sort1, TyP.wt]; omega) y hy

/-- The `RedexGot` the read produces for `fixDl`. -/
def fixGot (Aw : Nat → Nat) :
    RedexGot Aw (fixDl.wt Aw) emptyEnv 0 [] (.sort l1) (.sort l0) (.sort l0) :=
  redexOfApp (envExt_refl emptyEnv) Aw (fixLamGot Aw) fixHArg (sort1 _)

/-- `domBit`'s receipt disjunct: the decoder's `Hg.H` sits at `[3, 0, 0]`. -/
theorem domBit_occ_witness (S : ScopedCtx Eₐ emptyEnv 0 []) :
    P2Query.subAt (.es fixBeta S id []) 0 [3, 0, 0] =
      some (.ty (betaDomTy fixDl)) := rfl

/-- `argCl`'s receipt disjunct: the decoder's `ha` sits at `[3, 1]`. -/
theorem argTy_occ_witness (S : ScopedCtx Eₐ emptyEnv 0 []) :
    P2Query.subAt (.es fixBeta S id []) 0 [3, 1] =
      some (.ty (betaArgTy fixDl)) := rfl

/-- The `star` arm's receipt disjunct: `dl.reg.2` sits at `[3, 2]`. -/
theorem reg2_occ_witness (S : ScopedCtx Eₐ emptyEnv 0 []) :
    P2Query.subAt (.es fixBeta S id []) 0 [3, 2] =
      some (.ty fixDl.reg.2) := rfl

/-- `argTag`'s `appDomain` receipt: `betaAppDomTy fixDl`'s `piDomSrc` walk
    lands on `fixHA` with `rfl`-reducible re-indexings, so the node sits at
    `[0]` — `hA`'s own child slot. -/
theorem appDom_occ_witness (S : ScopedCtx Eₐ emptyEnv 0 []) :
    P2Query.subAt (.es fixBeta S id []) 0 [0] =
      some (.ty (betaAppDomTy fixDl)) := rfl

/-- `BetaClPortsClosed` is inhabited at the read's `RedexGot`: every
    receipt disjunct by `rfl` (the `hA`-anchored `argTag` route at `[3, 1]`
    with `(appSource fixDl rfl).A = .sort l1` by `rfl` and the eps bridge by
    `rfl` — the read's `harg` is `ewk`-transparent), and every verbatim port
    by `Iff.rfl`/`ConvMod.refl`. -/
def fixPortsClosed (Aw : Nat → Nat) (tbl : List CRule)
    (S : ScopedCtx Eₐ emptyEnv 0 []) :
    BetaClPortsClosed Aw tbl fixHA fixHBody fixHArg fixDl fixDr S id []
      (fixGot Aw) where
  domBit := .inl ⟨[3, 0, 0], rfl⟩
  argTag := .inl ⟨⟨[3, 1], rfl⟩, rfl, rfl⟩
  argCl := .inl ⟨⟨[3, 1], rfl⟩, rfl⟩
  bodyTag := Iff.rfl
  bodyCl := ConvMod.refl _
  reductCl := ConvMod.refl _

/-- The `appDomain`-anchored `argTag` route is inhabited too: `betaArgTy`
    at `[3, 1]`, `betaAppDomTy` at `[0]` (`appDom_occ_witness`), eps bridge
    and `l2`-bit equality by `rfl`. -/
def fixPortsClosedDom (Aw : Nat → Nat) (tbl : List CRule)
    (S : ScopedCtx Eₐ emptyEnv 0 []) :
    BetaClPortsClosed Aw tbl fixHA fixHBody fixHArg fixDl fixDr S id []
      (fixGot Aw) where
  domBit := .inl ⟨[3, 0, 0], rfl⟩
  argTag := .inr (.inl ⟨⟨[3, 1], rfl⟩, ⟨[0], rfl⟩, rfl, rfl⟩)
  argCl := .inl ⟨⟨[3, 1], rfl⟩, rfl⟩
  bodyTag := Iff.rfl
  bodyCl := ConvMod.refl _
  reductCl := ConvMod.refl _

/-- The `star` arm's `PBit` fallback is satisfiable too: `fixDl`'s
    erasure is a concrete non-`★` application and `fixDl.reg.1 = l2` is
    non-zero, so both iff legs are `false ↔ false`. -/
theorem fixStarPair :
    PBit id [] fixDl fixDl.reg.2 ∧ PBit id [] fixDr fixDl.reg.2 := by
  refine ⟨⟨(fun h => nomatch h), (fun h => nomatch h)⟩, ?_⟩
  constructor
  · intro h
    have h' : (instEnd fixHBody fixHArg fixHA).eps id [] = .star := h
    rw [instEnd_eps_keep fixHBody fixHArg fixHA
      (hu := (show levelIsZero (id l2) = false from rfl))] at h'
    cases h'
  · intro h
    cases h

/-- The `none` verdict's whole `BetaPorts` is satisfiable at `fixGot`:
    `redexClauseOf` of the fixture `RedexGot` computes to `fixDl`'s
    erasure, `domBit` is `l2 = l2`, and the remaining ports are
    `Iff.rfl`/`ConvMod.refl` as in `fixPortsClosed`. -/
def fixBetaPorts (Aw : Nat → Nat) (tbl : List CRule) :
    BetaPorts Aw tbl fixHA fixHBody fixHArg fixDl fixDr id [] where
  got := fixGot Aw
  eps := rfl
  domBit := rfl
  argTag := Iff.rfl
  argCl := ConvMod.refl _
  bodyTag := Iff.rfl
  bodyCl := ConvMod.refl _
  reductCl := ConvMod.refl _

end ClosedControls

end Rcic.Syn

#print axioms Rcic.Syn.betaDomTy
#print axioms Rcic.Syn.betaArgTy
#print axioms Rcic.Syn.betaAppDomTy
#print axioms Rcic.Syn.betaDomTy_ap
#print axioms Rcic.Syn.betaArgTy_ap
#print axioms Rcic.Syn.betaAppDomTy_ap
#print axioms Rcic.Syn.beta_domBit_of_occ
#print axioms Rcic.Syn.beta_argCl_of_occ
#print axioms Rcic.Syn.beta_argCl_of_occ_eps
#print axioms Rcic.Syn.beta_domBit_of_read
#print axioms Rcic.Syn.beta_issued_harg_pb
#print axioms Rcic.Syn.beta_issued_argCast_pb
#print axioms Rcic.Syn.beta_issued_appArg_pb
#print axioms Rcic.Syn.beta_argTag_of_occ_eps
#print axioms Rcic.Syn.beta_argTag_of_appDom_occ
#print axioms Rcic.Syn.BetaClPortsClosed
#print axioms Rcic.Syn.BetaFieldResidClosed
#print axioms Rcic.Syn.BetaClPortsClosed.toBetaClPorts
#print axioms Rcic.Syn.es_beta_closed
#print axioms Rcic.Syn.ClosedControls.fixPortsClosed
#print axioms Rcic.Syn.ClosedControls.fixPortsClosedDom
#print axioms Rcic.Syn.ClosedControls.appDom_occ_witness
#print axioms Rcic.Syn.ClosedControls.fixStarPair
#print axioms Rcic.Syn.ClosedControls.fixBetaPorts

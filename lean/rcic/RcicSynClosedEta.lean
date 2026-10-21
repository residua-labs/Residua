import rcic.RcicSynStepFields4
import rcic.RcicSynDomainSource
import rcic.RcicSynEtaBody
import rcic.RcicSynEtaLam
import rcic.RcicSynEtaMeet
import rcic.RcicSynRead

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-!
# `StepSuppliers.es_eta` — the closed fragments

`swe-eta` lane of the RCIC `sortRow` supplier effort.
`research/rcic/sortrow/STEP_SUPPLIERS.md`,
`BELOWC_FAILED_READERS_AND_LET_BODY.md` §3.2, **W-ER2-SHIFTED-VALUE-SCOPE**.
`closure_claim = 0`.

Composition only: the landed field filler `eta_caseStep_of_ports`
(`RcicSynStepFields4.lean:1335`) does the assembly over `EtaPorts`
(`RcicSynStepFields4.lean:1309`); the `Below`-route fillers
`es_eta_of_below_drop` / `es_eta_of_below_keep`
(`RcicSynEtaMeet.lean:218`/`244`) remain conditional on `Below`. No landed
statement is edited and no landed proof is copied.

## §0 Measurement — every port, classified

Categories: (a) already discharged on main; (b) answerable from `StepIH`
through an existing `Issues` row; (c) provable outright from landed lemmas;
(d) genuinely open — kept as a named premise with a satisfiability witness.

### `EtaPorts` (`RcicSynStepFields4.lean:1309`), for
`CaseStep Aw tbl (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ)`

| port | exact type | class | evidence |
|---|---|---|---|
| `tableWF` | `TableWF tbl` | data | allowed field-group datum; `tableWF_build` (`RcicSynTableBuild.lean:222`) issues it from `EnvWfT` |
| `u` | `Level` | **(c)** | `(etaDom dl).u` below — `lamDomain` (`RcicSynDomainSource.lean:235`) is a *total* structural decoder (it decodes the `lsub`/`cctx`/`linst`/`esub`/`wk` heads the readers decline) |
| `hA` | `TyP E n Γ A (.sort u)` | **(c)** | `etaDom_hA dl` below — `lamDomain`'s `H` field, index-cast by `hT`/`he'`; `wt` descent `lamDomain_wt_lt` (`:293`), `AssumpPref` descent `lamDomain_ap` (`:357`) |
| `got` | `AppGot Aw (dl.wt Aw) E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0)` | **(d)** | `meetEta`/`readLam`/`readApp` are partial (`readLam` declines `.lsub`/`.cctx`, `RcicSynRedex.lean:226`; `readApp` declines `cctx`/subst-born bodies, `RcicSynEtaBody.lean:255`). Name search (`bodySource`/`lamBody` decoder) and type search (a `TyP … (.lam A body) … → AppGot …` producer) find nothing total on main. Satisfiable: `etaResiduum_etaLam` below instantiates it on the canonical `etaLam` redex |
| `eps` | `dl.eps σ ρ = lamErasure (levelIsZero (σ u)) (appClauseOf got σ (binderDisp (levelIsZero (σ u)) :: ρ))` | **(d)** | `etaVerdict`'s `.clause` case (`RcicSynEtaMeet.lean`) produces the equation only when the walk returned `.yes` *and* the body erased to an `appClause`; `.star`/`.raw`/`.none` verdicts produce nothing. `eta_eps_closed` below is the exact residual adapter: two clause equations + the level pin `lamDomain_u_of_readLam` (`RcicSynDomainSource.lean:694`) close it |
| `funCl` | `CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) got.hf (wkAtZero (A := A) hf)` | **(d)** | binder-display `CL` — no `Issues` row: `eta_issued_cl_variants` (`RcicSynStepFields4.lean:1375`) proves every `.cl` an `eta` node issues is `occ_cl | eta_cl`, both same-site `(Γ, ρ)`; the port is at `binderDisp … :: ρ` inside `assumption A :: Γ`. Name/type searches find no producer. Satisfiable at the canonical `got` (`etaResiduum_etaLam`) |
| `argCl` | `CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) got.ha (etaArg hA)` | **(d)** | same `Issues`-row absence; satisfiable at the canonical `got` |
| `argTag` | `TagCoh σ (binderDisp (…) :: ρ) σ (binderDisp (…) :: ρ) got.ha (etaArg hA)` | **(d)** | `TagCoh` is not an `Issues` `.cl` child at all; no row exists. Satisfiable at the canonical `got` (`TagCoh` reduces to an eps-`Iff` of two defeq erasures) |

### `es_eta_of_below_drop`/`es_eta_of_below_keep` (`RcicSynEtaMeet.lean:218`/`244`)

| port | class | evidence |
|---|---|---|
| `hA : TyP E n Γ A (.sort u)` | **(c)** | `etaDom_hA dl` — `es_eta_below_drop_closed`/`es_eta_below_keep_closed` below |
| `Bl : Below Aw tbl (cvMeas Aw (CvP.eta …))` | **(d)** | `Below` is the documented-vacuous domain pending the ρ-respect repair (`RcicSynBelowRho`); kept verbatim |
| `a : AppGot …`, `hW`, `hvar` | **(d)** | same reader/verdict conditionals as above; kept verbatim |
| `hρ : DispFor σ E n Γ ρ` | **(d)** | context-respect; `Demand.routed` gives `RoutedDisp`, not `DispFor` — name/type search finds no `RoutedDisp → DispFor` producer |
| `hu`, `hTW` | data | level bit / `TableWF` |

Net effect: `u`/`hA` are discharged outright (`etaDom_hA`); the residual
ports are named verbatim in `EtaResiduum`, and `etaResiduum_etaLam` shows
the whole package is inhabited — no port is weakened, dropped silently,
or replaced by an equivalent restatement.
-/

/-! ## §1 `hA` discharged: the domain source of an η left endpoint -/

/-- The η left endpoint's domain source — `lamDomain` is total, so this
    never asks the caller for a domain typing. -/
def etaDom {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f A B : Expr Nat}
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B)) :
    DomainSource E n Γ A :=
  lamDomain dl rfl

/-- The domain sort-typing itself: the `u`/`hA` pair of `EtaPorts` (and the
    `hA` port of `es_eta_of_below_*`), produced from `dl` alone. The index
    cast goes through the landed `tyCast` wrapper. -/
def etaDom_hA {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f A B : Expr Nat}
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B)) :
    TyP E n Γ A (.sort (etaDom dl).u) :=
  tyCast (etaDom dl).he' (etaDom dl).hT (etaDom dl).H

/-- `wt` ignores `tyCast` repackaging — casts preserve weight. -/
theorem TyP.wt_tyCast (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e e' T T' : Expr Nat} (he : e = e') (hT : T = T')
    (D : TyP E n Γ e T) : (tyCast he hT D).wt Aw = D.wt Aw := by
  unfold tyCast
  rw [TyP.wt_castS, TyP.wt_castT]

/-- `AssumpPref` ignores `tyCast` repackaging. -/
theorem TyP.ap_tyCast {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e e' T T' : Expr Nat} (he : e = e') (hT : T = T')
    (D : TyP E n Γ e T) : (tyCast he hT D).AssumpPref = D.AssumpPref := by
  unfold tyCast
  rw [TyP.ap_castS, TyP.ap_castT]

/-- `wt` descent through the cast — strictly below `dl`, so `etaDom_hA`
    can feed descent engines. -/
theorem etaDom_wt_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat}
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B)) :
    (etaDom_hA dl).wt Aw < dl.wt Aw := by
  show (tyCast (etaDom dl).he' (etaDom dl).hT (etaDom dl).H).wt Aw < dl.wt Aw
  rw [TyP.wt_tyCast]
  exact lamDomain_wt_lt Aw dl rfl

/-- `AssumpPref` descent through the cast. -/
theorem etaDom_ap {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f A B : Expr Nat}
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (hAP : dl.AssumpPref) : (etaDom_hA dl).AssumpPref := by
  show (tyCast (etaDom dl).he' (etaDom dl).hT (etaDom dl).H).AssumpPref
  rw [TyP.ap_tyCast]
  exact lamDomain_ap dl rfl hAP

/-! ## §2 reader/verdict adapters -/

/-- `meetEta = .yes` unpacks to the two reader successes it ran —
    `readLam` on `dl` and `readApp` on the resulting body typing. -/
theorem eta_reads_of_meetEta {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat}
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    {a : AppGot Aw (dl.wt Aw) E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0)}
    (hm : meetEta (envExt_refl E) Aw dl rfl = .yes a) :
    ∃ g : LamGot Aw (dl.wt Aw) E n Γ A (.app (lift 0 1 f) (.bvar 0)),
      readLam (envExt_refl E) Aw dl rfl = .yes g ∧
        readApp (envExt_refl E) Aw (dl.wt Aw) g.hbody rfl g.lt = .yes a := by
  unfold meetEta at hm
  cases hL : readLam (envExt_refl E) Aw dl rfl with
  | no => rw [hL] at hm; dsimp only at hm; exact EtaMeet.noConfusion hm
  | yes g =>
      rw [hL] at hm
      dsimp only at hm
      cases hA' : readApp (envExt_refl E) Aw (dl.wt Aw) g.hbody rfl g.lt with
      | no => rw [hA'] at hm; dsimp only at hm; exact EtaMeet.noConfusion hm
      | yes a' =>
          rw [hA'] at hm
          dsimp only at hm
          cases hm
          exact ⟨g, rfl, hA'⟩

/-- The `eps` port, closed once both walks produced their clause equations.
    `lamDomain_u_of_readLam` pins the decoder's `u` to the reader's `g.u`,
    so the residual is genuinely conditional — nothing about `dl`'s erasure
    is assumed without a walk. -/
theorem eta_eps_closed {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f A B : Expr Nat}
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    {g : LamGot Aw (dl.wt Aw) E n Γ A (.app (lift 0 1 f) (.bvar 0))}
    (hg : readLam (envExt_refl E) Aw dl rfl = .yes g)
    {a : AppGot Aw (dl.wt Aw) E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0)}
    (σ : Level → Level) (ρ : List Disp)
    (hL : dl.eps σ ρ = lamClauseOf g σ ρ)
    (hA' : g.hbody.eps σ (binderDisp (levelIsZero (σ g.u)) :: ρ) =
      appClauseOf a σ (binderDisp (levelIsZero (σ g.u)) :: ρ)) :
    dl.eps σ ρ =
      lamErasure (levelIsZero (σ (etaDom dl).u))
        (appClauseOf a σ (binderDisp (levelIsZero (σ (etaDom dl).u)) :: ρ)) := by
  have hu := lamDomain_u_of_readLam (envExt_refl E) Aw dl rfl hg
  unfold etaDom
  rw [hu, hL]
  unfold lamClauseOf
  rw [hA']

/-! ## §3 the residual and the field -/

/-- The exact remaining ports of `StepSuppliers.es_eta`, named verbatim
    against `EtaPorts`. `u`/`hA` are gone — `etaDom` discharges them. -/
structure EtaResiduum {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f A B : Expr Nat}
    (hf : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (σ : Level → Level) (ρ : List Disp) : Type where
  tableWF : TableWF tbl
  got : AppGot Aw (dl.wt Aw) E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0)
  eps :
    dl.eps σ ρ =
      lamErasure (levelIsZero (σ (etaDom dl).u))
        (appClauseOf got σ (binderDisp (levelIsZero (σ (etaDom dl).u)) :: ρ))
  funCl :
    CL tbl σ (binderDisp (levelIsZero (σ (etaDom dl).u)) :: ρ)
      got.hf (wkAtZero (A := A) hf)
  argCl :
    CL tbl σ (binderDisp (levelIsZero (σ (etaDom dl).u)) :: ρ)
      got.ha (etaArg (etaDom_hA dl))
  argTag :
    TagCoh σ (binderDisp (levelIsZero (σ (etaDom dl).u)) :: ρ)
      σ (binderDisp (levelIsZero (σ (etaDom dl).u)) :: ρ)
      got.ha (etaArg (etaDom_hA dl))

/-- The discharge map: `EtaResiduum` + `etaDom` gives `EtaPorts`. -/
def etaPorts_of_residuum {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat}
    (hf : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (σ : Level → Level) (ρ : List Disp)
    (r : EtaResiduum Aw tbl hf dl σ ρ) : EtaPorts Aw tbl hf dl σ ρ where
  tableWF := r.tableWF
  u := (etaDom dl).u
  hA := etaDom_hA dl
  got := r.got
  eps := r.eps
  funCl := r.funCl
  argCl := r.argCl
  argTag := r.argTag

/-- `StepSuppliers.es_eta` closed down to `EtaResiduum` — the `dr` leg is
    issued by `StepIH` through `Issues.eta_cl` inside
    `eta_caseStep_of_ports`, so it never appears here. -/
theorem es_eta_closed {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f A B : Expr Nat}
    (hf : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (r : EtaResiduum Aw tbl hf dl σ ρ) :
    CaseStep Aw tbl (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ) :=
  eta_caseStep_of_ports (Aw := Aw) (tbl := tbl) hf dl dr S σ ρ
    (etaPorts_of_residuum Aw tbl hf dl σ ρ r)

/-! ## §4 the `Below`-route theorems with `hA` discharged -/

/-- `es_eta_of_below_drop` with the `(c)` port `hA` produced by `etaDom_hA`.
    The remaining premises are the named `(d)` ports — `Below` (vacuous
    pending the ρ-respect repair), the `AppGot` read, `DispFor`, and the
    two verdict clauses. -/
theorem es_eta_below_drop_closed {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat}
    (h : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (Bl : Below Aw tbl (cvMeas Aw (CvP.eta E n Γ f A B h dl dr)))
    (a : AppGot Aw (dl.wt Aw) E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ (etaDom dl).u) = true)
    (hW : dl.eps σ ρ = lamErasure true (appClauseOf a σ (.drop :: ρ)))
    (hvar : a.ha.eps σ (.drop :: ρ) = .star) :
    ES tbl σ ρ (CvP.eta E n Γ f A B h dl dr) :=
  es_eta_of_below_drop Aw tbl h dl dr (etaDom_hA dl) Bl a σ ρ hρ hu hW hvar

/-- `es_eta_of_below_keep` with the `(c)` port `hA` produced by `etaDom_hA`. -/
theorem es_eta_below_keep_closed {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat}
    (h : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (Bl : Below Aw tbl (cvMeas Aw (CvP.eta E n Γ f A B h dl dr)))
    (a : AppGot Aw (dl.wt Aw) E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ (etaDom dl).u) = false)
    (hW : dl.eps σ ρ = lamErasure false (appClauseOf a σ (.keep :: ρ)))
    (hvar : a.ha.eps σ (.keep :: ρ) = .bvar 0)
    (hTW : TableWF tbl) :
    ES tbl σ ρ (CvP.eta E n Γ f A B h dl dr) :=
  es_eta_of_below_keep Aw tbl h dl dr (etaDom_hA dl) Bl a σ ρ hρ hu hW hvar hTW

/-! ## §5 non-vacuity: `EtaResiduum` is inhabited on the canonical redex -/

/-- The residual package is satisfiable: on the canonical η redex
    `etaLam hf hA hB` the reader's `AppGot` exists outright
    (`appOfNode` on the eta application), `eps` is the landed
    `etaLam_eps_*` computation, and both `CL`/`TagCoh` ports are
    reflexivity/`Iff.rfl` on defeq erasures — `appOfNode` under
    `envExt_refl` wraps the pieces in `ewk`, and `eps_ewk` is `rfl`.
    This witnesses `got`, `eps`, `funCl`, `argCl`, `argTag` all at once. -/
theorem etaResiduum_etaLam {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {u v : Level}
    (hf : TyP E n Γ f (.pi A B)) (hA : TyP E n Γ A (.sort u))
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (hTW : TableWF tbl) (σ : Level → Level) (ρ : List Disp) :
    Nonempty (EtaResiduum Aw tbl hf (etaLam hf hA hB) σ ρ) := by
  have hu0 : (etaDom (etaLam hf hA hB)).u = u := by
    show (lamDomain (etaLam hf hA hB) rfl).u = u
    rfl
  have h1 : (etaLam hf hA hB).wt Aw =
      1 + hA.wt Aw + (etaApp hf hA hB).wt Aw + hB.wt Aw := by
    rw [etaLam_expand]
    show 1 + hA.wt Aw +
      (tyCast rfl (instantiate_bvar_lift_id 0 B) (etaApp hf hA hB)).wt Aw +
      hB.wt Aw = _
    rw [TyP.wt_tyCast]
  have h2 : (etaApp hf hA hB).wt Aw =
      1 + (wkAtZero (A := A) hf).wt Aw + (etaArg hA).wt Aw + hB.wt Aw := by
    show 1 + (wkAtZero (A := A) hf).wt Aw + (etaArg hA).wt Aw +
      (tyCast (instantiate_bvar_lift_id 0 B).symm rfl hB).wt Aw = _
    rw [TyP.wt_tyCast]
  have hAt : ∀ y ∈ (TyP.app E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0)
      (lift 0 1 A) (lift 1 1 B) v (wkAtZero (A := A) hf) (etaArg hA)
      (tyCast (instantiate_bvar_lift_id 0 B).symm rfl hB)).atoms Aw,
      y < (etaLam hf hA hB).wt Aw := by
    intro y hy
    simp only [TyP.atoms] at hy
    obtain rfl := List.mem_singleton.mp hy
    show 1 + (wkAtZero (A := A) hf).wt Aw + (etaArg hA).wt Aw +
      (tyCast (instantiate_bvar_lift_id 0 B).symm rfl hB).wt Aw <
        (etaLam hf hA hB).wt Aw
    rw [TyP.wt_tyCast, h1, h2]
    omega
  refine ⟨{ tableWF := hTW
            got := appOfNode (envExt_refl E) Aw _ (wkAtZero (A := A) hf)
              (etaArg hA) (tyCast (instantiate_bvar_lift_id 0 B).symm rfl hB)
              hAt
            eps := ?_
            funCl := ConvMod.refl _
            argCl := ConvMod.refl _
            argTag := Iff.rfl }⟩
  rw [hu0]
  cases hu : levelIsZero (σ u) with
  | true =>
      rw [binderDisp_drop]
      show (etaLam hf hA hB).eps σ ρ =
        appClause ((wkAtZero (A := A) hf).eps σ (.drop :: ρ))
          ((etaArg hA).eps σ (.drop :: ρ))
      rw [etaLam_eps_drop hf hA hB σ ρ hu, eta_fun_drop,
        eta_arg_drop hA σ ρ hu, appClause_right_star]
  | false =>
      rw [binderDisp_keep]
      show (etaLam hf hA hB).eps σ ρ =
        lamClause (appClause ((wkAtZero (A := A) hf).eps σ (.keep :: ρ))
          ((etaArg hA).eps σ (.keep :: ρ)))
      by_cases hn : hf.eps σ ρ = .star
      · rw [etaLam_eps_keep_star hf hA hB σ ρ hu hn, eta_fun_keep,
          eta_arg_rel hA σ ρ hu, hn]
        rfl
      · rw [etaLam_eps_keep hf hA hB σ ρ hu hn, eta_fun_keep,
          eta_arg_rel hA σ ρ hu,
          appClause_app (lift_ne_star hn) (by rintro ⟨⟩)]
        rfl

end Rcic.Syn

#print axioms Rcic.Syn.etaDom
#print axioms Rcic.Syn.etaDom_hA
#print axioms Rcic.Syn.TyP.wt_tyCast
#print axioms Rcic.Syn.TyP.ap_tyCast
#print axioms Rcic.Syn.etaDom_wt_lt
#print axioms Rcic.Syn.etaDom_ap
#print axioms Rcic.Syn.eta_reads_of_meetEta
#print axioms Rcic.Syn.eta_eps_closed
#print axioms Rcic.Syn.EtaResiduum
#print axioms Rcic.Syn.etaPorts_of_residuum
#print axioms Rcic.Syn.es_eta_closed
#print axioms Rcic.Syn.es_eta_below_drop_closed
#print axioms Rcic.Syn.es_eta_below_keep_closed
#print axioms Rcic.Syn.etaResiduum_etaLam

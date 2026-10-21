import rcic.RcicSynStepFields4

/-!
# sortRow port discharge — `es_letE` / `es_eta` (sortrow-ports wave)

`research/rcic/sortrow/STEP_SUPPLIERS.md` §2–§3,
`BELOWC_FAILED_READERS_AND_LET_BODY.md` §3.2 / §8. `closure_claim = 0`.

This module discharges the named ports of the landed `StepSuppliers` fields
`es_letE` (`LetEPorts`, `RcicSynStepFields4.lean:899`) and `es_eta`
(`EtaPorts`, `RcicSynStepFields4.lean:1309`), delivering the exact field
statements `es_letE_field` and `es_eta_field` from the landed closers
`letE_caseStep_of_ports` (:923) and `eta_caseStep_of_ports` (:1335).

## `LetEPorts` classification

* `tableClosed : TableClosed tbl` — **(d) named ambient.** A fact about the
  arbitrary rewrite table, not about the query; no `Issues` row emits it.
  Same status as `TableWF` (`stepsuppliers-measure.md` §TableWF).
* `displayFits : DisplayFits Γ ρ` — **(d) named ambient.** Structural fit of
  the arbitrary incoming display `ρ` (`RcicSynBelowBoundary.lean:62`); ρ is a
  field input, never demanded.
* `leftSurfaceCl : CL tbl σ ρ dl (letLeftSurface hA hv hb dl)` — **(d).**
  `letE_issued_cl_is_occurrence` (:1055) is the kernel check that every `.cl`
  `Issues` emits from `.es (CvP.letE …)` is an `occ_cl` occurrence pair, and
  `letLeftSurface` (:779) is freshly assembled from `hA.dl`, `hv.dl`, `hb.dl`,
  `dl.reg` — it sits at no `P2Query.subAt` path of the query, so `StepIH` can
  never supply it.
* `valuePBLeft`, `valuePBRight` — **(a), discharged.** `Issues.occ_pb` issues
  `.pb hv.dl hA.dl` / `.pb hv.dr hA.dl` and `dmStep_pair_below` proves the
  `Before` edge (`letE_issued_val_pb_left` :541, `letE_issued_val_pb_right`
  :577). What remains named is only the *occurrence evidence* `pA`, `pvL`,
  `pvR`, `occA`, `occvL`, `occvR`: `hA.dl`/`hv.dl`/`hv.dr` occur in the
  derivation forest only when their nodes' roots expose them — for a
  transport-headed `hA` (`wk`/`linst`/`ewk`/`cctx`) `hA.dl` is a transported
  node, never a `subAt` descendant — so the paths/receipts are shape-dependent
  data, not derivable facts.
* `body : BodyAnswers …` — **(d) named.** A per-node structural demand over the
  whole of `hb.dr`'s tree (`RcicSynLetBridge.lean:192`: `BvarGate` gates,
  `esub`/`lsub` `PBit`s, scope certificates); no `Issues` row enumerates it.
* `rightSurfaceCl : CL tbl σ ρ (letRightSurface w hA hv hb.dr _ _) dr` —
  **(d) named**, same occurrence-kernel reason as `leftSurfaceCl`
  (`letRightSurface`, `RcicSynLetRight.lean:36`, is freshly assembled).
* The walk hypothesis `w : CvWalkHyp E` is ambient data the `body`/
  `rightSurfaceCl` statements need; it rides along as a named parameter.

## `EtaPorts` classification

`eta_caseStep_of_ports` already spends the only `StepIH`-derivable piece —
`CL tbl σ ρ hf dr` via `eta_issued_fun_cl` (:1084, `Issues.eta_cl`) — inside
the closer. Of the remaining ports:

* `tableWF : TableWF tbl` — **(d) named ambient** (OPEN named hypothesis per
  `stepsuppliers-measure.md` §TableWF; no `TableWF (tableOf E hE)` inhabitant).
* `u`, `hA : TyP E n Γ A (.sort u)` — **(d) named.** The η-expansion's domain
  typing lives inside `dl`'s lam node only when `dl` is `TyP.lam`-rooted;
  there is no landed lam-inversion, and `readApp`/`epsWalkApp` return `.no`
  on non-canonical endpoints.
* `got : AppGot Aw (dl.wt Aw) …` — **(d) named.** `appOfNode`
  (`RcicSynEtaBody.lean:58`) builds it from a literal `TyP.app` body node
  bounded by `dl.wt Aw`; for a generic `dl` the body node is not exposed.
* `eps` — **(d) named.** The "dl reads as the η-expansion" equation; no
  landed lemma produces it for a generic `dl`.
* `funCl` — **(d) named.** `got.hf` is `appOfNode`-`ewk`-transported, at no
  occurrence path; `eta_issued_cl_variants` (:1375) confines issued `.cl` from
  `.es (CvP.eta …)` to `occ_cl` pairs and the `eta_cl` (`hf` vs `dr`) edge.
* `argCl`, `argTag` — **(d) named.** `etaArg hA` is a fresh bvar surface; the
  same kernel check excludes the `CL`, and no `Issues` row emits a `TagCoh`
  request at all.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-- The exact `StepSuppliers.es_letE` field statement
    (`RcicSynStepSkeleton.lean:472`), delivered from the landed closer
    `letE_caseStep_of_ports` with `valuePBLeft`/`valuePBRight` discharged from
    `StepIH` (`letE_issued_val_pb_left`/`letE_issued_val_pb_right`). Remaining
    ports ride as named hypotheses with their exact statements:
    `tableClosed`, `displayFits`, `leftSurfaceCl`, the occurrence pack
    `pA pvL pvR` + `occA occvL occvR`, `body`, and `rightSurfaceCl`
    (plus the ambient `w : CvWalkHyp E` they mention). -/
theorem es_letE_field
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (w : CvWalkHyp E)
    (tableClosed : TableClosed tbl)
    (displayFits : DisplayFits Γ ρ)
    (leftSurfaceCl : CL tbl σ ρ dl (letLeftSurface hA hv hb dl))
    (pA pvL pvR : List Nat)
    (occA :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pA = some (.ty hA.dl))
    (occvL :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pvL = some (.ty hv.dl))
    (occvR :
      P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pvR = some (.ty hv.dr))
    (body :
      BodyAnswers w (iotaPack_of_cvWalkHyp w)
        (fun hext' h => derivedIotaExt hext' h) tbl σ (envExt_refl E) hb.dr
        (packNilL (rfl : List.get? (.letBinding A v :: Γ) 0 = some (.letBinding A v)) hA hv)
        (letDisp (hv.dl.eps σ ρ) :: ρ) [] .nil
        (letDisp (hv.dr.eps σ ρ) :: ρ))
    (rightSurfaceCl :
      CL tbl σ ρ (letRightSurface w hA hv hb.dr hb.dr.reg.1 hb.dr.reg.2) dr) :
    CaseStep Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ) := by
  intro hq ih
  have hpbL : PBit σ ρ hv.dl hA.dl :=
    letE_issued_val_pb_left Aw tbl hA hv hb dl dr S σ ρ pvL pA occvL occA hq ih
  have hpbR : PBit σ ρ hv.dr hA.dl :=
    letE_issued_val_pb_right Aw tbl hA hv hb dl dr S σ ρ pvR pA occvR occA hq ih
  exact letE_caseStep_of_ports Aw tbl hA hv hb dl dr S σ ρ w
    { tableClosed := tableClosed
      displayFits := displayFits
      leftSurfaceCl := leftSurfaceCl
      valuePBLeft := hpbL
      valuePBRight := hpbR
      body := body
      rightSurfaceCl := rightSurfaceCl }
    hq ih

/-- The exact `StepSuppliers.es_eta` field statement
    (`RcicSynStepSkeleton.lean:482`), delivered from the landed closer
    `eta_caseStep_of_ports`. `StepIH`'s one contribution — `CL tbl σ ρ hf dr`
    via `eta_issued_fun_cl` — is already spent inside the closer; every
    `EtaPorts` field remains a named hypothesis with its exact statement
    (`tableWF`, `u`/`hA`, `got`, `eps`, `funCl`, `argCl`, `argTag`). -/
theorem es_eta_field
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat}
    (hf : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (tableWF : TableWF tbl)
    (u : Level)
    (hA : TyP E n Γ A (.sort u))
    (got : AppGot Aw (dl.wt Aw) E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0))
    (eps :
      dl.eps σ ρ =
        lamErasure (levelIsZero (σ u))
          (appClauseOf got σ (binderDisp (levelIsZero (σ u)) :: ρ)))
    (funCl :
      CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) got.hf (wkAtZero (A := A) hf))
    (argCl :
      CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) got.ha (etaArg hA))
    (argTag :
      TagCoh σ (binderDisp (levelIsZero (σ u)) :: ρ)
        σ (binderDisp (levelIsZero (σ u)) :: ρ) got.ha (etaArg hA)) :
    CaseStep Aw tbl (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ) :=
  eta_caseStep_of_ports Aw tbl hf dl dr S σ ρ
    { tableWF := tableWF
      u := u
      hA := hA
      got := got
      eps := eps
      funCl := funCl
      argCl := argCl
      argTag := argTag }

#print axioms Rcic.Syn.es_letE_field
#print axioms Rcic.Syn.es_eta_field

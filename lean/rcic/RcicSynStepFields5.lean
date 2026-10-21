import rcic.RcicSynStepFields2
import rcic.RcicSynDomainSource
import rcic.RcicSynClauseAlg
import rcic.RcicERPiSlotConv
import rcic.RcicSynSharedRank
import rcic.RcicSynTagCoh

/-!
# `es_app` / `es_pi` field assemblies (STEP_SUPPLIERS, `RcicSynStepFields5`)

The `CaseStep` halves of the `es_app`/`es_pi` `StepSuppliers` fields
(`RcicSynStepSkeleton.lean`), now that `RcicSynDomainSource` (#7475) supplies
the total decoders `appSource`/`piDomain` with subject equations, `wt` bounds
and `AssumpPref` transport.

## Port classification (per `BELOWC_FAILED_READERS_AND_LET_BODY` §3.3/§3.5/§4.1)

* `es_app`. `ES[h1]`, `ES[h2]` are **discharged** from `StepIH` by the landed
  `es_app_ih_fun`/`es_app_ih_arg` (`Issues.app_es1`/`app_es2` +
  `rule_sub_before`). `CL[h1.dr, R.hf]` and `CL[h2.dr, R.ha]` — same-subject
  pairs after `appSource`'s `feq`/`aeq` — are **issuable** by `Issues.occ_cl`
  once the two `subAt` occurrence paths are supplied (`AppPorts.pH1`, `pH2`,
  `pF`, `pA`); the `Before` bound is `DNode.subAt_wt_lt` on the receipts plus
  `TyP.wt_castS` for the subject cast. The remaining obligations stay named
  ports: `CL[dl, appLeftSurface]` (a fresh surface sits at no `subAt` path),
  the four `PB[·, ·.reg.2]` (a `reg` output is never a `dchildren` child, so
  `occ_pb` cannot name it), `TagCoh[hᵢ.dr, R.·]` (no `tagCoh` query tag exists),
  and `drClause` — the §4.1 `AppClauseNeed(dr)` worker equation, whose proof
  needs the site `PB`s the route collects.
* `es_pi`. `ES[hA]`, `ES[hB]` are **discharged** (`pi_esA`/`pi_esB`,
  `binder_body_before`). For `HR := dr.piDomain rfl`, the domain
  `CL[hA.dr, he' ▸ HR.H]` and the sort-gate `BIT[hA.dr, hT ▸ he' ▸ HR.H]` are
  **issuable** by `Issues.occ_cl`/`Issues.occ_bitCoh` once the `subAt` receipts
  `PiPorts.occHA`/`occHR` are supplied (`Before` is `DNode.subAt_wt_lt` +
  `dmStep_pair_below`, same frame); the issued bit re-gates the `piSlot`
  binder from `σ u` to `σ HR.u`. The π surfaces are `piLeftSurface` and
  `piRightSurface hA hB dr` — the latter rebuilt at `HR.H`/`HR.u`. The
  residual is `rightCl`: the `CL` of `dr` against that surface — spec §3.5's
  "deeper body route", i.e. the codomain comparison `piDomain` does not
  supply. `convMod_piSlot` (real `TableClosed`) moves the issued body `ES`
  across the pad before the re-gate.

`closure_claim` stays 0: the ports are the residue, exposed not discharged.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §0 casts through `eps`/`DNode` -/

/-- `eps` is index-insensitive: subject casts preserve it. -/
theorem TyP.eps_castS {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T e e' : Expr Nat} (h : e = e') (D : TyP E n Γ e T) (σ : Level → Level)
    (ρ : List Disp) : (h ▸ D).eps σ ρ = D.eps σ ρ := by
  cases h
  rfl

/-- `eps` is index-insensitive: type casts preserve it. -/
theorem TyP.eps_castT {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T T' : Expr Nat} (h : T = T') (D : TyP E n Γ e T) (σ : Level → Level)
    (ρ : List Disp) : (h ▸ D).eps σ ρ = D.eps σ ρ := by
  cases h
  rfl

/-- A `subAt` receipt for a subject-cast derivation: `▸` leaves the forest
    node itself unchanged. -/
theorem dnode_ty_castS {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T e e' : Expr Nat} (h : e = e') (D : TyP E n Γ e T) :
    DNode.ty (h ▸ D) = DNode.ty D := by
  cases h
  rfl

/-- A `subAt` receipt for a type-cast derivation: `▸` leaves the forest
    node itself unchanged. -/
theorem dnode_ty_castT {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T T' : Expr Nat} (h : T = T') (D : TyP E n Γ e T) :
    DNode.ty (h ▸ D) = DNode.ty D := by
  cases h
  rfl

/-! ## §1 the canonical `app`/`pi` surfaces -/

/-- The canonical left application surface: the `TyP.app` node rebuilt from
    the `CvP.app`'s own left endpoints `h1.dl`, `h2.dl` and `dl`'s regularity
    — the `leftSurface` of §3.3. -/
noncomputable def appLeftSurface {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B)) :
    TyP E n Γ (.app f a) (instantiate0 a B) :=
  TyP.app E n Γ f a A B dl.reg.1 h1.dl h2.dl dl.reg.2

/-- `appLeftSurface` is strictly lighter than the enclosing `CvP.app` node:
    `wt_dl_lt` twice, `wt_reg_le`, `wt_pos dr`. -/
theorem appLeftSurface_wt_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B)) :
    (appLeftSurface h1 h2 dl).wt Aw <
      (CvP.app E n Γ f g a b A B h1 h2 dl dr).wt Aw := by
  have hf := CvP.wt_dl_lt Aw h1
  have ha := CvP.wt_dl_lt Aw h2
  have hreg := TyP.wt_reg_le Aw dl
  have hdr := TyP.wt_pos Aw dr
  simp only [appLeftSurface, TyP.wt, CvP.wt]
  omega

/-- `appLeftSurface` preserves `AssumpPref` when the `CvP.app`'s own
    components satisfy it. -/
theorem appLeftSurface_ap {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (hh1 : h1.AssumpPref) (hh2 : h2.AssumpPref) (hdl : dl.AssumpPref) :
    (appLeftSurface h1 h2 dl).AssumpPref :=
  ⟨assumpPref_dl hh1, assumpPref_dl hh2, assumpPref_reg hdl⟩

/-- The surface erases to the exact `appClause` of the two endpoint
    erasures — `eps_app_appClause` on the reconstructed node. -/
theorem appLeftSurface_eps {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B)) (σ : Level → Level)
    (ρ : List Disp) :
    (appLeftSurface h1 h2 dl).eps σ ρ =
      appClause (h1.dl.eps σ ρ) (h2.dl.eps σ ρ) :=
  eps_app_appClause h1.dl h2.dl dl.reg.2 σ ρ

/-- The canonical left Π surface: the `TyP.pi` node rebuilt from the
    `CvP.pi`'s own left endpoints — the bounded left surface of §3.5. -/
noncomputable def piLeftSurface {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v)) :
    TyP E n Γ (.pi A B) (.sort (.imax u v)) :=
  TyP.pi E n Γ A u B v hA.dl hB.dl

/-- `piLeftSurface` is strictly lighter than the enclosing `CvP.pi` node. -/
theorem piLeftSurface_wt_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v))) :
    (piLeftSurface hA hB).wt Aw <
      (CvP.pi E n Γ A A' B B' u v hA hB dl dr).wt Aw := by
  have hAw := CvP.wt_dl_lt Aw hA
  have hBw := CvP.wt_dl_lt Aw hB
  have hdl := TyP.wt_pos Aw dl
  have hdr := TyP.wt_pos Aw dr
  simp only [piLeftSurface, TyP.wt, CvP.wt]
  omega

/-- `piLeftSurface` preserves `AssumpPref` when the `CvP.pi`'s own components
    satisfy it. -/
theorem piLeftSurface_ap {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (hhA : hA.AssumpPref) (hhB : hB.AssumpPref) :
    (piLeftSurface hA hB).AssumpPref :=
  ⟨assumpPref_dl hhA, assumpPref_dl hhB⟩

/-- The canonical right Π surface against a decoded domain source: the
    `TyP.pi` node rebuilt from `hT ▸ he' ▸ HR.H` — the recorded domain at its
    own sort `HR.u` — and the `cctx hB.dr hA` codomain view (§3.5). `HR` is a
    binder so the `he'`/`hT` casts land on one fixed instance. -/
noncomputable def piRightSurfaceSrc {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (HR : DomainSource E n Γ A') :
    TyP E n Γ (.pi A' B') (.sort (.imax HR.u v)) :=
  TyP.pi E n Γ A' HR.u B' v (tyCast HR.he' HR.hT HR.H)
    (TyP.cctx E n Γ B' (.sort v) A A' u hB.dr hA)

/-- The canonical right Π surface for `dr`'s recorded domain
    (`HR := dr.piDomain rfl`): the domain `CL`/`BIT` are issued against the
    `occHA`/`occHR` receipts; the codomain comparison is the residual
    `rightCl` port. -/
noncomputable def piRightSurface {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v))) :
    TyP E n Γ (.pi A' B') (.sort (.imax (TyP.piDomain dr rfl).u v)) :=
  piRightSurfaceSrc hA hB (dr.piDomain rfl)

/-- `piRightSurfaceSrc` preserves `AssumpPref` when the `CvP.pi`'s own
    components and the source domain derivation satisfy it. -/
theorem piRightSurfaceSrc_ap {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (HR : DomainSource E n Γ A')
    (hhA : hA.AssumpPref) (hhB : hB.AssumpPref) (hHR : HR.H.AssumpPref) :
    (piRightSurfaceSrc hA hB HR).AssumpPref := by
  show (tyCast HR.he' HR.hT HR.H).AssumpPref ∧
      (TyP.cctx E n Γ B' (.sort v) A A' u hB.dr hA).AssumpPref
  exact ⟨by rw [tyCast, TyP.ap_castS, TyP.ap_castT]; exact hHR,
    assumpPref_dr hhB, hhA⟩

/-- `piRightSurface` preserves `AssumpPref` when the `CvP.pi`'s own
    components and `dr` satisfy it. -/
theorem piRightSurface_ap {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (hhA : hA.AssumpPref) (hhB : hB.AssumpPref) (hdr : dr.AssumpPref) :
    (piRightSurface hA hB dr).AssumpPref :=
  piRightSurfaceSrc_ap hA hB (dr.piDomain rfl) hhA hhB
    (TyP.piDomain_ap dr rfl hdr)

/-- The left π surface erases to `.pi` of the endpoint erasures — the
    codomain is the `piSlot`-padded body erasure under the binder
    disposition. -/
theorem piLeftSurface_eps {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (σ : Level → Level) (ρ : List Disp) :
    (piLeftSurface hA hB).eps σ ρ =
      .pi (hA.dl.eps σ ρ)
        (piSlot (levelIsZero (σ u))
          (hB.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))) := by
  cases hb : levelIsZero (σ u) <;>
    simp only [piLeftSurface, TyP.eps, hb, binderDisp, piSlot_true,
      piSlot_false]

/-- The right π surface erases to `.pi` of the decoded domain erasure and the
    `piSlot`-padded `hB.dr` codomain erasure under the decoded binder
    disposition — the §3.5 residual shape (domain/gate already issued, the
    codomain is the "deeper body route"). Generalized over the `DomainSource`
    binder so the `he'`/`hT` casts rewrite through `eps_castS`/`eps_castT`. -/
theorem piRightSurfaceSrc_eps {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (HR : DomainSource E n Γ A')
    (σ : Level → Level) (ρ : List Disp) :
    (piRightSurfaceSrc hA hB HR).eps σ ρ =
      .pi (HR.H.eps σ ρ)
        (piSlot (levelIsZero (σ HR.u))
          (hB.dr.eps σ (binderDisp (levelIsZero (σ HR.u)) :: ρ))) := by
  cases hb : levelIsZero (σ HR.u) <;>
    simp only [piRightSurfaceSrc, TyP.eps, hb, binderDisp, piSlot_true,
      piSlot_false, tyCast, TyP.eps_castT, TyP.eps_castS]

theorem piRightSurface_eps {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (σ : Level → Level) (ρ : List Disp) :
    (piRightSurface hA hB dr).eps σ ρ =
      .pi ((TyP.piDomain dr rfl).H.eps σ ρ)
        (piSlot (levelIsZero (σ (TyP.piDomain dr rfl).u))
          (hB.dr.eps σ
            (binderDisp (levelIsZero (σ (TyP.piDomain dr rfl).u)) :: ρ))) :=
  piRightSurfaceSrc_eps hA hB (dr.piDomain rfl) σ ρ

/-! ## §2 `appClause` congruence -/

/-- `appClause` is a `ConvMod` congruence when the two sides agree on `★`:
    the deleted-function and deleted-argument branches need the star status
    iff to pick the same branch on both sides. -/
theorem convMod_appClause {tbl : List CRule} {ef eg ea eb : ETm}
    (hf : ConvMod (EStep tbl) LvlEq ef eg)
    (ha : ConvMod (EStep tbl) LvlEq ea eb)
    (hsf : (ef = .star) ↔ (eg = .star))
    (hsa : (ea = .star) ↔ (eb = .star)) :
    ConvMod (EStep tbl) LvlEq (appClause ef ea) (appClause eg eb) := by
  by_cases hfe : ef = .star
  · subst hfe
    have hge : eg = .star := hsf.mp rfl
    subst hge
    exact .refl _
  · have hge : eg ≠ .star := fun h => hfe (hsf.mpr h)
    by_cases hae : ea = .star
    · subst hae
      have hbe : eb = .star := hsa.mp rfl
      subst hbe
      rw [appClause_right_star, appClause_right_star]
      exact hf
    · have hbe : eb ≠ .star := fun h => hae (hsa.mpr h)
      rw [appClause_app hfe hae, appClause_app hge hbe]
      exact convMod_app hf ha

/-! ## §3 `es_app` -/

/-- Residual ports for `StepSuppliers.es_app` (§3.3/§4.1). `ES[h1]`, `ES[h2]`
    are omitted: `StepIH` supplies them (`es_app_ih_fun`, `es_app_ih_arg`).
    `CL[h1.dr, R.hf]`, `CL[h2.dr, R.ha]` are also omitted: `Issues.occ_cl`
    issues them in the issuer's own frame once the occurrence paths are
    supplied (`pH1`, `pH2`, `pF`, `pA`). What remains is exactly the spec's
    port list: the left-surface `CL`, the four `PB`s (a `reg` output has no
    `subAt` path), the two `TagCoh`s (no query tag exists), and `drClause` —
    the §4.1 `AppClauseNeed(dr)` worker equation. -/
structure AppPorts (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) : Prop where
  /-- `CL[dl, leftSurface]` — the fresh `appLeftSurface` sits at no `subAt`
      path of the payload, so `occ_cl` cannot serve it. -/
  leftCl : CL tbl σ ρ dl (appLeftSurface h1 h2 dl)
  /-- occurrence path receipt of `h1.dr` inside the `.cv h1` payload
      subtree. -/
  occH1 : ∃ p : List Nat,
    P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
      0 p = some (.ty h1.dr)
  /-- occurrence path receipt of `h2.dr` inside the `.cv h2` payload
      subtree. -/
  occH2 : ∃ p : List Nat,
    P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
      0 p = some (.ty h2.dr)
  /-- occurrence path receipt of `(appSource dr rfl).hf` inside the `.ty dr`
      payload subtree — `appSource` computes no path; the port carries the
      receipt a path-instrumented decoder would emit. -/
  occF : ∃ p : List Nat,
    P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
      0 p = some (.ty (appSource dr rfl).hf)
  /-- occurrence path receipt of `(appSource dr rfl).ha` inside `.ty dr`. -/
  occA : ∃ p : List Nat,
    P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
      0 p = some (.ty (appSource dr rfl).ha)
  /-- `PB[h1.dl, h1.dl.reg.2]` — `h1.dl`'s star status is its `.pi` type's
      proof bit. -/
  pbFunL : PBit σ ρ h1.dl h1.dl.reg.2
  /-- `PB[h1.dr, h1.dl.reg.2]` — the same sort typing carries `h1.dr`'s bit,
      giving `h1.dl.eps = ★ ↔ h1.dr.eps = ★`. -/
  pbFunR : PBit σ ρ h1.dr h1.dl.reg.2
  /-- `PB[h2.dl, h2.dl.reg.2]` — the argument's left endpoint bit. -/
  pbArgL : PBit σ ρ h2.dl h2.dl.reg.2
  /-- `PB[h2.dr, h2.dl.reg.2]` — the argument's right endpoint bit. -/
  pbArgR : PBit σ ρ h2.dr h2.dl.reg.2
  /-- `Tag[h1.dr, R.hf]` — same subject `g` after the decoder's `feq`. -/
  funTag : TagCoh σ ρ σ ρ h1.dr ((appSource dr rfl).feq ▸ (appSource dr rfl).hf)
  /-- `Tag[h2.dr, R.ha]` — same subject `b` after the decoder's `aeq`. -/
  argTag : TagCoh σ ρ σ ρ h2.dr ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha)
  /-- `AppClauseNeed(dr)` (§4.1): `dr`'s erasure is the `appClause` of its
      decoded function/argument sources. -/
  drClause : dr.eps σ ρ =
    appClause ((appSource dr rfl).hf.eps σ ρ) ((appSource dr rfl).ha.eps σ ρ)

/-- `CL[D₁, D₂]` for two `subAt`-reachable derivations of an `es c` query at
    a non-transport conversion node: `Issues.occ_cl` + `DNode.subAt_wt_lt` +
    `dmStep_pair_below`. The paths and the `AssumpPref`s are the port; the
    `Before` is discharged. Generic in `c` — `es_app`/`es_pi` share it. -/
theorem es_issued_occ_cl (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (c : CvP E n Γ a b T) (hc : c.isTransport = false)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (p₁ p₂ : List Nat)
    (hocc₁ : P2Query.subAt (.es c S σ ρ) 0 p₁ = some (.ty D₁))
    (hocc₂ : P2Query.subAt (.es c S σ ρ) 0 p₂ = some (.ty D₂))
    (hap₁ : D₁.AssumpPref) (hap₂ : D₂.AssumpPref)
    (hq : Demand (.es c S σ ρ)) (ih : StepIH Aw tbl (.es c S σ ρ)) :
    CL tbl σ ρ D₁ D₂ := by
  have hp₁ : p₁ ≠ [] := by
    rintro rfl
    rw [P2Query.subAt] at hocc₁
    simp only [P2Query.payload, List.getElem?_cons_zero, Option.some_bind,
      DNode.subAt] at hocc₁
    exact DNode.noConfusion (Option.some.inj hocc₁)
  have hp₂ : p₂ ≠ [] := by
    rintro rfl
    rw [P2Query.subAt] at hocc₂
    simp only [P2Query.payload, List.getElem?_cons_zero, Option.some_bind,
      DNode.subAt] at hocc₂
    exact DNode.noConfusion (Option.some.inj hocc₂)
  have hw₁ : D₁.wt Aw < c.wt Aw :=
    DNode.subAt_wt_lt Aw p₁ hp₁ _ _ hocc₁
  have hw₂ : D₂.wt Aw < c.wt Aw :=
    DNode.subAt_wt_lt Aw p₂ hp₂ _ _ hocc₂
  exact ih_issue Aw tbl hq ih (.cl D₁ D₂ S σ ρ)
    (Issues.occ_cl hocc₁ hocc₂ hap₁ hap₂)
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw c hc D₁ D₂ hw₁ hw₂))))

/-- `BIT[D₁, D₂]` for two `subAt`-reachable sort-typings of one subject of an
    `es c` query: `Issues.occ_bitCoh` + the same `Before` discharge. Answers
    `levelIsZero (σ u) = levelIsZero (σ v)`. -/
theorem es_issued_occ_bitCoh (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (c : CvP E n Γ a b T) (hc : c.isTransport = false)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    {T' : Expr Nat} {u₁ u₂ : Level}
    (D₁ : TyP E n Γ T' (.sort u₁)) (D₂ : TyP E n Γ T' (.sort u₂))
    (p₁ p₂ : List Nat)
    (hocc₁ : P2Query.subAt (.es c S σ ρ) 0 p₁ = some (.ty D₁))
    (hocc₂ : P2Query.subAt (.es c S σ ρ) 0 p₂ = some (.ty D₂))
    (hap₁ : D₁.AssumpPref) (hap₂ : D₂.AssumpPref)
    (hq : Demand (.es c S σ ρ)) (ih : StepIH Aw tbl (.es c S σ ρ)) :
    BitCoh σ D₁ D₂ := by
  have hp₁ : p₁ ≠ [] := by
    rintro rfl
    rw [P2Query.subAt] at hocc₁
    simp only [P2Query.payload, List.getElem?_cons_zero, Option.some_bind,
      DNode.subAt] at hocc₁
    exact DNode.noConfusion (Option.some.inj hocc₁)
  have hp₂ : p₂ ≠ [] := by
    rintro rfl
    rw [P2Query.subAt] at hocc₂
    simp only [P2Query.payload, List.getElem?_cons_zero, Option.some_bind,
      DNode.subAt] at hocc₂
    exact DNode.noConfusion (Option.some.inj hocc₂)
  have hw₁ : D₁.wt Aw < c.wt Aw :=
    DNode.subAt_wt_lt Aw p₁ hp₁ _ _ hocc₁
  have hw₂ : D₂.wt Aw < c.wt Aw :=
    DNode.subAt_wt_lt Aw p₂ hp₂ _ _ hocc₂
  exact ih_issue Aw tbl hq ih (.bitCoh D₁ D₂ S σ ρ)
    (Issues.occ_bitCoh hocc₁ hocc₂ hap₁ hap₂)
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw c hc D₁ D₂ hw₁ hw₂))))

/-- `es_app` under `AppPorts`: the issued `ES[h1]`/`ES[h2]` halves, the
    `occ_cl`-issued decoder `CL`s, the left-surface `CL`, the `appClause`
    congruence, and `drClause` compose to the `CvP.app` `CaseStep`. The
    `StepSuppliers.es_app` field statement with the residue as the explicit
    `ports` hypothesis. -/
theorem es_app_field (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : AppPorts Aw tbl h1 h2 dl dr S σ ρ) :
    CaseStep Aw tbl (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) := by
  intro hq ih
  obtain ⟨hap1, hap2, hapdl, hapdr⟩ := hq.ap
  obtain ⟨pH1, occH1⟩ := ports.occH1
  obtain ⟨pH2, occH2⟩ := ports.occH2
  obtain ⟨pF, occF⟩ := ports.occF
  obtain ⟨pA, occA⟩ := ports.occA
  -- the two `occ_cl`-issuable decoder CLs:
  -- `CL[h1.dr, feq ▸ R.hf]`, `CL[h2.dr, aeq ▸ R.ha]` for `R = appSource dr rfl`
  have hapF : ((appSource dr rfl).feq ▸ (appSource dr rfl).hf).AssumpPref :=
    TyP.ap_castS (appSource dr rfl).feq (appSource dr rfl).hf ▸
      (appSource_ap dr rfl hapdr).1
  have occF' :
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 pF =
        some (.ty ((appSource dr rfl).feq ▸ (appSource dr rfl).hf)) := by
    rw [dnode_ty_castS (appSource dr rfl).feq (appSource dr rfl).hf]
    exact occF
  have hclF : CL tbl σ ρ h1.dr
      ((appSource dr rfl).feq ▸ (appSource dr rfl).hf) :=
    es_issued_occ_cl Aw tbl (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
      h1.dr _ pH1 pF occH1 occF' (assumpPref_dr hap1) hapF hq ih
  have hapA : ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha).AssumpPref :=
    TyP.ap_castS (appSource dr rfl).aeq (appSource dr rfl).ha ▸
      (appSource_ap dr rfl hapdr).2
  have occA' :
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 pA =
        some (.ty ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha)) := by
    rw [dnode_ty_castS (appSource dr rfl).aeq (appSource dr rfl).ha]
    exact occA
  have hclA : CL tbl σ ρ h2.dr
      ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha) :=
    es_issued_occ_cl Aw tbl (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
      h2.dr _ pH2 pA occH2 occA' (assumpPref_dr hap2) hapA hq ih
  -- the two issued ES halves (a)
  have hf_es : ConvMod (EStep tbl) LvlEq (h1.dl.eps σ ρ) (h1.dr.eps σ ρ) :=
    es_app_ih_fun Aw tbl h1 h2 dl dr S σ ρ hq ih
  have ha_es : ConvMod (EStep tbl) LvlEq (h2.dl.eps σ ρ) (h2.dr.eps σ ρ) :=
    es_app_ih_arg Aw tbl h1 h2 dl dr S σ ρ hq ih
  -- star-status chains: PB pairs give endpoint agreement, Tag ports bridge
  -- to the decoder's operands
  have hsf : (h1.dl.eps σ ρ = .star) ↔ (h1.dr.eps σ ρ = .star) :=
    ports.pbFunL.trans ports.pbFunR.symm
  have hsa : (h2.dl.eps σ ρ = .star) ↔ (h2.dr.eps σ ρ = .star) :=
    ports.pbArgL.trans ports.pbArgR.symm
  have hsf' : (h1.dr.eps σ ρ = .star) ↔
      (((appSource dr rfl).feq ▸ (appSource dr rfl).hf).eps σ ρ = .star) :=
    ports.funTag
  have hsa' : (h2.dr.eps σ ρ = .star) ↔
      (((appSource dr rfl).aeq ▸ (appSource dr rfl).ha).eps σ ρ = .star) :=
    ports.argTag
  -- the clause chain
  have hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
      (appClause (h1.dl.eps σ ρ) (h2.dl.eps σ ρ)) :=
    appLeftSurface_eps h1 h2 dl σ ρ ▸ ports.leftCl
  have hMid : ConvMod (EStep tbl) LvlEq
      (appClause (h1.dl.eps σ ρ) (h2.dl.eps σ ρ))
      (appClause (h1.dr.eps σ ρ) (h2.dr.eps σ ρ)) :=
    convMod_appClause hf_es ha_es hsf hsa
  have hMidR : ConvMod (EStep tbl) LvlEq
      (appClause (h1.dr.eps σ ρ) (h2.dr.eps σ ρ))
      (appClause (((appSource dr rfl).feq ▸ (appSource dr rfl).hf).eps σ ρ)
        (((appSource dr rfl).aeq ▸ (appSource dr rfl).ha).eps σ ρ)) :=
    convMod_appClause hclF hclA hsf' hsa'
  have hR : ConvMod (EStep tbl) LvlEq
      (appClause (((appSource dr rfl).feq ▸ (appSource dr rfl).hf).eps σ ρ)
        (((appSource dr rfl).aeq ▸ (appSource dr rfl).ha).eps σ ρ))
      (dr.eps σ ρ) := by
    rw [TyP.eps_castS (appSource dr rfl).feq (appSource dr rfl).hf,
      TyP.eps_castS (appSource dr rfl).aeq (appSource dr rfl).ha,
      ← ports.drClause]
    exact .refl _
  exact hL.trans (hMid.trans (hMidR.trans hR))

/-! ## §4 `es_pi` -/

/-- Residual ports for `StepSuppliers.es_pi` (§3.5). `ES[hA]`, `ES[hB]` are
    omitted: `StepIH` supplies them (`es_pi_ih_dom`, `es_pi_ih_body`), and the
    domain `CL[hA.dr, he' ▸ HR.H]` / `BIT[hA.dr, hT ▸ he' ▸ HR.H]` for
    `HR := dr.piDomain rfl` are issued from `StepIH` against the `occHA`/`occHR`
    `subAt` receipts — the sort-gate bit rewrites the `piSlot` binder. The
    listed residue is `leftCl` (the bounded left surface, fresh — no `occ_cl`
    reaches it) and `rightCl`: the `CL` of `dr` against its canonical right
    surface `piRightSurface hA hB dr` — the decoded-domain π compared at
    `dr`'s own recorded sort — whose residual is the deeper codomain route
    `piDomain` does not supply. `tableClosed` is the real `TableClosed` the
    `piSlot` pad needs. -/
structure PiPorts (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) : Prop where
  tableClosed : TableClosed tbl
  /-- `CL[dl, leftSurface]` — the fresh `piLeftSurface` sits at no `subAt`
      path. -/
  leftCl : CL tbl σ ρ dl (piLeftSurface hA hB)
  /-- `subAt` receipt for `hA.dr` (the π domain conversion's right
      derivation). -/
  occHA : ∃ p : List Nat,
    P2Query.subAt (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ) 0 p =
      some (.ty hA.dr)
  /-- `subAt` receipt for `(dr.piDomain rfl).H` (`dr`'s recorded domain
      source, before its `he'`/`hT` casts). -/
  occHR : ∃ p : List Nat,
    P2Query.subAt (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ) 0 p =
      some (.ty (dr.piDomain rfl).H)
  /-- `CL[piRightSurface hA hB dr, dr]` — the decoded right comparison; the
      §3.5 residual is the deeper codomain route `piDomain` does not supply
      (the domain conversion and sort-gate are issued, not ported). -/
  rightCl : CL tbl σ ρ (piRightSurface hA hB dr) dr

/-- `es_pi` under `PiPorts`: the issued `ES[hA]`/`ES[hB]` halves, the
    `occ_cl`/`occ_bitCoh`-issued domain conversion and sort-gate against
    `dr.piDomain rfl`, the `piSlot`-padded body (re-gated by the issued bit),
    and the two surface `CL`s compose to the `CvP.pi` `CaseStep`. The
    `StepSuppliers.es_pi` field statement with the residue as the explicit
    `ports` hypothesis. -/
theorem es_pi_field (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : PiPorts Aw tbl hA hB dl dr S σ ρ) :
    CaseStep Aw tbl (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ) := by
  intro hq ih
  obtain ⟨hapA, _hapB, _hapdl, hapdr⟩ := hq.ap
  obtain ⟨pA, occHA⟩ := ports.occHA
  obtain ⟨pH, occHR⟩ := ports.occHR
  -- issued domain halves (a)+(b): `CL[hA.dr, he' ▸ H]` and
  -- `BIT[hA.dr, hT ▸ he' ▸ H]` for `H = (dr.piDomain rfl).H`
  have hapH : ((dr.piDomain rfl).he' ▸ (dr.piDomain rfl).H).AssumpPref :=
    TyP.ap_castS (dr.piDomain rfl).he' (dr.piDomain rfl).H ▸
      TyP.piDomain_ap dr rfl hapdr
  have occHR_cl :
      P2Query.subAt (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ) 0 pH =
        some (.ty ((dr.piDomain rfl).he' ▸ (dr.piDomain rfl).H)) := by
    rw [dnode_ty_castS (dr.piDomain rfl).he' (dr.piDomain rfl).H]
    exact occHR
  have hDom : CL tbl σ ρ hA.dr
      ((dr.piDomain rfl).he' ▸ (dr.piDomain rfl).H) :=
    es_issued_occ_cl Aw tbl (CvP.pi E n Γ A A' B B' u v hA hB dl dr) rfl S σ ρ
      hA.dr _ pA pH occHA occHR_cl (assumpPref_dr hapA) hapH hq ih
  have hapH' :
      ((dr.piDomain rfl).hT ▸
        ((dr.piDomain rfl).he' ▸ (dr.piDomain rfl).H)).AssumpPref :=
    TyP.ap_castT (dr.piDomain rfl).hT ((dr.piDomain rfl).he' ▸
      (dr.piDomain rfl).H) ▸ hapH
  have occHR_bit :
      P2Query.subAt (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ) 0 pH =
        some (.ty ((dr.piDomain rfl).hT ▸
          ((dr.piDomain rfl).he' ▸ (dr.piDomain rfl).H))) := by
    simp only [dnode_ty_castT, dnode_ty_castS]
    exact occHR
  have hbit : BitCoh σ hA.dr ((dr.piDomain rfl).hT ▸
      ((dr.piDomain rfl).he' ▸ (dr.piDomain rfl).H)) :=
    es_issued_occ_bitCoh Aw tbl (CvP.pi E n Γ A A' B B' u v hA hB dl dr) rfl
      S σ ρ hA.dr _ pA pH occHA occHR_bit (assumpPref_dr hapA) hapH' hq ih
  have hbit' :
      levelIsZero (σ u) = levelIsZero (σ (dr.piDomain rfl).u) := hbit
  -- the issued ES halves (a); the domain leg continues through the issued
  -- `CL` to the decoded domain's erasure
  have hAd : ConvMod (EStep tbl) LvlEq (hA.dl.eps σ ρ)
      ((dr.piDomain rfl).H.eps σ ρ) :=
    (es_pi_ih_dom Aw tbl hA hB dl dr S σ ρ hq ih).trans
      (TyP.eps_castS (dr.piDomain rfl).he' (dr.piDomain rfl).H σ ρ ▸ hDom)
  have hB_es : ConvMod (EStep tbl) LvlEq
      (hB.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))
      (hB.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ)) :=
    es_pi_ih_body Aw tbl hA hB dl dr S σ ρ hq ih
  have hBd_slot : ConvMod (EStep tbl) LvlEq
      (piSlot (levelIsZero (σ u))
        (hB.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ)))
      (piSlot (levelIsZero (σ u))
        (hB.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))) :=
    convMod_piSlot ports.tableClosed _ hB_es
  -- the issued sort-gate bit re-gates the body pad at the decoded sort
  have hCod : ConvMod (EStep tbl) LvlEq
      (piSlot (levelIsZero (σ u))
        (hB.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ)))
      (piSlot (levelIsZero (σ (dr.piDomain rfl).u))
        (hB.dr.eps σ
          (binderDisp (levelIsZero (σ (dr.piDomain rfl).u)) :: ρ))) := by
    rw [hbit']
    exact .refl _
  have hBd := hBd_slot.trans hCod
  have hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
      (.pi (hA.dl.eps σ ρ)
        (piSlot (levelIsZero (σ u))
          (hB.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ)))) :=
    piLeftSurface_eps hA hB σ ρ ▸ ports.leftCl
  have hR : ConvMod (EStep tbl) LvlEq
      (.pi ((dr.piDomain rfl).H.eps σ ρ)
        (piSlot (levelIsZero (σ (dr.piDomain rfl).u))
          (hB.dr.eps σ
            (binderDisp (levelIsZero (σ (dr.piDomain rfl).u)) :: ρ))))
      (dr.eps σ ρ) :=
    piRightSurface_eps hA hB dr σ ρ ▸ ports.rightCl
  exact es_pi hA hB dl dr hAd hBd hL hR

end Rcic.Syn

#print axioms Rcic.Syn.TyP.eps_castS
#print axioms Rcic.Syn.TyP.eps_castT
#print axioms Rcic.Syn.dnode_ty_castS
#print axioms Rcic.Syn.dnode_ty_castT
#print axioms Rcic.Syn.appLeftSurface_wt_lt
#print axioms Rcic.Syn.appLeftSurface_ap
#print axioms Rcic.Syn.appLeftSurface_eps
#print axioms Rcic.Syn.piLeftSurface_wt_lt
#print axioms Rcic.Syn.piLeftSurface_ap
#print axioms Rcic.Syn.piLeftSurface_eps
#print axioms Rcic.Syn.piRightSurfaceSrc_ap
#print axioms Rcic.Syn.piRightSurfaceSrc_eps
#print axioms Rcic.Syn.piRightSurface_ap
#print axioms Rcic.Syn.piRightSurface_eps
#print axioms Rcic.Syn.convMod_appClause
#print axioms Rcic.Syn.es_issued_occ_cl
#print axioms Rcic.Syn.es_issued_occ_bitCoh
#print axioms Rcic.Syn.es_app_field
#print axioms Rcic.Syn.es_pi_field

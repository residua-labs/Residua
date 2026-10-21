import rcic.RcicSynStepFields3

/-!
# `es_lam_field` — `StepSuppliers.es_lam` after the landed λ-verdict reads

Continuation of `RcicSynStepFields3.es_lam` (fields 3 of 17, batch 145 /
#7430; sortRow ports assignment).  `closure_claim = 0`.

`RcicSynStepFields3` proved `es_lam` *modulo `LamPorts`* — the eleven ports
the issued-row grammar cannot supply.  This module re-runs the port
classification against the **landed** `epsReadLam` verdict machine
(`RcicSynRead.lean`), applied independently to the two endpoints `dl`
(`λ A b`) and `dr` (`λ A' b'`): each `readLam` produces a `LamRead` and each
`epsReadLam` classifies the endpoint's erasure into one of four verdicts:

- `LamVerdict.clause h` — read `.yes g` *and* `D.eps σ ρ = lamClauseOf g σ ρ`:
  that endpoint's `got`/`eps` ports are **discharged outright** (the
  residual's port bundles are parameterised on the read's own `g`).
- `LamVerdict.star h` — `D.eps σ ρ = .star` while that is *not* the got's
  clause.  The `LamPorts` path is unusable (`eps` would be false).  On a
  single `star` the residual is the **proof-bit pair** `PBit σ ρ dl
  dl.reg.2 ∧ PBit σ ρ dr dl.reg.2` (`BELOWC_FAILED_READERS_AND_LET_BODY.md`
  §3.2: `dl` and `dr` share the ascribed type `.pi A B`, so `dl.reg.2` is
  a sort typing for both): the starred side's bit reads `levelIsZero (σ
  dl.reg.1)` off its `eps = ★`, the other bit writes the second `★`, and
  `ES` closes by `ConvMod.refl` — never a `ConvMod` equivalent to the
  goal.  Whenever `dl.reg.2` sits at a `P2Query.subAt` occurrence path
  `pReg`, `StepIH` supplies both bits via `Issues.occ_pb`
  (`lam_issued_dl_reg_pb`/`lam_issued_dr_reg_pb`/`es_lam_of_dl_star_reg_occ`/
  `es_lam_of_dr_star_reg_occ`).  On `(star, star)` the goal is `ConvMod
  .star .star`, closed by `ConvMod.refl` — a genuine discharge, the
  residual is `PUnit`.
- `LamVerdict.raw` — read `.yes g` but the walk does not identify the
  erasure: `got` is discharged, `eps` stays an exact residual.
- `LamVerdict.none` — `readLam = .no` (`cctx` heads, substitution-born λs):
  the endpoint's `got` *and* `eps` stay residual (`PSigma`-packaged).

The non-read ports stay open on **every** verdict — none is discharged:

- `bitL`/`bitR` (`BIT[g.u, u]`): `LamGot` carries no domain proof `H`;
  `occ_bitCoh` needs both typings at `subAt` paths of the payload and the
  wrapped-domain child is never one — needs the unlanded `lamDomain` source.
- `bodyL`/`bodyR` (`CL[g.hbody, hb.dl]` / `CL[cctx hb.dr hA, g.hbody]` at
  `binderDisp … :: ρ`): `occ_cl` is same-site-`Γ`, same-`ρ`; no row can ever
  issue a query at a binder-raised display.
- `tagL`/`tagR`/`bodyTag` (star-status pairs): `Issues` has no tag row.

`LamLResid`/`LamRResid` are the per-endpoint residual families;
`LamFieldResid` the whole-field residual; `es_lam_field` the field theorem.
The skeleton, `RcicSynP2Shared` and `RcicSynStepFields3` are untouched.
`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 one endpoint's port bundles -/

/-- Left endpoint's ports surviving a `clause` verdict (`got`+`epsL`
    discharged): `bitL`/`bodyL`/`tagL` parameterised on the read's `g`. -/
structure LamLClPorts (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (σ : Level → Level) (ρ : List Disp)
    (g : LamGot Aw (dl.wt Aw) E n Γ A b) : Type where
  /-- `BIT[HL.H, hA.dl]`. -/
  bit : levelIsZero (σ g.u) = levelIsZero (σ u)
  /-- `CL[g.hbody, hb.dl]` at the binder display. -/
  body : CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) g.hbody hb.dl
  /-- `Tag[g.hbody, hb.dl]`. -/
  tag : (g.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
    (hb.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star)

/-- Left endpoint's ports after `got` is known: `epsL` plus the
    `bitL`/`bodyL`/`tagL` fields — the residual for `raw` (and, packaged in
    a `PSigma` with `g` itself, for `none`). -/
structure LamLPorts (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (σ : Level → Level) (ρ : List Disp)
    (g : LamGot Aw (dl.wt Aw) E n Γ A b) : Type where
  /-- `dl` erases to `g`'s λ clause. -/
  eps : dl.eps σ ρ = lamClauseOf g σ ρ
  /-- `BIT[HL.H, hA.dl]`. -/
  bit : levelIsZero (σ g.u) = levelIsZero (σ u)
  /-- `CL[g.hbody, hb.dl]` at the binder display. -/
  body : CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) g.hbody hb.dl
  /-- `Tag[g.hbody, hb.dl]`. -/
  tag : (g.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
    (hb.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star)

/-- Right endpoint's ports surviving a `clause` verdict (`got`+`epsR`
    discharged): `bitR`/`bodyR`/`tagR` parameterised on the read's `g`. -/
structure LamRClPorts (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (σ : Level → Level) (ρ : List Disp)
    (g : LamGot Aw (dr.wt Aw) E n Γ A' b') : Type where
  /-- `BIT[HR.H, hA.dr]` — the regularity side, not `piDomSrc dr.reg.2`. -/
  bit : levelIsZero (σ g.u) = levelIsZero (σ u)
  /-- `CL[cctx hb.dr hA, g.hbody]` at the binder display. -/
  body : CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ)
    (TyP.cctx E n Γ b' B A A' u hb.dr hA) g.hbody
  /-- `Tag[hb.dr, g.hbody]` (through `eps_cctx`). -/
  tag : (hb.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
    (g.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star)

/-- Right endpoint's ports after `got` is known: `epsR`/`bitR`/`bodyR`/
    `tagR` — residual for `raw`, and `PSigma`-packaged for `none`. -/
structure LamRPorts (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (σ : Level → Level) (ρ : List Disp)
    (g : LamGot Aw (dr.wt Aw) E n Γ A' b') : Type where
  /-- `dr` erases to `g`'s λ clause. -/
  eps : dr.eps σ ρ = lamClauseOf g σ ρ
  /-- `BIT[HR.H, hA.dr]` — the regularity side, not `piDomSrc dr.reg.2`. -/
  bit : levelIsZero (σ g.u) = levelIsZero (σ u)
  /-- `CL[cctx hb.dr hA, g.hbody]` at the binder display. -/
  body : CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ)
    (TyP.cctx E n Γ b' B A A' u hb.dr hA) g.hbody
  /-- `Tag[hb.dr, g.hbody]` (through `eps_cctx`). -/
  tag : (hb.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
    (g.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star)

/-- The body's own pair tag — independent of both reads, open on every
    non-`star` verdict combination. -/
abbrev LamBodyTag {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A b b' B : Expr Nat} (u : Level)
    (hb : CvP E n (.assumption A :: Γ) b b' B)
    (σ : Level → Level) (ρ : List Disp) : Prop :=
  (hb.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
    (hb.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star)

/-! ## §2 per-side and whole residuals -/

/-- Left endpoint's residual after `epsReadLam dl`'s verdict.  `clause`
    keeps the three un-issued ports parameterised on the read's `g`; `star`
    is handled at the goal level (`PUnit` here); `raw` keeps `eps` plus the
    three ports at the read's `g`; `none` packages a `g` with its four
    ports. -/
def LamLResid (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (σ : Level → Level) (ρ : List Disp) :
    (r : LamRead Aw (dl.wt Aw) E n Γ A b) → LamVerdict dl σ ρ r → Type
  | .yes g, .clause _ => LamLClPorts Aw tbl hA hb dl dr σ ρ g
  | .yes _, .star _ => PUnit
  | .yes g, .raw => LamLPorts Aw tbl hA hb dl dr σ ρ g
  | .no, _ => PSigma fun g => LamLPorts Aw tbl hA hb dl dr σ ρ g

/-- Right endpoint's residual after `epsReadLam dr`'s verdict — mirrors
    `LamLResid`. -/
def LamRResid (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (σ : Level → Level) (ρ : List Disp) :
    (r : LamRead Aw (dr.wt Aw) E n Γ A' b') → LamVerdict dr σ ρ r → Type
  | .yes g, .clause _ => LamRClPorts Aw tbl hA hb dl dr σ ρ g
  | .yes _, .star _ => PUnit
  | .yes g, .raw => LamRPorts Aw tbl hA hb dl dr σ ρ g
  | .no, _ => PSigma fun g => LamRPorts Aw tbl hA hb dl dr σ ρ g

/-- What `es_lam` still owes after both `epsReadLam` verdicts.  Any `star`
    endpoint kills the `LamPorts` route (`eps` would be false) — the residual
    is the proof-bit pair `PB[dl, dl.reg.2] ∧ PB[dr, dl.reg.2]` (the §3.2
    local finish: the starred side's bit exports `levelIsZero (σ dl.reg.1)`,
    the other bit forces the second `★`; `dl` and `dr` share `.pi A B`),
    never a `ConvMod` equivalent to the goal.  `(star, star)` is closed by
    `ConvMod.refl` (`PUnit`, no residual).  Otherwise the residual is the
    two side residuals plus the read-independent `bodyTag`. -/
def LamFieldResid (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (σ : Level → Level) (ρ : List Disp) :
    (rL : LamRead Aw (dl.wt Aw) E n Γ A b) → LamVerdict dl σ ρ rL →
    (rR : LamRead Aw (dr.wt Aw) E n Γ A' b') → LamVerdict dr σ ρ rR → Type
  | .yes _, .star _, .yes _, .star _ => PUnit
  | .yes _, .star _, _, _ =>
      PLift (PBit σ ρ dl dl.reg.2 ∧ PBit σ ρ dr dl.reg.2)
  | _, _, .yes _, .star _ =>
      PLift (PBit σ ρ dl dl.reg.2 ∧ PBit σ ρ dr dl.reg.2)
  | rL, vL, rR, vR =>
      PProd (LamLResid Aw tbl hA hb dl dr σ ρ rL vL)
        (PProd (LamRResid Aw tbl hA hb dl dr σ ρ rR vR)
          (LamBodyTag u hb σ ρ))

/-! ## §3 the field theorem -/

/-- `StepSuppliers.es_lam` after maximal port discharge.  Exact field
    telescope plus the double-verdict residual; the `ES` is finished by the
    landed `es_lam` whenever neither endpoint is `star`, by the `PBit`-pair
    residual + `ConvMod.refl` on single-`star` combinations, and outright
    on `(star, star)` via `ConvMod.refl`. -/
theorem es_lam_field (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (resid : LamFieldResid Aw tbl hA hb dl dr σ ρ
      (readLam (envExt_refl E) Aw dl rfl)
      (epsReadLam (envExt_refl E) Aw σ dl rfl ρ)
      (readLam (envExt_refl E) Aw dr rfl)
      (epsReadLam (envExt_refl E) Aw σ dr rfl ρ)) :
    CaseStep Aw tbl (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ) := by
  intro hq ih
  -- Make both reads' indices variables so the indexed `cases` unify.
  have key : PSigma fun (rL : LamRead Aw (dl.wt Aw) E n Γ A b) =>
      PSigma fun (vL : LamVerdict dl σ ρ rL) =>
      PSigma fun (rR : LamRead Aw (dr.wt Aw) E n Γ A' b') =>
      PSigma fun (vR : LamVerdict dr σ ρ rR) =>
        LamFieldResid Aw tbl hA hb dl dr σ ρ rL vL rR vR :=
    ⟨readLam (envExt_refl E) Aw dl rfl,
      epsReadLam (envExt_refl E) Aw σ dl rfl ρ,
      readLam (envExt_refl E) Aw dr rfl,
      epsReadLam (envExt_refl E) Aw σ dr rfl ρ, resid⟩
  obtain ⟨rL, vL, rR, vR, res⟩ := key
  cases vL with
  | clause hL =>
      cases vR with
      | clause hR =>
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨_, hL, _, hR, res.1.bit, res.2.1.bit, res.1.body, res.2.1.body,
              res.1.tag, res.2.1.tag, res.2.2⟩ hq ih
      | star hR =>
          show ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)
          rw [res.down.1.mpr (res.down.2.mp hR), hR]
          exact ConvMod.refl _
      | raw =>
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨_, hL, _, res.2.1.eps, res.1.bit, res.2.1.bit, res.1.body,
              res.2.1.body, res.1.tag, res.2.1.tag, res.2.2⟩ hq ih
      | none =>
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨_, hL, res.2.1.1, res.2.1.2.eps, res.1.bit, res.2.1.2.bit,
              res.1.body, res.2.1.2.body, res.1.tag, res.2.1.2.tag, res.2.2⟩
              hq ih
  | star hL =>
      cases vR with
      | clause hR =>
          show ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)
          rw [hL, res.down.2.mpr (res.down.1.mp hL)]
          exact ConvMod.refl _
      | star hR =>
          show ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)
          rw [hL, hR]
          exact ConvMod.refl _
      | raw =>
          show ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)
          rw [hL, res.down.2.mpr (res.down.1.mp hL)]
          exact ConvMod.refl _
      | none =>
          show ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)
          rw [hL, res.down.2.mpr (res.down.1.mp hL)]
          exact ConvMod.refl _
  | raw =>
      cases vR with
      | clause hR =>
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨_, res.1.eps, _, hR, res.1.bit, res.2.1.bit, res.1.body,
              res.2.1.body, res.1.tag, res.2.1.tag, res.2.2⟩ hq ih
      | star hR =>
          show ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)
          rw [res.down.1.mpr (res.down.2.mp hR), hR]
          exact ConvMod.refl _
      | raw =>
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨_, res.1.eps, _, res.2.1.eps, res.1.bit, res.2.1.bit, res.1.body,
              res.2.1.body, res.1.tag, res.2.1.tag, res.2.2⟩ hq ih
      | none =>
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨_, res.1.eps, res.2.1.1, res.2.1.2.eps, res.1.bit, res.2.1.2.bit,
              res.1.body, res.2.1.2.body, res.1.tag, res.2.1.2.tag, res.2.2⟩
              hq ih
  | none =>
      cases vR with
      | clause hR =>
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨res.1.1, res.1.2.eps, _, hR, res.1.2.bit, res.2.1.bit,
              res.1.2.body, res.2.1.body, res.1.2.tag, res.2.1.tag, res.2.2⟩
              hq ih
      | star hR =>
          show ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)
          rw [res.down.1.mpr (res.down.2.mp hR), hR]
          exact ConvMod.refl _
      | raw =>
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨res.1.1, res.1.2.eps, _, res.2.1.eps, res.1.2.bit, res.2.1.bit,
              res.1.2.body, res.2.1.body, res.1.2.tag, res.2.1.tag, res.2.2⟩
              hq ih
      | none =>
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨res.1.1, res.1.2.eps, res.2.1.1, res.2.1.2.eps, res.1.2.bit,
              res.2.1.2.bit, res.1.2.body, res.2.1.2.body, res.1.2.tag,
              res.2.1.2.tag, res.2.2⟩ hq ih

/-! ## §4 the `StepIH`-discharged `PBit` landing (`Issues.occ_pb`)

`BELOWC_FAILED_READERS_AND_LET_BODY.md` §3.2: an actual whole-read
`D.eps μρ = ★` on either λ endpoint has a further local finish with
`PB[dl, dl.reg.2]` and `PB[dr, dl.reg.2]` — `dl` and `dr` share the
ascribed type `.pi A B`, so `dl.reg.2` is a sort typing for both.  Whenever
`dl.reg.2` sits at a `P2Query.subAt` occurrence path `pReg` of the query,
both bits are class (a): issuable and answered by `StepIH` through
`Issues.occ_pb` + `DNode.subAt_wt_lt` + `dmStep_pair_below` — the same
route as `eta_issued_dl_reg_pb`/`es_eta_of_dl_star_reg_occ`
(`RcicSynStepFields4.lean:1136`,`:1198`).  `dl` sits at `(0, [2])`, `dr` at
`(0, [3])`.  (`dl.reg.2`/`dr.reg.2` are synthesized `TyP.pi` nodes for
`TyP.lam`, so `pReg`/`hocc` stay hypotheses — the landing covers whichever
`subAt`-visible `reg.2` a caller has.) -/

/-- Whenever `dl.reg.2` sits at a `P2Query.subAt` occurrence path `pReg` of
    `.es (CvP.lam ...) S σ ρ` (`dl` sits at `(0, [2])`, and both `dl` and
    `dr` have ascribed type `.pi A B`), `StepIH` and `Issues.occ_pb` supply
    `PBit σ ρ dl dl.reg.2`, with weight bounds and `AssumpPref` discharged
    automatically from `TyP.wt_reg_le` and `hq.ap`. -/
theorem lam_issued_dl_reg_pb (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2))
    (hq : Demand (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)) :
    PBit σ ρ dl dl.reg.2 := by
  obtain ⟨_, _, hapdl, _⟩ := hq.ap
  have hreg_wt : dl.reg.2.wt Aw ≤ dl.wt Aw := TyP.wt_reg_le Aw dl
  exact ih_issue Aw tbl hq ih (.pb dl dl.reg.2 S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := [2]) (k₂ := 0) (p₂ := pReg)
      rfl hocc hapdl (assumpPref_reg hapdl))
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.lam E n Γ A A' b b' B u hA hb dl dr)
        rfl dl dl.reg.2
        (by simp only [CvP.wt]; omega)
        (by simp only [CvP.wt]; omega)))))

/-- Whenever `dl.reg.2` sits at a `P2Query.subAt` occurrence path `pReg` of
    `.es (CvP.lam ...) S σ ρ` (`dr` sits at `(0, [3])`, and both `dl` and
    `dr` have ascribed type `.pi A B`), `StepIH` and `Issues.occ_pb` supply
    `PBit σ ρ dr dl.reg.2`, with weight bounds and `AssumpPref` discharged
    automatically from `TyP.wt_reg_le` and `hq.ap`. -/
theorem lam_issued_dr_reg_pb (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2))
    (hq : Demand (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)) :
    PBit σ ρ dr dl.reg.2 := by
  obtain ⟨_, _, hapdl, hapdr⟩ := hq.ap
  have hreg_wt : dl.reg.2.wt Aw ≤ dl.wt Aw := TyP.wt_reg_le Aw dl
  exact ih_issue Aw tbl hq ih (.pb dr dl.reg.2 S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := [3]) (k₂ := 0) (p₂ := pReg)
      rfl hocc hapdr (assumpPref_reg hapdl))
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.lam E n Γ A A' b b' B u hA hb dl dr)
        rfl dr dl.reg.2
        (by simp only [CvP.wt]; omega)
        (by simp only [CvP.wt]; omega)))))

/-- §3.2 proof-result closure of `es_lam` (`BELOWC_FAILED_READERS_AND_LET_BODY.md`
    §3.2): whenever `levelIsZero (σ dl.reg.1) = true` and `dl.reg.2` sits at
    occurrence path `pReg`, `StepIH` (`lam_issued_dl_reg_pb` and
    `lam_issued_dr_reg_pb`) forces both `dl.eps σ ρ = .star` and
    `dr.eps σ ρ = .star`, closing `CaseStep` with **zero `CL`, `PBit`, or
    `LamPorts` hypotheses**. -/
theorem es_lam_proof_of_reg_occ (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ dl.reg.1) = true)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2)) :
    CaseStep Aw tbl (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ) := by
  intro hq ih
  have hpbL : PBit σ ρ dl dl.reg.2 :=
    lam_issued_dl_reg_pb Aw tbl hA hb dl dr S σ ρ pReg hocc hq ih
  have hpbR : PBit σ ρ dr dl.reg.2 :=
    lam_issued_dr_reg_pb Aw tbl hA hb dl dr S σ ρ pReg hocc hq ih
  have hdl_star : dl.eps σ ρ = .star := hpbL.mpr hu
  have hdr_star : dr.eps σ ρ = .star := hpbR.mpr hu
  show ES tbl σ ρ _
  unfold ES
  simp only [CvP.dl, CvP.dr, hdl_star, hdr_star]
  exact ConvMod.refl _

/-- §3.2 whole-read-star closure of `es_lam` (left): whenever
    `dl.eps σ ρ = .star` and `dl.reg.2` sits at occurrence path `pReg`,
    `StepIH` (`lam_issued_dl_reg_pb` and `lam_issued_dr_reg_pb`) forces
    `dr.eps σ ρ = .star` as well, closing `CaseStep` with **zero `CL`,
    `PBit`, or `LamPorts` hypotheses**. -/
theorem es_lam_of_dl_star_reg_occ (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hdl_star : dl.eps σ ρ = .star)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2)) :
    CaseStep Aw tbl (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ) := by
  intro hq ih
  have hpbL : PBit σ ρ dl dl.reg.2 :=
    lam_issued_dl_reg_pb Aw tbl hA hb dl dr S σ ρ pReg hocc hq ih
  exact es_lam_proof_of_reg_occ Aw tbl hA hb dl dr S σ ρ
    (hpbL.mp hdl_star) pReg hocc hq ih

/-- §3.2 whole-read-star closure of `es_lam` (right): whenever
    `dr.eps σ ρ = .star` and `dl.reg.2` sits at occurrence path `pReg`,
    `StepIH` (`lam_issued_dr_reg_pb` and `lam_issued_dl_reg_pb`) forces
    `dl.eps σ ρ = .star` as well, closing `CaseStep` with **zero `CL`,
    `PBit`, or `LamPorts` hypotheses**. -/
theorem es_lam_of_dr_star_reg_occ (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hdr_star : dr.eps σ ρ = .star)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2)) :
    CaseStep Aw tbl (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ) := by
  intro hq ih
  have hpbR : PBit σ ρ dr dl.reg.2 :=
    lam_issued_dr_reg_pb Aw tbl hA hb dl dr S σ ρ pReg hocc hq ih
  exact es_lam_proof_of_reg_occ Aw tbl hA hb dl dr S σ ρ
    (hpbR.mp hdr_star) pReg hocc hq ih

end Rcic.Syn

#print axioms Rcic.Syn.LamLClPorts
#print axioms Rcic.Syn.LamLPorts
#print axioms Rcic.Syn.LamRClPorts
#print axioms Rcic.Syn.LamRPorts
#print axioms Rcic.Syn.LamLResid
#print axioms Rcic.Syn.LamRResid
#print axioms Rcic.Syn.LamFieldResid
#print axioms Rcic.Syn.es_lam_field
#print axioms Rcic.Syn.lam_issued_dl_reg_pb
#print axioms Rcic.Syn.lam_issued_dr_reg_pb
#print axioms Rcic.Syn.es_lam_proof_of_reg_occ
#print axioms Rcic.Syn.es_lam_of_dl_star_reg_occ
#print axioms Rcic.Syn.es_lam_of_dr_star_reg_occ

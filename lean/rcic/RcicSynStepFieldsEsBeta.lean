import rcic.RcicSynStepFields3

/-!
# `es_beta_field` — `StepSuppliers.es_beta` after the landed redex-verdict read

Continuation of `RcicSynStepFields3.es_beta` (fields 3 of 17, batch 145 /
#7430; sortRow ports assignment).  `closure_claim = 0`.

`RcicSynStepFields3` proved `es_beta` *modulo `BetaPorts`* — the seven ports
the issued-row grammar cannot supply.  This module re-runs the port
classification against the **landed** `epsReadRedex` verdict machine
(`RcicSynRead.lean:1436`), which walks any `dl` whose subject is
`.app (.lam A body) arg` and reports one of four verdicts on
`readRedex (envExt_refl E) Aw dl rfl`:

- `RedexVerdict.clause h` — read `.yes g` *and* `dl.eps σ ρ = redexClauseOf g σ ρ`:
  the `got`/`eps` ports are **discharged outright** (classification (c):
  directly provable from the landed reader — no hypothesis remains).
- `RedexVerdict.star h` — `dl.eps σ ρ = .star` while that is *not* the got's
  clause.  The `BetaPorts` path is unusable (`eps` would be false).  The
  residual is the **proof-bit pair** `PBit σ ρ dl dl.reg.2 ∧ PBit σ ρ dr
  dl.reg.2` (`BELOWC_FAILED_READERS_AND_LET_BODY.md` §3.2: a whole-read
  `dl.eps = ★` has the local finish through `PB[dl, dl.reg.2]` and
  `PB[dr, dl.reg.2]` — `dl` and `dr` share the ascribed type
  `instantiate0 arg B`): the left bit reads `levelIsZero (σ dl.reg.1)` off
  `dl.eps = ★`, the right bit writes `dr.eps = ★`, and `ES` closes by
  `ConvMod.refl`.  Whenever `dl.reg.2` sits at a `P2Query.subAt` occurrence
  path `pReg` of the query, `StepIH` supplies both bits via `Issues.occ_pb`
  (`beta_issued_dl_reg_pb`/`beta_issued_dr_reg_pb`/`es_beta_of_dl_star_reg_occ`);
  for a direct `TyP.app` left endpoint `pReg = [3, 2]` by `rfl`
  (`es_beta_direct_app_of_dl_star`).  When it is not an occurrence the
  `PBit` pair stays the named residual — never the goal itself.
- `RedexVerdict.raw` — read `.yes g` but the walk does not identify the
  erasure (`esub`-here `keep` spines): `got` is discharged, `eps` stays an
  exact residual ((d)), plus the six always-open ports.
- `RedexVerdict.none` — `readRedex = .no` (`lsub`/`cctx` heads,
  substitution-born redexes): the whole `BetaPorts` stays residual; the
  `RcicSynDomainSource` decoders that would cover it are not landed
  (#7475 is open) — classification (d), named in the measure.

The six `BetaClPorts` stay open on **every** verdict — none is discharged:

- `domBit` (`BIT[Hg.H, hA]`): `RedexGot` carries no domain proof `Hg.H`;
  `occ_bitCoh` needs both typings at `subAt` paths of the payload and the
  wrapped-domain child is never one — needs the unlanded `lamDomain` source.
- `argTag`/`bodyTag`: `Issues` has no tag row; the needed `PB` sort proofs are
  synthesized (`reg.2`-style), never `subAt` occurrences.
- `argCl` (`CL[g.harg, harg]`): `g.harg` from a pushed read is `ewk`-wrapped,
  not a literal `subAt` occurrence; `occ_cl` cannot issue it.
- `bodyCl` (`CL[g.hbody, hbody]` at `binderDisp … :: ρ` in
  `.assumption A :: Γ`): `occ_cl` is same-site-`Γ`, same-`ρ`; no row can ever
  issue a query at a binder-raised display.
- `reductCl` (`CL[instEnd hbody harg hA, dr]`): `instEnd` is a synthesized
  canonical node, never a `subAt` occurrence.

One new declaration per residual concept; the skeleton, `RcicSynP2Shared`
and `RcicSynStepFields3` are untouched.  `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the six ports that survive every verdict -/

/-- The `es_beta` obligations that remain open even after the redex read
    supplies `got`: every field is the exact `BetaPorts` statement, now
    parameterized on the `g` the read (or the caller) produced.  None is
    issuable through `Issues` for the reasons in the module docstring. -/
structure BetaClPorts (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (σ : Level → Level) (ρ : List Disp)
    (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg) : Type where
  /-- `BIT[Hg.H, hA]` ∘ reader compatibility `Hg.u = g.u`. -/
  domBit : levelIsZero (σ g.u) = levelIsZero (σ u)
  /-- `Tag[g.harg, harg]` at the site display. -/
  argTag : (g.harg.eps σ ρ = .star) ↔ (harg.eps σ ρ = .star)
  /-- `CL[g.harg, harg]` at the site display. -/
  argCl : CL tbl σ ρ g.harg harg
  /-- `Tag[g.hbody, hbody]` at the body display. -/
  bodyTag : (g.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
    (hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star)
  /-- `CL[g.hbody, hbody]` at the body display. -/
  bodyCl : CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) g.hbody hbody
  /-- `CL[instEnd hbody harg hA, dr]` at the site display. -/
  reductCl : CL tbl σ ρ (instEnd hbody harg hA) dr

/-- Assemble a `BetaPorts` from a read's `got`, its `eps`, and the clause
    ports — composition only, no proof copying. -/
def BetaClPorts.toBetaPorts {Aw : Nat → Nat} {tbl : List CRule}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    {hA : TyP E n Γ A (.sort u)} {hbody : TyP E n (.assumption A :: Γ) body B}
    {harg : TyP E n Γ arg A}
    {dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B)}
    {dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B)}
    {σ : Level → Level} {ρ : List Disp}
    {g : RedexGot Aw (dl.wt Aw) E n Γ A body arg}
    (eps : dl.eps σ ρ = redexClauseOf g σ ρ)
    (ports : BetaClPorts Aw tbl hA hbody harg dl dr σ ρ g) :
    BetaPorts Aw tbl hA hbody harg dl dr σ ρ :=
  ⟨g, eps, ports.domBit, ports.argTag, ports.argCl, ports.bodyTag, ports.bodyCl,
    ports.reductCl⟩

/-! ## §2 the verdict-indexed residual -/

/-- What `es_beta` still owes after `epsReadRedex`'s verdict on `dl`:
    per-verdict exact residual.  `clause` discharges `got`/`eps` (the read
    produced them); `star` keeps the `PBit` pair `PB[dl, dl.reg.2] ∧
    PB[dr, dl.reg.2]` — not a `ConvMod` equivalent to the goal; `raw` keeps
    the eps equation; `none` keeps the whole `BetaPorts`. -/
def BetaFieldResid (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (σ : Level → Level) (ρ : List Disp) :
    (r : RedexRead Aw (dl.wt Aw) E n Γ A body arg) →
    RedexVerdict dl σ ρ r → Type
  | .yes g, .clause _ => BetaClPorts Aw tbl hA hbody harg dl dr σ ρ g
  | .yes _, .star _ =>
      PLift (PBit σ ρ dl dl.reg.2 ∧ PBit σ ρ dr dl.reg.2)
  | .yes g, .raw => PProd (dl.eps σ ρ = redexClauseOf g σ ρ)
      (BetaClPorts Aw tbl hA hbody harg dl dr σ ρ g)
  | .no, _ => BetaPorts Aw tbl hA hbody harg dl dr σ ρ

/-! ## §3 the field theorem -/

/-- `StepSuppliers.es_beta` after maximal port discharge.  Exact field
    telescope plus the verdict-indexed residual; the `ES` is finished by the
    landed `es_beta` on every non-`star` verdict and by the `ConvMod`
    residual on `star`. -/
theorem es_beta_field (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (resid : BetaFieldResid Aw tbl hA hbody harg dl dr σ ρ
      (readRedex (envExt_refl E) Aw dl rfl)
      (epsReadRedex (envExt_refl E) Aw σ dl rfl ρ)) :
    CaseStep Aw tbl (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) := by
  intro _hq _ih
  -- Make the read's index a variable so the indexed-family `cases` unifies.
  have key : PSigma fun (r : RedexRead Aw (dl.wt Aw) E n Γ A body arg) =>
      PSigma fun (v : RedexVerdict dl σ ρ r) =>
        BetaFieldResid Aw tbl hA hbody harg dl dr σ ρ r v :=
    ⟨readRedex (envExt_refl E) Aw dl rfl,
      epsReadRedex (envExt_refl E) Aw σ dl rfl ρ, resid⟩
  obtain ⟨r, v, res⟩ := key
  cases v with
  | clause heps =>
      exact es_beta Aw tbl hA hbody harg dl dr S σ ρ
        (BetaClPorts.toBetaPorts heps res) _hq _ih
  | star heps =>
      show ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)
      rw [heps, res.down.2.mpr (res.down.1.mp heps)]
      exact ConvMod.refl _
  | raw =>
      exact es_beta Aw tbl hA hbody harg dl dr S σ ρ
        (BetaClPorts.toBetaPorts res.1 res.2) _hq _ih
  | none =>
      exact es_beta Aw tbl hA hbody harg dl dr S σ ρ res _hq _ih

/-! ## §4 the `StepIH`-discharged `PBit` landing (`Issues.occ_pb`)

`BELOWC_FAILED_READERS_AND_LET_BODY.md` §3.2: for β an actual whole-read
`dl.eps μρ = ★` has a further local finish with `PB[dl, dl.reg.2]` and
`PB[dr, dl.reg.2]` — `dl` and `dr` share the ascribed type
`instantiate0 arg B`, so `dl.reg.2` is a sort typing for both.  Whenever
`dl.reg.2` sits at a `P2Query.subAt` occurrence path `pReg` of the query,
both bits are class (a): issuable and answered by `StepIH` through
`Issues.occ_pb` + `DNode.subAt_wt_lt` + `dmStep_pair_below` — the same
route as `letE_issued_dl_reg_pb`/`es_letE_of_dl_star_reg_occ`
(`RcicSynStepFields4.lean:641`,`:736`).  `dl` sits at `(0, [3])`, `dr` at
`(0, [4])`. -/

/-- Whenever `dl.reg.2` sits at a `P2Query.subAt` occurrence path `pReg` of
    `.es (CvP.beta ...) S σ ρ` (`dl` sits at `(0, [3])`, and both `dl` and
    `dr` have ascribed type `instantiate0 arg B`), `StepIH` and
    `Issues.occ_pb` supply `PBit σ ρ dl dl.reg.2`, with weight bounds and
    `AssumpPref` discharged automatically from `TyP.wt_reg_le` and `hq.ap`. -/
theorem beta_issued_dl_reg_pb (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2))
    (hq : Demand (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)) :
    PBit σ ρ dl dl.reg.2 := by
  obtain ⟨_, _, _, hapdl, _⟩ := hq.ap
  have hreg_wt : dl.reg.2.wt Aw ≤ dl.wt Aw := TyP.wt_reg_le Aw dl
  exact ih_issue Aw tbl hq ih (.pb dl dl.reg.2 S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := [3]) (k₂ := 0) (p₂ := pReg)
      rfl hocc hapdl (assumpPref_reg hapdl))
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.beta E n Γ A body arg B u hA hbody harg dl dr)
        rfl dl dl.reg.2
        (by simp only [CvP.wt]; omega)
        (by simp only [CvP.wt]; omega)))))

/-- Whenever `dl.reg.2` sits at a `P2Query.subAt` occurrence path `pReg` of
    `.es (CvP.beta ...) S σ ρ` (`dr` sits at `(0, [4])`, and both `dl` and
    `dr` have ascribed type `instantiate0 arg B`), `StepIH` and
    `Issues.occ_pb` supply `PBit σ ρ dr dl.reg.2`, with weight bounds and
    `AssumpPref` discharged automatically from `TyP.wt_reg_le` and `hq.ap`. -/
theorem beta_issued_dr_reg_pb (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2))
    (hq : Demand (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)) :
    PBit σ ρ dr dl.reg.2 := by
  obtain ⟨_, _, _, hapdl, hapdr⟩ := hq.ap
  have hreg_wt : dl.reg.2.wt Aw ≤ dl.wt Aw := TyP.wt_reg_le Aw dl
  exact ih_issue Aw tbl hq ih (.pb dr dl.reg.2 S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := [4]) (k₂ := 0) (p₂ := pReg)
      rfl hocc hapdr (assumpPref_reg hapdl))
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.beta E n Γ A body arg B u hA hbody harg dl dr)
        rfl dr dl.reg.2
        (by simp only [CvP.wt]; omega)
        (by simp only [CvP.wt]; omega)))))

/-- §3.2 proof-result closure of `es_beta` (`BELOWC_FAILED_READERS_AND_LET_BODY.md`
    §3.2): whenever `levelIsZero (σ dl.reg.1) = true` and `dl.reg.2` sits at
    occurrence path `pReg`, `StepIH` (`beta_issued_dl_reg_pb` and
    `beta_issued_dr_reg_pb`) forces both `dl.eps σ ρ = .star` and
    `dr.eps σ ρ = .star`, closing `CaseStep` with **zero `CL`, `PBit`, or
    `BetaPorts` hypotheses**. -/
theorem es_beta_proof_of_reg_occ (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ dl.reg.1) = true)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2)) :
    CaseStep Aw tbl (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) := by
  intro hq ih
  have hpbL : PBit σ ρ dl dl.reg.2 :=
    beta_issued_dl_reg_pb Aw tbl hA hbody harg dl dr S σ ρ pReg hocc hq ih
  have hpbR : PBit σ ρ dr dl.reg.2 :=
    beta_issued_dr_reg_pb Aw tbl hA hbody harg dl dr S σ ρ pReg hocc hq ih
  have hdl_star : dl.eps σ ρ = .star := hpbL.mpr hu
  have hdr_star : dr.eps σ ρ = .star := hpbR.mpr hu
  show ES tbl σ ρ _
  unfold ES
  simp only [CvP.dl, CvP.dr, hdl_star, hdr_star]
  exact ConvMod.refl _

/-- §3.2 whole-read-star closure of `es_beta`: whenever `dl.eps σ ρ = .star`
    and `dl.reg.2` sits at occurrence path `pReg`, `StepIH`
    (`beta_issued_dl_reg_pb` and `beta_issued_dr_reg_pb`) forces
    `dr.eps σ ρ = .star` as well, closing `CaseStep` with **zero `CL`,
    `PBit`, or `BetaPorts` hypotheses**. -/
theorem es_beta_of_dl_star_reg_occ (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hdl_star : dl.eps σ ρ = .star)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2)) :
    CaseStep Aw tbl (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) := by
  intro hq ih
  have hpbL : PBit σ ρ dl dl.reg.2 :=
    beta_issued_dl_reg_pb Aw tbl hA hbody harg dl dr S σ ρ pReg hocc hq ih
  exact es_beta_proof_of_reg_occ Aw tbl hA hbody harg dl dr S σ ρ
    (hpbL.mp hdl_star) pReg hocc hq ih

/-- Direct-left-`TyP.app` whole-read-star closure of `es_beta`: when
    `dl = TyP.app E n Γ (.lam A body) arg A' B w hf ha hT`, `dl.reg.2 = hT`
    sits at occurrence path `(0, [3, 2])` by `rfl`, so `dl.eps σ ρ = .star`
    alone (e.g. the `RedexVerdict.star` of the landed read) closes
    `CaseStep` from `StepIH` with **zero extra hypotheses**. -/
theorem es_beta_direct_app_of_dl_star (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B A' : Expr Nat} {u w : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (hf : TyP E n Γ (.lam A body) (.pi A' B)) (ha : TyP E n Γ arg A')
    (hT : TyP E n Γ (instantiate0 arg B) (.sort w))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hdl_star :
      (TyP.app E n Γ (.lam A body) arg A' B w hf ha hT).eps σ ρ = .star) :
    CaseStep Aw tbl (.es (CvP.beta E n Γ A body arg B u hA hbody harg
      (TyP.app E n Γ (.lam A body) arg A' B w hf ha hT) dr) S σ ρ) :=
  es_beta_of_dl_star_reg_occ Aw tbl hA hbody harg
    (TyP.app E n Γ (.lam A body) arg A' B w hf ha hT) dr S σ ρ
    hdl_star [3, 2] rfl

end Rcic.Syn

#print axioms Rcic.Syn.BetaClPorts
#print axioms Rcic.Syn.BetaFieldResid
#print axioms Rcic.Syn.es_beta_field
#print axioms Rcic.Syn.beta_issued_dl_reg_pb
#print axioms Rcic.Syn.beta_issued_dr_reg_pb
#print axioms Rcic.Syn.es_beta_proof_of_reg_occ
#print axioms Rcic.Syn.es_beta_of_dl_star_reg_occ
#print axioms Rcic.Syn.es_beta_direct_app_of_dl_star

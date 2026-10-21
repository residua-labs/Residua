import rcic.RcicSynStepFieldsEsLam
import rcic.RcicSynStepFields5
import rcic.RcicSynDomainSource

/-!
# `RcicSynClosedEslam` — `es_lam` closed under its genuine walls

swe-eslam lane (sortRow `StepSuppliers` supplier group `es_lam`;
filler `es_lam_field` `RcicSynStepFieldsEsLam.lean:203` under the
double-verdict residual `LamFieldResid` `:179`; the earlier flat
`LamPorts` route is `RcicSynStepFields3.es_lam` `:207`).
`closure_claim = 0`.

## Discharge, measured on main 2026-10-19 (revised after audit)

`es_lam` (`RcicSynStepSkeleton.lean`): `CaseStep` of
`.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ`, residual
indexed by `epsReadLam` of `dl` and `dr`.  All discharge is
**branch-scoped** — no top-level occurrence premise: every receipt is a
`PSum`/`PSigma` leg inside the residual of exactly the branch that
consumes it, so `(star, star)` stays `PUnit`, `none` branches keep the
landed `LamLPorts`/`LamRPorts` wholesale, and `clause`/`raw` never
demand `reg2`.

| residual slot | class | evidence |
|---|---|---|
| `(star, star)` → `PUnit` | (a) | landed: `ConvMod .star .star` by `ConvMod.refl` (`es_lam_field` `RcicSynStepFieldsEsLam.lean:253`) |
| single-`star` → `PLift (PBit σ ρ dl dl.reg.2 ∧ PBit σ ρ dr dl.reg.2)` | (b) | `lam_issued_dl_reg_pb`/`lam_issued_dr_reg_pb` (`RcicSynStepFieldsEsLam.lean:326`/`:356`) discharge both bits from `StepIH` via `Issues.occ_pb` + `TyP.wt_reg_le` whenever `dl.reg.2` sits at a `subAt` path.  `LamStarResid` (`:96`) is `PSum` of the landed premise and the receipt — strictly weaker, never harder: callers on `conv`-headed `dl` supply `.inr` (the receipt, e.g. `lam_reg2_occ_conv` `[2,1,2]`); callers on bare `TyP.lam` keep `.inl` (the receipt is absent there — `lam_reg2_absent_at_sort_lam`, a kernel-checked `¬ ∃ p`).  `occ_pb` is the only `Issues` row emitting `.pb` (`RcicSynP2Shared.lean`). |
| `bit : levelIsZero (σ g.u) = levelIsZero (σ u)` on `.yes` reads (`clause`/`raw`) | (b) where the two receipts hold, else (d) | `lamDomain` landed (`RcicSynDomainSource.lean:235`) + `lamDomain_u_of_readLam` identify `g.u` with `(lamDomain dl rfl).u`; `es_issued_occ_bitCoh` (`RcicSynStepFields5.lean`) issues `.bitCoh` between `H` and `hA.dl`.  The `*Closed` bundles keep `bit` as `PSum (bit) (receipts)` — the landed premise is still there (`.inl`), the receipt route is *additional* (`.inr`): `LamBitOccL`/`LamBitOccR` never replace the port, and `none` branches keep the landed `LamLPorts` verbatim (the `PSigma` `g` has no `lamDomain` link).  `domL`/`domR` hold for `conv`-free outer spines (`lam_dom_occ_direct`/`lam_domR_occ_direct`, `[2,0]`/`[3,0]`); `hAdl`/`hAdr` hold when `hA` is not transport-headed (`lam_hAdl_occ_refl`/`lam_hAdr_occ_refl`, `[0,1]`/`[0,2]`; also `[0,0]`/`[0,1]` for `.sorts` `hA`). |
| `got` — the `PSigma` `LamGot` on `none` | (d) | `readLam` answers `.no` on `lsub`/`cctx` heads (`RcicSynRead.lean`); `LamGot` is a body typing plus an atom bound — the bound is the honest gap.  Inhabited concretely at `EslamFix.lamGotSort`. |
| `eps : dl.eps σ ρ = lamClauseOf g σ ρ` on `raw` | (d) | the port is exactly the `clause` verdict's payload — satisfiable iff the read identifies the erasure; `raw` means it does not.  Inhabited concretely at `lam_eps_at_sort_lam` (`dl_can` reads to `.yes lamGotSort` and its `eps` is `.lam (.sort .zero)`, `rfl`). |
| `body : CL tbl σ (binderDisp … :: ρ) g.hbody hb.dl` / `bodyR` | (d) | `Issues.occ_cl` emits `.cl` at the query's own site `Γ`/`ρ`; `lam_esB` is the only binder-raised issue and emits `.es`, not `.cl`.  Inhabited at identical endpoints: `lam_bodyCl_self`. |
| `tag`/`tagR`/`bodyTag` (star-status iffs) | (d) | the `Issues` grammar has no star-status row.  Inhabited whenever the two erasures are equal (`lam_tag_of_eps_eq`/`lam_bodyTag_of_eps_eq`), concretely at `lam_tag_at_sort_lam`/`lam_bodyTag_at_sort_lam` (`Iff.rfl` on the fixture). |
| `bit` inside `LamLPorts`/`LamRPorts` on `none` | (d) | the `PSigma`-supplied `g.u` has no `lamDomain` link (the read failed); kept verbatim inside the landed `LamLPorts`/`LamRPorts`. |

Non-vacuity: every retained port is inhabited — the `EslamFix` canonical
fixture (a bare `TyP.lam` over sort domains, `nilScope`/`id`/`[]`)
exhibits `got`, `eps`, `tag`, `bodyTag`, the `dom`/`hA` receipts and
both `LamBitOcc*` bundles concretely, while `lam_reg2_absent_at_sort_lam`
is a kernel-checked refutation showing the `reg2` receipt is genuinely
absent there — which is exactly why it is a `PSum` leg, not a premise.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv}

/-! ## §1 branch-scoped occurrence receipts (data, not premises) -/

/-- The two `subAt` receipts that make a `.yes`-read `bitL`
    StepIH-issuable: `(lamDomain dl rfl).H` (the decoded domain typing)
    and `hA.dl` both at payload paths of the `.es (CvP.lam …)` query.
    `Type`-valued data — a caller may supply it *instead of* proving
    `bit` (`lam_bitL_of_occ` discharges it via `StepIH`). -/
structure LamBitOccL {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) : Type where
  /-- payload path of the decoded `(lamDomain dl rfl).H`. -/
  pH : List Nat
  hoccH : P2Query.subAt (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)
    0 pH = some (.ty (lamDomain dl rfl).H)
  /-- payload path of `hA.dl`. -/
  pA : List Nat
  hoccA : P2Query.subAt (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)
    0 pA = some (.ty hA.dl)

/-- Right-side mirror of `LamBitOccL`: `(lamDomain dr rfl).H` and
    `hA.dr` at payload paths. -/
structure LamBitOccR {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) : Type where
  /-- payload path of the decoded `(lamDomain dr rfl).H`. -/
  pH : List Nat
  hoccH : P2Query.subAt (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)
    0 pH = some (.ty (lamDomain dr rfl).H)
  /-- payload path of `hA.dr`. -/
  pA : List Nat
  hoccA : P2Query.subAt (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)
    0 pA = some (.ty hA.dr)

/-- The single-`star` residual: the landed `PBit` pair premise *or* a
    `subAt` receipt for `dl.reg.2` from which `StepIH` issues both bits
    (`lam_issued_dl_reg_pb`/`lam_issued_dr_reg_pb`).  Strictly weaker
    than the landed `PLift` — `.inl` embeds every inhabitant of the
    landed residual; `.inr` is the receipt route for `conv`-headed
    `dl` (`lam_reg2_occ_conv`).  At a bare `TyP.lam` the receipt is
    absent (`lam_reg2_absent_at_sort_lam`), so `.inl` must be used. -/
def LamStarResid {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) : Type :=
  PSum (PLift (PBit σ ρ dl dl.reg.2 ∧ PBit σ ρ dr dl.reg.2))
    (PSigma fun (pReg : List Nat) =>
      P2Query.subAt (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2))

/-! ## §2 the reduced port bundles (`bit` weakened, everything else verbatim) -/

/-- `LamLClPorts` with `bit` weakened to `PSum bit receipts` — `body`
    and `tag` are the landed fields verbatim. -/
structure LamLClPortsClosed (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (g : LamGot Aw (dl.wt Aw) E n Γ A b) : Type where
  /-- `BIT[HL.H, hA.dl]` — the landed premise, or the `LamBitOccL`
      receipt pair from which `StepIH` issues it (`lam_bitL_of_occ`). -/
  bit : PSum (levelIsZero (σ g.u) = levelIsZero (σ u))
    (LamBitOccL hA hb dl dr S σ ρ)
  /-- `CL[g.hbody, hb.dl]` at the binder display — (d), verbatim. -/
  body : CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) g.hbody hb.dl
  /-- `Tag[g.hbody, hb.dl]` — (d), verbatim. -/
  tag : (g.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
    (hb.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star)

/-- `LamLPorts` with `bit` weakened to `PSum bit receipts` — `eps`,
    `body`, `tag` verbatim. -/
structure LamLPortsClosed (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (g : LamGot Aw (dl.wt Aw) E n Γ A b) : Type where
  /-- `dl` erases to `g`'s λ clause — (d), verbatim. -/
  eps : dl.eps σ ρ = lamClauseOf g σ ρ
  /-- `BIT[HL.H, hA.dl]` — landed premise or receipt pair. -/
  bit : PSum (levelIsZero (σ g.u) = levelIsZero (σ u))
    (LamBitOccL hA hb dl dr S σ ρ)
  /-- `CL[g.hbody, hb.dl]` at the binder display — (d), verbatim. -/
  body : CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) g.hbody hb.dl
  /-- `Tag[g.hbody, hb.dl]` — (d), verbatim. -/
  tag : (g.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
    (hb.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star)

/-- `LamRClPorts` with `bit` weakened — `body`/`tag` verbatim. -/
structure LamRClPortsClosed (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (g : LamGot Aw (dr.wt Aw) E n Γ A' b') : Type where
  /-- `BIT[HR.H, hA.dr]` — landed premise or the `LamBitOccR` pair. -/
  bit : PSum (levelIsZero (σ g.u) = levelIsZero (σ u))
    (LamBitOccR hA hb dl dr S σ ρ)
  /-- `CL[cctx hb.dr hA, g.hbody]` at the binder display — (d), verbatim. -/
  body : CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ)
    (TyP.cctx E n Γ b' B A A' u hb.dr hA) g.hbody
  /-- `Tag[hb.dr, g.hbody]` — (d), verbatim. -/
  tag : (hb.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
    (g.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star)

/-- `LamRPorts` with `bit` weakened — `eps`/`body`/`tag` verbatim. -/
structure LamRPortsClosed (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (g : LamGot Aw (dr.wt Aw) E n Γ A' b') : Type where
  /-- `dr` erases to `g`'s λ clause — (d), verbatim. -/
  eps : dr.eps σ ρ = lamClauseOf g σ ρ
  /-- `BIT[HR.H, hA.dr]` — landed premise or the `LamBitOccR` pair. -/
  bit : PSum (levelIsZero (σ g.u) = levelIsZero (σ u))
    (LamBitOccR hA hb dl dr S σ ρ)
  /-- `CL[cctx hb.dr hA, g.hbody]` at the binder display — (d), verbatim. -/
  body : CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ)
    (TyP.cctx E n Γ b' B A A' u hb.dr hA) g.hbody
  /-- `Tag[hb.dr, g.hbody]` — (d), verbatim. -/
  tag : (hb.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
    (g.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star)

/-- Left endpoint's residual: `clause`/`raw` keep the `*Closed` bundles
    (weakened `bit`, verbatim `body`/`tag`/`eps`); `star` is `PUnit`;
    `none` keeps the landed `LamLPorts` wholesale — the `PSigma` `g` has
    no `lamDomain` link, so no receipt route exists there. -/
def LamLResidClosed (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    (r : LamRead Aw (dl.wt Aw) E n Γ A b) → LamVerdict dl σ ρ r → Type
  | .yes g, .clause _ => LamLClPortsClosed Aw tbl hA hb dl dr S σ ρ g
  | .yes _, .star _ => PUnit
  | .yes g, .raw => LamLPortsClosed Aw tbl hA hb dl dr S σ ρ g
  | .no, _ => PSigma fun g => LamLPorts Aw tbl hA hb dl dr σ ρ g

/-- Right endpoint's residual — mirrors `LamLResidClosed`. -/
def LamRResidClosed (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    (r : LamRead Aw (dr.wt Aw) E n Γ A' b') → LamVerdict dr σ ρ r → Type
  | .yes g, .clause _ => LamRClPortsClosed Aw tbl hA hb dl dr S σ ρ g
  | .yes _, .star _ => PUnit
  | .yes g, .raw => LamRPortsClosed Aw tbl hA hb dl dr S σ ρ g
  | .no, _ => PSigma fun g => LamRPorts Aw tbl hA hb dl dr σ ρ g

/-- The whole-field residual: `(star, star)` is `PUnit`; a single `star`
    owes `LamStarResid` (the landed `PBit` pair or the `reg2` receipt);
    everything else is the two side residuals plus `LamBodyTag`, with
    `bit` weakened to the receipt-`PSum` on `.yes` reads only.  No
    premise is demanded outside the branch that consumes it. -/
def LamFieldResidClosed (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    (rL : LamRead Aw (dl.wt Aw) E n Γ A b) → LamVerdict dl σ ρ rL →
    (rR : LamRead Aw (dr.wt Aw) E n Γ A' b') → LamVerdict dr σ ρ rR → Type
  | .yes _, .star _, .yes _, .star _ => PUnit
  | .yes _, .star _, _, _ => LamStarResid hA hb dl dr S σ ρ
  | _, _, .yes _, .star _ => LamStarResid hA hb dl dr S σ ρ
  | rL, vL, rR, vR =>
      PProd (LamLResidClosed Aw tbl hA hb dl dr S σ ρ rL vL)
        (PProd (LamRResidClosed Aw tbl hA hb dl dr S σ ρ rR vR)
          (LamBodyTag u hb σ ρ))

/-! ## §3 the (b) discharges, receipt-parameterized -/

/-- `bit` on a `.yes g` left read from the `LamBitOccL` receipts:
    `BIT[tyCast (lamDomain dl)·H, hA.dl]` issued by `StepIH` through
    `Issues.occ_bitCoh`, with `g.u` identified as `lamDomain`'s level by
    `lamDomain_u_of_readLam`.  A conditional (b) discharge — used only
    where the caller supplied the receipts. -/
theorem lam_bitL_of_occ (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    {g : LamGot Aw (dl.wt Aw) E n Γ A b}
    (hread : readLam (envExt_refl E) Aw dl rfl = .yes g)
    (occ : LamBitOccL hA hb dl dr S σ ρ)
    (hq : Demand (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)) :
    levelIsZero (σ g.u) = levelIsZero (σ u) := by
  obtain ⟨hapA, -, hapdl, -⟩ := hq.ap
  have hapH : (((lamDomain dl rfl).hT ▸
      ((lamDomain dl rfl).he' ▸ (lamDomain dl rfl).H))).AssumpPref :=
    TyP.ap_castT (lamDomain dl rfl).hT ((lamDomain dl rfl).he' ▸
      (lamDomain dl rfl).H) ▸
      (TyP.ap_castS (lamDomain dl rfl).he' (lamDomain dl rfl).H ▸
        lamDomain_ap dl rfl hapdl)
  have hoccH' : P2Query.subAt
      (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ) 0 occ.pH =
        some (.ty ((lamDomain dl rfl).hT ▸
          ((lamDomain dl rfl).he' ▸ (lamDomain dl rfl).H))) := by
    simp only [dnode_ty_castT, dnode_ty_castS]
    exact occ.hoccH
  have hbit : BitCoh σ
      ((lamDomain dl rfl).hT ▸ ((lamDomain dl rfl).he' ▸ (lamDomain dl rfl).H))
      hA.dl :=
    es_issued_occ_bitCoh Aw tbl (CvP.lam E n Γ A A' b b' B u hA hb dl dr) rfl
      S σ ρ _ hA.dl occ.pH occ.pA hoccH' occ.hoccA hapH (assumpPref_dl hapA)
      hq ih
  exact lamDomain_u_of_readLam (envExt_refl E) Aw dl rfl hread ▸ hbit

/-- `bit` on a `.yes g` right read from the `LamBitOccR` receipts —
    mirrors `lam_bitL_of_occ`. -/
theorem lam_bitR_of_occ (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    {g : LamGot Aw (dr.wt Aw) E n Γ A' b'}
    (hread : readLam (envExt_refl E) Aw dr rfl = .yes g)
    (occ : LamBitOccR hA hb dl dr S σ ρ)
    (hq : Demand (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)) :
    levelIsZero (σ g.u) = levelIsZero (σ u) := by
  obtain ⟨hapA, -, -, hapdr⟩ := hq.ap
  have hapH : (((lamDomain dr rfl).hT ▸
      ((lamDomain dr rfl).he' ▸ (lamDomain dr rfl).H))).AssumpPref :=
    TyP.ap_castT (lamDomain dr rfl).hT ((lamDomain dr rfl).he' ▸
      (lamDomain dr rfl).H) ▸
      (TyP.ap_castS (lamDomain dr rfl).he' (lamDomain dr rfl).H ▸
        lamDomain_ap dr rfl hapdr)
  have hoccH' : P2Query.subAt
      (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ) 0 occ.pH =
        some (.ty ((lamDomain dr rfl).hT ▸
          ((lamDomain dr rfl).he' ▸ (lamDomain dr rfl).H))) := by
    simp only [dnode_ty_castT, dnode_ty_castS]
    exact occ.hoccH
  have hbit : BitCoh σ
      ((lamDomain dr rfl).hT ▸ ((lamDomain dr rfl).he' ▸ (lamDomain dr rfl).H))
      hA.dr :=
    es_issued_occ_bitCoh Aw tbl (CvP.lam E n Γ A A' b b' B u hA hb dl dr) rfl
      S σ ρ _ hA.dr occ.pH occ.pA hoccH' occ.hoccA hapH (assumpPref_dr hapA)
      hq ih
  exact lamDomain_u_of_readLam (envExt_refl E) Aw dr rfl hread ▸ hbit

/-- The single-`star` residual yields the proof-bit pair: `.inl` is the
    landed premise itself; `.inr` is the `dl.reg.2` `subAt` receipt, and
    `StepIH` + `Issues.occ_pb` supply both bits
    (`lam_issued_dl_reg_pb`/`lam_issued_dr_reg_pb`). -/
def lam_pbPair_of_starRes (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (res : LamStarResid hA hb dl dr S σ ρ)
    (hq : Demand (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)) :
    PLift (PBit σ ρ dl dl.reg.2 ∧ PBit σ ρ dr dl.reg.2) := by
  rcases res with pb | ⟨pReg, occReg⟩
  · exact pb
  · exact ⟨lam_issued_dl_reg_pb Aw tbl hA hb dl dr S σ ρ pReg occReg hq ih,
      lam_issued_dr_reg_pb Aw tbl hA hb dl dr S σ ρ pReg occReg hq ih⟩

/-- `bit` off the weakened left bundles: `.inl` is the landed premise;
    `.inr` goes through `lam_bitL_of_occ`. -/
theorem lam_bitL_of_psum (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    {g : LamGot Aw (dl.wt Aw) E n Γ A b}
    (hread : readLam (envExt_refl E) Aw dl rfl = .yes g)
    (bit : PSum (levelIsZero (σ g.u) = levelIsZero (σ u))
      (LamBitOccL hA hb dl dr S σ ρ))
    (hq : Demand (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)) :
    levelIsZero (σ g.u) = levelIsZero (σ u) := by
  rcases bit with hbit | occ
  · exact hbit
  · exact lam_bitL_of_occ Aw tbl hA hb dl dr S σ ρ hread occ hq ih

/-- `bit` off the weakened right bundles — mirrors `lam_bitL_of_psum`. -/
theorem lam_bitR_of_psum (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    {g : LamGot Aw (dr.wt Aw) E n Γ A' b'}
    (hread : readLam (envExt_refl E) Aw dr rfl = .yes g)
    (bit : PSum (levelIsZero (σ g.u) = levelIsZero (σ u))
      (LamBitOccR hA hb dl dr S σ ρ))
    (hq : Demand (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)) :
    levelIsZero (σ g.u) = levelIsZero (σ u) := by
  rcases bit with hbit | occ
  · exact hbit
  · exact lam_bitR_of_occ Aw tbl hA hb dl dr S σ ρ hread occ hq ih

/-! ## §4 the field theorem under the branch-scoped residual -/

/-- `es_lam` under `LamFieldResidClosed`: identical in shape to
    `es_lam_field`, but `bit` may be supplied as raw receipt data (`.inr`)
    on `.yes` reads and the single-`star` `PBit` pair may be supplied as
    a `dl.reg.2` `subAt` receipt (`.inr`).  `(star, star)` stays `PUnit`;
    `none` branches keep the landed `LamLPorts`/`LamRPorts` wholesale;
    no receipt is ever demanded of a branch that cannot use it. -/
theorem es_lam_closed (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (resid : LamFieldResidClosed Aw tbl hA hb dl dr S σ ρ
      (readLam (envExt_refl E) Aw dl rfl)
      (epsReadLam (envExt_refl E) Aw σ dl rfl ρ)
      (readLam (envExt_refl E) Aw dr rfl)
      (epsReadLam (envExt_refl E) Aw σ dr rfl ρ)) :
    CaseStep Aw tbl (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ) := by
  intro hq ih
  -- Make both reads' indices variables so the indexed `cases` unify;
  -- keep the read equations for `lamDomain_u_of_readLam`.
  have key : PSigma fun (rL : LamRead Aw (dl.wt Aw) E n Γ A b) =>
      PSigma fun (vL : LamVerdict dl σ ρ rL) =>
      PSigma fun (_ : rL = readLam (envExt_refl E) Aw dl rfl) =>
      PSigma fun (rR : LamRead Aw (dr.wt Aw) E n Γ A' b') =>
      PSigma fun (vR : LamVerdict dr σ ρ rR) =>
      PSigma fun (_ : rR = readLam (envExt_refl E) Aw dr rfl) =>
        LamFieldResidClosed Aw tbl hA hb dl dr S σ ρ rL vL rR vR :=
    ⟨readLam (envExt_refl E) Aw dl rfl,
      epsReadLam (envExt_refl E) Aw σ dl rfl ρ, rfl,
      readLam (envExt_refl E) Aw dr rfl,
      epsReadLam (envExt_refl E) Aw σ dr rfl ρ, rfl, resid⟩
  obtain ⟨rL, vL, hrL, rR, vR, hrR, res⟩ := key
  cases vL with
  | clause hL =>
      cases vR with
      | clause hR =>
          have hbitL := lam_bitL_of_psum Aw tbl hA hb dl dr S σ ρ
            hrL.symm res.1.bit hq ih
          have hbitR := lam_bitR_of_psum Aw tbl hA hb dl dr S σ ρ
            hrR.symm res.2.1.bit hq ih
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨_, hL, _, hR, hbitL, hbitR, res.1.body, res.2.1.body,
              res.1.tag, res.2.1.tag, res.2.2⟩ hq ih
      | star hR =>
          have pbPair := lam_pbPair_of_starRes Aw tbl hA hb dl dr S σ ρ
            res hq ih
          show ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)
          rw [pbPair.down.1.mpr (pbPair.down.2.mp hR), hR]
          exact ConvMod.refl _
      | raw =>
          have hbitL := lam_bitL_of_psum Aw tbl hA hb dl dr S σ ρ
            hrL.symm res.1.bit hq ih
          have hbitR := lam_bitR_of_psum Aw tbl hA hb dl dr S σ ρ
            hrR.symm res.2.1.bit hq ih
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨_, hL, _, res.2.1.eps, hbitL, hbitR, res.1.body,
              res.2.1.body, res.1.tag, res.2.1.tag, res.2.2⟩ hq ih
      | none =>
          have hbitL := lam_bitL_of_psum Aw tbl hA hb dl dr S σ ρ
            hrL.symm res.1.bit hq ih
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨_, hL, res.2.1.1, res.2.1.2.eps, hbitL, res.2.1.2.bit,
              res.1.body, res.2.1.2.body, res.1.tag, res.2.1.2.tag, res.2.2⟩
              hq ih
  | star hL =>
      cases vR with
      | clause hR =>
          have pbPair := lam_pbPair_of_starRes Aw tbl hA hb dl dr S σ ρ
            res hq ih
          show ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)
          rw [hL, pbPair.down.2.mpr (pbPair.down.1.mp hL)]
          exact ConvMod.refl _
      | star hR =>
          show ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)
          rw [hL, hR]
          exact ConvMod.refl _
      | raw =>
          have pbPair := lam_pbPair_of_starRes Aw tbl hA hb dl dr S σ ρ
            res hq ih
          show ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)
          rw [hL, pbPair.down.2.mpr (pbPair.down.1.mp hL)]
          exact ConvMod.refl _
      | none =>
          have pbPair := lam_pbPair_of_starRes Aw tbl hA hb dl dr S σ ρ
            res hq ih
          show ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)
          rw [hL, pbPair.down.2.mpr (pbPair.down.1.mp hL)]
          exact ConvMod.refl _
  | raw =>
      cases vR with
      | clause hR =>
          have hbitL := lam_bitL_of_psum Aw tbl hA hb dl dr S σ ρ
            hrL.symm res.1.bit hq ih
          have hbitR := lam_bitR_of_psum Aw tbl hA hb dl dr S σ ρ
            hrR.symm res.2.1.bit hq ih
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨_, res.1.eps, _, hR, hbitL, hbitR, res.1.body,
              res.2.1.body, res.1.tag, res.2.1.tag, res.2.2⟩ hq ih
      | star hR =>
          have pbPair := lam_pbPair_of_starRes Aw tbl hA hb dl dr S σ ρ
            res hq ih
          show ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)
          rw [pbPair.down.1.mpr (pbPair.down.2.mp hR), hR]
          exact ConvMod.refl _
      | raw =>
          have hbitL := lam_bitL_of_psum Aw tbl hA hb dl dr S σ ρ
            hrL.symm res.1.bit hq ih
          have hbitR := lam_bitR_of_psum Aw tbl hA hb dl dr S σ ρ
            hrR.symm res.2.1.bit hq ih
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨_, res.1.eps, _, res.2.1.eps, hbitL, hbitR, res.1.body,
              res.2.1.body, res.1.tag, res.2.1.tag, res.2.2⟩ hq ih
      | none =>
          have hbitL := lam_bitL_of_psum Aw tbl hA hb dl dr S σ ρ
            hrL.symm res.1.bit hq ih
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨_, res.1.eps, res.2.1.1, res.2.1.2.eps, hbitL,
              res.2.1.2.bit, res.1.body, res.2.1.2.body, res.1.tag,
              res.2.1.2.tag, res.2.2⟩ hq ih
  | none =>
      cases vR with
      | clause hR =>
          have hbitR := lam_bitR_of_psum Aw tbl hA hb dl dr S σ ρ
            hrR.symm res.2.1.bit hq ih
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨res.1.1, res.1.2.eps, _, hR, res.1.2.bit, hbitR,
              res.1.2.body, res.2.1.body, res.1.2.tag, res.2.1.tag, res.2.2⟩
              hq ih
      | star hR =>
          have pbPair := lam_pbPair_of_starRes Aw tbl hA hb dl dr S σ ρ
            res hq ih
          show ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)
          rw [pbPair.down.1.mpr (pbPair.down.2.mp hR), hR]
          exact ConvMod.refl _
      | raw =>
          have hbitR := lam_bitR_of_psum Aw tbl hA hb dl dr S σ ρ
            hrR.symm res.2.1.bit hq ih
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨res.1.1, res.1.2.eps, _, res.2.1.eps, res.1.2.bit,
              hbitR, res.1.2.body, res.2.1.body, res.1.2.tag, res.2.1.tag,
              res.2.2⟩ hq ih
      | none =>
          exact es_lam Aw tbl hA hb dl dr S σ ρ
            ⟨res.1.1, res.1.2.eps, res.2.1.1, res.2.1.2.eps,
              res.1.2.bit, res.2.1.2.bit, res.1.2.body, res.2.1.2.body,
              res.1.2.tag, res.2.1.2.tag, res.2.2⟩ hq ih

/-! ## §5 non-vacuity — the canonical bare-lam fixture and receipt paths -/

-- The canonical fixture: a bare `TyP.lam` over sort domains at the
-- empty scope — the shape on which the audit's counterexample showed
-- `reg2` absent.
namespace EslamFix

abbrev S0 : Expr Nat := .sort .zero
abbrev S1 : Expr Nat := .sort (.succ .zero)
abbrev S2 : Expr Nat := .sort (.succ (.succ .zero))

def dS0 : TyP emptyEnv 0 [] S0 S1 :=
  TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _)
def hA_can : CvP emptyEnv 0 [] S0 S0 S1 :=
  CvP.sorts emptyEnv 0 [] .zero .zero (eqN_refl _) dS0 dS0
def dS0_ctx : TyP emptyEnv 0 [.assumption S0] S0 S1 :=
  TyP.sort emptyEnv 0 [.assumption S0] .zero (.succ .zero) (eqN_refl _)
def dS1_ctx : TyP emptyEnv 0 [.assumption S0] S1 S2 :=
  TyP.sort emptyEnv 0 [.assumption S0] (.succ .zero) (.succ (.succ .zero))
    (eqN_refl _)
def hb_can : CvP emptyEnv 0 [.assumption S0] S0 S0 S1 :=
  CvP.sorts emptyEnv 0 [.assumption S0] .zero .zero (eqN_refl _)
    dS0_ctx dS0_ctx
def dl_can : TyP emptyEnv 0 [] (.lam S0 S0) (.pi S0 S1) :=
  TyP.lam emptyEnv 0 [] S0 (.succ .zero) S0 S1 (.succ (.succ .zero))
    dS0 dS0_ctx dS1_ctx

/-- A concrete `LamGot` at the canonical fixture — the `got` port is
    inhabited (the atom bound holds: `dS0_ctx`'s only atom is `1 < 4`). -/
def lamGotSort : LamGot id (dl_can.wt id) emptyEnv 0 [] S0 S0 where
  B := S1
  u := .succ .zero
  hbody := dS0_ctx
  lt := by
    intro y hy
    have hmem : y ∈ [1] := hy
    have hy1 : y = 1 := List.mem_singleton.mp hmem
    have hw : dl_can.wt id = 4 := rfl
    omega

/-- The canonical `es_lam` query at the fixture. -/
abbrev query : P2Query emptyEnv :=
  .es (CvP.lam emptyEnv 0 [] S0 S0 S0 S0 S1 (.succ .zero)
    hA_can hb_can dl_can dl_can) nilScope id []

end EslamFix

open EslamFix

/-- `eps` is inhabited at the fixture: `dl_can.eps` computes to
    `.lam (.sort .zero)` — exactly `lamClauseOf lamGotSort`. -/
theorem lam_eps_at_sort_lam :
    dl_can.eps id [] = lamClauseOf lamGotSort id [] := rfl

/-- `tag` is inhabited at the fixture — both sides are `dS0_ctx`'s
    erasure. -/
theorem lam_tag_at_sort_lam :
    (lamGotSort.hbody.eps id
        (binderDisp (levelIsZero (id lamGotSort.u)) :: []) = .star) ↔
      (hb_can.dl.eps id
        (binderDisp (levelIsZero (id lamGotSort.u)) :: []) = .star) :=
  Iff.rfl

/-- `bodyTag` is inhabited at the fixture — `hb_can.dl = hb_can.dr =
    dS0_ctx`. -/
theorem lam_bodyTag_at_sort_lam : LamBodyTag (.succ .zero) hb_can id [] :=
  Iff.rfl

/-- The `domL` receipt holds at the canonical fixture: `dl`'s domain
    source `dS0` sits at payload path `[2,0]` (`dl` is `.cv`-child `2`,
    `hA₀` its first `.ty` child). -/
theorem lam_dom_occ_at_sort_lam :
    P2Query.subAt EslamFix.query 0 [2, 0] =
      some (.ty (lamDomain dl_can rfl).H) := rfl

/-- The `domR` receipt holds at the canonical fixture — `[3,0]` of the
    right endpoint (`dr = dl_can`). -/
theorem lam_domR_occ_at_sort_lam :
    P2Query.subAt EslamFix.query 0 [3, 0] =
      some (.ty (lamDomain dl_can rfl).H) := rfl

/-- The `hAdl` receipt holds at the canonical fixture: `hA_can.dl` is
    `dS0`, `.cv`-child `0`'s first `.ty` child — `[0,0]`. -/
theorem lam_hAdl_occ_at_sort_lam :
    P2Query.subAt EslamFix.query 0 [0, 0] =
      some (.ty hA_can.dl) := rfl

/-- The `hAdr` receipt holds at the canonical fixture — `[0,1]`. -/
theorem lam_hAdr_occ_at_sort_lam :
    P2Query.subAt EslamFix.query 0 [0, 1] =
      some (.ty hA_can.dr) := rfl

/-- Both `LamBitOcc` bundles are inhabited at the canonical fixture —
    concrete inhabitants for the `.inr` legs of the weakened `bit`s. -/
def lamBitOccL_can : LamBitOccL hA_can hb_can dl_can dl_can nilScope id [] :=
  ⟨[2, 0], rfl, [0, 0], rfl⟩

def lamBitOccR_can : LamBitOccR hA_can hb_can dl_can dl_can nilScope id [] :=
  ⟨[3, 0], rfl, [0, 1], rfl⟩

/-- The `reg2` receipt is **absent** at the canonical fixture: every
    payload `subAt` path either misses, or lands on `dS0`/`dS0_ctx`/
    `dS1_ctx`/`dl_can` itself — never the freshly synthesized
    `dl_can.reg.2` (`TyP.pi …`).  This is why `reg2` is a `PSum` leg of
    the single-`star` residual and not a premise: on this shape a caller
    must supply the landed `.inl` proof-bit pair. -/
theorem lam_reg2_absent_at_sort_lam (p : List Nat) :
    P2Query.subAt EslamFix.query 0 p ≠ some (.ty dl_can.reg.2) := by
  have hne0 : DNode.ty dS0 ≠ DNode.ty dl_can.reg.2 := fun h => by cases h
  have hne1 : DNode.ty dS0_ctx ≠ DNode.ty dl_can.reg.2 := fun h => by cases h
  have hne2 : DNode.ty dS1_ctx ≠ DNode.ty dl_can.reg.2 := fun h => by cases h
  have hneL : DNode.ty dl_can ≠ DNode.ty dl_can.reg.2 := fun h => by cases h
  match p with
  | [] | [0] | [1] => intro hp; cases hp
  | [2] | [3] => intro hp; exact hneL (Option.some.inj hp)
  | (_ + 4) :: _ => intro hp; exact Option.noConfusion hp
  | [0, 0] | [0, 1] | [2, 0] | [3, 0] =>
      intro hp; exact hne0 (Option.some.inj hp)
  | [1, 0] | [1, 1] | [2, 1] | [3, 1] =>
      intro hp; exact hne1 (Option.some.inj hp)
  | [2, 2] | [3, 2] => intro hp; exact hne2 (Option.some.inj hp)
  | 0 :: (_ + 2) :: _ | 1 :: (_ + 2) :: _ =>
      intro hp; exact Option.noConfusion hp
  | 2 :: (_ + 3) :: _ | 3 :: (_ + 3) :: _ =>
      intro hp; exact Option.noConfusion hp
  | 0 :: 0 :: _ :: _ | 0 :: 1 :: _ :: _
  | 1 :: 0 :: _ :: _ | 1 :: 1 :: _ :: _
  | 2 :: 0 :: _ :: _ | 2 :: 1 :: _ :: _ | 2 :: 2 :: _ :: _
  | 3 :: 0 :: _ :: _ | 3 :: 1 :: _ :: _ | 3 :: 2 :: _ :: _ =>
      intro hp; exact Option.noConfusion hp

/-- `domL` is satisfiable generally at a bare `TyP.lam` left endpoint —
    payload path `[2,0]`. -/
theorem lam_dom_occ_direct
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A A' b b' B : Expr Nat} {u u₀ v₀ : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (hA₀ : TyP E n Γ A (.sort u₀))
    (hb₀ : TyP E n (.assumption A :: Γ) b B)
    (hB₀ : TyP E n (.assumption A :: Γ) B (.sort v₀))
    (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    P2Query.subAt
      (.es (CvP.lam E n Γ A A' b b' B u hA hb
        (TyP.lam E n Γ A u₀ b B v₀ hA₀ hb₀ hB₀) dr) S σ ρ) 0 [2, 0] =
      some (.ty (lamDomain
        (TyP.lam E n Γ A u₀ b B v₀ hA₀ hb₀ hB₀) rfl).H) := rfl

/-- `domR` is satisfiable generally — `[3,0]` at a reflexive domain
    (`dr`'s ascribed `.pi A B` forces `A' = A` on a bare `TyP.lam`). -/
theorem lam_domR_occ_direct
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A b b' B : Expr Nat} {u u₀ v₀ : Level}
    (hA : CvP E n Γ A A (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B))
    (hA₀ : TyP E n Γ A (.sort u₀))
    (hb₀ : TyP E n (.assumption A :: Γ) b' B)
    (hB₀ : TyP E n (.assumption A :: Γ) B (.sort v₀))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    P2Query.subAt
      (.es (CvP.lam E n Γ A A b b' B u hA hb dl
        (TyP.lam E n Γ A u₀ b' B v₀ hA₀ hb₀ hB₀)) S σ ρ) 0 [3, 0] =
      some (.ty (lamDomain
        (TyP.lam E n Γ A u₀ b' B v₀ hA₀ hb₀ hB₀) rfl).H) := rfl

/-- `hAdl` is satisfiable generally: at a `.refl`-headed domain
    conversion `hA.dl` is `.cv`-child `0`'s second `.ty` child —
    `[0,1]`. -/
theorem lam_hAdl_occ_refl
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A b b' B : Expr Nat} {u : Level}
    (ht dA dA' : TyP E n Γ A (.sort u))
    (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    P2Query.subAt
      (.es (CvP.lam E n Γ A A b b' B u
        (CvP.refl E n Γ A (.sort u) ht dA dA') hb dl dr) S σ ρ) 0 [0, 1] =
      some (.ty (CvP.refl E n Γ A (.sort u) ht dA dA').dl) := rfl

/-- `hAdr` is satisfiable generally — `[0,2]` of the same `.refl` head. -/
theorem lam_hAdr_occ_refl
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A b b' B : Expr Nat} {u : Level}
    (ht dA dA' : TyP E n Γ A (.sort u))
    (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    P2Query.subAt
      (.es (CvP.lam E n Γ A A b b' B u
        (CvP.refl E n Γ A (.sort u) ht dA dA') hb dl dr) S σ ρ) 0 [0, 2] =
      some (.ty (CvP.refl E n Γ A (.sort u) ht dA dA').dr) := rfl

/-- `reg2` is satisfiable generally — it is ctor-shape-indexed.  At a
    `conv`-headed `dl` whose conversion is `.refl`, `dl.reg.2` IS the
    `refl`'s `dr` (`TyP.reg`'s `conv` case reads `hc.dr`), at
    `[2,1,2]`. -/
theorem lam_reg2_occ_conv
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A A' b b' B : Expr Nat} {u w : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (h : TyP E n Γ (.lam A b) (.pi A B))
    (ht : TyP E n Γ (.pi A B) (.sort w))
    (dL dR : TyP E n Γ (.pi A B) (.sort w))
    (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    P2Query.subAt
      (.es (CvP.lam E n Γ A A' b b' B u hA hb
        (TyP.conv E n Γ (.lam A b) (.pi A B) (.pi A B) w h
          (CvP.refl E n Γ (.pi A B) (.sort w) ht dL dR)) dr) S σ ρ)
        0 [2, 1, 2] =
      some (.ty (TyP.conv E n Γ (.lam A b) (.pi A B) (.pi A B) w h
        (CvP.refl E n Γ (.pi A B) (.sort w) ht dL dR)).reg.2) := rfl

/-- `body` is satisfiable — a `CL` against the same derivation is
    `ConvMod.refl`. -/
theorem lam_bodyCl_self (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) (σ : Level → Level) (ρ : List Disp) :
    CL tbl σ ρ D D := ConvMod.refl _

/-- `tag`/`tagR` hold whenever the two erasures are equal. -/
theorem lam_tag_of_eps_eq {x y : ETm} (h : x = y) :
    (x = .star) ↔ (y = .star) :=
  ⟨fun hl => h ▸ hl, fun hr => h.symm ▸ hr⟩

/-- `bodyTag` holds whenever `hb`'s two endpoint erasures are equal. -/
theorem lam_bodyTag_of_eps_eq
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A b b' B : Expr Nat} {u : Level}
    (hb : CvP E n (.assumption A :: Γ) b b' B) {σ : Level → Level} {ρ : List Disp}
    (h : hb.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) =
      hb.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ)) :
    LamBodyTag u hb σ ρ :=
  ⟨fun hl => h ▸ hl, fun hr => h.symm ▸ hr⟩

#print axioms Rcic.Syn.LamBitOccL
#print axioms Rcic.Syn.LamBitOccR
#print axioms Rcic.Syn.LamStarResid
#print axioms Rcic.Syn.LamLClPortsClosed
#print axioms Rcic.Syn.LamLPortsClosed
#print axioms Rcic.Syn.LamRClPortsClosed
#print axioms Rcic.Syn.LamRPortsClosed
#print axioms Rcic.Syn.LamLResidClosed
#print axioms Rcic.Syn.LamRResidClosed
#print axioms Rcic.Syn.LamFieldResidClosed
#print axioms Rcic.Syn.lam_bitL_of_occ
#print axioms Rcic.Syn.lam_bitR_of_occ
#print axioms Rcic.Syn.lam_pbPair_of_starRes
#print axioms Rcic.Syn.lam_bitL_of_psum
#print axioms Rcic.Syn.lam_bitR_of_psum
#print axioms Rcic.Syn.es_lam_closed
#print axioms Rcic.Syn.EslamFix.dS0
#print axioms Rcic.Syn.EslamFix.hA_can
#print axioms Rcic.Syn.EslamFix.dS0_ctx
#print axioms Rcic.Syn.EslamFix.dS1_ctx
#print axioms Rcic.Syn.EslamFix.hb_can
#print axioms Rcic.Syn.EslamFix.dl_can
#print axioms Rcic.Syn.EslamFix.lamGotSort
#print axioms Rcic.Syn.lam_eps_at_sort_lam
#print axioms Rcic.Syn.lam_tag_at_sort_lam
#print axioms Rcic.Syn.lam_bodyTag_at_sort_lam
#print axioms Rcic.Syn.lam_dom_occ_at_sort_lam
#print axioms Rcic.Syn.lam_domR_occ_at_sort_lam
#print axioms Rcic.Syn.lam_hAdl_occ_at_sort_lam
#print axioms Rcic.Syn.lam_hAdr_occ_at_sort_lam
#print axioms Rcic.Syn.lamBitOccL_can
#print axioms Rcic.Syn.lamBitOccR_can
#print axioms Rcic.Syn.lam_reg2_absent_at_sort_lam
#print axioms Rcic.Syn.lam_dom_occ_direct
#print axioms Rcic.Syn.lam_domR_occ_direct
#print axioms Rcic.Syn.lam_hAdl_occ_refl
#print axioms Rcic.Syn.lam_hAdr_occ_refl
#print axioms Rcic.Syn.lam_reg2_occ_conv
#print axioms Rcic.Syn.lam_bodyCl_self
#print axioms Rcic.Syn.lam_tag_of_eps_eq
#print axioms Rcic.Syn.lam_bodyTag_of_eps_eq

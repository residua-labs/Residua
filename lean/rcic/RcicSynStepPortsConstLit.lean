import rcic.RcicSynStepFields1
import rcic.RcicSynStepFields4

/-!
# `StepSuppliers` port discharge — `es_lit`, `es_consts` (ct001 sortrow wave)

Spec: `~/.residua-lean/briefs/sortrow-ports.md` over the field measure
`~/.residua-lean/briefs/stepsuppliers-measure.md`.  Each `*_field` theorem below
repeats the field's EXACT `StepSuppliers` statement (`RcicSynStepSkeleton.lean`
:358 `es_consts` / :433 `es_lit`) proved from the landed closer with every
dischargeable port closed; the remaining ports are the explicit named
hypotheses, one per line, with their exact statements.

## `es_lit` — closer `lit_caseStep_of_surface_cl` (`RcicSynStepFields1.lean:91`)

| port | class | disposition |
|---|---|---|
| `Dlit` | (c) provable | the canonical `TyP.lit` surface `litSurface` below: `cases hlit` pins `exp := natExpand t` (`LiteralExpansion.of` is the only ctor, `RcicDeclarative.lean:2561`), then `TyP.lit … hexp` (`RcicConvPlus.lean:99`) |
| `hmid` | (c) provable | `litSurface_eps` — `rfl` on the `.lit` arm of `TyP.eps` (`RcicSynErase.lean:195`) |
| `hL : CL tbl σ ρ dl Dlit` | (d) retained | `lit_issued_cl_variants` (`RcicSynStepFields1.lean:111`) proves every `.cl` child the `lit` node issues is an `occ_cl` pair or `lit_cl`; `lit_cl` is the OTHER half `CL hexp dr`, supplied by `lit_issued_expansion_cl` (`:74`) from `StepIH` via `below_lit`.  The freshly built `.lit t` surface never sits at a payload `subAt` position (`RcicSynP2Shared` §G), and `rootCl` pins `ρ = S.can σ` — arbitrary here.  Not (b)-issuable: adding a `.cl` row for `lit` would falsify the landed `lit_issued_cl_variants`. |

## `es_consts` — closer `consts_caseStep_of_ports` (`RcicSynStepFields4.lean:1718`)

Via `ConstsPorts.ofRegSurfaces` (`:1673`), which fixes the two ascription
typings at the endpoints' own regularity receipts:

| port | class | disposition |
|---|---|---|
| `uL uR` | (c) | `dl.reg.1` / `dr.reg.1` |
| `hTL hTR` | (c) | `dl.reg.2` / `dr.reg.2` |
| `wtL wtR` | (c) | `TyP.wt_reg_le` + `omega` inside `ofRegSurfaces` |
| `apL apR` | (c) | `assumpPref_reg` of `dl.AssumpPref` / `dr.AssumpPref`, read off `Demand.ap hq`: `P2Query.AP` of an `.es` node is the `CvP`'s `AssumpPref` (`RcicSynP2Shared.lean:288`), whose `consts` arm is `dl.AssumpPref ∧ dr.AssumpPref` (`RcicSynLetInline.lean:128`) |
| `pL pR`, `occL occR` | (d) retained | occurrence receipts of `dl.reg.2` / `dr.reg.2` inside the node's payload.  `TyP.reg`/`TyP.dchildren` pattern-match the derivation ctor (`RcicConvPlus.lean:429`, `RcicSynSlotKind.lean:146`), so for arbitrary `dl`/`dr` no literal path resolves uniformly — the paths exist only once the endpoint shape is fixed (cf. `es_consts_direct` `:1461`, where `dl`/`dr` ARE `TyP.const` nodes and `[0,0]`/`[1,0]` work).  Not (a)/(b): `occ_*` rows *consume* paths, none mint one. |
| `leftCl rightCl` | (d) retained | `CL` against the freshly built canonical surfaces `constsCanonLeft`/`constsCanonRight`; `consts_issued_cl_is_occurrence` (`RcicSynStepFields4.lean:1748`) proves every `.cl` child the node issues is an `occ_cl` pair, and a freshly built `TyP.const` is never at a payload `subAt` position. |

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-- The canonical `.lit t` surface for `es_lit`'s retained `CL` port: the
    `TyP.lit` node over the field's own expansion typing.  `cases hlit` pins
    `exp := natExpand t` (`LiteralExpansion` has the single ctor `of`), making
    `hexp` a `TyP … (natExpand t) T` — the exact argument `TyP.lit` wants. -/
def litSurface {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {exp T : Expr Nat}
    (hlit : LiteralExpansion t exp) (hexp : TyP E n Γ exp T) : TyP E n Γ (.lit t) T := by
  cases hlit
  exact TyP.lit E n Γ t T hexp

/-- The canonical surface's erasure is the expansion's (`TyP.eps` `.lit` arm) —
    `lit_caseStep_of_surface_cl`'s `hmid` port, discharged. -/
theorem litSurface_eps {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat}
    {exp T : Expr Nat} (hlit : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
    (σ : Level → Level) (ρ : List Disp) :
    (litSurface hlit hexp).eps σ ρ = hexp.eps σ ρ := by
  cases hlit
  rfl

/-- `es_lit` discharged modulo its one genuine port: `CL` of the literal's
    stored endpoint `dl` against the canonical `.lit t` surface
    `litSurface hlit hexp` — the `lit.surfaceCL` obligation of
    `BELOWC_DEMAND_GRAMMAR_CONTINUATION.md` §3.3. -/
theorem es_lit_field
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t : Nat} {exp T : Expr Nat}
    (hlit : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
    (dl : TyP E n Γ (.lit t) T) (dr : TyP E n Γ exp T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hL : CL tbl σ ρ dl (litSurface hlit hexp)) :
    CaseStep Aw tbl (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ) :=
  lit_caseStep_of_surface_cl Aw tbl hlit hexp dl dr S σ ρ
    (litSurface hlit hexp) hL (litSurface_eps hlit hexp σ ρ)

/-- `es_consts` discharged modulo the occurrence receipts and the two canonical
    `CL`s.  `ConstsPorts.ofRegSurfaces` fixes `uL uR hTL hTR` at `dl.reg`/`dr.reg`
    and discharges `wtL wtR apL apR` — the `AssumpPref`s coming from `hq.ap`
    (the demanded node's `CvP.AssumpPref` is the `dl`/`dr` pair). -/
theorem es_consts_field
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pL pR : List Nat)
    (occL :
      P2Query.subAt (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr) S σ ρ)
        0 pL = some (.ty dl.reg.2))
    (occR :
      P2Query.subAt (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr) S σ ρ)
        0 pR = some (.ty dr.reg.2))
    (leftCl : CL tbl σ ρ dl (constsCanonLeft hres hlen hwf dl))
    (rightCl : CL tbl σ ρ dr (constsCanonRight hres hlen hwf' hls dr)) :
    CaseStep Aw tbl (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr) S σ ρ) :=
  fun hq ih =>
    consts_caseStep_of_ports Aw tbl hres hlen hwf hwf' hls dl dr S σ ρ
      (ConstsPorts.ofRegSurfaces Aw tbl hres hlen hwf hwf' hls dl dr S σ ρ
        pL pR occL occR hq.ap.1 hq.ap.2 leftCl rightCl)
      hq ih

#print axioms Rcic.Syn.litSurface
#print axioms Rcic.Syn.litSurface_eps
#print axioms Rcic.Syn.es_lit_field
#print axioms Rcic.Syn.es_consts_field

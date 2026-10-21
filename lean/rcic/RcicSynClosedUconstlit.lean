import rcic.RcicSynStepPortsConstLit
import rcic.RcicSynAdm

/-!
# `RcicSynClosedUconstlit` — `es_lit` + `es_consts` closed under their genuine walls

swe-constlit lane (sortRow `StepSuppliers` supplier group
`es_consts` + `es_lit`; closers `lit_caseStep_of_surface_cl`
`RcicSynStepFields1.lean:91`, `consts_caseStep_of_ports`
`RcicSynStepFields4.lean:1718` via `ConstsPorts.ofRegSurfaces` `:1673`).
`closure_claim = 0`.

## Discharge, measured on main 2026-10-19

`es_lit` (`RcicSynStepSkeleton.lean:433`):

| port | class | evidence |
|---|---|---|
| `Dlit` | (c) | `litSurface` (`RcicSynStepPortsConstLit.lean:49`) |
| `hmid` | (c) | `litSurface_eps` (`:57`) |
| `hL : CL tbl σ ρ dl (litSurface hlit hexp)` | (d) | **W `lit.surfaceCL`** (`BELOWC_DEMAND_GRAMMAR_CONTINUATION.md` §3.3). Not (b): `lit_issued_cl_variants` (`Fields1:111`) kernel-proves every issued `.cl` is `occ_cl` or `lit_cl`, and the freshly built surface sits at no payload `subAt` position (`DNode.subAt` resolves only real forest children). Not (c): `CL dl s` is `ConvMod` of `dl.eps`; an arbitrary `dl : TyP E n Γ (.lit t) T`'s erasure follows its derivation (`conv`/`ewk`/`cctx` pass through, `wk`/`esub`/`lsub`/`linst` transform, `TyP.eps` `RcicSynErase.lean:196–215`), and `AssumpPref` (`RcicSynLetInline.lean:102`) is only a transport-cutoff guard — it does not pin the ctor shape. |

`es_consts` (`RcicSynStepSkeleton.lean:358`):

| port | class | evidence |
|---|---|---|
| `uL uR`, `hTL hTR`, `wtL wtR`, `apL apR` | (c) | `ConstsPorts.ofRegSurfaces`: `dl.reg`/`dr.reg`, `TyP.wt_reg_le`, `assumpPref_reg` of `hq.ap` |
| `pL pR`, `occL occR` | (d) | occurrence receipts of `dl.reg.2`/`dr.reg.2`. The path is **ctor-shape-indexed**: `[0,0]`/`[1,0]` for direct `TyP.const` endpoints (`es_consts_direct` `Fields4:1461`), `[0,1,2]` through `.cv hc` for a `conv`-wrapped `dl` (`consts_reg_occ_conv` below), and for transport-shaped `dl` (`wk`/`esub`/`lsub`/`linst`/`ewk`/`cctx`) `reg.2` is a freshly built node (`TyP.reg` `RcicConvPlus.lean:441–458`) not literally in the forest — `consts_occL_refuted_conv` below refuses the direct path at a real `conv` fixture. No `Issues` row emits `.bitCoh dl.reg.2 dr.reg.2` from an `.es consts` parent — `consts_issued_cl_is_occurrence` (`Fields4:1748`) and the grammar itself (`Issues` `RcicSynP2Shared.lean:496`: the only `bitCoh`-emitting rows are `occ_bitCoh`, which *needs* the paths, `pb_bvar_bitCoh`, `head_leg*`, `bitCoh_cl_reg*`, `bitCoh_eut`). |
| `leftCl rightCl` | (d) | **W-COV-CONST-ASCRIPTION-LEVELS** (S21 §2, `RcicSynStepSkeleton.lean:357`). Same surfaceCL shape as `hL`: `constsCanonLeft`/`Right` are freshly built, never at payload positions, and `ConvMod (dl.eps) (canon.eps)` holds only once the recorded sort (`dl.reg.1`) and the erasure shape agree — for arbitrary `dl` undetermined. |

Non-vacuity: every retained port is inhabited at the canonical/direct fixture —
`lit_surfaceCl_witness`, `consts_ports_direct` (an actual `ConstsPorts` value).
Non-equivalence: each retained port is one leg of a midpoint decomposition —
`hL` says nothing about `hexp ↔ dr`; `occL/occR`+`leftCl/rightCl` say nothing
about the `BitCoh`/`mixedCL` middle they feed. `es_lit_at_surface` and
`es_consts_closed_direct` show the fields themselves inhabited.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-! ## §1 `es_lit` — closed under `lit.surfaceCL` -/

/-- `es_lit` with every (b)/(c) port discharged; the sole remaining premise is
    the named wall `lit.surfaceCL`: `CL` of the stored `.lit t` endpoint `dl`
    against the canonical surface `litSurface hlit hexp`. -/
theorem es_lit_closed
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t : Nat} {exp T : Expr Nat}
    (hlit : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
    (dl : TyP E n Γ (.lit t) T) (dr : TyP E n Γ exp T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hL : CL tbl σ ρ dl (litSurface hlit hexp)) :
    CaseStep Aw tbl (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ) :=
  es_lit_field Aw tbl hlit hexp dl dr S σ ρ hL

/-- **Non-vacuity witness** of `lit.surfaceCL`: the canonical surface itself
    satisfies the port — `CL` against itself is `ConvMod.refl`. -/
theorem lit_surfaceCl_witness
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {exp T : Expr Nat}
    (hlit : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
    (σ : Level → Level) (ρ : List Disp) :
    CL tbl σ ρ (litSurface hlit hexp) (litSurface hlit hexp) :=
  .refl _

/-- The `es_lit` field is inhabited: at the canonical endpoint `dl :=
    litSurface hlit hexp` the retained port is `refl` and the `CaseStep` is
    unconditional. -/
theorem es_lit_at_surface
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t : Nat} {exp T : Expr Nat}
    (hlit : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
    (dr : TyP E n Γ exp T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl (.es (CvP.lit E n Γ t exp T hlit hexp
      (litSurface hlit hexp) dr) S σ ρ) :=
  es_lit_closed Aw tbl hlit hexp _ dr S σ ρ (.refl _)

/-! ## §2 `es_consts` — closed under the ascription-levels wall -/

/-- `es_consts` with every (b)/(c) port discharged; the remaining premises are
    the named wall `W-COV-CONST-ASCRIPTION-LEVELS`: the occurrence receipts of
    the two endpoint regularities (`pL`/`occL`, `pR`/`occR`) and the two
    canonical-surface `CL`s (`leftCl`, `rightCl`). -/
theorem es_consts_closed
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
  es_consts_field Aw tbl hres hlen hwf hwf' hls dl dr S σ ρ pL pR occL occR leftCl rightCl

/-- **Non-vacuity witness** of `es_consts`' retained ports: at direct
    `TyP.const` endpoints the full `ConstsPorts` structure is inhabited —
    the regularities sit at the literal paths `[0,0]`/`[1,0]` (`TyP.reg` and
    `TyP.dchildren` of a `const` node compute) and the canonical `CL`s are
    `refl` (each canonical surface is the node itself, up to its proof fields). -/
noncomputable def consts_ports_direct
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {m : CheckedMember} {uL uR : Level}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (hresL : E.members r = some m) (hlenL : ls.length = m.arity)
    (hwfL : levelsBounded n ls = true) (heqL : eqNList ls ls)
    (hTL : TyP E n Γ (instantiateLevels ls m.mtype) (.sort uL))
    (hresR : E.members r = some m) (hlenR : ls'.length = m.arity)
    (hwfR : levelsBounded n ls' = true) (heqR : eqNList ls' ls)
    (hTR : TyP E n Γ (instantiateLevels ls m.mtype) (.sort uR))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hdl : (TyP.const E n Γ r ls ls m uL hresL hlenL hwfL heqL hTL).AssumpPref)
    (hdr : (TyP.const E n Γ r ls' ls m uR hresR hlenR hwfR heqR hTR).AssumpPref) :
    ConstsPorts Aw tbl hres hlen hwf hwf' hls
      (TyP.const E n Γ r ls ls m uL hresL hlenL hwfL heqL hTL)
      (TyP.const E n Γ r ls' ls m uR hresR hlenR hwfR heqR hTR) S σ ρ :=
  ConstsPorts.ofRegSurfaces Aw tbl hres hlen hwf hwf' hls _ _ S σ ρ
    [0, 0] [1, 0] rfl rfl hdl hdr (.refl _) (.refl _)

/-- The `es_consts` field is inhabited: the direct endpoints' port structure
    (`consts_ports_direct`) plugs into `consts_caseStep_of_ports` for an
    unconditional `CaseStep` — the landed `es_consts_direct`
    (`RcicSynStepFields4.lean:1461`) proves the same instance from the IH alone. -/
theorem es_consts_closed_direct
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {m : CheckedMember} {uL uR : Level}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (hresL : E.members r = some m) (hlenL : ls.length = m.arity)
    (hwfL : levelsBounded n ls = true) (heqL : eqNList ls ls)
    (hTL : TyP E n Γ (instantiateLevels ls m.mtype) (.sort uL))
    (hresR : E.members r = some m) (hlenR : ls'.length = m.arity)
    (hwfR : levelsBounded n ls' = true) (heqR : eqNList ls' ls)
    (hTR : TyP E n Γ (instantiateLevels ls m.mtype) (.sort uR))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls
      (TyP.const E n Γ r ls ls m uL hresL hlenL hwfL heqL hTL)
      (TyP.const E n Γ r ls' ls m uR hresR hlenR hwfR heqR hTR)) S σ ρ) :=
  fun hq ih =>
    consts_caseStep_of_ports Aw tbl hres hlen hwf hwf' hls _ _ S σ ρ
      (consts_ports_direct Aw tbl hres hlen hwf hwf' hls
        hresL hlenL hwfL heqL hTL hresR hlenR hwfR heqR hTR S σ ρ hq.ap.1 hq.ap.2)
      hq ih

/-- **Tooth — the `reg.2` occurrence path is ctor-shape-indexed.** For a
    `conv`-wrapped left endpoint `dl.reg.2` IS reachable — at `[0, 1, 2]`
    (through `.cv hc` of the `conv` child list), not at the direct `[0,0]`.
    The port is satisfiable, but no single literal serves arbitrary `dl`. -/
theorem consts_reg_occ_conv
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {m : CheckedMember} {u : Level}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (h : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (ht dl₀ dr₀ : TyP E n Γ (instantiateLevels ls m.mtype) (.sort u))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    P2Query.subAt
      (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls
        (TyP.conv E n Γ (.const r ls) (instantiateLevels ls m.mtype)
          (instantiateLevels ls m.mtype) u h
          (CvP.refl E n Γ (instantiateLevels ls m.mtype) (.sort u) ht dl₀ dr₀))
        dr) S σ ρ)
      0 [0, 1, 2] =
      some (.ty (TyP.conv E n Γ (.const r ls) (instantiateLevels ls m.mtype)
        (instantiateLevels ls m.mtype) u h
        (CvP.refl E n Γ (instantiateLevels ls m.mtype) (.sort u) ht dl₀ dr₀)).reg.2) := rfl

/-! ## §3 fixture tooth: the direct path provably fails for a wrapped `dl` -/

/-- A minimal member: one opaque arity-0 member whose type is `sort 1`. -/
def toothMember : CheckedMember := ⟨.opaqueM, 0, .sort (.succ .zero), none⟩

/-- Its one-member environment. -/
def toothEnv : ResolvedEnv := extendEnv emptyEnv 0 toothMember

/-- `sort 1 : sort 2` in `toothEnv`'s empty context. -/
def toothST : TyP toothEnv 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  TyP.sort toothEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

/-- `const 0 [] : sort 1` in `toothEnv` — `instantiateLevels []` is the identity. -/
def toothH : TyP toothEnv 0 [] (.const 0 []) (.sort (.succ .zero)) :=
  TyP.const toothEnv 0 [] 0 [] [] toothMember (.succ (.succ .zero))
    (members_extend_self emptyEnv 0 toothMember) rfl rfl (eqNList_refl []) toothST

/-- The reflexivity conversion `sort 1 ≡ sort 1` at `sort 2`. -/
def toothC : CvP toothEnv 0 [] (.sort (.succ .zero)) (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) :=
  CvP.refl toothEnv 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))
    toothST toothST toothST

/-- A `conv`-wrapped endpoint `const 0 [] : sort 1` — the `es_consts` `dl`
    shape the direct path does not serve. -/
def toothDl : TyP toothEnv 0 [] (.const 0 []) (.sort (.succ .zero)) :=
  TyP.conv toothEnv 0 [] (.const 0 []) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.succ (.succ .zero)) toothH toothC

/-- **Tooth — the direct path `[0,0]` provably does not satisfy `occL` for a
    `conv`-wrapped `dl`.** `[0,0]` resolves to `.ty toothH` (the wrapped
    derivation, subject `.const 0 []`) while `toothDl.reg.2` is `toothST`
    (subject `.sort 1`): the `some` equation would force `.const 0 [] =
    .sort 1`. The same receipt IS reachable at the shape-indexed `[0,1,2]`
    (`consts_reg_occ_conv`). -/
theorem consts_occL_refuted_conv
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (dr : TyP toothEnv 0 [] (.const 0 []) (.sort (.succ .zero))) :
    ¬ (P2Query.subAt
        (.es (CvP.consts toothEnv 0 [] 0 [] [] toothMember
          (members_extend_self emptyEnv 0 toothMember) rfl rfl rfl (eqNList_refl [])
          toothDl dr) S σ ρ)
        0 [0, 0] = some (.ty toothDl.reg.2)) := by
  intro h
  have hres : P2Query.subAt
      (.es (CvP.consts toothEnv 0 [] 0 [] [] toothMember
        (members_extend_self emptyEnv 0 toothMember) rfl rfl rfl (eqNList_refl [])
        toothDl dr) S σ ρ)
      0 [0, 0] = some (.ty toothH) := rfl
  rw [hres] at h
  cases Option.some.inj h

#print axioms Rcic.Syn.es_lit_closed
#print axioms Rcic.Syn.lit_surfaceCl_witness
#print axioms Rcic.Syn.es_lit_at_surface
#print axioms Rcic.Syn.es_consts_closed
#print axioms Rcic.Syn.consts_ports_direct
#print axioms Rcic.Syn.es_consts_closed_direct
#print axioms Rcic.Syn.consts_reg_occ_conv
#print axioms Rcic.Syn.toothMember
#print axioms Rcic.Syn.toothEnv
#print axioms Rcic.Syn.toothST
#print axioms Rcic.Syn.toothH
#print axioms Rcic.Syn.toothC
#print axioms Rcic.Syn.toothDl
#print axioms Rcic.Syn.consts_occL_refuted_conv

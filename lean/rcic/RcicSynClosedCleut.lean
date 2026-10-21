import rcic.RcicSynStepPortsClEut

/-!
# `cl_case`/`eut_case` supplier fields — per-cell closures + residual witnesses (swe-cleut)

Spec: `~/.residua-lean/briefs/swe-sortrow-common.md`; the landed field
assembly is `es_cl_field` / `es_eut_field` (`RcicSynStepPortsClEut.lean:108`/
`:243`), each the exact `StepSuppliers.cl_case` / `.eut_case` statement
(`RcicSynStepSkeleton.lean:504`/`:511`). `closure_claim = 0`.

## Discharged here (class (c), from `hTbl : TableWF tbl`)

`TableClosed tbl` is *definitionally* `TableWF.closed`
(`RcicSynCommute.lean:158` vs `RcicSynE.lean:527`), so the rule-table ports are
the `hTbl` data the assembly already supplies
(`step_of_suppliers_derivedMixed`, `RcicSynStepSkeleton.lean`):

| landed port field | type | closed by |
|---|---|---|
| `ClPiPorts.hTC`   (`RcicSynStepCore4.lean:444`) | `TableClosed tbl` | `hTbl.closed` |
| `EutPiPorts.hW`   (`RcicSynStepCore4.lean:825`) | `TableWF tbl` | `hTbl` |
| `EutLamPorts.hTC` (`RcicSynStepCore4.lean:874`) | `TableClosed tbl` | `hTbl.closed` |
| `EutAppPorts.hW`  (`RcicSynStepCore4.lean:927`) | `TableWF tbl` | `hTbl` |

## Per-cell closed theorems (audit 7692: no `∀`-lifted port premises)

Each `*_caseStep_of_ports` closer gets a `*_caseStep_closed` theorem that
quantifies **only over the cell's own data** (the two `TyP` derivations'
fields, `S`, `σ`, `ρ`) and names each retained port field as a plain
hypothesis — every one is satisfiable (see the `CleutWit` witnesses below).

The `const`/`const` cells keep their full side-conditions (`hres`, `hlen`,
`hwf`, `hls`): the two sides may carry different `CheckedMember`s, bridged
by `Option.some.inj` on the shared `hres` receipt, exactly as `constCell`
inside `es_cl_field`.

## Retained residuals (class (d)) — why `Issues` cannot name them

The full `Issues` grammar (`RcicSynP2Shared.lean:496–902`) only issues
same-site `(S, σ, ρ)` goals at `DNode.subAt` payload positions; the only
display-shifting rows are `.es`-bound, and `StepIH` answers *direct* issues
only. Retained, stated exactly as hypotheses of the per-cell theorems:

* `ClPiPorts.bodyCl`, `ClLamPorts.bodyCl`, `EutLamPorts.convB`:
  binder-display-shifted `CL`/`ConvMod` (`binderDisp … :: ρ` is not an
  issued display).
* `ClLamPorts.shape`, `ClAppPorts.shape`, `ClLetEPorts.{shape,bodyDrop,
  bodyInline}`: `★`-dichotomies of `eps` values — not `Goal` shapes at all.
* `ClConstPorts.hbit`: the cross-subject (`ls₁ ≠ ls₂`) gate bit.
* `EutConvLPorts.regCl` / `EutConvRPorts.regCl`: `CL` against `h.reg.2`, a
  `TyP.reg`-rebuilt derivation, not a `subAt` position.
* `EutPiPorts.{edgeL,edgeR}`: `reg.2`-vs-`sortNode` `CL`s (the
  `bitCoh_cl_regL/R` route that issues these lives on `.bitCoh` issuers,
  unreachable from `.eut` two hops away); `cohB : SortCoh σ hB₁ hB₂` is not
  a `Goal` shape.
* `EutAppPorts` minus `hW`: the Π-surface witnesses `hAᵢ hBᵢ` (`piInv` needs
  `CvWalkHyp E` at the derivation env — `.eut` queries can carry `E ≠` the
  frame env `E₀` of `S`, e.g. an `occ_eut` under an `ewk_es` child, so
  `S.env : EnvWfT E₀` cannot supply it) plus `hbit`, `piL`, `piR`,
  `instL`, `instR` — `reg.2`/`pi`-node/`instEnd` composites, all off the
  payload grid.
* `EutLetEPorts.{linkL,mid,linkR}`: `letSub`-rebuilt composites.
* `EutConstPorts.{adm,q₁,q₂}`: `TypeAdm E Aw r m` needs `EnvWfP E` at the
  derivation env and the ambient `Aw`; the admission views mention
  `adm.hT`, not a payload node.
* `clOther` / `eutOther` (the `clResidualTag`/`eutResidualTag` cells):
  non-`.conv` pairs with a transport-headed operand. Their port is a
  `CaseStep` at the cell — the one residual that is goal-shaped; the
  diagonal half is closed here outright (`cl_diag_caseStep`,
  `eut_diag_caseStep`), leaving the genuinely-different-operands cells open.

## Non-vacuity (compiled, `CleutWit`)

Every retained port type is inhabited; each witness is a `theorem` in the
`CleutWit` namespace, compiled on the empty environment's sort/bvar
derivations:

* `clPi_bodyCl_sat` — identical-body `CL` by `ConvMod.refl`.
* `clLamPorts_sat` — non-`★` `shape` branch (`.sort`-headed `eps`) + refl body.
* `clAppPorts_sat` — the all-non-`★` branch at `σ = fun _ ↦ .succ .zero`
  (`bvar`/`sort` erasures, never `★`).
* `clLetEPorts_sat` — non-`★` value `eps`, refl bodies.
* `clConstPorts_sat` — `ls₁ = ls₂` makes `hbit` vacuous.
* `eutConvLPorts_sat`, `eutConvRPorts_sat` — `reg.2` of a `.sort` leaf IS the
  canonical `sortNode` shape, so `regCl` is refl at a `CvP.refl`.
* `eutPi_edgeL_sat`, `eutPi_edgeR_sat` — a `bvar`-headed domain satisfies
  `isSortOrPiHead = false` and `reg.2 = hA` is `sortNode`-shaped.
* `eutPi_cohB_sat` — `SortCoh σ D D` is `eqN_refl`.
* `eutLam_convB_sat` — refl at the binder display.
* `eutApp_resid_sat` — the five residuals at once: `hT := instEnd hB ha hA`
  makes `instL`/`instR` refl, `hf := bvar` at the `pi` node makes
  `piL`/`piR` refl, `u₁ = u₂` makes `hbit` refl.
* `eutLetPorts_sat` — `hT := (letSub hb hv hA).reg.2` makes the links refl;
  `mid` is identical-`L` `EUT`.
* `eutConstPorts_sat` — `TypeAdm` at `E₀ = E = emptyEnv`, `Aw := fun _ ↦ 2`;
  `q₁`/`q₂` refl after `contextLift [] = id` and `instLevel [] = id`.
* `cl_residual_cell_sat`, `eut_residual_cell_sat` — a transport-headed
  residual cell (`wk`/`wk`, tag `= true` by `cl_residual_tag_wk`/
  `eut_residual_tag_wk`) is inhabited on the diagonal.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-! ## §1 `cl` cells — retained ports named at the cell's own data -/

/-- `cl` `pi`-`pi`: `hTC` discharged by `hTbl.closed`; the residual `bodyCl`
    is the body `CL` at the `binderDisp`-shifted display. -/
theorem cl_pi_pi_caseStep_closed (hTbl : TableWF tbl)
    {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {A B : Expr Nat}
    {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (bodyCl : CL tbl σ (binderDisp (levelIsZero (σ u₁)) :: ρ) hB₁ hB₂) :
    CaseStep Aw tbl
      (.cl (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁) (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂)
        S σ ρ) :=
  cl_pi_pi_caseStep_of_ports Aw tbl hA₁ hB₁ hA₂ hB₂ S σ ρ ⟨hTbl.closed, bodyCl⟩

/-- `cl` `lam`-`lam`: both `ClLamPorts` fields residual — body `CL` at the
    binder display and the `.keep`-display `★` split. -/
theorem cl_lam_lam_caseStep_closed
    {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {A body B₁ B₂ : Expr Nat}
    {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (bodyCl : CL tbl σ (binderDisp (levelIsZero (σ u₁)) :: ρ) hb₁ hb₂)
    (shape : (hb₁.eps σ (.keep :: ρ) = .star ∧ hb₂.eps σ (.keep :: ρ) = .star) ∨
        (hb₁.eps σ (.keep :: ρ) ≠ .star ∧ hb₂.eps σ (.keep :: ρ) ≠ .star)) :
    CaseStep Aw tbl
      (.cl (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) S σ ρ) :=
  cl_lam_lam_caseStep_of_ports Aw tbl hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ
    ⟨bodyCl, shape⟩

/-- `cl` `app`-`app`: the sole residual is `ClAppPorts.shape`, the
    `★`-shape three-way split. -/
theorem cl_app_app_caseStep_closed
    {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {f a A₁ B₁ A₂ B₂ : Expr Nat} {w₁ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (shape : (hf₁.eps σ ρ = .star ∧ hf₂.eps σ ρ = .star) ∨
        (ha₁.eps σ ρ = .star ∧ ha₂.eps σ ρ = .star) ∨
        (hf₁.eps σ ρ ≠ .star ∧ ha₁.eps σ ρ ≠ .star ∧
          hf₂.eps σ ρ ≠ .star ∧ ha₂.eps σ ρ ≠ .star)) :
    CaseStep Aw tbl
      (.cl (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
        (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) S σ ρ) :=
  cl_app_app_caseStep_of_ports Aw tbl hf₁ ha₁ hT₁ hf₂ ha₂ hT₂ S σ ρ ⟨shape⟩

/-- `cl` `letE`-`letE`: `ClLetEPorts` verbatim — the value-`eps` shape split
    and the two display-routed body `CL`s. -/
theorem cl_letE_letE_caseStep_closed
    {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {A v b B₁ B₂ : Expr Nat}
    {u₁ w₁ u₂ w₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hv₁ : TyP E n Γ v A)
    (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
    (hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hv₂ : TyP E n Γ v A)
    (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂)
    (hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (shape : (hv₁.eps σ ρ = .star ∧ hv₂.eps σ ρ = .star) ∨
        (∃ ev : ETm, ev ≠ .star ∧ hv₁.eps σ ρ = ev ∧ hv₂.eps σ ρ = ev))
    (bodyDrop : hv₁.eps σ ρ = .star → hv₂.eps σ ρ = .star →
        CL tbl σ (.drop :: ρ) hb₁ hb₂)
    (bodyInline : ∀ {ev : ETm}, ev ≠ .star → hv₁.eps σ ρ = ev →
        hv₂.eps σ ρ = ev → CL tbl σ (.inline ev :: ρ) hb₁ hb₂) :
    CaseStep Aw tbl
      (.cl (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
        (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂) S σ ρ) :=
  cl_letE_letE_caseStep_of_ports Aw tbl hA₁ hv₁ hb₁ hT₁ hA₂ hv₂ hb₂ hT₂ S σ ρ
    ⟨shape, bodyDrop, bodyInline⟩

/-- `cl` `const`-`const`: the member receipts force `m₁ = m₂`; the residual
    `hbit` is owed only on the cross-subject `ls₁ ≠ ls₂` branch (the
    `ls₁ = ls₂` half is issued inside the closer). -/
theorem cl_const_const_caseStep_closed
    {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {r : Nat}
    {ls ls₁ ls₂ : List Level} {m₁ m₂ : CheckedMember} {u₁ u₂ : Level}
    (hres₁ : E.members r = some m₁) (hlen₁ : ls.length = m₁.arity)
    (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls₁)
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m₁.mtype) (.sort u₁))
    (hres₂ : E.members r = some m₂) (hlen₂ : ls.length = m₂.arity)
    (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls₂)
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m₂.mtype) (.sort u₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hbit : ls₁ ≠ ls₂ → levelIsZero (σ u₁) = levelIsZero (σ u₂)) :
    CaseStep Aw tbl
      (.cl (TyP.const E n Γ r ls ls₁ m₁ u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
        (TyP.const E n Γ r ls ls₂ m₂ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) S σ ρ) := by
  have hm : m₁ = m₂ := Option.some.inj (hres₁.symm.trans hres₂)
  subst hm
  exact cl_const_const_caseStep_of_port Aw tbl hres₁ hlen₁ hwf₁ hls₁ hT₁
    hres₂ hlen₂ hwf₂ hls₂ hT₂ S σ ρ ⟨hbit⟩

/-! ## §2 `eut` cells -/

/-- `eut` conv-left: the residual `regCl` is the `CL` between `hc.dl` and
    the regularity-rebuilt `h.reg.2`. -/
theorem eut_conv_left_caseStep_closed
    {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {e A B T₂ : Expr Nat}
    {u : Level}
    (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u)) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (regCl : CL tbl σ ρ hc.dl h.reg.2) :
    CaseStep Aw tbl (.eut (TyP.conv E n Γ e A B u h hc) D₂ S σ ρ) :=
  eut_conv_left_caseStep_of_ports Aw tbl h hc D₂ S σ ρ ⟨regCl⟩

/-- `eut` conv-right: the residual `regCl` is `CL h.reg.2 hc.dl`. -/
theorem eut_conv_right_caseStep_closed
    {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {e T₁ A B : Expr Nat}
    {u : Level}
    (D₁ : TyP E n Γ e T₁) (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (regCl : CL tbl σ ρ h.reg.2 hc.dl) :
    CaseStep Aw tbl (.eut D₁ (TyP.conv E n Γ e A B u h hc) S σ ρ) :=
  eut_conv_right_caseStep_of_ports Aw tbl D₁ h hc S σ ρ ⟨regCl⟩

/-- `eut` `pi`-`pi`: `hW` discharged by `hTbl`; residuals are the two
    `reg.2`-edge `CL`s (off the `isSortOrPiHead` fast path) and the codomain
    `SortCoh`. -/
theorem eut_pi_pi_caseStep_closed (hTbl : TableWF tbl)
    {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {A B : Expr Nat}
    {u₁ u₂ v₁ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (edgeL : hA₁.isSortOrPiHead = false →
        CL tbl σ ρ hA₁.reg.2 (sortNode E n Γ u₁))
    (edgeR : hA₂.isSortOrPiHead = false →
        CL tbl σ ρ hA₂.reg.2 (sortNode E n Γ u₂))
    (cohB : SortCoh σ hB₁ hB₂) :
    CaseStep Aw tbl
      (.eut (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁) (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂)
        S σ ρ) :=
  eut_pi_pi_caseStep_of_ports Aw tbl hA₁ hB₁ hA₂ hB₂ S σ ρ
    ⟨hTbl, edgeL, edgeR, cohB⟩

/-- `eut` `lam`-`lam`: `hTC` discharged by `hTbl.closed`; the residual
    `convB` is the codomain `ConvMod` at the binder display. -/
theorem eut_lam_lam_caseStep_closed (hTbl : TableWF tbl)
    {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {A body B₁ B₂ : Expr Nat}
    {u₁ u₂ v₁ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (convB : ConvMod (EStep tbl) LvlEq
        (hB₁.eps σ (binderDisp (levelIsZero (σ u₁)) :: ρ))
        (hB₂.eps σ (binderDisp (levelIsZero (σ u₁)) :: ρ))) :
    CaseStep Aw tbl
      (.eut (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) S σ ρ) :=
  eut_lam_lam_caseStep_of_ports Aw tbl hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ
    ⟨hTbl.closed, convB⟩

/-- `eut` `app`-`app`: `hW` discharged by `hTbl`; residuals are the
    Π-surface witnesses `hAᵢ hBᵢ` (cell data), the domain bit `hbit`, the
    `reg.2`-vs-`pi`-node `CL`s, and the `instEnd` bridges. -/
theorem eut_app_app_caseStep_closed (hTbl : TableWF tbl)
    {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {f a A₁ B₁ A₂ B₂ : Expr Nat} {w₁ w₂ u₁' v₁' u₂' v₂' : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (hA₁ : TyP E n Γ A₁ (.sort u₁')) (hB₁ : TyP E n (.assumption A₁ :: Γ) B₁ (.sort v₁'))
    (hA₂ : TyP E n Γ A₂ (.sort u₂')) (hB₂ : TyP E n (.assumption A₂ :: Γ) B₂ (.sort v₂'))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hbit : levelIsZero (σ u₁') = levelIsZero (σ u₂'))
    (piL : CL tbl σ ρ hf₁.reg.2 (TyP.pi E n Γ A₁ u₁' B₁ v₁' hA₁ hB₁))
    (piR : CL tbl σ ρ (TyP.pi E n Γ A₂ u₂' B₂ v₂' hA₂ hB₂) hf₂.reg.2)
    (instL : CL tbl σ ρ hT₁ (instEnd hB₁ ha₁ hA₁))
    (instR : CL tbl σ ρ (instEnd hB₂ ha₂ hA₂) hT₂) :
    CaseStep Aw tbl
      (.eut (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
        (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) S σ ρ) :=
  eut_app_app_caseStep_of_ports Aw tbl hf₁ ha₁ hT₁ hf₂ ha₂ hT₂
    hA₁ hB₁ hA₂ hB₂ S σ ρ ⟨hTbl, hbit, piL, piR, instL, instR⟩

/-- `eut` `letE`-`letE`: `EutLetEPorts` verbatim — the two regularity links
    at the `letSub` composites and the reduct `EUT`. -/
theorem eut_letE_letE_caseStep_closed
    {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {A v b B₁ B₂ : Expr Nat}
    {u₁ w₁ u₂ w₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hv₁ : TyP E n Γ v A)
    (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
    (hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hv₂ : TyP E n Γ v A)
    (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂)
    (hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (linkL : CL tbl σ ρ hT₁ (letSub hb₁ hv₁ hA₁).reg.2)
    (mid : EUT tbl σ ρ (letSub hb₁ hv₁ hA₁) (letSub hb₂ hv₂ hA₂))
    (linkR : CL tbl σ ρ (letSub hb₂ hv₂ hA₂).reg.2 hT₂) :
    CaseStep Aw tbl
      (.eut (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
        (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂) S σ ρ) :=
  eut_letE_letE_caseStep_of_ports Aw tbl hA₁ hv₁ hb₁ hT₁ hA₂ hv₂ hb₂ hT₂ S σ ρ
    ⟨linkL, mid, linkR⟩

/-- `eut` `const`-`const`: member bridge as on the `cl` side; residuals are
    the admission cell `TypeAdm` and the two admission-view `ConvMod`s. -/
theorem eut_const_const_caseStep_closed
    {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {r : Nat}
    {ls ls₁ ls₂ : List Level} {m₁ m₂ : CheckedMember} {u₁ u₂ : Level}
    (hres₁ : E.members r = some m₁) (hlen₁ : ls.length = m₁.arity)
    (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls₁)
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m₁.mtype) (.sort u₁))
    (hres₂ : E.members r = some m₂) (hlen₂ : ls.length = m₂.arity)
    (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls₂)
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m₂.mtype) (.sort u₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (adm : TypeAdm E Aw r m₁)
    (q₁ : ConvMod (EStep tbl) LvlEq (hT₁.eps σ ρ)
        (contextLift (ρ.take Γ.length)
          (adm.hT.eps (fun l => σ (instLevel ls₁ l)) (ρ.drop Γ.length))))
    (q₂ : ConvMod (EStep tbl) LvlEq (hT₂.eps σ ρ)
        (contextLift (ρ.take Γ.length)
          (adm.hT.eps (fun l => σ (instLevel ls₂ l)) (ρ.drop Γ.length)))) :
    CaseStep Aw tbl
      (.eut (TyP.const E n Γ r ls ls₁ m₁ u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
        (TyP.const E n Γ r ls ls₂ m₂ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) S σ ρ) := by
  have hm : m₁ = m₂ := Option.some.inj (hres₁.symm.trans hres₂)
  subst hm
  exact eut_const_const_caseStep_of_port Aw tbl hres₁ hlen₁ hwf₁ hls₁ hT₁
    hres₂ hlen₂ hwf₂ hls₂ hT₂ S σ ρ ⟨adm, q₁, q₂⟩

/-! ## §3 the diagonal sub-cells of `clOther`/`eutOther` are closed outright -/

/-- Every identical `.cl` pair — including every `clResidualTag`
    transport-headed pair — is `CL`-reflexive: no ports needed. -/
theorem cl_diag_caseStep {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl (.cl D D S σ ρ) := fun _ _ => ConvMod.refl _

/-- Every identical `.eut` pair is `EUT`-reflexive. -/
theorem eut_diag_caseStep {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl (.eut D D S σ ρ) := fun _ _ => ConvMod.refl _

/-- A `wk`/`wk` pair is `clResidualTag`-residual (transport head, no
    `.conv`). -/
theorem cl_residual_tag_wk {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T) (d : LocalDecl) (c : Nat) :
    clResidualTag (TyP.wk E n Γ e T d c D).headTag
      (TyP.wk E n Γ e T d c D).headTag = true := rfl

/-- A `wk`/`wk` pair is `eutResidualTag`-residual. -/
theorem eut_residual_tag_wk {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T) (d : LocalDecl) (c : Nat) :
    eutResidualTag (TyP.wk E n Γ e T d c D).headTag
      (TyP.wk E n Γ e T d c D).headTag = true := rfl

/-- The `clOther` residual port — a `CaseStep` at a transport-headed cell —
    is inhabited on the diagonal. -/
theorem cl_residual_cell_sat {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T) (d : LocalDecl) (c : Nat)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl
      (.cl (TyP.wk E n Γ e T d c D) (TyP.wk E n Γ e T d c D) S σ ρ) :=
  cl_diag_caseStep Aw tbl _ S σ ρ

/-- The `eutOther` residual port is inhabited on the diagonal. -/
theorem eut_residual_cell_sat {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T) (d : LocalDecl) (c : Nat)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl
      (.eut (TyP.wk E n Γ e T d c D) (TyP.wk E n Γ e T d c D) S σ ρ) :=
  eut_diag_caseStep Aw tbl _ S σ ρ

/-! ## §4 compiled non-vacuity witnesses -/

namespace CleutWit

/-- `S0 : S1`, in any context (a `.sort` leaf). -/
def d0 {Γ : LCtx} : TyP emptyEnv 0 Γ (.sort .zero) (.sort (.succ .zero)) :=
  TyP.sort emptyEnv 0 Γ .zero (.succ .zero) (eqN_refl _)

/-- `S1 : S2`, in any context. -/
def d1 {Γ : LCtx} : TyP emptyEnv 0 Γ (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) :=
  TyP.sort emptyEnv 0 Γ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

/-- `ClPiPorts.bodyCl` is inhabited on identical bodies at any shifted
    display — `CL`-reflexivity. -/
theorem clPi_bodyCl_sat {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B : Expr Nat} {v : Level}
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (σ : Level → Level) (ρ : List Disp) (u₁ : Level) :
    CL tbl σ (binderDisp (levelIsZero (σ u₁)) :: ρ) hB hB :=
  ConvMod.refl _

/-- `ClLamPorts` at an identical-`hb` instance: refl body `CL`, and the
    `shape`'s non-`★` branch since a `.sort` node's `eps` is `.sort`-headed
    for every `σ`. -/
theorem clLamPorts_sat (σ : Level → Level) (ρ : List Disp) (u₁ : Level) :
    ClLamPorts tbl σ ρ u₁ (d1 (Γ := [.assumption (.sort .zero)]))
      (d1 (Γ := [.assumption (.sort .zero)])) :=
  ⟨ConvMod.refl _,
    .inr ⟨fun h => ETm.noConfusion h, fun h => ETm.noConfusion h⟩⟩

/-- `ClAppPorts.shape`: the all-non-`★` branch. At `σ = fun _ ↦ .succ .zero`
    the `bvar` erasure is `resolve [] 0 = .bvar 0` and the `sort` erasure is
    `.sort _`, both non-`★`. -/
def wΓ : LCtx := [.assumption (.pi (.sort (.succ .zero)) (.sort (.succ .zero)))]

def wPiT : TyP emptyEnv 0 wΓ
    (.pi (.sort (.succ .zero)) (.sort (.succ .zero)))
    (.sort (.imax (.succ (.succ .zero)) (.succ (.succ .zero)))) :=
  TyP.pi emptyEnv 0 wΓ (.sort (.succ .zero)) (.succ (.succ .zero))
    (.sort (.succ .zero)) (.succ (.succ .zero)) d1 d1

def wF : TyP emptyEnv 0 wΓ (.bvar 0)
    (.pi (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  TyP.bvar emptyEnv 0 wΓ 0 (.pi (.sort (.succ .zero)) (.sort (.succ .zero)))
    (.imax (.succ (.succ .zero)) (.succ (.succ .zero))) rfl wPiT

theorem clAppPorts_sat :
    ClAppPorts [] (fun _ => .succ .zero) [] wF d0 wF d0 :=
  ⟨.inr (.inr ⟨fun h => ETm.noConfusion h, fun h => ETm.noConfusion h,
      fun h => ETm.noConfusion h, fun h => ETm.noConfusion h⟩)⟩

/-- `ClLetEPorts`: identical value/body instance — `shape` via the non-`★`
    value erasure, both routed body `CL`s refl. -/
theorem clLetEPorts_sat (σ : Level → Level) (ρ : List Disp) :
    ClLetEPorts tbl σ ρ d0
      (d1 (Γ := [.letBinding (.sort (.succ .zero)) (.sort .zero)]))
      (d1 (Γ := [.letBinding (.sort (.succ .zero)) (.sort .zero)])) d0 :=
  ⟨.inr ⟨.sort (σ .zero), fun h => ETm.noConfusion h, rfl, rfl⟩,
    fun _ _ => ConvMod.refl _,
    fun _ _ _ => ConvMod.refl _⟩

/-- `ClConstPorts.hbit`: at `ls₁ = ls₂` the antecedent `ls₁ ≠ ls₂` is false,
    so the gate bit is vacuously satisfied (its real content — the
    cross-subject case — is the residual). -/
def wMem : CheckedMember :=
  { mclass := .axiomM, arity := 0, mtype := .sort .zero, body := none }

def wTy : TyP emptyEnv 0 [] (instantiateLevels [] wMem.mtype)
    (.sort (.succ .zero)) := d0

theorem clConstPorts_sat (σ : Level → Level) (ρ : List Disp) :
    ClConstPorts tbl σ ρ wTy wTy := ⟨fun h => (h rfl).elim⟩

/-- `EutConvLPorts.regCl`: at a `.sort`-headed `h`, `h.reg.2` is
    definitionally `sortNode`-shaped, so the `CL` to `hc.dl` is refl at a
    `CvP.refl` with a `sort`-typed `dl`. -/
def wCv : CvP emptyEnv 0 [] (.sort (.succ .zero)) (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) :=
  CvP.refl emptyEnv 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))
    d1 d1 d1

theorem eutConvLPorts_sat (σ : Level → Level) (ρ : List Disp) :
    EutConvLPorts tbl σ ρ d0 wCv := ⟨ConvMod.refl _⟩

theorem eutConvRPorts_sat (σ : Level → Level) (ρ : List Disp) :
    EutConvRPorts tbl σ ρ d0 wCv := ⟨ConvMod.refl _⟩

/-- `EutPiPorts`'s edge residuals: at a `bvar`-headed domain typing
    (`isSortOrPiHead = false`, so the implication's antecedent is inhabited)
    `reg.2` is the `hA` field — a `.sort` node whose `eps` matches
    `sortNode`'s. -/
def wΓb : LCtx := [.assumption (.sort (.succ .zero))]

def wDomB : TyP emptyEnv 0 wΓb (.bvar 0) (.sort (.succ .zero)) :=
  TyP.bvar emptyEnv 0 wΓb 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl d1

theorem eutPi_edgeL_sat (σ : Level → Level) (ρ : List Disp) :
    wDomB.isSortOrPiHead = false →
      CL tbl σ ρ wDomB.reg.2
        (sortNode emptyEnv 0 wΓb (.succ .zero)) :=
  fun _ => ConvMod.refl _

theorem eutPi_edgeR_sat (σ : Level → Level) (ρ : List Disp) :
    wDomB.isSortOrPiHead = false →
      CL tbl σ ρ wDomB.reg.2
        (sortNode emptyEnv 0 wΓb (.succ .zero)) :=
  fun _ => ConvMod.refl _

/-- `EutPiPorts.cohB`: `SortCoh σ D D` is `eqN_refl`. -/
theorem eutPi_cohB_sat (σ : Level → Level) :
    SortCoh σ (d1 (Γ := [])) (d1 (Γ := [])) := eqN_refl _

/-- `EutLamPorts.convB`: identical codomain typings are `ConvMod`-refl at
    the binder display. -/
theorem eutLam_convB_sat (σ : Level → Level) (ρ : List Disp) (u₁ : Level) :
    ConvMod (EStep tbl) LvlEq
      ((d1 (Γ := [.assumption (.sort .zero)])).eps σ
        (binderDisp (levelIsZero (σ u₁)) :: ρ))
      ((d1 (Γ := [.assumption (.sort .zero)])).eps σ
        (binderDisp (levelIsZero (σ u₁)) :: ρ)) :=
  ConvMod.refl _

/-- `EutAppPorts` minus `hW` (the residual five): choosing `hT` as the
    `instEnd` composite itself makes `instL`/`instR` refl, `hf` a `bvar` at
    the `pi` node makes `piL`/`piR` refl, and `u₁' = u₂'` makes `hbit`
    refl. -/
def wArg : TyP emptyEnv 0 wΓ (.sort .zero) (.sort (.succ .zero)) := d0

def wT : TyP emptyEnv 0 wΓ (instantiate0 (.sort .zero) (.sort (.succ .zero)))
    (.sort (.succ (.succ .zero))) :=
  instEnd (d1 (Γ := .assumption (.sort (.succ .zero)) :: wΓ)) wArg
    (d1 (Γ := wΓ))

theorem eutApp_resid_sat (σ : Level → Level) :
    levelIsZero (σ (.succ (.succ .zero))) =
        levelIsZero (σ (.succ (.succ .zero))) ∧
    CL [] σ [] wF.reg.2 wPiT ∧
    CL [] σ [] wPiT wF.reg.2 ∧
    CL [] σ [] wT (instEnd (d1 (Γ := .assumption (.sort (.succ .zero)) :: wΓ))
        wArg (d1 (Γ := wΓ))) ∧
    CL [] σ [] (instEnd (d1 (Γ := .assumption (.sort (.succ .zero)) :: wΓ))
        wArg (d1 (Γ := wΓ))) wT :=
  ⟨rfl, ConvMod.refl _, ConvMod.refl _, ConvMod.refl _, ConvMod.refl _⟩

/-- `EutLetEPorts`: with `hT := (letSub hb hv hA).reg.2` the two links are
    refl and `mid` is the identical-`L` `EUT`. -/
def wHv : TyP emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) := d0

def wHA : TyP emptyEnv 0 [] (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) := d1

def wHb : TyP emptyEnv 0 [.letBinding (.sort (.succ .zero)) (.sort .zero)]
    (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := d1

def wLet : TyP emptyEnv 0 [] (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) :=
  letSub wHb wHv wHA

theorem eutLetPorts_sat (σ : Level → Level) (ρ : List Disp) :
    EutLetEPorts tbl σ ρ wHA wHv wHb wLet.reg.2 wHA wHv wHb wLet.reg.2 :=
  ⟨ConvMod.refl _, ConvMod.refl _, ConvMod.refl _⟩

/-- `EutConstPorts`: `adm` at the trivial admission (`E₀ = E`, `Aw r = 2`,
    `hT` a `.sort` leaf of weight `1`); `q₁`/`q₂` refl since
    `contextLift [] t = t` and `instLevel [] .zero = .zero`. -/
def wAdm : TypeAdm emptyEnv (fun _ => 2) 0 wMem :=
  ⟨emptyEnv, envExt_refl emptyEnv, .succ .zero, d0, by decide⟩

def eutConstPorts_sat (σ : Level → Level) :
    EutConstPorts (fun _ => 2) [] σ [] 0 wTy wTy :=
  ⟨wAdm, ConvMod.refl _, ConvMod.refl _⟩

end CleutWit

#print axioms Rcic.Syn.cl_pi_pi_caseStep_closed
#print axioms Rcic.Syn.cl_lam_lam_caseStep_closed
#print axioms Rcic.Syn.cl_app_app_caseStep_closed
#print axioms Rcic.Syn.cl_letE_letE_caseStep_closed
#print axioms Rcic.Syn.cl_const_const_caseStep_closed
#print axioms Rcic.Syn.eut_conv_left_caseStep_closed
#print axioms Rcic.Syn.eut_conv_right_caseStep_closed
#print axioms Rcic.Syn.eut_pi_pi_caseStep_closed
#print axioms Rcic.Syn.eut_lam_lam_caseStep_closed
#print axioms Rcic.Syn.eut_app_app_caseStep_closed
#print axioms Rcic.Syn.eut_letE_letE_caseStep_closed
#print axioms Rcic.Syn.eut_const_const_caseStep_closed
#print axioms Rcic.Syn.cl_diag_caseStep
#print axioms Rcic.Syn.eut_diag_caseStep
#print axioms Rcic.Syn.cl_residual_tag_wk
#print axioms Rcic.Syn.eut_residual_tag_wk
#print axioms Rcic.Syn.cl_residual_cell_sat
#print axioms Rcic.Syn.eut_residual_cell_sat
#print axioms Rcic.Syn.CleutWit.clPi_bodyCl_sat
#print axioms Rcic.Syn.CleutWit.clLamPorts_sat
#print axioms Rcic.Syn.CleutWit.clAppPorts_sat
#print axioms Rcic.Syn.CleutWit.clLetEPorts_sat
#print axioms Rcic.Syn.CleutWit.clConstPorts_sat
#print axioms Rcic.Syn.CleutWit.eutConvLPorts_sat
#print axioms Rcic.Syn.CleutWit.eutConvRPorts_sat
#print axioms Rcic.Syn.CleutWit.eutPi_edgeL_sat
#print axioms Rcic.Syn.CleutWit.eutPi_edgeR_sat
#print axioms Rcic.Syn.CleutWit.eutPi_cohB_sat
#print axioms Rcic.Syn.CleutWit.eutLam_convB_sat
#print axioms Rcic.Syn.CleutWit.eutApp_resid_sat
#print axioms Rcic.Syn.CleutWit.eutLetPorts_sat
#print axioms Rcic.Syn.CleutWit.eutConstPorts_sat

end Rcic.Syn

import rcic.RcicSynTableOfIFull
import rcic.RcicSynStepZetaField
import rcic.RcicSynZetaMeasureRefute

/-!
# sortRow census row 4 (`es_zetaLocal`) at `tableOfI` — both missing lemmas refuted

GLM lane `glm-sr1` (rows 2/3/4), `research/rcic/sortrow/TABLEOFI_SUPPLIER_CENSUS.md`
row 4, BRIEF 2026-10-20. `closure_claim = 0`.

The census lists two missing lemmas for row 4: `zetaLocal_surface_cl` (the
`zetaLocalBvarSurface` `CL`) and `zetaLocal_res_conv` (the display-side `resolve`
`ConvMod` for the `levelIsZero = false` branch). Both are stated here as ONE
named `Prop` each (`ZetaLocalSurfaceWall`, `ZetaLocalResConvWall`) and both are
refuted at `tbl := tableOfI EnvWfT.empty` with every premise of the lemma
inhabited by an explicit fixture:

* `ZetaLocalSurfaceWall` dies on `zlWkDl`, a `TyP.wk`-headed typing of `.bvar 0`
  in `wkZetaCtx` at the CANONICAL Entry disposition
  `(wkZetaCtxP emptyEnv 0).disp id = [.inline (.bvar 1), .keep, .keep]`
  (`DispFor` by the landed `dispFor_ctxP_id`): `removeAt` does not un-lift the
  `.inline (.bvar 1)` value, so `TyP.eps`'s outer `.lift 0 1` lifts it a second
  time — `zlWkDl.eps id ρ = .bvar 2` while the canonical surface erases to
  `.bvar 1` (the same double-lift the landed `not_es_wk_inline` pins on the
  `CvP` side). `.bvar 2` and `.bvar 1` are `EStep`-normal and not `LvlEq`
  (`not_convMod_bvar_ne`).
* `ZetaLocalResConvWall` dies on the plain `zetaCtx` fixture `x₀ : sort 1 :=
  sort 0` with `hv` the `TyP.sort` typing of the stored value and `ρ := [.keep]`:
  `resolve [.keep] 0 = .bvar 0` while `hv.eps id [.keep] = .sort .zero`, and
  `.bvar 0` is not convertible to `.sort .zero` (`not_convMod_bvar_sort`).

Both refutations hold for the `TableWF (tableOfI EnvWfT.empty)` supplied by
`tableWF_tableOfI_full` (merged from `devin/swe-tableicompat`, #7771). The row
therefore cannot be discharged through its named missing lemmas; the walls stay
as the two named `Prop`s below (not bundled, not supplied).
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the two walls, each restated as ONE named `Prop` -/

/-- `zetaLocal_surface_cl`, the census row-4 surface missing lemma, as ONE
    named `Prop`: the `es_zetaLocal` field's retained `hsurf` port, verbatim.
    False at `tableOfI EnvWfT.empty` (`zetaLocal_surface_cl_refuted`). -/
def ZetaLocalSurfaceWall (tbl : List CRule) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat}
    (hty : lookupType Γ i = some A) (dl : TyP E n Γ (.bvar i) A)
    (σ : Level → Level) (ρ : List Disp),
    CL tbl σ ρ dl (zetaLocalBvarSurface hty dl)

/-- `zetaLocal_res_conv`, the census row-4 display-side missing lemma, as ONE
    named `Prop`: the `es_zetaLocal` field's retained `hres` port (with the
    field's own data as premises), verbatim. False at
    `tableOfI EnvWfT.empty` (`zetaLocal_res_conv_refuted`). -/
def ZetaLocalResConvWall (tbl : List CRule) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (σ : Level → Level) (ρ : List Disp),
    levelIsZero (σ dl.reg.1) = false →
    ConvMod (EStep tbl) LvlEq (resolve ρ i) (hv.eps σ ρ)

/-! ## §2 `ZetaLocalSurfaceWall` fixture and refutation -/

/-- `S` is not a premise of either lemma (it never occurs in the wall
    statements), so no `ScopedCtx` fixture is needed. The field data fixtures:
    `.bvar 0 : sort 1` in `zetaLetCtx`, weakened at `c = 1`. -/
def zlInner : TyP emptyEnv 0 zetaLetCtx (.bvar 0) (.sort (.succ .zero)) :=
  TyP.bvar emptyEnv 0 zetaLetCtx 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
    (TyP.sort emptyEnv 0 zetaLetCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))

/-- `dl`: `TyP.wk` at `c = 1` of `zlInner` — a `wkZetaCtx` typing of `.bvar 0`.
    This is exactly the `dl` of the landed `wkZetaNode` refutation. -/
def zlWkDl : TyP emptyEnv 0 wkZetaCtx (.bvar 0) (.sort (.succ .zero)) :=
  TyP.wk emptyEnv 0 zetaLetCtx (.bvar 0) (.sort (.succ .zero))
    (.assumption (.sort (.succ .zero))) 1 zlInner

/-- The canonical Entry disposition of `wkZetaCtx` (`DispFor` by
    `dispFor_ctxP_id (wkZetaCtxP emptyEnv 0)`). -/
def zlRho : List Disp := (wkZetaCtxP emptyEnv 0).disp id

/-- At `zlRho` the `wk`-headed `dl` erases to `.bvar 2` (double lift) while the
    canonical `zetaLocalBvarSurface` erases to `.bvar 1`: the surface `CL` is
    false for every `TableWF tbl`. -/
theorem not_cl_zetaLocal_surface_tableWF (tbl : List CRule) (hW : TableWF tbl) :
    ¬ CL tbl id zlRho zlWkDl
      (zetaLocalBvarSurface (rfl : lookupType wkZetaCtx 0 = some (.sort (.succ .zero)))
        zlWkDl) := by
  intro h
  have h1 : zlWkDl.eps id zlRho = .bvar 2 := rfl
  have h2 : (zetaLocalBvarSurface
      (rfl : lookupType wkZetaCtx 0 = some (.sort (.succ .zero))) zlWkDl).eps id zlRho =
      .bvar 1 := rfl
  unfold CL at h
  rw [h1, h2] at h
  exact not_convMod_bvar_ne hW (by decide) h

/-- `zetaLocal_surface_cl` is FALSE at `tableOfI EnvWfT.empty`: the wall fails
    on `zlWkDl` at the canonical disposition, with the lemma's premises
    (`hty`, `dl`, `σ`, `ρ`) all inhabited. -/
theorem zetaLocal_surface_cl_refuted :
    ¬ ZetaLocalSurfaceWall (tableOfI EnvWfT.empty) := by
  intro h
  have hcl : CL (tableOfI EnvWfT.empty) id zlRho zlWkDl
      (zetaLocalBvarSurface
        (rfl : lookupType wkZetaCtx 0 = some (.sort (.succ .zero))) zlWkDl) :=
    h (rfl : lookupType wkZetaCtx 0 = some (.sort (.succ .zero))) zlWkDl id zlRho
  exact not_cl_zetaLocal_surface_tableWF _ (tableWF_tableOfI_full EnvWfT.empty) hcl

/-! ## §3 `ZetaLocalResConvWall` fixture and refutation -/

/-- `x₀ : sort 1 := sort 0` — the landed `zetaCtx`. The stored value `v` is
    `.sort .zero` (`lookupValue zetaCtx 0 = some (lift 0 1 (.sort .zero))`). -/
def zrHv : TyP emptyEnv 0 zetaCtx (.sort .zero) (.sort (.succ .zero)) :=
  TyP.sort emptyEnv 0 zetaCtx .zero (.succ .zero) (eqN_refl _)

/-- `dl`: the direct `.bvar 0` typing, whose `reg.1 = .succ (.succ .zero)` makes
    the `levelIsZero = false` guard hold at `σ := id`. -/
def zrDl : TyP emptyEnv 0 zetaCtx (.bvar 0) (.sort (.succ .zero)) :=
  TyP.bvar emptyEnv 0 zetaCtx 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
    (TyP.sort emptyEnv 0 zetaCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))

/-- `dr`: the same judgment as `zrHv` (an arbitrary second typing of `v`). -/
def zrDr : TyP emptyEnv 0 zetaCtx (.sort .zero) (.sort (.succ .zero)) := zrHv

/-- With `ρ := [.keep]` the routed display is `.bvar 0` while the stored
    value's erasure is `.sort .zero`: the display-side `ConvMod` is false for
    every `TableWF tbl`. -/
theorem not_res_conv_zetaLocal_tableWF (tbl : List CRule) (hW : TableWF tbl) :
    ¬ (levelIsZero (id zrDl.reg.1) = false →
      ConvMod (EStep tbl) LvlEq (resolve [.keep] 0) (zrHv.eps id [.keep])) := by
  intro h
  exact not_convMod_bvar_sort hW 0 .zero (h rfl)

/-- `zetaLocal_res_conv` is FALSE at `tableOfI EnvWfT.empty`: the wall fails on
    the `zetaCtx` fixture with `ρ := [.keep]`, with the lemma's premises
    (`hval`, `hty`, `hv`, `dl`, `dr`, `σ`, `ρ`) all inhabited. -/
theorem zetaLocal_res_conv_refuted :
    ¬ ZetaLocalResConvWall (tableOfI EnvWfT.empty) := by
  intro h
  have hc : levelIsZero (id zrDl.reg.1) = false →
      ConvMod (EStep (tableOfI EnvWfT.empty)) LvlEq
        (resolve [.keep] 0) (zrHv.eps id [.keep]) :=
    h (rfl : lookupValue zetaCtx 0 = some (.sort .zero))
      (rfl : lookupType zetaCtx 0 = some (.sort (.succ .zero)))
      zrHv zrDl zrDr id [.keep]
  exact not_res_conv_zetaLocal_tableWF _ (tableWF_tableOfI_full EnvWfT.empty) hc

end Rcic.Syn

#print axioms Rcic.Syn.ZetaLocalSurfaceWall
#print axioms Rcic.Syn.ZetaLocalResConvWall
#print axioms Rcic.Syn.not_cl_zetaLocal_surface_tableWF
#print axioms Rcic.Syn.zetaLocal_surface_cl_refuted
#print axioms Rcic.Syn.not_res_conv_zetaLocal_tableWF
#print axioms Rcic.Syn.zetaLocal_res_conv_refuted

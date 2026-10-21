import rcic.RcicSynSRBetaZetaLocal
import rcic.RcicSynLetSub

/-!
# sortRow census row 3 (`es_zeta`) at `tableOfI` — both missing lemmas refuted

GLM lane `glm-sr1` (rows 2/3/4), `research/rcic/sortrow/TABLEOFI_SUPPLIER_CENSUS.md`
row 3, BRIEF 2026-10-20. `closure_claim = 0`.

The census lists two missing lemmas for row 3: `zeta_surface_cl` (the canonical
`TyP.letE` surface `CL`) and `zeta_reduct_cl` (the `letSub` reduct `CL`). Both
are stated here as ONE named `Prop` each (`ZetaSurfaceWall`, `ZetaReductWall`)
and both are refuted at `tbl := tableOfI EnvWfT.empty` with every premise of
the lemma inhabited by an explicit fixture in `wkZetaCtx`
(`x₂ : sort 1, x₁ : sort 1, x₀ : sort 1 := x₂`) at the CANONICAL Entry
disposition `zlRho = [.inline (.bvar 1), .keep, .keep]` (`DispFor` by the
landed `dispFor_ctxP_id`):

* `ZetaSurfaceWall` dies on `zzWkDl`, a `TyP.wk`-headed typing (at `c = 1`) of
  `.letE (sort 1) (.bvar 0) (.bvar 0)`: the `wk` lifts the inner erasure
  `.bvar 1` a second time to `.bvar 2` while the canonical `TyP.letE` surface
  (built from the field's own `hv`/`hb`) erases to `.bvar 1`
  (`not_convMod_bvar_ne`).
* `ZetaReductWall` dies on `zzDr` (also `TyP.wk`-headed): `letSub zzHB zzHV zzHA`
  erases to `.bvar 1` (the landed `letSub_eps` with `hv.eps = .bvar 1`), while
  `zzDr.eps = .bvar 2` (`not_convMod_bvar_ne`).

Row 4's refutations live in `RcicSynSRBetaZetaLocal`; the fixtures `zlRho` /
`zlInner` are reused from there.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the two walls, each restated as ONE named `Prop` -/

/-- `zeta_surface_cl`, the census row-3 surface missing lemma, as ONE named
    `Prop`: the `es_zeta` field's retained `hsurf` port, verbatim. False at
    `tableOfI EnvWfT.empty` (`zeta_surface_cl_refuted`). -/
def ZetaSurfaceWall (tbl : List CRule) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (σ : Level → Level) (ρ : List Disp),
    CL tbl σ ρ dl (TyP.letE E n Γ A u value B body dl.reg.1 hA hv hb dl.reg.2)

/-- `zeta_reduct_cl`, the census row-3 reduct missing lemma, as ONE named
    `Prop`: the `es_zeta` field's retained `hreduct` port, verbatim. False at
    `tableOfI EnvWfT.empty` (`zeta_reduct_cl_refuted`). -/
def ZetaReductWall (tbl : List CRule) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (σ : Level → Level) (ρ : List Disp),
    CL tbl σ ρ (letSub hb hv hA) dr

/-! ## §2 the `wkZetaCtx` field-data fixtures (`A = B = sort 1`,
    `value = body = .bvar 0`, `u = 2`) -/

def zzHA : TyP emptyEnv 0 wkZetaCtx (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  TyP.sort emptyEnv 0 wkZetaCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

def zzHV : TyP emptyEnv 0 wkZetaCtx (.bvar 0) (.sort (.succ .zero)) :=
  TyP.bvar emptyEnv 0 wkZetaCtx 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
    (TyP.sort emptyEnv 0 wkZetaCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))

def zzHB : TyP emptyEnv 0 (.letBinding (.sort (.succ .zero)) (.bvar 0) :: wkZetaCtx)
    (.bvar 0) (.sort (.succ .zero)) :=
  TyP.bvar emptyEnv 0 (.letBinding (.sort (.succ .zero)) (.bvar 0) :: wkZetaCtx)
    0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
    (TyP.sort emptyEnv 0 (.letBinding (.sort (.succ .zero)) (.bvar 0) :: wkZetaCtx)
      (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))

/-- The canonical inner `letE` typing in `zetaLetCtx`. -/
def zzInnerLet : TyP emptyEnv 0 zetaLetCtx
    (.letE (.sort (.succ .zero)) (.bvar 0) (.bvar 0)) (.sort (.succ .zero)) :=
  TyP.letE emptyEnv 0 zetaLetCtx (.sort (.succ .zero)) (.succ (.succ .zero))
    (.bvar 0) (.sort (.succ .zero)) (.bvar 0) (.succ (.succ .zero))
    (TyP.sort emptyEnv 0 zetaLetCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    (TyP.bvar emptyEnv 0 zetaLetCtx 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
      (TyP.sort emptyEnv 0 zetaLetCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))
    (TyP.bvar emptyEnv 0 (.letBinding (.sort (.succ .zero)) (.bvar 0) :: zetaLetCtx)
      0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
      (TyP.sort emptyEnv 0 (.letBinding (.sort (.succ .zero)) (.bvar 0) :: zetaLetCtx)
        (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))
    (TyP.sort emptyEnv 0 zetaLetCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))

/-- `dl`: `TyP.wk` at `c = 1` of `zzInnerLet`. -/
def zzWkDl : TyP emptyEnv 0 wkZetaCtx
    (.letE (.sort (.succ .zero)) (.bvar 0) (.bvar 0)) (.sort (.succ .zero)) :=
  TyP.wk emptyEnv 0 zetaLetCtx (.letE (.sort (.succ .zero)) (.bvar 0) (.bvar 0))
    (instantiate0 (.bvar 0) (.sort (.succ .zero))) (.assumption (.sort (.succ .zero))) 1
    zzInnerLet

/-- `dr`: `TyP.wk` at `c = 1` of the row-4 `zlInner` (a `.bvar 0` typing); its
    subject `instantiate0 (.bvar 0) (.bvar 0)` is definitionally `.bvar 0`. -/
def zzDr : TyP emptyEnv 0 wkZetaCtx (instantiate0 (.bvar 0) (.bvar 0))
    (instantiate0 (.bvar 0) (.sort (.succ .zero))) :=
  TyP.wk emptyEnv 0 zetaLetCtx (.bvar 0) (.sort (.succ .zero))
    (.assumption (.sort (.succ .zero))) 1 zlInner

/-! ## §3 `ZetaSurfaceWall` refutation -/

theorem not_cl_zeta_surface_tableWF (tbl : List CRule) (hW : TableWF tbl) :
    ¬ CL tbl id zlRho zzWkDl
      (TyP.letE emptyEnv 0 wkZetaCtx (.sort (.succ .zero)) (.succ (.succ .zero))
        (.bvar 0) (.sort (.succ .zero)) (.bvar 0) zzWkDl.reg.1 zzHA zzHV zzHB
        zzWkDl.reg.2) := by
  intro h
  have h1 : zzWkDl.eps id zlRho = .bvar 2 := rfl
  have h2 : (TyP.letE emptyEnv 0 wkZetaCtx (.sort (.succ .zero)) (.succ (.succ .zero))
      (.bvar 0) (.sort (.succ .zero)) (.bvar 0) zzWkDl.reg.1 zzHA zzHV zzHB
      zzWkDl.reg.2).eps id zlRho = .bvar 1 := rfl
  unfold CL at h
  rw [h1, h2] at h
  exact not_convMod_bvar_ne hW (by decide) h

/-- `zeta_surface_cl` is FALSE at `tableOfI EnvWfT.empty`: the wall fails on
    `zzWkDl` at the canonical disposition, with the lemma's premises (`hA`,
    `hv`, `hb`, `dl`, `dr`, `σ`, `ρ`) all inhabited. -/
theorem zeta_surface_cl_refuted :
    ¬ ZetaSurfaceWall (tableOfI EnvWfT.empty) := by
  intro h
  exact not_cl_zeta_surface_tableWF _ (tableWF_tableOfI_full EnvWfT.empty)
    (h zzHA zzHV zzHB zzWkDl zzDr id zlRho)

/-! ## §4 `ZetaReductWall` refutation -/

theorem not_cl_zeta_reduct_tableWF (tbl : List CRule) (hW : TableWF tbl) :
    ¬ CL tbl id zlRho (letSub zzHB zzHV zzHA) zzDr := by
  intro h
  have h1 : (letSub zzHB zzHV zzHA).eps id zlRho = .bvar 1 := by
    rw [letSub_eps]
    rfl
  have h2 : zzDr.eps id zlRho = .bvar 2 := rfl
  unfold CL at h
  rw [h1, h2] at h
  exact not_convMod_bvar_ne hW (by decide) h

/-- `zeta_reduct_cl` is FALSE at `tableOfI EnvWfT.empty`: the wall fails on
    `zzDr` at the canonical disposition, with the lemma's premises (`hA`,
    `hv`, `hb`, `dl`, `dr`, `σ`, `ρ`) all inhabited. -/
theorem zeta_reduct_cl_refuted :
    ¬ ZetaReductWall (tableOfI EnvWfT.empty) := by
  intro h
  exact not_cl_zeta_reduct_tableWF _ (tableWF_tableOfI_full EnvWfT.empty)
    (h zzHA zzHV zzHB zzWkDl zzDr id zlRho)

end Rcic.Syn

#print axioms Rcic.Syn.ZetaSurfaceWall
#print axioms Rcic.Syn.ZetaReductWall
#print axioms Rcic.Syn.not_cl_zeta_surface_tableWF
#print axioms Rcic.Syn.zeta_surface_cl_refuted
#print axioms Rcic.Syn.not_cl_zeta_reduct_tableWF
#print axioms Rcic.Syn.zeta_reduct_cl_refuted

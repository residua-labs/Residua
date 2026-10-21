import rcic.RcicSynSRBetaZetaField
import rcic.RcicSynRedex
import rcic.RcicSynRead
import rcic.RcicSynInstEnd

/-!
# sortRow census row 2 (`es_beta`) at `tableOfI` — `beta_body_cl` and
# `beta_reduct_cl` refuted; `beta_body_tag` restated as an open wall

GLM lane `glm-sr1` (rows 2/3/4), `research/rcic/sortrow/TABLEOFI_SUPPLIER_CENSUS.md`
row 2, BRIEF 2026-10-20. `closure_claim = 0`.

The census lists three missing lemmas for row 2, the three verbatim
`(d)` ports of `BetaClPortsClosed` (RcicSynClosedEsbeta.lean:487) that
`es_beta_closed` consumes through `BetaFieldResidClosed`'s `clause`/`raw`
arms at `r := readRedex (envExt_refl E) Aw dl rfl`. Each is restated here
as ONE named `Prop` with exactly `toBetaClPorts`'s binder list (the closer's
telescope plus the read's `g` and `hr`; `S`/`hq`/`ih` do not occur in the
port statements):

* `beta_body_cl` = `BetaBodyClWall` — FALSE at `tableOfI EnvWfT.empty`
  (`beta_body_cl_refuted`).
* `beta_reduct_cl` = `BetaReductClWall` — FALSE at `tableOfI EnvWfT.empty`
  (`beta_reduct_cl_refuted`).
* `beta_body_tag` = `BetaBodyTagWall` — restated, left open (see the
  module boundary note below).

The fixture is the row-3/4 `wkZetaCtx` double-lift wedge, beta-shaped:
`dl` is a `TyP.wk` at `c = 1` of a canonical `TyP.app (TyP.lam …) …` in
`zetaLetCtx` with `A = sort 1`, inner body `.bvar 1`, `arg = .bvar 0`.
The read of that `dl` is `.yes` with `g.hbody` the `pushRedexWk` body, a
`TyP.wk` at `c = 2` of the lam's direct `.bvar 1` body typing, wrapped in
`tyCastCtx`/`tyCast` (`bGot`, `bDl_hr`). At the canonical disposition
`zlRho`:

* `g.hbody.eps id (binderDisp false :: zlRho) = .bvar 3` — the `wk` lifts
  the inert `.inline (.bvar 1)` value twice (the same wedge the landed
  `not_es_wk_inline` pins) — while the direct `bHBody` erases to `.bvar 2`
  (`not_convMod_bvar_ne`): `beta_body_cl` dies.
* `(instEnd bHBody bHArg bHA).eps id zlRho = ETm.inst 0 (.bvar 1) (.bvar 2)
  = .bvar 1` (landed `instEnd_eps_keep`) while `bDr = zlWkDl` erases to
  `.bvar 2` (`not_convMod_bvar_ne`): `beta_reduct_cl` dies.

`dl.eps id zlRho = .app (.lam (.bvar 3)) (.bvar 2)` is not `★`
(`bDl_eps_not_star`), so the real `epsReadRedex` verdict at the refuting
fixtures is `clause` or `raw` — both arms of `BetaFieldResidClosed` carry
`BetaClPortsClosed`, so the closer consumes the refuted ports at exactly
these binders.

`beta_body_tag` is NOT refuted: at every audited fixture family the two
iff legs' `★`-behaviour is coherent (the `wk` lift and the `resolve` walks
hit the same drop slots, `ETm.lift` preserves `★`, and both bvar `u`-bits
are the shared `B`-level), and an `esub`/`lsub`-headed `hbody` with a
landed `★` needs a removed-slot/subject pattern the `assumption`/`letBinding`
contexts above cannot supply. The wall stays the named `Prop` below, not
bundled, not supplied.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the three walls, each restated as ONE named `Prop` -/

/-- `beta_body_cl`, the census row-2 body missing lemma, as ONE named
    `Prop`: `BetaClPortsClosed.bodyCl` at the read's `g`, verbatim (the
    binders are `toBetaClPorts`'s). False at `tableOfI EnvWfT.empty`
    (`beta_body_cl_refuted`). -/
def BetaBodyClWall (tbl : List CRule) : Prop :=
  ∀ {Aw : Nat → Nat} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (σ : Level → Level) (ρ : List Disp)
    (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg)
    (hr : readRedex (envExt_refl E) Aw dl rfl = .yes g),
    CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) g.hbody hbody

/-- `beta_body_tag`, the census row-2 body-tag missing lemma, as ONE named
    `Prop`: `BetaClPortsClosed.bodyTag` at the read's `g`, verbatim.
    Restated as an open wall (not refuted, not supplied). -/
def BetaBodyTagWall (tbl : List CRule) : Prop :=
  ∀ {Aw : Nat → Nat} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (σ : Level → Level) (ρ : List Disp)
    (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg)
    (hr : readRedex (envExt_refl E) Aw dl rfl = .yes g),
    (g.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
    (hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star)

/-- `beta_reduct_cl`, the census row-2 reduct missing lemma, as ONE named
    `Prop`: `BetaClPortsClosed.reductCl` at the read's `g`, verbatim.
    False at `tableOfI EnvWfT.empty` (`beta_reduct_cl_refuted`). -/
def BetaReductClWall (tbl : List CRule) : Prop :=
  ∀ {Aw : Nat → Nat} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (σ : Level → Level) (ρ : List Disp)
    (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg)
    (hr : readRedex (envExt_refl E) Aw dl rfl = .yes g),
    CL tbl σ ρ (instEnd hbody harg hA) dr

/-! ## §2 the fixture: `A = sort 1`, inner body `.bvar 1`, `arg = .bvar 0`,
`dl` = `TyP.wk` at `c = 1` of the canonical app typing in `zetaLetCtx` -/

/-- Any weight function; the read is `.yes` for every `Aw`. -/
def bAw : Nat → Nat := fun _ => 0

def ibHA : TyP emptyEnv 0 zetaLetCtx (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) :=
  TyP.sort emptyEnv 0 zetaLetCtx (.succ (.zero))
    (.succ (.succ .zero)) (eqN_refl _)

/-- The lam's body typing: direct `.bvar 1` in `assumption (sort 1) ::
zetaLetCtx` (index 1 = the `letBinding`, type `sort 1`). -/
def ibHBody : TyP emptyEnv 0 (.assumption (.sort (.succ .zero)) :: zetaLetCtx)
    (.bvar 1) (.sort (.succ .zero)) :=
  TyP.bvar emptyEnv 0 (.assumption (.sort (.succ .zero)) :: zetaLetCtx)
    1 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
    (TyP.sort emptyEnv 0 (.assumption (.sort (.succ .zero)) :: zetaLetCtx)
      (.succ (.zero)) (.succ (.succ (.zero))) (eqN_refl _))

def ibHB : TyP emptyEnv 0 (.assumption (.sort (.succ .zero)) :: zetaLetCtx)
    (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  TyP.sort emptyEnv 0 (.assumption (.sort (.succ .zero)) :: zetaLetCtx)
    (.succ (.zero)) (.succ (.succ (.zero))) (eqN_refl _)

/-- The canonical inner app typing in `zetaLetCtx`:
    `.app (.lam (sort 1) (.bvar 1)) (.bvar 0)`. -/
def bApp : TyP emptyEnv 0 zetaLetCtx
    (.app (.lam (.sort (.succ .zero)) (.bvar 1)) (.bvar 0))
    (instantiate0 (.bvar 0) (.sort (.succ .zero))) :=
  TyP.app emptyEnv 0 zetaLetCtx (.lam (.sort (.succ .zero)) (.bvar 1))
    (.bvar 0) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.succ (.succ .zero))
    (TyP.lam emptyEnv 0 zetaLetCtx (.sort (.succ .zero))
      (.succ (.succ .zero)) (.bvar 1) (.sort (.succ .zero))
      (.succ (.succ .zero)) ibHA ibHBody ibHB)
    zlInner
    (TyP.sort emptyEnv 0 zetaLetCtx (.succ (.zero))
      (.succ (.succ .zero)) (eqN_refl _))

/-- `dl`: the read surface, `TyP.wk` at `c = 1` of `bApp` into
    `wkZetaCtx`; the lifted subject is `.app (.lam (sort 1) (.bvar 1))
    (.bvar 0)` (index 1 is below both cutoffs). -/
def bDl : TyP emptyEnv 0 wkZetaCtx
    (.app (.lam (.sort (.succ .zero)) (.bvar 1)) (.bvar 0))
    (instantiate0 (.bvar 0) (.sort (.succ .zero))) :=
  TyP.wk emptyEnv 0 zetaLetCtx
    (.app (.lam (.sort (.succ .zero)) (.bvar 1)) (.bvar 0))
    (instantiate0 (.bvar 0) (.sort (.succ .zero)))
    (.assumption (.sort (.succ .zero))) 1 bApp

/-- The closer-telescope surface fixtures at `Γ = wkZetaCtx`:
    `hA`, the direct `hbody`, the direct `harg`, and `dr = zlWkDl`
    (its subject `.bvar 0` is `instantiate0 (.bvar 0) (.bvar 1)`). -/
def bHA : TyP emptyEnv 0 wkZetaCtx (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) :=
  TyP.sort emptyEnv 0 wkZetaCtx (.succ (.zero))
    (.succ (.succ .zero)) (eqN_refl _)

def bHBody : TyP emptyEnv 0 (.assumption (.sort (.succ .zero)) :: wkZetaCtx)
    (.bvar 1) (.sort (.succ .zero)) :=
  TyP.bvar emptyEnv 0 (.assumption (.sort (.succ .zero)) :: wkZetaCtx)
    1 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
    (TyP.sort emptyEnv 0 (.assumption (.sort (.succ .zero)) :: wkZetaCtx)
      (.succ (.zero)) (.succ (.succ .zero)) (eqN_refl _))

def bHArg : TyP emptyEnv 0 wkZetaCtx (.bvar 0) (.sort (.succ .zero)) :=
  TyP.bvar emptyEnv 0 wkZetaCtx 0 (.sort (.succ .zero))
    (.succ (.succ .zero)) rfl bHA

def bDr : TyP emptyEnv 0 wkZetaCtx
    (instantiate0 (.bvar 0) (.bvar 1))
    (instantiate0 (.bvar 0) (.sort (.succ .zero))) := zlWkDl

/-! ## §3 the read is `.yes`; its `g`; the consumed verdict arm -/

theorem bDl_read_isYes :
    (readRedex (envExt_refl emptyEnv) bAw bDl rfl).isYes = true := by rfl

/-- The read's `RedexGot`: `g.hbody` is `pushRedexWk`'s, a `tyCastCtx`/
    `tyCast`-wrapped `TyP.wk` at `c = 2` of the lam's `ibHBody`. The `.no`
    arm is dead by `bDl_read_isYes`. -/
def bGot : RedexGot bAw (bDl.wt bAw) emptyEnv 0 wkZetaCtx
    (.sort (.succ .zero)) (.bvar 1) (.bvar 0) :=
  match h : readRedex (envExt_refl emptyEnv) bAw bDl rfl with
  | .yes g => g
  | .no => (by
      have hy := bDl_read_isYes
      rw [h] at hy
      exact Bool.noConfusion hy)

theorem bDl_hr : readRedex (envExt_refl emptyEnv) bAw bDl rfl = .yes bGot := by
  cases hr : readRedex (envExt_refl emptyEnv) bAw bDl rfl with
  | yes g =>
      have hg : bGot = g := by
        unfold bGot
        split
        · next g' heq =>
            rw [hr] at heq
            injection heq with he
            rw [he]
        · next heq =>
            have hy := bDl_read_isYes
            rw [heq] at hy
            exact Bool.noConfusion hy
      rw [hg]
  | no =>
      have hy := bDl_read_isYes
      rw [hr] at hy
      exact Bool.noConfusion hy

/-- `dl.eps id zlRho` is a concrete application, not `★`: the `star`
    verdict constructor (which carries `dl.eps = .star`) is impossible, so
    the real `epsReadRedex` verdict at the refuting binders is `clause` or
    `raw` — the `BetaFieldResidClosed` arms that consume `BetaClPortsClosed`. -/
theorem bDl_eps_not_star : (bDl.eps id zlRho) ≠ .star := by
  intro h
  have hval : bDl.eps id zlRho =
      ETm.app (ETm.lam (.bvar 3)) (.bvar 2) := rfl
  rw [hval] at h
  exact ETm.noConfusion h

/-! ## §4 `beta_body_cl` refuted -/

/-- For every `TableWF tbl`: at the canonical disposition the read's body
    erases to `.bvar 3` (the `wk` lifts the inert `.inline (.bvar 1)`
    value twice) while the direct `bHBody` erases to `.bvar 2`. -/
theorem not_cl_beta_body_tableWF (tbl : List CRule) (hW : TableWF tbl) :
    ¬ CL tbl id (binderDisp (levelIsZero (id (.succ (.succ .zero)))) :: zlRho)
      bGot.hbody bHBody := by
  intro h
  have h1 : bGot.hbody.eps id
      (binderDisp (levelIsZero (id (.succ (.succ .zero)))) :: zlRho) = .bvar 3 := rfl
  have h2 : bHBody.eps id
      (binderDisp (levelIsZero (id (.succ (.succ .zero)))) :: zlRho) = .bvar 2 := rfl
  unfold CL at h
  rw [h1, h2] at h
  exact not_convMod_bvar_ne hW (by decide) h

/-- `beta_body_cl` is FALSE at `tableOfI EnvWfT.empty`: the wall fails on
    the read of `bDl` at the canonical disposition, with the lemma's
    premises (`hA`, `hbody`, `harg`, `dl`, `dr`, `σ`, `ρ`, `g`, `hr`) all
    inhabited, `g` the real read output. -/
theorem beta_body_cl_refuted : ¬ BetaBodyClWall (tableOfI EnvWfT.empty) := by
  intro h
  exact not_cl_beta_body_tableWF _ (tableWF_tableOfI_full EnvWfT.empty)
    (h bHA bHBody bHArg bDl bDr id zlRho bGot bDl_hr)

/-! ## §5 `beta_reduct_cl` refuted -/

/-- For every `TableWF tbl`: `instEnd bHBody bHArg bHA` erases to
    `ETm.inst 0 (.bvar 1) (.bvar 2) = .bvar 1` (landed `instEnd_eps_keep`)
    while `bDr = zlWkDl` erases to `.bvar 2`. -/
theorem not_cl_beta_reduct_tableWF (tbl : List CRule) (hW : TableWF tbl) :
    ¬ CL tbl id zlRho (instEnd bHBody bHArg bHA) bDr := by
  intro h
  have h1 : (instEnd bHBody bHArg bHA).eps id zlRho = .bvar 1 := by
    rw [instEnd_eps_keep bHBody bHArg bHA
      (hu := (show levelIsZero (id (.succ (.succ .zero))) = false from rfl))]
    rfl
  have h2 : bDr.eps id zlRho = .bvar 2 := rfl
  unfold CL at h
  rw [h1, h2] at h
  exact not_convMod_bvar_ne hW (by decide) h

/-- `beta_reduct_cl` is FALSE at `tableOfI EnvWfT.empty`: same fixtures,
    same inhabited premises; `bDr = zlWkDl` is the row-4 double-lift
    reduct surface. -/
theorem beta_reduct_cl_refuted :
    ¬ BetaReductClWall (tableOfI EnvWfT.empty) := by
  intro h
  exact not_cl_beta_reduct_tableWF _ (tableWF_tableOfI_full EnvWfT.empty)
    (h bHA bHBody bHArg bDl bDr id zlRho bGot bDl_hr)

end Rcic.Syn

#print axioms Rcic.Syn.BetaBodyClWall
#print axioms Rcic.Syn.BetaBodyTagWall
#print axioms Rcic.Syn.BetaReductClWall
#print axioms Rcic.Syn.bDl_read_isYes
#print axioms Rcic.Syn.bGot
#print axioms Rcic.Syn.bDl_hr
#print axioms Rcic.Syn.bDl_eps_not_star
#print axioms Rcic.Syn.not_cl_beta_body_tableWF
#print axioms Rcic.Syn.beta_body_cl_refuted
#print axioms Rcic.Syn.not_cl_beta_reduct_tableWF
#print axioms Rcic.Syn.beta_reduct_cl_refuted

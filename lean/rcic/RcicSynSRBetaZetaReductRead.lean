/-
# `RcicSynSRBetaZetaReductRead` — `beta_reduct_cl` restated at the read's own `instEnd`

`BetaReductClWall` (refuted, `beta_reduct_cl_refuted`) built the canonical
reduct from the NODE-side `hbody`/`harg`.  Under a `wk`-transported read the
read's `g.hbody` carries an extra `keep`-lift (`.bvar 3` where the direct
`hbody` gives `.bvar 2` on the `wkZetaCtx` double-lift), so
`instEnd hbody harg hA` erases to `.bvar 1` while `dr` erases to `.bvar 2`.

The same `inst 0` that broke the node-side reduct heals the read-side one:
`inst 0 (.bvar 2) (.bvar 3) = .bvar 2`.  `ReductClReadWall` restates the
clause with the READ's `instEnd` — `instEnd g.hbody (tyCast .. g.harg) hA'` —
which is also the `es_beta` consumption shape: the β-step out of `dl.eps`
through `redexClauseOf g` produces exactly
`inst 0 (g.harg.eps σ ρ) (g.hbody.eps σ (.keep :: ρ))`, the read-side
`instEnd`'s eps (`instEnd_eps_keep`).  With `reductCl` in this form the
landed `argCl`/`bodyCl` transports (both refuted on the wedge) are no longer
on the chain.

New premises vs `BetaReductClWall`:

- `hAA : g.Aarg = A` — the recovered argument domain is the lam's domain;
  `RedexGot` carries no `Cv` compatibility field, so this is exposed.
- `hA' : TyP E n Γ A (.sort u')` — a sort typing of the domain, e.g.
  `g.harg.reg.2` (its subject is `g.Aarg`, `= A` by `hAA`).

The wedge instance is inhabited: `reductClRead_wedge` proves the corrected
clause at the same fixtures that refuted `beta_reduct_cl`.  The wall itself
stays open — `instEnd` is a synthesized node, never a `subAt` occurrence, so
no `occ_cl` row can issue it.

§3 pins `RedexBodyAPWall` on-cone twice: inhabited on the direct `bApp`
surface, vacuous on the `wk`-transported `bDl` (which is off-`AssumpPref`
at its outermost row).
-/

import rcic.RcicSynSRBetaZetaBeta
import rcic.RcicSynSRBetaZetaIssueCT

namespace Rcic.Syn

open Rcic.Declarative

/-- `beta_reduct_cl`, corrected: `CL` between the read's own
    `instEnd g.hbody g.harg hA'` and `dr`. -/
def ReductClReadWall (tbl : List CRule) : Prop :=
  ∀ {Aw : Nat → Nat} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (σ : Level → Level) (ρ : List Disp)
    (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg)
    (hr : readRedex (envExt_refl E) Aw dl rfl = .yes g)
    (hAA : g.Aarg = A) (u' : Level) (hA' : TyP E n Γ A (.sort u')),
    CL tbl σ ρ (instEnd g.hbody (tyCast rfl hAA g.harg) hA') dr

/-! ## the wedge instance is inhabited -/

theorem bGot_Aarg : bGot.Aarg = .sort (.succ .zero) := rfl

theorem bGot_hbody_eps_keep :
    bGot.hbody.eps id (.keep :: zlRho) = .bvar 3 := rfl

theorem bGot_harg_eps : bGot.harg.eps id zlRho = .bvar 2 := rfl

/-- The corrected clause at the refuting fixtures:
    `instEnd bGot.hbody bGot.harg (bGot.harg.reg.2)` erases to
    `inst 0 (.bvar 2) (.bvar 3) = .bvar 2 = bDr.eps` — kernel-checked. -/
theorem reductClRead_wedge :
    CL (tableOfI EnvWfT.empty) id zlRho
      (instEnd bGot.hbody (tyCast rfl rfl bGot.harg) bGot.harg.reg.2) bDr := by
  have h1 : (instEnd bGot.hbody (tyCast rfl rfl bGot.harg)
      bGot.harg.reg.2).eps id zlRho = .bvar 2 := by
    rw [instEnd_eps_keep _ _ _
      (hu := (show levelIsZero (id bGot.harg.reg.1) = false from rfl))]
    rfl
  have h2 : bDr.eps id zlRho = .bvar 2 := rfl
  unfold CL
  rw [h1, h2]
  exact ConvMod.refl _

/-- The wall instantiated at the wedge fixtures — all premises inhabited
    (`bGot.harg.reg.2` supplies the domain's sort typing). -/
theorem reductClReadWall_at_wedge :
    ReductClReadWall (tableOfI EnvWfT.empty) →
      CL (tableOfI EnvWfT.empty) id zlRho
        (instEnd bGot.hbody (tyCast rfl rfl bGot.harg) bGot.harg.reg.2) bDr :=
  fun h => h bHA bHBody bHArg bDl bDr id zlRho bGot bDl_hr rfl _
    bGot.harg.reg.2

/-! ## §3 `RedexBodyAPWall` — pinned on-cone instances

`RedexBodyAPWall` carries no `CL` clause — the refuted double-lift wedge
does not touch it.  Two on-cone pins of its conclusion:

- `redexBodyAP_bApp`: the DIRECT app surface `bApp` — `bApp.AssumpPref`
  is inhabited (all leaves are `sort`/`bvar`; no transport rows at all)
  and `bAppGot.hbody = TyP.ewk ibHBody` keeps it (`AssumpPref` is
  `ewk`-transparent).  Premise and conclusion both inhabited — the wall's
  real shape.
- `redexBodyAP_bDl`: the `wk`-transported surface `bDl` —
  `bDl.AssumpPref` is FALSE (`AssumptionPrefix zetaLetCtx 1` fails: the
  take-1 prefix is `[.letBinding …]`), so the implication is vacuous.
  The double-lift wedge lives off-`AssumpPref` entirely — it violates
  `bodyCl`, never this wall. -/

/-- `bApp` is `AssumpPref`-inhabited: `app`/`lam`/`bvar`/`sort` leaves only. -/
theorem bApp_assumpPref : bApp.AssumpPref :=
  ⟨⟨trivial, trivial, trivial⟩, trivial, trivial⟩

/-- `bDl`'s `wk` sits at `c = 1` over `zetaLetCtx`, whose take-1 prefix is
    the `.letBinding` — `AssumpPref` fails at the outermost row. -/
theorem bDl_not_assumpPref : ¬ bDl.AssumpPref :=
  fun h => not_assumptionPrefix_zetaLetCtx_one h.1

/-- `bApp`'s redex read is `.yes` (the lam is `TyP.lam`-rooted). -/
theorem bApp_read_isYes :
    (readRedex (envExt_refl emptyEnv) bAw bApp rfl).isYes = true := rfl

/-- `bApp`'s read output; `g.hbody = TyP.ewk ibHBody`, `g.harg =
    TyP.ewk zlInner`, `g.Aarg = .sort 1`. -/
def bAppGot : RedexGot bAw (bApp.wt bAw) emptyEnv 0 zetaLetCtx
    (.sort (.succ .zero)) (.bvar 1) (.bvar 0) :=
  match h : readRedex (envExt_refl emptyEnv) bAw bApp rfl with
  | .yes g => g
  | .no => (by
      have hy := bApp_read_isYes
      rw [h] at hy
      exact Bool.noConfusion hy)

theorem bApp_hr :
    readRedex (envExt_refl emptyEnv) bAw bApp rfl = .yes bAppGot := by
  cases hr : readRedex (envExt_refl emptyEnv) bAw bApp rfl with
  | yes g =>
      have hg : bAppGot = g := by
        unfold bAppGot
        split
        · next g' heq =>
            rw [hr] at heq
            injection heq with he
            rw [he]
        · next heq =>
            have hy := bApp_read_isYes
            rw [heq] at hy
            exact Bool.noConfusion hy
      rw [hg]
  | no =>
      have hy := bApp_read_isYes
      rw [hr] at hy
      exact Bool.noConfusion hy

/-- `bAppGot.hbody` is `TyP.ewk ibHBody`: `ewk`-transparent `AssumpPref`
    reduces to `ibHBody`'s, a `bvar`-of-`sort` — `True`. -/
theorem bAppGot_hbody_assumpPref : bAppGot.hbody.AssumpPref := trivial

/-- The inhabited pin: `bApp`'s read preserves `AssumpPref`, both sides
    inhabited. -/
theorem redexBodyAP_bApp :
    bApp.AssumpPref → bAppGot.hbody.AssumpPref :=
  fun _ => bAppGot_hbody_assumpPref

/-- The vacuous pin on the `wk` surface: `bDl` is off-`AssumpPref`. -/
theorem redexBodyAP_bDl :
    bDl.AssumpPref → bGot.hbody.AssumpPref :=
  fun h => absurd h bDl_not_assumpPref

/-- `RedexBodyAPWall` instantiated at `bApp` — binders typecheck against
    the real fixture and real read. -/
theorem redexBodyAPWall_at_bApp :
    RedexBodyAPWall → (bApp.AssumpPref → bAppGot.hbody.AssumpPref) :=
  fun h => h (envExt_refl emptyEnv) bApp rfl bAppGot bApp_hr

end Rcic.Syn

#print axioms Rcic.Syn.ReductClReadWall
#print axioms Rcic.Syn.bGot_Aarg
#print axioms Rcic.Syn.bGot_hbody_eps_keep
#print axioms Rcic.Syn.bGot_harg_eps
#print axioms Rcic.Syn.reductClRead_wedge
#print axioms Rcic.Syn.reductClReadWall_at_wedge
#print axioms Rcic.Syn.bApp_assumpPref
#print axioms Rcic.Syn.bDl_not_assumpPref
#print axioms Rcic.Syn.bApp_read_isYes
#print axioms Rcic.Syn.bAppGot
#print axioms Rcic.Syn.bApp_hr
#print axioms Rcic.Syn.bAppGot_hbody_assumpPref
#print axioms Rcic.Syn.redexBodyAP_bApp
#print axioms Rcic.Syn.redexBodyAP_bDl
#print axioms Rcic.Syn.redexBodyAPWall_at_bApp

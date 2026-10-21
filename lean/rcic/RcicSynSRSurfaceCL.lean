import rcic.RcicSynSRBetaZetaBeta
import rcic.RcicSynSRBetaZetaField
import rcic.RcicSynSRBetaZetaLocal
import rcic.RcicSynSRClEutClCase

/-!
# RcicSynSRSurfaceCL — the surface-CL wall family under ONE predicate

The sortRow surface-CL walls of #7780 (rows 2/3/4: `BetaBodyClWall`,
`BetaBodyTagWall`'s siblings `BetaBodyClWall`/`BetaReductClWall`,
`ZetaSurfaceWall`, `ZetaReductWall`, `ZetaLocalSurfaceWall`,
`ZetaLocalResConvWall`) and row 14's `cl_case_wall` (#7781,
`RcicSynSRClEutClCase`) all stop at one goal shape: coherence, at `tbl`,
between a display datum built inside the step and the given datum. That
common goal has exactly three syntactic faces:

* face A — the `CL` conclusion itself: two typings of one term in one
  context erase to `ConvMod (EStep tbl) LvlEq`-convertible erasures
  (beta body/reduct, zeta surface/reduct, zetaLocal surface);
* face B — the zetaLocal display routing: a non-inlined `.bvar i` resolves
  to the erasure of its stored value's typing (`zetaLocal_res_conv`);
* face C — the gate bit: two sort-typings of one member's instantiations
  agree on `levelIsZero` when the instantiations differ (`ClConstPorts.hbit`).

`SurfaceCLAt tbl` is the ∀-closure of these three faces over their
goal-relevant data only. It is NOT the conjunction of the walls: every
closer-telescope binder the walls carry and their goal does not mention
(`hA`/`harg`/`g`/`hr` receipts, `dr` in face B, the `cl_case_wall`
member/gate receipts) is dropped. Each wall is an instance of a face
(`surfaceCLAt_*_cl` below), and the family question reduces to ONE prop.

Verdict: `SurfaceCLAt (tableOfI EnvWfT.empty)` is FALSE
(`surfaceCLAt_tableOfI_refuted`) — by modus tollens through
`beta_body_cl_refuted`, the read's `pushRedexWk` double-lift wedge at a
`TableWF` table. No uniform surface-coherence supply exists for this
family at `tableOfI`. Not a supply; `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- The common goal of the surface-CL wall family at `tbl`: the ∀-closure
    of the three goal faces (same-subject `CL`, zetaLocal resolve routing,
    gate-bit coherence) over goal-relevant data. -/
def SurfaceCLAt (tbl : List CRule) : Prop :=
  (∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
      (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
      (σ : Level → Level) (ρ : List Disp),
      CL tbl σ ρ D₁ D₂)
  ∧ (∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A v : Expr Nat}
      (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
      (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A)
      (σ : Level → Level) (ρ : List Disp),
      levelIsZero (σ dl.reg.1) = false →
      ConvMod (EStep tbl) LvlEq (resolve ρ i) (hv.eps σ ρ))
  ∧ (∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ls₁ ls₂ : List Level}
      {m : CheckedMember} {u₁ u₂ : Level}
      (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
      (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂))
      (σ : Level → Level),
      ls₁ ≠ ls₂ → levelIsZero (σ u₁) = levelIsZero (σ u₂))

/-! ## Face instances: `SurfaceCLAt` implies each wall of the family -/

/-- Row 2 `beta_body_cl`: the wall's `CL` goal is face A at the read's
    surface `g.hbody` vs the given `hbody`, display list
    `binderDisp (levelIsZero (σ u)) :: ρ`. -/
theorem surfaceCLAt_beta_body_cl (tbl : List CRule) (h : SurfaceCLAt tbl) :
    BetaBodyClWall tbl :=
  fun _hA hbody _harg _dl _dr σ ρ g _hr =>
    h.1 g.hbody hbody σ (binderDisp (levelIsZero (σ _)) :: ρ)

/-- Row 2 `beta_reduct_cl`: face A at the step-built `instEnd` surface vs
    the given `dr`. -/
theorem surfaceCLAt_beta_reduct_cl (tbl : List CRule) (h : SurfaceCLAt tbl) :
    BetaReductClWall tbl :=
  fun hA hbody harg _dl dr σ ρ _g _hr => h.1 (instEnd hbody harg hA) dr σ ρ

/-- Row 3 `zeta_surface_cl`: face A at the given `dl` vs the step-built
    `TyP.letE` surface. -/
theorem surfaceCLAt_zeta_surface_cl (tbl : List CRule) (h : SurfaceCLAt tbl) :
    ZetaSurfaceWall tbl :=
  fun hA hv hb dl _dr σ ρ =>
    h.1 dl (TyP.letE _ _ _ _ _ _ _ _ dl.reg.1 hA hv hb dl.reg.2) σ ρ

/-- Row 3 `zeta_reduct_cl`: face A at the step-built `letSub` surface vs
    the given `dr`. -/
theorem surfaceCLAt_zeta_reduct_cl (tbl : List CRule) (h : SurfaceCLAt tbl) :
    ZetaReductWall tbl :=
  fun hA hv hb _dl dr σ ρ => h.1 (letSub hb hv hA) dr σ ρ

/-- Row 4 `zetaLocal_surface_cl`: face A at the given `dl` vs the step's
    `zetaLocalBvarSurface` surface. -/
theorem surfaceCLAt_zetaLocal_surface_cl (tbl : List CRule)
    (h : SurfaceCLAt tbl) : ZetaLocalSurfaceWall tbl :=
  fun hty dl σ ρ => h.1 dl (zetaLocalBvarSurface hty dl) σ ρ

/-- Row 4 `zetaLocal_res_conv`: the wall's display-side `ConvMod` goal is
    face B verbatim (the wall's `dr` binder is goal-irrelevant). -/
theorem surfaceCLAt_zetaLocal_res_conv (tbl : List CRule)
    (h : SurfaceCLAt tbl) : ZetaLocalResConvWall tbl :=
  fun hval hty hv dl _dr σ ρ hgd => h.2.1 hval hty hv dl σ ρ hgd

/-- Row 14 `cl_case_wall` (#7781): the wall's goal `ClConstPorts` has the
    single field `hbit`, which is face C at the cell's own `hT₁`/`hT₂`. -/
theorem surfaceCLAt_cl_case {E : ResolvedEnv} (hW : EnvWfT E)
    (h : SurfaceCLAt (tableOfI hW)) : cl_case_wall hW :=
  fun _hres₁ _hlen₁ _hwf₁ _hls₁ hT₁ _hres₂ _hlen₂ _hwf₂ _hls₂ hT₂ =>
    ⟨fun hne => h.2.2 hT₁ hT₂ _ hne⟩

/-! ## The family verdict at `tableOfI` -/

/-- `SurfaceCLAt` is FALSE at `tableOfI EnvWfT.empty`: modus tollens of
    `surfaceCLAt_beta_body_cl` and `beta_body_cl_refuted` (#7780's
    kernel refutation — the read's `pushRedexWk` double-lift wedge, which
    needed `TableWF (tableOfI EnvWfT.empty)`). This refutes exactly
    `SurfaceCLAt`; by the implications above, no uniform surface-coherence
    supply closes the family at `tableOfI`. -/
theorem surfaceCLAt_tableOfI_refuted :
    ¬ SurfaceCLAt (tableOfI EnvWfT.empty) :=
  fun h => beta_body_cl_refuted (surfaceCLAt_beta_body_cl _ h)

end Rcic.Syn

#print axioms Rcic.Syn.SurfaceCLAt
#print axioms Rcic.Syn.surfaceCLAt_beta_body_cl
#print axioms Rcic.Syn.surfaceCLAt_beta_reduct_cl
#print axioms Rcic.Syn.surfaceCLAt_zeta_surface_cl
#print axioms Rcic.Syn.surfaceCLAt_zeta_reduct_cl
#print axioms Rcic.Syn.surfaceCLAt_zetaLocal_surface_cl
#print axioms Rcic.Syn.surfaceCLAt_zetaLocal_res_conv
#print axioms Rcic.Syn.surfaceCLAt_cl_case
#print axioms Rcic.Syn.surfaceCLAt_tableOfI_refuted




import rcic.RcicSynSRBetaZetaStepWRows
import rcic.RcicSynSRLitPiEswLegs
import rcic.RcicSynSRLitPiEswPi

/-!
# `RcicSynSRLitPiCLW` — THE common wall: typing-erasure coherence at routed displays

cc 2026-10-20 22:50Z: after epsW + `LevelHom`, the sortRow CLW walls (rows
2/3/4), `ZetaLocalResConvWallRoutedW`, `litW_erasure_unique_wall` (row 7) and
the 1/5/8/10 field walls all reduce to one statement — for the same subject,
two typings at the same routed display have `ConvMod`-related `epsW` erasures.

§0 states it (`TypingEpsCoherenceW`). §1 is the check `wall <- coherence`:
a one-line theorem wherever the wall follows on the cone `Demand` actually
supplies (`Demand.hom`, `Demand.routed`), and a named reason + residual Prop
wherever it does not. §2 attacks coherence by induction.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §0 THE common wall -/

/-- Typing-erasure coherence at routed displays: at the canonical table of
    `hW`, any two typings of the same subject, at a homomorphic level map
    and a routed display, erase convertibly. Table from `hW`, typings at
    any environment (the rows consume the walls exactly so). -/
def TypingEpsCoherenceW : Prop :=
  ∀ {E : ResolvedEnv} (hW : EnvWfT E) {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E' n Γ e T₁) (D₂ : TyP E' n Γ e T₂)
    {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp}
    (hρ : RoutedDisp σ E' n Γ ρ),
    CLW (tableOfI hW) σ ρ D₁ D₂

#print axioms Rcic.Syn.TypingEpsCoherenceW

/-! ## §1 the check `wall <- coherence`

The demand cone first: every demanded query is hom'd and routed
(`Demand.hom`/`Demand.routed`), so the on-cone instances below are the ones
the rows actually consume. -/

/-- `coherence` supplies `TransportHeadSortAtW` on-cone at `tableOfI hW`:
    every `thsaW_*` decoder leg (rows 1/5/8) is thereby fed by coherence. -/
theorem thsaW_of_coherence (coh : TypingEpsCoherenceW) {E : ResolvedEnv} (hW : EnvWfT E)
    {E' : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} (D : TyP E' n Γ e T)
    {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp} (hρ : RoutedDisp σ E' n Γ ρ) :
    TransportHeadSortAtW (tableOfI hW) σ hσ ρ D :=
  fun D' => coh hW _ _ hσ hρ

/-! ### rows 2/3 (`es_zeta`/`es_beta`): the four CLW walls

None of the four follows from coherence AS STATED: each quantifies `σ`/`ρ`
(and `tbl`) with no cone hypotheses, while coherence claims only the
`LevelHom`/`RoutedDisp` instances at `tableOfI hW`. What follows, one line
each, is the on-cone instance — and that is all the row consumes
(`esW_zeta_field_of_coherence` below supplies the field from coherence
alone, via `Demand.hom`/`Demand.routed`). -/

/-- `ZetaSurfaceClWallW` on-cone from coherence (row 3 wall 1). -/
theorem zetaSurfaceClWallW_cone_of_coherence (coh : TypingEpsCoherenceW)
    {E : ResolvedEnv} (hW : EnvWfT E) {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E' n Γ A (.sort u)) (hv : TyP E' n Γ value A)
    (hb : TyP E' n (.letBinding A value :: Γ) body B)
    (dl : TyP E' n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E' n Γ (instantiate0 value body) (instantiate0 value B))
    (σ : Level → Level) (hσ : LevelHom σ) (ρ : List Disp) (hρ : RoutedDisp σ E' n Γ ρ) :
    CLW (tableOfI hW) σ ρ dl
      (TyP.letE E' n Γ A u value B body dl.reg.1 hA hv hb dl.reg.2) :=
  coh hW _ _ hσ hρ

/-- `ZetaReductClWallW` on-cone from coherence (row 3 wall 2). -/
theorem zetaReductClWallW_cone_of_coherence (coh : TypingEpsCoherenceW)
    {E : ResolvedEnv} (hW : EnvWfT E) {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E' n Γ A (.sort u)) (hv : TyP E' n Γ value A)
    (hb : TyP E' n (.letBinding A value :: Γ) body B)
    (dl : TyP E' n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E' n Γ (instantiate0 value body) (instantiate0 value B))
    (σ : Level → Level) (hσ : LevelHom σ) (ρ : List Disp) (hρ : RoutedDisp σ E' n Γ ρ) :
    CLW (tableOfI hW) σ ρ (letSub hb hv hA) dr :=
  coh hW _ _ hσ hρ

/-! ### row 3 supplied from coherence alone -/

/-- The row-3 `StepSuppliersW.es_zeta` field from coherence ALONE (no wall
    premises): the query is demanded, so `Demand.hom`/`Demand.routed` put
    the consumption point on the cone, and the two `CLW` ports of
    `zeta_caseStepW_of_port_cls` are coherence instances. This is the
    exact content of `ZetaSurfaceClWallW`/`ZetaReductClWallW` the row
    actually uses. -/
theorem esW_zeta_field_of_coherence (coh : TypingEpsCoherenceW)
    {E : ResolvedEnv} (hW : EnvWfT E) {Aw : Nat → Nat} :
    ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A value body B : Expr Nat} {u : Level}
      (hA : TyP E' n Γ A (.sort u)) (hv : TyP E' n Γ value A)
      (hb : TyP E' n (.letBinding A value :: Γ) body B)
      (dl : TyP E' n Γ (.letE A value body) (instantiate0 value B))
      (dr : TyP E' n Γ (instantiate0 value body) (instantiate0 value B))
      (S : ScopedCtx E E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
      CaseStepW Aw (tableOfI hW)
        (.es (CvP.zeta E' n Γ A value body B u hA hv hb dl dr) S σ ρ) := by
  intro _ _ _ _ _ _ _ _ _ _ _ hA hv hb dl dr S σ ρ hq ih
  exact zeta_caseStepW_of_port_cls hA hv hb dl dr S σ ρ
    (coh hW _ _ (Demand.hom hq) (Demand.routed hq))
    (coh hW _ _ (Demand.hom hq) (Demand.routed hq)) hq ih

/-! ### row 4 (`es_zetaLocal`): the routed res-conv wall -/

/-- `ZetaLocalSurfaceClWallW` on-cone from coherence: the surface port is
    same-subject (`dl` vs `zetaLocalBvarSurface hty dl`, both typing
    `.bvar i`). -/
theorem zetaLocalSurfaceClWallW_cone_of_coherence (coh : TypingEpsCoherenceW)
    {E : ResolvedEnv} (hW : EnvWfT E) {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A : Expr Nat} (hty : lookupType Γ i = some A)
    (hv : TyP E' n Γ v A) (dl : TyP E' n Γ (.bvar i) A)
    (σ : Level → Level) (hσ : LevelHom σ) (ρ : List Disp) (hρ : RoutedDisp σ E' n Γ ρ) :
    CLW (tableOfI hW) σ ρ dl (zetaLocalBvarSurface hty dl) :=
  coh hW _ _ hσ hρ

/-- The definitional bridge: at the false bit, the bvar surface's `epsW`
    IS `resolve ρ i` (the `epsW` `.bvar` arm at the surface's own
    `dl.reg.1`). -/
theorem zetaLocalBvarSurface_epsW_resolve {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A : Expr Nat} (hty : lookupType Γ i = some A)
    (dl : TyP E n Γ (.bvar i) A) {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ dl.reg.1) = false) :
    (zetaLocalBvarSurface hty dl).epsW σ ρ = resolve ρ i := by
  simp [zetaLocalBvarSurface, TyP.epsW, hu]

#print axioms Rcic.Syn.zetaLocalSurfaceClWallW_cone_of_coherence
/-- `CLW` with all index discipline dropped: two typings of possibly
    different subjects at possibly different scopes erase convertibly.
    `CLW D₁ D₂` is definitionally `CLWx D₁ D₂` when the indices agree. -/
def CLWx (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx} {e₁ T₁ : Expr Nat}
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (D₁ : TyP E₁ n₁ Γ₁ e₁ T₁) (D₂ : TyP E₂ n₂ Γ₂ e₂ T₂) : Prop :=
  ConvMod (EStep tbl) LvlEq (D₁.epsW σ ρ) (D₂.epsW σ ρ)

/-- **The residual Prop.** `ZetaLocalResConvWallRoutedW` does NOT follow
    from coherence: its two typings have DIFFERENT subjects (`zetaLocalBvarSurface`
    types `.bvar i`, `hv` types the looked-up value `v`), and same-subject
    coherence is silent across subjects. Its exact content is the
    cross-subject extension below — coherence for the environment-linked
    pair (the stored value vs the bvar that resolves to it), a
    canonicity-scale fact about the re-typing universe of stored values. -/
def ClwBvarValueConeW (tbl : List CRule) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (σ : Level → Level) (hσ : LevelHom σ) (ρ : List Disp)
    (hρ : RoutedDisp σ E n Γ ρ),
    levelIsZero (σ dl.reg.1) = false →
    CLWx tbl σ ρ (zetaLocalBvarSurface hty dl) hv

/-- `ZetaLocalResConvWallRoutedW <- ClwBvarValueConeW`, one line modulo the
    definitional bridge: the res wall IS the cross-subject CLW between the
    bvar surface and the value typing. -/
theorem zetaLocalResConvWallRoutedW_of_clwBvarValue {tbl : List CRule}
    (h : ClwBvarValueConeW tbl) : ZetaLocalResConvWallRoutedW tbl := by
  intro E n Γ i A v hval hty hv dl dr σ hσ ρ hρ hu
  have hc : CLWx tbl σ ρ (zetaLocalBvarSurface hty dl) hv :=
    h hval hty hv dl dr σ hσ ρ hρ hu
  unfold CLWx at hc
  rw [zetaLocalBvarSurface_epsW_resolve hty dl hu] at hc
  exact hc

#print axioms Rcic.Syn.CLWx
#print axioms Rcic.Syn.ClwBvarValueConeW

/-- The canon display is routed (the cone's `canon` base): the on-cone
    claim below lives where the demand cone actually routes. -/
theorem clwBvarValueConeW_canon_routed :
    RoutedDisp id emptyEnv 0 zetaCtx ((zetaCtxP emptyEnv 0).disp id) :=
  RoutedDisp.canon (zetaCtxP emptyEnv 0)

/-- **The on-cone inhabited instance** for the named residual: every
    premise of `ClwBvarValueConeW` is inhabited at the canonical Entry
    disposition of `zetaCtx` — `hval`/`hty` by `rfl`, `hv` = `zrHv`,
    `dl` = `zrDl`, `dr` = `zrDr`, `σ` = `id` (a hom), `ρ` = the canon
    display (routed above) — and the wall's goal at those data is exactly
    the landed `zl_res_convW_canon` modulo the surface `epsW` bridge.
    The refuting family of the off-cone (unrouted) wall cannot recur on
    the cone (`zl_routed_no_keep_at_zetaCtx`): the residual is not known
    false anywhere the demand cone routes. -/
theorem clwBvarValueConeW_canon :
    CLWx (tableOfI EnvWfT.empty) id ((zetaCtxP emptyEnv 0).disp id)
      (zetaLocalBvarSurface (rfl : lookupType zetaCtx 0 = some (.sort (.succ .zero))) zrDl)
      zrHv := by
  unfold CLWx
  rw [zetaLocalBvarSurface_epsW_resolve _ zrDl
    (show levelIsZero (id zrDl.reg.1) = false from rfl)]
  exact zl_res_convW_canon

#print axioms Rcic.Syn.clwBvarValueConeW_canon_routed
#print axioms Rcic.Syn.clwBvarValueConeW_canon

/-! ### row 4 supplied from coherence + the named residuals -/

/-- The row-4 field from coherence + the two named residuals: the surface
    port is a coherence instance; the res port is `ClwBvarValueConeW` (the
    cross-subject extension); the occurrence port is the eps-free
    `ZetaLocalRegOccWallW` (orthogonal to coherence — an existential
    `P2Query.subAt` fact, not an erasure judgment). -/
theorem esW_zetaLocal_field_of_coherence (coh : TypingEpsCoherenceW)
    {E : ResolvedEnv} (hW : EnvWfT E) {Aw : Nat → Nat}
    (hocc : ZetaLocalRegOccWallW E Aw (tableOfI hW))
    (hbv : ClwBvarValueConeW (tableOfI hW)) :
    ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {i : Nat} {A v : Expr Nat}
      (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
      (hv : TyP E' n Γ v A) (dl : TyP E' n Γ (.bvar i) A) (dr : TyP E' n Γ v A)
      (S : ScopedCtx E E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
      (hq : Demand (.es (CvP.zetaLocal E' n Γ i A v hval hty hv dl dr) S σ ρ))
      (ih : StepIHW Aw (tableOfI hW)
        (.es (CvP.zetaLocal E' n Γ i A v hval hty hv dl dr) S σ ρ)),
      GoalW (tableOfI hW) (.es (CvP.zetaLocal E' n Γ i A v hval hty hv dl dr) S σ ρ) := by
  intro E₀ n₀ Γ₀ E' n Γ i A v hval hty hv dl dr S σ ρ hq ih
  exact esW_zetaLocal_field_portsW Aw (tableOfI hW) hval hty hv dl dr S σ ρ
    (coh hW _ _ (Demand.hom hq) (Demand.routed hq)) (hocc hval hty hv dl dr S σ ρ)
    (fun hu => by
      have hc := hbv hval hty hv dl dr σ (Demand.hom hq) ρ (Demand.routed hq) hu
      unfold CLWx at hc
      rw [zetaLocalBvarSurface_epsW_resolve hty dl hu] at hc
      exact hc) hq ih

/-! ### row 2 (`es_beta`): the body/reduct CLW walls and the tag wall -/

/-- `BetaBodyClWallW` on-cone from coherence (row 2 wall 1): the binder
    display is routed by `RoutedDisp.assumption` from the ambient one. -/
theorem betaBodyClWallW_cone_of_coherence (coh : TypingEpsCoherenceW)
    {E : ResolvedEnv} (hW : EnvWfT E) {Aw : Nat → Nat} {E' : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E' n Γ A (.sort u)) (hbody : TyP E' n (.assumption A :: Γ) body B)
    (harg : TyP E' n Γ arg A)
    (dl : TyP E' n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E' n Γ (instantiate0 arg body) (instantiate0 arg B))
    (σ : Level → Level) (hσ : LevelHom σ) (ρ : List Disp) (hρ : RoutedDisp σ E' n Γ ρ)
    (g : RedexGot Aw (dl.wt Aw) E' n Γ A body arg)
    (hr : readRedex (envExt_refl E') Aw dl rfl = .yes g) :
    CLW (tableOfI hW) σ (binderDisp (levelIsZero (σ u)) :: ρ) g.hbody hbody :=
  coh hW _ _ hσ (RoutedDisp.assumption hρ hA)

/-- `BetaReductClWallW` on-cone from coherence (row 2 wall 3). -/
theorem betaReductClWallW_cone_of_coherence (coh : TypingEpsCoherenceW)
    {E : ResolvedEnv} (hW : EnvWfT E) {Aw : Nat → Nat} {E' : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E' n Γ A (.sort u)) (hbody : TyP E' n (.assumption A :: Γ) body B)
    (harg : TyP E' n Γ arg A)
    (dl : TyP E' n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E' n Γ (instantiate0 arg body) (instantiate0 arg B))
    (σ : Level → Level) (hσ : LevelHom σ) (ρ : List Disp) (hρ : RoutedDisp σ E' n Γ ρ)
    (g : RedexGot Aw (dl.wt Aw) E' n Γ A body arg)
    (hr : readRedex (envExt_refl E') Aw dl rfl = .yes g) :
    CLW (tableOfI hW) σ ρ (instEnd hbody harg hA) dr :=
  coh hW _ _ hσ hρ

/-- **The tag-wall residual.** `BetaBodyTagWallW` does NOT follow from
    coherence alone: its content is an iff of `.star`-tags, and moving a
    tag across a `ConvMod` needs star-invariance of conversion at the
    table — not on the tree under this shape (the landed star lemmas are
    per-normal-form, e.g. `not_convMod_star_const`). Named: -/
def ConvModStarIffW (tbl : List CRule) : Prop :=
  ∀ (a b : ETm), ConvMod (EStep tbl) LvlEq a b → (a = .star ↔ b = .star)

/-- `BetaBodyTagWallW` on-cone from coherence + `ConvModStarIffW`: the tag
    iff is the star-invariance image of the body CLW coherence instance. -/
theorem betaBodyTagWallW_cone_of_coherence (coh : TypingEpsCoherenceW)
    {E : ResolvedEnv} (hW : EnvWfT E) (hstar : ConvModStarIffW (tableOfI hW))
    {Aw : Nat → Nat} {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E' n Γ A (.sort u)) (hbody : TyP E' n (.assumption A :: Γ) body B)
    (harg : TyP E' n Γ arg A)
    (dl : TyP E' n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E' n Γ (instantiate0 arg body) (instantiate0 arg B))
    (σ : Level → Level) (hσ : LevelHom σ) (ρ : List Disp) (hρ : RoutedDisp σ E' n Γ ρ)
    (g : RedexGot Aw (dl.wt Aw) E' n Γ A body arg)
    (hr : readRedex (envExt_refl E') Aw dl rfl = .yes g) :
    (g.hbody.epsW σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
      (hbody.epsW σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) :=
  hstar _ _ (betaBodyClWallW_cone_of_coherence coh hW hA hbody harg dl dr σ hσ ρ hρ g hr)

#print axioms Rcic.Syn.ConvModStarIffW
/-! ### row 7 (`es_lit`): `litW_erasure_unique_wall` -/

/-- `litW_erasure_unique_wall` does NOT follow from coherence, for two
    independent reasons: (1) the wall concludes EQUALITY of the two
    erasures, coherence only convertibility; (2) the wall quantifies ALL
    displays, coherence only the routed ones. What follows, one line, is
    the on-cone `ConvMod` reading — the judgment class the row's `.es`
    goal itself lives in. -/
theorem litW_erasureConv_cone_of_coherence (coh : TypingEpsCoherenceW)
    {E : ResolvedEnv} (hW : EnvWfT E) {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t : Nat} {T : Expr Nat} {σ : Level → Level} (hσ : LevelHom σ)
    {ρ : List Disp} (hρ : RoutedDisp σ E' n Γ ρ)
    (D₁ D₂ : TyP E' n Γ (natExpand t) T) :
    CLW (tableOfI hW) σ ρ D₁ D₂ :=
  coh hW _ _ hσ hρ

/-! ### rows 1/5/8 (`es_consts`/`es_delta`/`es_app`): the CLW leg layer

The field walls do NOT follow one-line: each needs its per-row `CaseStepW`
composer (the `esW_<row>` case lemma chaining the CLW ports with the node
rewrite and the IH), which is not on the tree for these rows. The CLW
leg layer they DO consume is fed by coherence verbatim — the `thsaW_*`
legs take `TransportHeadSortAtW` premises, and `thsaW_of_coherence`
supplies those on-cone. The row-1 canon legs, as direct instances: -/

/-- Row 1: the two canon `CLW`s are coherence instances (the endpoints
    `dl`/`dr` vs the canonical `constsCanon*` typings of the same
    subjects). -/
theorem constsW_clwLegs_of_coherence (coh : TypingEpsCoherenceW)
    {E : ResolvedEnv} (hW : EnvWfT E) {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {m : CheckedMember}
    (hres : E'.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (dl : TyP E' n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E' n Γ (.const r ls') (instantiateLevels ls m.mtype))
    {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp} (hρ : RoutedDisp σ E' n Γ ρ) :
    CLW (tableOfI hW) σ ρ dl (constsCanonLeft hres hlen hwf dl) ∧
      CLW (tableOfI hW) σ ρ dr (constsCanonRight hres hlen hwf' hls dr) :=
  ⟨coh hW _ _ hσ hρ, coh hW _ _ hσ hρ⟩

/-- Row 5: the two kept-branch `CLW` legs are coherence instances. -/
theorem deltaW_clwLegs_of_coherence (coh : TypingEpsCoherenceW)
    {E : ResolvedEnv} (hW : EnvWfT E) {E' : ResolvedEnv} (hE : EnvWfT E') {n : Nat}
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E'.members r = some m) (hbody : m.body = some b)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hb : TyP E' n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E' n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (D_b : TyP E' m.arity [] b m.mtype)
    {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp} (hρ : RoutedDisp σ E' n Γ ρ) :
    CLW (tableOfI hW) σ ρ dl (deltaCanonL hres hlen hwf hb) ∧
      CLW (tableOfI hW) σ ρ (deltaDbΓ hE Γ hres hbody hlen hwf D_b) hb :=
  ⟨coh hW _ _ hσ hρ, coh hW _ _ hσ hρ⟩

/-- Row 8: the two occ-role decoder `CLW`s are coherence instances at the
    re-wrapped right endpoints. -/
theorem appW_clwLegs_of_coherence (coh : TypingEpsCoherenceW)
    {E : ResolvedEnv} (hW : EnvWfT E) {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g a b A B : Expr Nat}
    (h1 : CvP E' n Γ f g (.pi A B)) (h2 : CvP E' n Γ a b A)
    (dl : TyP E' n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E' n Γ (.app g b) (instantiate0 a B))
    {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp} (hρ : RoutedDisp σ E' n Γ ρ) :
    CLW (tableOfI hW) σ ρ h1.dr ((appSource dr rfl).feq ▸ (appSource dr rfl).hf) ∧
      CLW (tableOfI hW) σ ρ h2.dr ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha) :=
  ⟨coh hW _ _ hσ hρ, coh hW _ _ hσ hρ⟩

/-- Row 10: the left/right Π surface `CLW` ports are coherence instances. -/
theorem piW_clwPorts_of_coherence (coh : TypingEpsCoherenceW)
    {E : ResolvedEnv} (hW : EnvWfT E) {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E' n Γ A A' (.sort u)) (hB : CvP E' n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E' n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E' n Γ (.pi A' B') (.sort (.imax u v)))
    {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp} (hρ : RoutedDisp σ E' n Γ ρ) :
    CLW (tableOfI hW) σ ρ dl (piLeftSurface hA hB) ∧
      CLW (tableOfI hW) σ ρ dr (piRightSurface hA hB dr) :=
  ⟨coh hW _ _ hσ hρ, coh hW _ _ hσ hρ⟩

/-! ## §2 the attack on coherence itself

Induction on the pair `(D₁, D₂)`, typing inversion on the subject's head,
conv/tyConv steps absorbed by the `epsW` forwarding (they are `rfl` at the
erasure). Per-arm case lemmas below; the canonicity-scale cases are named
as separate Props. -/

/-- conv absorbs on the right: the `.conv` arm forwards `epsW`, so the
    pair is coherent by reflexivity — no induction needed. -/
theorem clw_convR (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (D : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u)) :
    CLW tbl σ ρ D (TyP.conv E n Γ e A B u D hc) :=
  ConvMod.refl _

/-- conv absorbs on the left: the pair with a conv-wrapped left endpoint
    IS the pair with the inner typing (the `.conv` arm forwards `epsW`,
    definitionally). -/
theorem clw_convL_of (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (Dinner : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u)) (D₂ : TyP E n Γ e B)
    (h : CLW tbl σ ρ Dinner D₂) :
    CLW tbl σ ρ (TyP.conv E n Γ e A B u Dinner hc) D₂ :=
  h

/-- `ewk` absorbs: the `.ewk` arm forwards `epsW` literally, so the pair
    with the wrapped left endpoint is the (cross-environment) pair of the
    inner typing — `CLWx` because the inner typing sits at `E₀`. -/
theorem clw_ewk_of (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    (hext : EnvExt E₀ E) (D : TyP E₀ n Γ e A) (D₂ : TyP E n Γ e A)
    (h : CLWx tbl σ ρ D D₂) :
    CLW tbl σ ρ (TyP.ewk E₀ E n Γ e A hext D) D₂ :=
  h

/-! ### head-matched arms: `sort`, `const`, `bvar`, `lit` -/

/-- `sort` arm: the erasure `ETm.sort (σ l)` reads `l` from the SUBJECT,
    so any two `sort`-typings of the same subject co-erase — no residual. -/
theorem clw_sort (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l k₁ k₂ : Level}
    (h₁ : eqN k₁ (.succ l)) (h₂ : eqN k₂ (.succ l)) :
    CLW tbl σ ρ (TyP.sort E n Γ l k₁ h₁) (TyP.sort E n Γ l k₂ h₂) :=
  ConvMod.refl _

/-- `const` arm: the erasure reads `r`/`ls` from the subject and only the
    bit from the derivation. Two typings of the same `.const r ls` co-erase
    whenever their stored universe bits agree — the residual is the bit
    (`ConstUnivBitCohW` below; the eqN-slack of the `ls₀`-type ladder). -/
theorem clw_const_of_bit (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls₀₁ ls₀₂ : List Level}
    {m : CheckedMember} {u₁ u₂ : Level}
    (hres₁ : E.members r = some m) (hlen₁ : ls.length = m.arity)
    (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls₀₁)
    (hT₁ : TyP E n Γ (instantiateLevels ls₀₁ m.mtype) (.sort u₁))
    (hres₂ : E.members r = some m) (hlen₂ : ls.length = m.arity)
    (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls₀₂)
    (hT₂ : TyP E n Γ (instantiateLevels ls₀₂ m.mtype) (.sort u₂))
    (hb : levelIsZero (σ u₁) = levelIsZero (σ u₂)) :
    CLW tbl σ ρ
      (TyP.const E n Γ r ls ls₀₁ m u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
      (TyP.const E n Γ r ls ls₀₂ m u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) := by
  unfold CLW
  cases hb2 : levelIsZero (σ u₂) with
  | true =>
      have hb1 : levelIsZero (σ u₁) = true := by rw [hb, hb2]
      simp only [TyP.epsW, hb1, hb2]
      exact ConvMod.refl _
  | false =>
      have hb1 : levelIsZero (σ u₁) = false := by rw [hb, hb2]
      simp only [TyP.epsW, hb1, hb2]
      exact ConvMod.refl _

/-- `bvar` arm: the erasure reads `i` from the subject (`resolve ρ i`) and
    only the bit from the derivation. Same-bit pairs co-erase; the residual
    bit is `BitCoh σ` of the two `hA` typings (the skeleton's own tag). -/
theorem clw_bvar_of_bit (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat}
    {u₁ u₂ : Level} (h : lookupType Γ i = some A)
    (hA₁ : TyP E n Γ A (.sort u₁)) (hA₂ : TyP E n Γ A (.sort u₂))
    (hb : levelIsZero (σ u₁) = levelIsZero (σ u₂)) :
    CLW tbl σ ρ (TyP.bvar E n Γ i A u₁ h hA₁) (TyP.bvar E n Γ i A u₂ h hA₂) := by
  unfold CLW
  cases hb2 : levelIsZero (σ u₂) with
  | true =>
      have hb1 : levelIsZero (σ u₁) = true := by rw [hb, hb2]
      simp only [TyP.epsW, hb1, hb2]
      exact ConvMod.refl _
  | false =>
      have hb1 : levelIsZero (σ u₁) = false := by rw [hb, hb2]
      simp only [TyP.epsW, hb1, hb2]
      exact ConvMod.refl _

/-- `lit` arm: the erasure forwards to the expansion typing, whose subject
    `natExpand t` is FORCED by the constructor — the lit pair is the
    expansion pair (pure recursion, no residual). -/
theorem clw_lit_of (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {T₁ T₂ : Expr Nat}
    (hexp₁ : TyP E n Γ (natExpand t) T₁) (hexp₂ : TyP E n Γ (natExpand t) T₂)
    (h : CLW tbl σ ρ hexp₁ hexp₂) :
    CLW tbl σ ρ (TyP.lit E n Γ t T₁ hexp₁) (TyP.lit E n Γ t T₂ hexp₂) :=
  h

/-! ### the `pi` arm and its named congruence residual -/

/-- **The pi-arm congruence residual.** `RStep`/`EtaStep` are closed under
    the raw `ETm.pi` constructors (`RStep.piL`/`piR`), but the
    `ConvMod`-level congruence — including the `true`-branch slot
    `piSlot true · = ·.lift 0 1` — is not on the tree under this shape.
    Named as ONE Prop: -/
def ConvModPiCongrW (tbl : List CRule) : Prop :=
  ∀ (b : Bool) (x x' y y' : ETm),
    ConvMod (EStep tbl) LvlEq x x' → ConvMod (EStep tbl) LvlEq y y' →
    ConvMod (EStep tbl) LvlEq (ETm.pi x (piSlot b y)) (ETm.pi x' (piSlot b y'))

/-- `pi` arm, proof-bit branch `true`: the erasure slots are `hA.epsW σ ρ`
    and `piSlot true (hB.epsW σ (.drop :: ρ))`; the pair is the congruence
    image of the two sub-pairs. -/
theorem clw_pi_true (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat}
    {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂))
    (cong : ConvModPiCongrW tbl)
    (hu₁ : levelIsZero (σ u₁) = true) (hu₂ : levelIsZero (σ u₂) = true)
    (cA : CLW tbl σ ρ hA₁ hA₂) (cB : CLW tbl σ (.drop :: ρ) hB₁ hB₂) :
    CLW tbl σ ρ (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁) (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂) := by
  unfold CLW
  simp only [TyP.epsW, hu₁, hu₂]
  exact cong true _ _ _ _ cA cB

/-- `pi` arm, proof-bit branch `false`: the codomain slot is the raw
    `hB.epsW σ (.keep :: ρ)` (`piSlot false · = ·`). -/
theorem clw_pi_false (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat}
    {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂))
    (cong : ConvModPiCongrW tbl)
    (hu₁ : levelIsZero (σ u₁) = false) (hu₂ : levelIsZero (σ u₂) = false)
    (cA : CLW tbl σ ρ hA₁ hA₂) (cB : CLW tbl σ (.keep :: ρ) hB₁ hB₂) :
    CLW tbl σ ρ (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁) (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂) := by
  unfold CLW
  simp only [TyP.epsW, hu₁, hu₂]
  exact cong false _ _ _ _ cA cB

/-! ### the named bit residual and the arm ledger -/

/-- **The const-arm bit residual.** The two typings' stored universes come
    from `hT`s of `eqN`-related types (`eqNList ls ls₀ᵢ`) — the eqN-slack
    of the sort ladder, the same tooth class the landed lit/pi refutations
    exploited off-cone (`sr2_σ`/`sr2_σ2` are not homs; at homs the measured
    teeth die by `levelIsZero_congr_hom`, but that lemma needs the `eqN`
    the ladder has not yet yielded here). Named as ONE Prop, OPEN: -/
def ConstUnivBitCohW (σ : Level → Level) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls₀₁ ls₀₂ : List Level}
    {m : CheckedMember} {u₁ u₂ : Level}
    (hσ : LevelHom σ)
    (hls₁ : eqNList ls ls₀₁) (hls₂ : eqNList ls ls₀₂)
    (hT₁ : TyP E n Γ (instantiateLevels ls₀₁ m.mtype) (.sort u₁))
    (hT₂ : TyP E n Γ (instantiateLevels ls₀₂ m.mtype) (.sort u₂)),
    levelIsZero (σ u₁) = levelIsZero (σ u₂)

/-! ### arm ledger (this branch)

* `conv`/`ewk`/`cctx` wrappers — PROVED absorbed (rfl; `clw_convR`,
  `clw_convL_of`, `clw_ewk_of`).
* `sort` — PROVED, no residual (`clw_sort`).
* `const` — PROVED modulo the bit: `clw_const_of_bit`; residual
  `ConstUnivBitCohW`, reduced to the eqN-ladder `ConstSortLadderEqNW`
  (`constUnivBitCohW_of_ladderEqN`, at every hom).
* `bvar` — PROVED modulo the bit: `clw_bvar_of_bit`; the bit is
  `BitCoh σ hA₁ hA₂` — the skeleton's own tag, an IH-pack edge in the
  closer (`bitCoh_goalW_of_ports`).
* `lit` — PROVED as pure recursion (`clw_lit_of`; the constructor forces
  the expansion subject `natExpand t`).
* `pi` — PROVED modulo `ConvModPiCongrW` (OPEN) + the `hA`/`hB` sub-pairs
  (`clw_pi_true`/`clw_pi_false`).
* `lam`/`app`/`letE`/`wk`/`esub`/`lsub`/`linst` and the head-mismatch
  (spine) cases — NOT YET ATTACKED here; `wk`/`esub`/`lsub` need the
  display-transport commutations (`wkInnerDisp`, `insertDisp`), `linst`
  needs `RoutedDisp.linst` + `sortTransport_levelHom_linst`. -/

#print axioms Rcic.Syn.ConstUnivBitCohW

/-- **The eqN-ladder residual** (the sharpened content of the bit wall):
    the const-member sort ladder is `eqN`-deterministic — two sort-typings
    of the same member type instantiated at `eqN`-related level lists have
    `eqN` universes. Canonicity-scale: the Syn-layer counterpart of the
    declarative lane's `SortUnique` interface (`RcicA2SortSupport.SortUnique`),
    the uniqueness domain the closer's own IH supplies via the issued
    `bitCoh_cl_reg*` rows — not provable lane-locally without re-doing the
    closer (cc 23:55Z ruling). -/
def ConstSortLadderEqNW : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ls₀₁ ls₀₂ : List Level}
    {m : CheckedMember} {u₁ u₂ : Level},
    eqNList ls₀₁ ls₀₂ →
    TyP E n Γ (instantiateLevels ls₀₁ m.mtype) (.sort u₁) →
    TyP E n Γ (instantiateLevels ls₀₂ m.mtype) (.sort u₂) →
    eqN u₁ u₂

/-- The bit wall reduces to the ladder residual at EVERY hom: the bits
    agree because the universes are `eqN` (`levelIsZero_congr_hom`). No
    other content — by contrapositive, `ConstUnivBitCohW` is false at some
    hom only if the ladder itself is non-deterministic, so no σ-side tooth
    exists on the hom cone. -/
theorem constUnivBitCohW_of_ladderEqN {σ : Level → Level}
    (h : ConstSortLadderEqNW) : ConstUnivBitCohW σ := by
  intro E n Γ r ls ls₀₁ ls₀₂ m u₁ u₂ hσ hls₁ hls₂ hT₁ hT₂
  exact levelIsZero_congr_hom hσ
    (h (eqNList_trans (eqNList_symm hls₁) hls₂) hT₁ hT₂)

#print axioms Rcic.Syn.ConstSortLadderEqNW
#print axioms Rcic.Syn.constUnivBitCohW_of_ladderEqN

/-! ### cc 05:45Z (b): the outer env induction on `ConstSortLadderEqNW`, measured

The closer IS parametrised by the env (`sortRow_of_suppliers_tableOfI` at
`hW : EnvWfT E`), and outer induction on the `EnvWfT` derivation is
well-founded; but it is NOT non-circular. Components:

1. STATEMENT LEVEL — `StepSuppliers.es_consts` quantifies its view env `E`
   (`hres : E.members r = some m`; `P2Query.es` carries `E` as an independent
   implicit) with no tie to the ambient `Eₐ`; only the `ScopedCtx` env is
   bounded (`EnvExt E₀ Eₐ`, reflexive). Supplies at `Eₐ` include the ladder's
   content at member-envs strictly beyond `Eₐ`: no prefix cone covers the
   field's quantifier, and the induction base (`Eₐ = emptyEnv`) already
   carries the beta/zeta/lit/pi legs (inner `E₀ = emptyEnv` is legal).
2. BRIDGE LEVEL — the repaired members-only induction needs every
   `TyP`-at-`E` wall instance reduced to admission-prefix facts; `TyP` has
   `conv` (CvP premise) and `ewk` (env-extension transport) constructors, so
   typings born at `E` may route through members added after the prefix.
   Removing them is a derivation-normalisation theorem relative to a sub-env
   — the walker's territory; the declarative cousin (full `SortConvChar`) is
   landed only on the `RedOnly` fragment (`sortConvChar_redOnly`).
3. FIXED-COST LEVEL — `SortRow E₀ ∧ PiRow E₀` at a prefix is reachable only
   through `sortRow_of_suppliers_tableOfI`, i.e. the WHOLE `StepSuppliers`
   at that prefix: rows 2–10's walls at `E₀`, none of which shrink with the
   prefix (component 1).
4. STRENGTH — the wall as named is env/context UNRESTRICTED; every landed
   determinacy interface is regularity-gated. The reduction below therefore
   targets the Wf-gated wall. -/

/-- The regularity-gated ladder: the strongest statement the landed
    determinacy interfaces (`SortRow`/`PiRow`/`typeUniq_of_sort_pi`) can see. -/
def ConstSortLadderEqNWWf : Prop :=
  ∀ {E : ResolvedEnv}, EnvWfT E → ∀ {n : Nat} {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {ls₀₁ ls₀₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level},
      eqNList ls₀₁ ls₀₂ →
      TyP E n Γ (instantiateLevels ls₀₁ m.mtype) (.sort u₁) →
      TyP E n Γ (instantiateLevels ls₀₂ m.mtype) (.sort u₂) → eqN u₁ u₂

/-- Bridge B1 (unlanded): TyP→HasTyT erasure, env-universal. -/
def TyPEraseW : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat},
    TyP E n Γ e A → Nonempty (HasTyT E n Γ e A)

/-- Bridge B2 (unlanded): two-list `eqN` instantiation congruence
    (`convT_instLevels` is same-list only). -/
def InstEqNCongrW : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {ls₀₁ ls₀₂ : List Level},
    eqNList ls₀₁ ls₀₂ →
    Nonempty (TyConvT E n Γ (instantiateLevels ls₀₁ A) (instantiateLevels ls₀₂ A))

/-- Bridge B3 (unlanded): subject-conv retype (conversion soundness for the
    subject position; `HasTyT.conv` moves the TYPE only). -/
def ConvSubjectRetypeW : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e e' A : Expr Nat},
    HasTyT E n Γ e A → TyConvT E n Γ e e' → Nonempty (HasTyT E n Γ e' A)

/-- THE REDUCTION (fixed-point shape): the Wf-gated ladder follows from the
    closer's own conclusion at EVERY env plus three named bridges. `hRows` is
    exactly what `sortRow_of_suppliers_tableOfI` (+ a PiRow counterpart)
    concludes — reached only THROUGH `es_consts`, i.e. through the ladder
    itself; and the bridges are not on the tree. The non-circularity deficit,
    machine-visible: the outer env induction does not discharge row 1 without
    rows 2–10 at every prefix (component 3) and the B1/B2/B3 bridges. -/
theorem constSortLadderEqNWWf_of_coneRows (hB1 : TyPEraseW) (hB2 : InstEqNCongrW)
    (hB3 : ConvSubjectRetypeW)
    (hRows : ∀ (E : ResolvedEnv) (_ : EnvWfT E) (n : Nat),
      NativeFamilyProjection.SortRow E n ∧ NativeFamilyProjection.PiRow E n) :
    ConstSortLadderEqNWWf := by
  intro E hW n Γ hΓ ls₀₁ ls₀₂ m u₁ u₂ hls hT₁ hT₂
  obtain ⟨k₁⟩ := hB1 hT₁
  obtain ⟨k₂⟩ := hB1 hT₂
  obtain ⟨hc⟩ := hB2 hls
  obtain ⟨k₂'⟩ := hB3 k₁ hc
  obtain ⟨hv⟩ := NativeFamilyProjection.typeUniq_of_sort_pi hW (hRows E hW n).1
    (hRows E hW n).2 hΓ k₂' k₂
  exact (hRows E hW n).1 hΓ hv

#print axioms Rcic.Syn.ConstSortLadderEqNWWf
#print axioms Rcic.Syn.constSortLadderEqNWWf_of_coneRows

/-! ### cc 05:45Z (c): `ClwBvarValueConeW` as a structural commutation, measured

`eps(subst D Dv) = eps(D)[eps(Dv)]` at the display IS structural and carries
NO typing-uniqueness input: it is, per constructor, the DEFINING EQUATION of
`TyP.epsW`'s transport arms (`esub`: `insertDisp .keep j ρ` + `ETm.inst`;
`lsub`: the `.inline (localize .. r)` re-display at `r := hv.epsW σ ρ`; `wk`:
`wkInnerDisp` + keep-lift; `linst`: the composite level map), while `conv`,
`ewk` and `cctx` nodes erase TRANSPARENTLY (`h.epsW σ ρ` — no cast blocks;
the `.conv` arm never inspects its `CvP` premise).

The wall is NOT that commutation alone. `RoutedDisp`'s `letInline`/`letDrop`/
`canon` arms pin the display's let-slot value to the erasure of the ROUTING
PROOF'S OWN derivation `hv_R : TyP E n Γ v A` (`.inline (hv.eps σ ρ)`), while
the wall supplies an ARBITRARY `hv` of the same judgment. After the
commutation and `zetaLocalBvarSurface_epsW_resolve`, the wall decomposes as:

1. `ZetaSlotAlignW` (below): the routed slot's `resolve ρ i` IS the `epsW`
   of some routing-carried derivation of the stored value — structural,
   by induction on the `RoutedDisp` derivation, no uniqueness input; only
   the canon instance is landed (`zl_res_convW_canon`), the general
   RoutedDisp-induction is NOT yet on the tree.
2. ONE same-subject coherence instance `coh hv_R hv` — the exact content of
   `TypingEpsCoherenceW` at `(E, n, Γ, v)`; its open arms are the CLW §2
   ledger's not-yet-attacked cases (`lam`/`app`/`letE`/`wk`/`esub`/`lsub`/
   `linst` + the head-mismatch spine) plus the `BitCoh` leg (row-1 class).

So no conversion/cast node blocks the wall; the blocker is DERIVATION CHOICE
at the routing slot (`hv_R` vs the supplied `hv`). -/

/-- The STRUCTURAL alignment residue (unique-free): at a letBinding slot, a
    routed display resolves to the `epsW` of some routing-carried derivation
    of the stored value. Landable by induction on `RoutedDisp` (the `epsW`
    transport arms are the commutation); `conv`/`ewk`/`cctx` vanish. -/
def ZetaSlotAlignW (tbl : List CRule) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {v : Expr Nat},
    lookupValue Γ i = some v → ∀ {σ : Level → Level} (_hσ : LevelHom σ)
      {ρ : List Disp}, RoutedDisp σ E n Γ ρ →
      ∃ (A : Expr Nat) (hvR : TyP E n Γ v A),
        ConvMod (EStep tbl) LvlEq (resolve ρ i) (hvR.epsW σ ρ)

/-- Row 4 decomposed: `ClwBvarValueConeW` = the structural slot alignment
    (unique-free, `RoutedDisp`-induction) + ONE same-subject coherence
    instance. The wall stays cross-subject only in APPEARANCE: the surface
    side never needed uniqueness, the value side needs exactly
    `TypingEpsCoherenceW`. -/
theorem clwBvarValueConeW_of_align_coh {E : ResolvedEnv} (hW : EnvWfT E)
    (align : ZetaSlotAlignW (tableOfI hW)) (coh : TypingEpsCoherenceW) :
    ClwBvarValueConeW (tableOfI hW) := by
  intro E' n Γ i A v hval hty hv dl dr σ hσ ρ hρ hu
  obtain ⟨A', hvR, hres⟩ := align hval hσ hρ
  have hc : ConvMod (EStep (tableOfI hW)) LvlEq
      (hvR.epsW σ ρ) (hv.epsW σ ρ) := coh hW hvR hv hσ hρ
  have hs : (zetaLocalBvarSurface hty dl).epsW σ ρ = resolve ρ i :=
    zetaLocalBvarSurface_epsW_resolve hty dl hu
  unfold CLWx
  rw [hs]
  exact hres.trans hc

#print axioms Rcic.Syn.ZetaSlotAlignW
#print axioms Rcic.Syn.clwBvarValueConeW_of_align_coh

end Rcic.Syn

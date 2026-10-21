import rcic.RcicSynSRLitPiEswW
import rcic.RcicSynDeltaKeptES
import rcic.RcicSynStepFields4
import rcic.RcicSynPBitAll
import rcic.RcicSynDomainSource

/-!
# `RcicSynSRLitPiEswLegs` — rows 8/5/1 decoder legs under epsW + `LevelHom`

cc 2026-10-20 20:00Z re-measure, gated replay of #7799's §3 under
`CLW`/`TransportHeadSortAtW`:

* row 8 (`es_app`): the occ-role decoder `CL`s `hclF`/`hclA` follow from
  `TransportHeadSortAtW` at the re-wrapped right endpoints
  (`thsaW_app_hclF`/`thsaW_app_hclA`).
* row 5 (`es_delta`): the kept-branch `CL` legs `hL`/`hB` follow from
  `TransportHeadSortAtWW` at `dl` and at the body surface node
  (`thsaW_delta_hL`/`thsaW_delta_hB`), at every display.
* row 1 (`es_consts`): the occ-role gate bit follows from `EUT` +
  `TransportHeadSortAtW` at the two reg-of-reg sort typings
  (`thsaW_consts_hgate`); the two canonical `CL`s are direct
  `TransportHeadSortAtW` instances (`thsaW_consts_hclL`/`_hclR`).

Each row's gated field verdict stays OPEN — the exact wall is the row's
`CaseStepW` statement (named here as ONE Prop each): row 8 retains the
`AppClauseNeed` leg, row 5 the `AgreeOn` admission-weight leg and the
unlanded (devin/sr-delta) kept-case closer, row 1 the `EUT` premise and
the epsW-restated `mixedCL` composition. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 row 8 (`es_app`) — the occ-role decoder legs -/

/-- `occH1`'s role under the gates: the function-leg decoder `CLW` `hclF`,
    from `TransportHeadSortAtW` at `h1.dr` (the `.ewk`-re-wrapped
    endpoint). -/
theorem thsaW_app_hclF (tbl : List CRule) (σ : Level → Level) (hσ : LevelHom σ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (ρ : List Disp)
    (h : TransportHeadSortAtW tbl σ hσ ρ h1.dr) :
    CLW tbl σ ρ h1.dr ((appSource dr rfl).feq ▸ (appSource dr rfl).hf) :=
  h _

/-- `occH2`'s role under the gates: the argument-leg decoder `CLW` `hclA`,
    from `TransportHeadSortAtW` at `h2.dr`. -/
theorem thsaW_app_hclA (tbl : List CRule) (σ : Level → Level) (hσ : LevelHom σ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (ρ : List Disp)
    (h : TransportHeadSortAtW tbl σ hσ ρ h2.dr) :
    CLW tbl σ ρ h2.dr ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha) :=
  h _

#print axioms Rcic.Syn.thsaW_app_hclF
#print axioms Rcic.Syn.thsaW_app_hclA

/-! ## §2 row 5 (`es_delta`) — the kept-branch `CLW` legs -/

/-- `hL` under the gates: `dl` against the canonical left surface, from
    `TransportHeadSortAtW` at `dl`, at every display. -/
theorem thsaW_delta_hL (tbl : List CRule) (σ : Level → Level) (hσ : LevelHom σ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (ρ : List Disp)
    (h : TransportHeadSortAtW tbl σ hσ ρ dl) :
    CLW tbl σ ρ dl (deltaCanonL hres hlen hwf hb) :=
  h _

/-- `hB` under the gates: the body surface node against `hb`, from
    `TransportHeadSortAtW` at the `deltaDbΓ`-shaped node (the adapter
    `D_b` abstract, as the landed kept-case closer consumes it). -/
theorem thsaW_delta_hB (tbl : List CRule) (σ : Level → Level) (hσ : LevelHom σ)
    {E : ResolvedEnv} (hE : EnvWfT E) {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (D_b : TyP E m.arity [] b m.mtype) (ρ : List Disp)
    (h : TransportHeadSortAtW tbl σ hσ ρ
      (deltaDbΓ hE Γ hres hbody hlen hwf D_b)) :
    CLW tbl σ ρ (deltaDbΓ hE Γ hres hbody hlen hwf D_b) hb :=
  h _

#print axioms Rcic.Syn.thsaW_delta_hL
#print axioms Rcic.Syn.thsaW_delta_hB

/-! ## §3 row 1 (`es_consts`) — the canon `CLW` legs

The occ-role gate bit (`bitCoh_of_eut_cl`'s epsW reading) needs the
`sortCoh` layer restated under `epsW` — sr1's PROGRESS already lists the
CL-layer closers (`esW_*` family) as open; it is named inside the row-1
wall below, not papered over. -/

/-- The left canon `CLW` is a direct `TransportHeadSortAtW` instance at
    `dl`. -/
theorem thsaW_consts_hclL (tbl : List CRule) (σ : Level → Level) (hσ : LevelHom σ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)) (ρ : List Disp)
    (h : TransportHeadSortAtW tbl σ hσ ρ dl) :
    CLW tbl σ ρ dl (constsCanonLeft hres hlen hwf dl) :=
  h _

/-- The right canon `CLW` is a direct `TransportHeadSortAtW` instance at
    `dr`. -/
theorem thsaW_consts_hclR (tbl : List CRule) (σ : Level → Level) (hσ : LevelHom σ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls' : List Level}
    {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls' = true) (hls : eqNList ls ls')
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype)) (ρ : List Disp)
    (h : TransportHeadSortAtW tbl σ hσ ρ dr) :
    CLW tbl σ ρ dr (constsCanonRight hres hlen hwf hls dr) :=
  h _

#print axioms Rcic.Syn.thsaW_consts_hclL
#print axioms Rcic.Syn.thsaW_consts_hclR

/-! ## §4 the gated field walls, ONE Prop each -/

/-- Row 8 under epsW + `LevelHom`: the gated `CaseStepW` obligation of the
    `es_app` field at `tableOfI`. The occ-role decoder legs are supplied
    above; what remains is `AppClauseNeed` (`app_drClause`) and the
    transport arms of the occ disjunctions, restated under `CLW`. -/
def appW_field_wall : Prop :=
  ∀ {E : ResolvedEnv} (hW : EnvWfT E) (Aw : Nat → Nat) {E₀ : ResolvedEnv}
    {n₀ : Nat} {Γ₀ : LCtx} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx E₀ E n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw (tableOfI hW)
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)

/-- Row 5 under epsW + `LevelHom`: the gated `CaseStepW` obligation of the
    `es_delta` field at `tableOfI`. The `hL`/`hB` `CLW` legs are supplied
    above; what remains is the `AgreeOn` admission-weight leg (erasure-free,
    untouched by the epsW switch) and the kept-case closer itself, whose
    `tableOfI` instantiation is devin/sr-delta's (not on this branch). -/
def deltaW_field_wall : Prop :=
  ∀ {E : ResolvedEnv} (hW : EnvWfT E) (Aw : Nat → Nat) {E₀ : ResolvedEnv}
    {n₀ : Nat} {Γ₀ : LCtx} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx E₀ E n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw (tableOfI hW)
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ)

/-- Row 1 under epsW + `LevelHom`: the gated `CaseStepW` obligation of the
    `es_consts` field at `tableOfI`. The two canon `CLW`s are supplied
    above; what remains is the occ-role gate bit — `bitCoh_of_eut_cl`'s
    `sortCoh` layer restated under `epsW` (sr1's open `esW_*` CL-closer
    family) — the `EUT` premise, and the `mixedCL` composition in its
    `CLW` reading. -/
def constsW_field_wall : Prop :=
  ∀ {E : ResolvedEnv} (hW : EnvWfT E) (Aw : Nat → Nat) {E₀ : ResolvedEnv}
    {n₀ : Nat} {Γ₀ : LCtx} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls' : List Level}
    {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (hls : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (S : ScopedCtx E₀ E n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw (tableOfI hW)
      (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr) S σ ρ)

#print axioms Rcic.Syn.appW_field_wall
#print axioms Rcic.Syn.deltaW_field_wall
#print axioms Rcic.Syn.constsW_field_wall

end Rcic.Syn

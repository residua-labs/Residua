import rcic.RcicSynSRDeltaMemberCoh
import rcic.RcicSynSRDeltaAdmW

/-!
# `RcicSynSRDeltaClosed` — row 5 `es_delta`, wall-free at `Aw := admW`

cc 16:40Z item: *"state it: ONE theorem giving the es_delta field at
`tableOfI hW` at `Aw := (enrichEnvWfT hW).admW` with NO wall premise
(compose `RcicSynSRDeltaMemberCoh` + `RcicSynSRDeltaAdmW`)."*

The composition is a direct instantiation:

* `es_delta_kept_memberCoh_tableOfI` (`RcicSynSRDeltaMemberCoh`) gives the
  kept-δ `CaseStep` at `tableOfI S.env` for any `Aw`, from field data +
  `hu` + `hag : AgreeOn E Aw (enrichEnvWfT S.env).admW` — the `hL`/`hB`
  `.cl` legs are already `ih` answers inside the proof
  (`cl_deltaCanonL_before`/`cl_deltaDbΓ_before`).
* `RcicSynSRDeltaAdmW` established that at `Aw := (enrichEnvWfT S.env).admW`
  the `hag` leg is `AgreeOn E admW admW` — reflexivity
  (`fun _ _ _ ↦ rfl`, the same payment as
  `esDeltaKeptWall_of_clWall_admW`).

So at the calibrated weight function NOTHING remains beyond field data and
the kept-branch guard `hu : levelIsZero (σ hb.reg.1) = false` — which is
not a wall premise but the branch condition of the kept-δ case itself.
Row 5's residual (`esDeltaKeptWall` = `hag` + `hL` + `hB`) is fully
discharged: `hL`/`hB` by `StepIH`, `hag` by `AgreeOn`-refl at `admW`.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- ROW 5, WALL-FREE AT `admW`: the kept-δ `CaseStep` at `tableOfI S.env`
    with the record's `Aw` calibrated to the receipt's own admission
    weights. Premises are field data only — the `esDeltaKeptWall` fields
    are gone: `hL`/`hB` discharge as `StepIH` answers (`Before`-below the δ
    node via `admW` payment), `hag` is `AgreeOn`-refl. -/
theorem es_delta_kept_admW_tableOfI {Eₐ E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level)
    (hu : levelIsZero (σ hb.reg.1) = false) :
    CaseStep (enrichEnvWfT S.env).admW (tableOfI S.env)
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        S σ (S.can σ)) :=
  es_delta_kept_memberCoh_tableOfI (enrichEnvWfT S.env).admW
    hres hbody htr hlen hwf hb dl dr S σ hu (fun _ _ _ ↦ rfl)

/-- The `tableOfI hW` pin: row 5 at `Aw := (enrichEnvWfT hW).admW`, no wall
    premise. -/
noncomputable def es_delta_kept_admW_tableOfI_pin {E : ResolvedEnv}
    (hW : EnvWfT E) {Eₐ : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat}
    {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (hext : EnvExt E Eₐ) (hctx : CtxWfT E n Γ) (σ : Level → Level)
    (hu : levelIsZero (σ hb.reg.1) = false) :
    CaseStep (enrichEnvWfT hW).admW (tableOfI hW)
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        ⟨hW, hext, hctx⟩ σ
        ((⟨hW, hext, hctx⟩ : ScopedCtx Eₐ E n Γ).can σ)) :=
  es_delta_kept_admW_tableOfI hres hbody htr hlen hwf hb dl dr
    ⟨hW, hext, hctx⟩ σ hu

/-- NON-VACUITY: the wall-free theorem instantiates end-to-end on the
    landed `srDeltaFixture*` fixture — a real `CaseStep` at
    `tableOfI srDeltaFixtureEnvWfT`, `Aw := srDeltaAdmW`, premises consumed
    = field data + `srDeltaHu` only. -/
theorem srDeltaEsKept_admW_closed_fixture :
    CaseStep srDeltaAdmW (tableOfI srDeltaFixtureEnvWfT)
      (.es (CvP.delta srDeltaFixtureEnv 0 [] 7 [] srDeltaFixtureMember
        (.sort .zero) srDeltaHres srDeltaHbody srDeltaHtr srDeltaHlen
        srDeltaHwf srDeltaHb srDeltaDl srDeltaHb)
        srDeltaScope id (srDeltaScope.can id)) :=
  es_delta_kept_admW_tableOfI srDeltaHres srDeltaHbody srDeltaHtr
    srDeltaHlen srDeltaHwf srDeltaHb srDeltaDl srDeltaHb srDeltaScope id
    srDeltaHu

#print axioms Rcic.Syn.es_delta_kept_admW_tableOfI
#print axioms Rcic.Syn.es_delta_kept_admW_tableOfI_pin
#print axioms Rcic.Syn.srDeltaEsKept_admW_closed_fixture

end Rcic.Syn

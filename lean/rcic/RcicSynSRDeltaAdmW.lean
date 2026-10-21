import rcic.RcicSynSRDelta

/-!
# `RcicSynSRDeltaAdmW` — row 5 `es_delta`: the `hag` discharge at `Aw := admW`

cc item (11:30Z), row-5 arm (1): *"prove that the weight function the closer's
record actually carries at tableOfI AGREES on the framed prefix with
`(enrichEnvWfT hW).admW`."*

Trace of the record's `Aw` (authoritative, not narrative): `Aw` is an implicit
parameter of `AllBelowScoped Eₐ Aw tbl` / `StepSuppliers Aw tbl Eₐ` and stays
universally quantified through every consumer
(`sortRow_of_allBelowScoped`, `sortRow_of_suppliers_envWfT`,
`sortUnique_of_allBelowScoped_*`, `RcicKernelRowsAssembly` §1) — **nobody
inside the machine instantiates `Aw`**: the record's `Aw` is whatever the
caller who supplies `AllBelowScoped`/`StepSuppliers` chooses. So `hag` is a
genuine constraint on that caller-chosen `Aw`, not a per-`Aw` producer:

* at `Aw := fun _ ↦ 0` it is kernel-refuted (`srDelta_agreeOn_zero_refuted`);
* at `Aw := (enrichEnvWfT S.env).admW` it is inhabited by reflexivity —
  `AgreeOn E admW admW` is `fun _ _ _ ↦ rfl`;
* `agreeOn_mono`/`agreeOn_setW`/`GroupMembersP.admW_old` cannot strengthen
  this to `AgreeOn E hWₐ.admW hW.admW` for `EnvExt E Eₐ`: `admW` is
  derivation-dependent (`EnvWfT` is `Type`), weights are `1 + wt` of each
  member's own admission derivation, and `EnvExt` is membership inclusion
  only — `E`'s derivation is not a structural prefix of `Eₐ`'s.

Hence the honest calibrated framed-prefix relation is exactly the
`admW`-calibration: at `Aw := admW` agreement holds by reflexivity. This
module names the residual at that calibration — `esDeltaCLWall`, the wall
minus `hag` — and discharges `hag` on-cone in the specialized field
`es_delta_kept_tableOfI_admW` (+ `tableOfI hW` pin), with non-vacuity on the
landed `srDeltaFixture*` fixture.

The two `CL` legs (`hL`/`hB`, same-subject erasure uniqueness of `dl`/`hb`
against `deltaCanonL`/`deltaDbΓ`) remain the named residual — they ride on
`thsaLhom_lit_wall` / the same-subject sort uniqueness under conversion,
which is not landed at `TyP` level (see module docstring of
`RcicSynSRLitPiTHSALhom`; the `esub`-collapsed-bvar arm needs a
conversion-preserves-sort fact that is DT-009-adjacent).
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the CL-only residual at `Aw := admW` -/

/-- ROW-5 CL-ONLY RESIDUAL: `esDeltaKeptWall` minus the `hag` leg — the two
    `CL` obligations at the demanded scope: `dl`'s erasure vs the canonical
    `deltaCanonL` (the `hL` leg), and `hb`'s erasure vs `deltaDbΓ` (the `hB`
    leg). This is the residual once `Aw` is calibrated to the receipt's own
    admission weights. -/
def esDeltaCLWall {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) : Prop :=
  Goal (tableOfI S.env)
      (.cl dl (deltaCanonL hres hlen hwf hb) S σ (S.can σ))
  ∧ Goal (tableOfI S.env)
      (.cl (deltaDbΓ S.env Γ hres hbody hlen hwf
        (deltaAdmDb (enrichEnvWfT S.env) hres hbody htr)) hb S σ (S.can σ))

/-- The `hag` discharge on-cone: at `Aw := (enrichEnvWfT S.env).admW`,
    `AgreeOn E admW admW` is reflexivity, so `esDeltaCLWall` embeds into
    `esDeltaKeptWall` at the calibrated weight function. -/
theorem esDeltaKeptWall_of_clWall_admW {Eₐ E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level)
    (h : esDeltaCLWall hres hbody htr hlen hwf hb dl S σ) :
    esDeltaKeptWall (enrichEnvWfT S.env).admW hres hbody htr hlen hwf hb dl
      S σ :=
  ⟨fun _ _ _ => rfl, h.1, h.2⟩

/-! ## §2 the `admW`-calibrated conditional field at `tableOfI S.env` -/

/-- `es_delta` (kept branch) at `tableOfI S.env` with the record's `Aw`
    calibrated to the receipt's own admission weights: `hag` discharged by
    reflexivity; the residual is exactly `esDeltaCLWall` (`hL`/`hB`). -/
theorem es_delta_kept_tableOfI_admW {Eₐ E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level)
    (hu : levelIsZero (σ hb.reg.1) = false)
    (hwall : esDeltaCLWall hres hbody htr hlen hwf hb dl S σ) :
    CaseStep (enrichEnvWfT S.env).admW (tableOfI S.env)
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        S σ (S.can σ)) :=
  es_delta_kept_tableOfI _ hres hbody htr hlen hwf hb dl dr S σ hu
    (esDeltaKeptWall_of_clWall_admW hres hbody htr hlen hwf hb dl S σ hwall)

/-- The `tableOfI hW` pin of the `admW`-calibrated field. -/
noncomputable def es_delta_kept_tableOfI_pin_admW {E : ResolvedEnv}
    (hW : EnvWfT E) {Eₐ : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat}
    {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (hext : EnvExt E Eₐ) (hctx : CtxWfT E n Γ) (σ : Level → Level)
    (hu : levelIsZero (σ hb.reg.1) = false)
    (hwall : esDeltaCLWall hres hbody htr hlen hwf hb dl
      ⟨hW, hext, hctx⟩ σ) :
    CaseStep (enrichEnvWfT hW).admW (tableOfI hW)
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        ⟨hW, hext, hctx⟩ σ
        ((⟨hW, hext, hctx⟩ : ScopedCtx Eₐ E n Γ).can σ)) :=
  es_delta_kept_tableOfI_admW hres hbody htr hlen hwf hb dl dr
    ⟨hW, hext, hctx⟩ σ hu hwall

/-! ## §3 non-vacuity of the CL-only wall on the landed fixture -/

/-- NON-VACUITY: `esDeltaCLWall` is inhabited on the `srDeltaFixture*` fixture
    — both `CL` legs by `ConvMod.refl` at `dl := deltaCanonL`,
    `hb := deltaDbΓ` (the same two payments as `srDeltaWall_fixture`). -/
theorem srDeltaCLWall_fixture :
    esDeltaCLWall srDeltaHres srDeltaHbody srDeltaHtr srDeltaHlen srDeltaHwf
      srDeltaHb srDeltaDl srDeltaScope id :=
  ⟨ConvMod.refl _, ConvMod.refl _⟩

/-- The `admW`-calibrated field end-to-end on the fixture: a real `CaseStep`
    at `tableOfI srDeltaFixtureEnvWfT` with `Aw := srDeltaAdmW` — the only
    premises consumed are the two `CL` legs (inhabited here by refl). -/
theorem srDeltaEsKept_tableOfI_admW_fixture :
    CaseStep srDeltaAdmW (tableOfI srDeltaFixtureEnvWfT)
      (.es (CvP.delta srDeltaFixtureEnv 0 [] 7 [] srDeltaFixtureMember
        (.sort .zero) srDeltaHres srDeltaHbody srDeltaHtr srDeltaHlen
        srDeltaHwf srDeltaHb srDeltaDl srDeltaHb)
        srDeltaScope id (srDeltaScope.can id)) :=
  es_delta_kept_tableOfI_admW srDeltaHres srDeltaHbody srDeltaHtr srDeltaHlen
    srDeltaHwf srDeltaHb srDeltaDl srDeltaHb srDeltaScope id srDeltaHu
    srDeltaCLWall_fixture

#print axioms Rcic.Syn.esDeltaCLWall
#print axioms Rcic.Syn.esDeltaKeptWall_of_clWall_admW
#print axioms Rcic.Syn.es_delta_kept_tableOfI_admW
#print axioms Rcic.Syn.es_delta_kept_tableOfI_pin_admW
#print axioms Rcic.Syn.srDeltaCLWall_fixture
#print axioms Rcic.Syn.srDeltaEsKept_tableOfI_admW_fixture

end Rcic.Syn

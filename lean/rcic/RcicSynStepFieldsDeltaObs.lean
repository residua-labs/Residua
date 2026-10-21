import rcic.RcicSynStepFieldsDeltaIota
import rcic.RcicSynStepFields1

/-!
# `StepSuppliers` field closures — `es_fsub`, `es_delta`, `delta_obs`

Sort-row port-discharge wave (cc 2026-10-18, `sortrow-ports.md`): fields `es_fsub`
(`RcicSynStepSkeleton.lean:491`), `es_delta` (`:408`), and `delta_obs` (`:548`),
from the landed closers of `RcicSynStepFields1` / `RcicSynStepFieldsDeltaIota`.

Port dispositions (spec categories (a)–(d)):

**`es_fsub`** — `ES[hab]` is **(a)**, discharged inside the closer from `StepIH`
via `fsub_es` (`fsub_issued_replacement_es`, `RcicSynStepFields1.lean:235`).
`TableClosed tbl` is **(d)**, a global premise on the rule table (same named-
hypothesis treatment as `TableWF`); the two `instEnd` `CL`s are **(d)**: every
`.cl` child the `fsub` node issues is an `occ_cl` occurrence pair at `subAt`
payload positions (`fsub_issued_cl_is_occurrence`, `:288`), and `instEnd` is a
supplier-built surface, never a stored subterm.

**`es_delta`** — `es_delta_field` case-splits on `levelIsZero (σ hb.reg.1)`:
`CL tbl σ ρ hb dr` is **(a)** inside (`delta_issued_cl`, `RcicSynStepFieldsDeltaIota.lean:160`).
On `true`, `hbPb` is **(a)** whenever `hb.reg.2` sits at a `subAt` path
(`hregOcc`, via `delta_issued_reg_pb`/`occ_pb`); `hL` at the fresh `deltaCanonL`
surface stays **(d)**. On `false`, `hE`/`D_b`/`hDb_cl`/`obs` are **(a)/**(c)**
inside `delta_kept_caseStep_of_obs_ih` (`:779`, via `deltaAdmDb` +
`deltaAdmDb_issued_obs_exchange`); `hE₀`, `hag`, `hap`, `hρ`, `hmem`, `hB` remain
flat named hypotheses (`hρ`/`hmem` are additionally **(c)** at the canonical
display `ρ = S.can σ` / `tbl = tableOf S.env`, `delta_kept_caseStep_tableOf`).

**`delta_obs`** — `DeltaObsPorts S hres hbody htr ls pos` at the field's own `pos`:
**(c)** at every position whose resolved level is bounded, `eqN` to a bounded
representative, a `.succ` gate, or a uniform gate (the `deltaObsPorts_*` lemmas
below), vacuously **(c)** out of bounds; **(d)** in general at an unbounded
internal index (`W-TABLE-DELTA-OBSERVATION-STABILITY`).
`delta_obs_field_of_completePlan` is the full close under `AdmObsPlan.Complete`.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-! ### `es_fsub` -/

/-- Exact `StepSuppliers.es_fsub` statement (the binder telescope copied verbatim
    from `RcicSynStepSkeleton.lean:491`) under its three residual ports. -/
theorem es_fsub_field
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B Sx a b : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B Sx) (hA : TyP E n Γ A (.sort u))
    (hab : CvP E n Γ a b A)
    (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a Sx))
    (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a Sx))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hcl : TableClosed tbl)
    (hL : CL tbl σ ρ dl (instEnd hB hab.dl hA))
    (hR : CL tbl σ ρ (instEnd hB hab.dr hA) dr) :
    CaseStep Aw tbl (.es (CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr) S σ ρ) :=
  fsub_caseStep_of_ports Aw tbl hB hA hab dl dr S σ ρ hcl hL hR

/-- Drop branch of `StepSuppliers.es_fsub` (`levelIsZero (σ u) = true`): needs only
    the two `instEnd` `CL` ports — `TableClosed` is consumed solely by the keep
    branch (`es_fsub_keep`). -/
theorem es_fsub_field_drop
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B Sx a b : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B Sx) (hA : TyP E n Γ A (.sort u))
    (hab : CvP E n Γ a b A)
    (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a Sx))
    (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a Sx))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ u) = true)
    (hL : CL tbl σ ρ dl (instEnd hB hab.dl hA))
    (hR : CL tbl σ ρ (instEnd hB hab.dr hA) dr) :
    CaseStep Aw tbl (.es (CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr) S σ ρ) := by
  intro _hq _ih
  have hLe := instEnd_eps_drop hB hab.dl hA (σ := σ) (ρ := ρ) hu
  have hRe := instEnd_eps_drop hB hab.dr hA (σ := σ) (ρ := ρ) hu
  refine es_fsub_drop hB hA hab dl dr ?_ ?_
  · simpa only [CL, hLe] using hL
  · simpa only [CL, hRe] using hR

/-! ### `es_delta` -/

/-- Exact `StepSuppliers.es_delta` statement (`RcicSynStepSkeleton.lean:408`),
    case-split on `levelIsZero (σ hb.reg.1)` with every residual port as a flat
    named hypothesis:

    - `hL : CL tbl σ ρ dl (deltaCanonL hres hlen hwf hb)` — (d) fresh canonical
      surface, needed on both branches.
    - `hregOcc` — guarded (a)-receipt for `hbPb : PBit σ ρ hb hb.reg.2` on the
      proof branch: whenever `hb.reg.2` sits at a `subAt` occurrence path,
      `Issues.occ_pb` supplies it from `StepIH` (`es_delta_proof_of_reg_occ`).
    - `hE₀ hag hap hρ hmem hB` — the kept-branch residue of
      `delta_kept_caseStep_of_obs_ih` after its internal discharges of
      `hR` (`delta_cl`), `hObs` (`delta_obs_out`/`delta_obs_gate` +
      `obsLvlEq_eps_delta` on the `deltaAdmDb` adapter), and `hDb_cl`
      (`deltaAdmDb_closedWf_of_envWfT`). Unused on the proof branch. -/
theorem es_delta_field
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hL : CL tbl σ ρ dl (deltaCanonL hres hlen hwf hb))
    (hregOcc : levelIsZero (σ hb.reg.1) = true →
      ∃ pReg : List Nat, (P2Query.es
        (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ).subAt
          0 pReg = some (.ty hb.reg.2))
    (hE₀ : E₀ = E)
    (hag : AgreeOn E Aw (enrichEnvWfT (hE₀ ▸ S.env)).admW)
    (hap : ((enrichEnvWfT (hE₀ ▸ S.env)).defAdm hres hbody htr).hv.AssumpPref)
    (hρ : DispFor σ E n Γ ρ)
    (hmem : deltaRule r (deltaAdmDb (enrichEnvWfT (hE₀ ▸ S.env)) hres hbody htr) ∈ tbl)
    (hB : CL tbl σ ρ (deltaDbΓ (hE₀ ▸ S.env) Γ hres hbody hlen hwf
      (deltaAdmDb (enrichEnvWfT (hE₀ ▸ S.env)) hres hbody htr)) hb) :
    CaseStep Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ) := by
  intro hq ih
  cases hzi : levelIsZero (σ hb.reg.1) with
  | true =>
      obtain ⟨pReg, hocc⟩ := hregOcc hzi
      exact es_delta_proof_of_reg_occ Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ
        hzi hL pReg hocc hq ih
  | false =>
      subst hE₀
      exact delta_kept_caseStep_of_obs_ih Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ
        hzi hag hap hρ hmem hL hB hq ih

/-- Retained-result branch of `StepSuppliers.es_delta` (`levelIsZero (σ hb.reg.1)
    = false`) under `DeltaAdmObsPorts` (`RcicSynStepFieldsDeltaIota.lean:815`):
    `D_b`/`hDb_cl`/`obs` are discharged from `StepIH` + the `deltaAdmDb` adapter. -/
theorem es_delta_field_of_admObsPorts
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : DeltaAdmObsPorts Aw tbl hres hbody htr hlen hwf hb dl S σ ρ) :
    CaseStep Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ) :=
  delta_kept_caseStep_of_admObsPorts Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ ports

/-- Proof-result branch of `StepSuppliers.es_delta` (`levelIsZero (σ hb.reg.1) =
    true`) when `hb.reg.2` sits at a `subAt` occurrence path `pReg`: `PBit` is
    discharged from `StepIH` via `Issues.occ_pb`; only the fresh-surface `hL`
    (category (d)) remains named. -/
theorem es_delta_field_proof_of_reg_occ
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ hb.reg.1) = true)
    (hL : CL tbl σ ρ dl (deltaCanonL hres hlen hwf hb))
    (pReg : List Nat)
    (hocc : (P2Query.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ).subAt
      0 pReg = some (.ty hb.reg.2)) :
    CaseStep Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ) :=
  es_delta_proof_of_reg_occ Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ hu hL pReg hocc

/-! ### `delta_obs` -/

/-- Exact `StepSuppliers.delta_obs` statement (the binder telescope copied verbatim
    from `RcicSynStepSkeleton.lean:548`) under a `DeltaObsPorts` at the field's own
    position `pos`. -/
theorem delta_obs_field
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true}
    {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
    {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    (_hδ : Demand (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (pos : ObsPos)
    (ports : DeltaObsPorts S hres hbody htr ls pos) :
    CaseStep Aw tbl (.observation ((enrichEnvWfT S.env).defAdm hres hbody htr).hv id
      (instLevel (ls.map σ)) (fun l => σ (instLevel ls l)) pos S σ []) :=
  delta_obs_caseStep_of_ports Aw tbl _hδ pos ports

/-- Exact `StepSuppliers.delta_obs` statement closed from a complete observation
    plan `p : AdmObsPlan ((enrichEnvWfT S.env).defAdm hres hbody htr) σ ls` —
    `p.Complete` is the named hypothesis. -/
theorem delta_obs_field_of_completePlan
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true}
    {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
    {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    (_hδ : Demand (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (p : AdmObsPlan ((enrichEnvWfT S.env).defAdm hres hbody htr) σ ls) (hc : p.Complete)
    (pos : ObsPos) :
    CaseStep Aw tbl (.observation ((enrichEnvWfT S.env).defAdm hres hbody htr).hv id
      (instLevel (ls.map σ)) (fun l => σ (instLevel ls l)) pos S σ []) :=
  delta_obs_caseStep_of_completePlan Aw tbl _hδ p hc pos

/-! ### `DeltaObsPorts` discharge lemmas (category (c)) -/

/-- `DeltaObsPorts` at `.out k` when every resolved level is bounded below
    `ls.length` — the S7 §3 row-1 route. -/
theorem deltaObsPorts_out_of_bounded {E : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {S : ScopedCtx Eₐ E n₀ Γ₀} {r : Nat} {m : CheckedMember} {b : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {ls : List Level} {k : Nat}
    (hb : ∀ l, (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.outLevels id)[k]? = some l →
      levelBounded ls.length l = true) :
    DeltaObsPorts S hres hbody htr ls (.out k) :=
  fun l hl => ⟨.bounded (hb l hl)⟩

/-- `DeltaObsPorts` at `.gate k` when every resolved level is bounded below
    `ls.length` — the S7 §3 row-1 route. -/
theorem deltaObsPorts_gate_of_bounded {E : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {S : ScopedCtx Eₐ E n₀ Γ₀} {r : Nat} {m : CheckedMember} {b : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {ls : List Level} {k : Nat}
    (hb : ∀ l, (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.gateLevels id)[k]? = some l →
      levelBounded ls.length l = true) :
    DeltaObsPorts S hres hbody htr ls (.gate k) :=
  fun l hl => ⟨.bounded (hb l hl)⟩

/-- `DeltaObsPorts` at `.out k` when position `k` is out of bounds — vacuous. -/
theorem deltaObsPorts_out_of_none {E : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {S : ScopedCtx Eₐ E n₀ Γ₀} {r : Nat} {m : CheckedMember} {b : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {ls : List Level} {k : Nat}
    (h : (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.outLevels id)[k]? = none) :
    DeltaObsPorts S hres hbody htr ls (.out k) :=
  fun l hl => by simp [h] at hl

/-- `DeltaObsPorts` at `.gate k` when position `k` is out of bounds — vacuous. -/
theorem deltaObsPorts_gate_of_none {E : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {S : ScopedCtx Eₐ E n₀ Γ₀} {r : Nat} {m : CheckedMember} {b : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {ls : List Level} {k : Nat}
    (h : (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.gateLevels id)[k]? = none) :
    DeltaObsPorts S hres hbody htr ls (.gate k) :=
  fun l hl => by simp [h] at hl

/-- `DeltaObsPorts` at `.out k` when every resolved level is `eqN` to a
    `ls.length`-bounded representative — the S7 §3 row-2 route. -/
theorem deltaObsPorts_out_of_eqNRep {E : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {S : ScopedCtx Eₐ E n₀ Γ₀} {r : Nat} {m : CheckedMember} {b : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {ls : List Level} {k : Nat}
    (hr : ∀ l, (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.outLevels id)[k]? = some l →
      ∃ l₀, eqN l l₀ ∧ levelBounded ls.length l₀ = true) :
    DeltaObsPorts S hres hbody htr ls (.out k) :=
  fun l hl => let ⟨l₀, he, hb⟩ := hr l hl; ⟨.eqNRep l₀ he hb⟩

/-- `DeltaObsPorts` at `.gate k` when every resolved level is `eqN` to a
    `ls.length`-bounded representative — the S7 §3 row-2 route. -/
theorem deltaObsPorts_gate_of_eqNRep {E : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {S : ScopedCtx Eₐ E n₀ Γ₀} {r : Nat} {m : CheckedMember} {b : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {ls : List Level} {k : Nat}
    (hr : ∀ l, (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.gateLevels id)[k]? = some l →
      ∃ l₀, eqN l l₀ ∧ levelBounded ls.length l₀ = true) :
    DeltaObsPorts S hres hbody htr ls (.gate k) :=
  fun l hl => let ⟨l₀, he, hb⟩ := hr l hl; ⟨.eqNRep l₀ he hb⟩

/-- `DeltaObsPorts` at `.gate k` when every resolved level is a successor — the
    S7 §3 row-3 route. -/
theorem deltaObsPorts_gate_of_succ {E : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {S : ScopedCtx Eₐ E n₀ Γ₀} {r : Nat} {m : CheckedMember} {b : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {ls : List Level} {k : Nat}
    (hs : ∀ l, (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.gateLevels id)[k]? = some l →
      ∃ l₀, l = .succ l₀) :
    DeltaObsPorts S hres hbody htr ls (.gate k) :=
  fun l hl => by
    obtain ⟨l₀, rfl⟩ := hs l hl
    exact ⟨.succGate l₀⟩

/-- `DeltaObsPorts` at `.gate k` when every resolved level is a parameter-free
    `UniformType` — the S7 §3 row-3′ route. -/
theorem deltaObsPorts_gate_of_uniformType {E : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {S : ScopedCtx Eₐ E n₀ Γ₀} {r : Nat} {m : CheckedMember} {b : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {ls : List Level} {k : Nat}
    (hu : ∀ l, (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.gateLevels id)[k]? = some l →
      UniformType l ∧ levelBounded 0 l = true) :
    DeltaObsPorts S hres hbody htr ls (.gate k) :=
  fun l hl => let ⟨hUT, hb⟩ := hu l hl; ⟨.uniformType hb hUT⟩

/-- `DeltaObsPorts` at `.gate k` when every resolved level is a parameter-free
    `UniformProp` — the S7 §3 row-4 route. -/
theorem deltaObsPorts_gate_of_uniformProp {E : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {S : ScopedCtx Eₐ E n₀ Γ₀} {r : Nat} {m : CheckedMember} {b : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {ls : List Level} {k : Nat}
    (hu : ∀ l, (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.gateLevels id)[k]? = some l →
      UniformProp l ∧ levelBounded 0 l = true) :
    DeltaObsPorts S hres hbody htr ls (.gate k) :=
  fun l hl => let ⟨hUP, hb⟩ := hu l hl; ⟨.uniformProp hb hUP⟩

#print axioms Rcic.Syn.es_fsub_field
#print axioms Rcic.Syn.es_fsub_field_drop
#print axioms Rcic.Syn.es_delta_field
#print axioms Rcic.Syn.es_delta_field_of_admObsPorts
#print axioms Rcic.Syn.es_delta_field_proof_of_reg_occ
#print axioms Rcic.Syn.delta_obs_field
#print axioms Rcic.Syn.delta_obs_field_of_completePlan
#print axioms Rcic.Syn.deltaObsPorts_gate_of_uniformProp

end Rcic.Syn

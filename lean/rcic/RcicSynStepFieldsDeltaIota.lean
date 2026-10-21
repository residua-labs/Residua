import rcic.RcicSynStepSkeleton
import rcic.RcicSynDeltaKeptES
import rcic.RcicSynP2Iota
import rcic.RcicSynTableBuild
import rcic.RcicSynIotaRoutePlan
import rcic.RcicSynListConsIota

/-!
# StepSuppliers Field Analysis & Conditional Closures — `es_delta`, `delta_obs`, `es_iota_retained`

Lane `agy-fields2` (`RcicSynStepSkeleton.StepSuppliers` fields `es_delta`, `delta_obs`, and
`es_iota_retained` in `research/rcic/sortrow/STEP_SUPPLIERS.md`):

1. **`StepSuppliers.es_delta` and the §2.1 `D_b` adapter (`RcicSynDeltaKeptES.es_delta_kept`)**:
   - **Issued ports proved from `Demand` + `StepIH`**:
     * `delta_issued_cl`: extracts `CL tbl σ ρ hb dr` from `Issues.delta_cl` (`ih_local` +
       `dmStep_pair_below`).
     * `delta_issued_reg_pb` and `delta_direct_const_issued_pb`: extract `PBit σ ρ hb hb.reg.2`
       from `StepIH` through `Issues.occ_pb` whenever `hb.reg.2` sits at a `P2Query.subAt`
       occurrence path `pReg` (and unconditionally at `pReg = [1, 0]` when
       `dl = deltaCanonL hres hlen hwf hb`).
     * `es_delta_direct_const_proof`: **zero-hypothesis** closure of `CaseStep` on the
       proof-result branch (`levelIsZero (σ hb.reg.1) = true`) when
       `dl = deltaCanonL hres hlen hwf hb`, using only `StepIH` (`Issues.occ_pb` +
       `Issues.delta_cl`).
     * `es_delta_proof_of_reg_occ`: proof-result branch from `StepIH` (`Issues.occ_pb` +
       `Issues.delta_cl`), `CL tbl σ ρ dl (deltaCanonL hres hlen hwf hb)`, and occurrence path
       `pReg` for `hb.reg.2` (**never assuming `PBit σ ρ hb hb.reg.2` or mentioning `dr`**).
     * `deltaCanonL_wt_lt` and `deltaCanonL_ap`: the canonical left surface
       `deltaCanonL hres hlen hwf hb` is strictly below `(CvP.delta ...).wt Aw` for every `Aw`
       and preserves `AssumpPref`.
     * `delta_obs_before_of_agreeOn`: generalizes `delta_obs_before` from
       `(enrichEnvWfT S.env).admW` to any ranking `Aw` satisfying
       `AgreeOn E Aw (enrichEnvWfT S.env).admW`.
     * `delta_issued_obs_out_at`, `delta_issued_obs_gate_at`, `delta_issued_obs_out`,
       `delta_issued_obs_gate`, and `delta_issued_obs_exchange`: extract every actual
       `OutLevels` and `GateLevels` observation of `((enrichEnvWfT S.env).defAdm hres hbody htr).hv`
       from `Issues.delta_obs_out` / `Issues.delta_obs_gate` via `ih_issue` and assemble the
       δ-exchange `LvlEq` via `obsLvlEq_eps_delta`.
   - **The §2.1 `D_b` adapter (`BELOWC_OBSERVATION_REQUESTS.md` §2.1)**:
     * `castArityZero` and `deltaAdmDb`: builds `D_b : TyP E m.arity [] b m.mtype` from
       `a := hE.defAdm hres hbody htr` (`a.hv : TyP a.E₀ 0 [] b m.mtype`, `a.ext : EnvExt a.E₀ E`,
       `a.arity : m.arity = 0`) via `a.arity.symm ▸ TyP.ewk a.E₀ E 0 [] b m.mtype a.ext a.hv`.
     * `deltaAdmDb_eps`, `deltaAdmDb_outLevels`, `deltaAdmDb_gateLevels`, `deltaAdmDb_closedWf`,
       `deltaAdmDb_deltaRule`: preservation of `.eps`, observation lists, `ClosedWf`, and
       `deltaRule r` across the `ewk + arity` adapter.
     * `defAdm_closedWf` and `deltaAdmDb_closedWf_of_envWfT`: proves unconditionally for any
       `hEnv : EnvWfT E` that `(deltaAdmDb (enrichEnvWfT hEnv) hres hbody htr).ClosedWf` holds.
     * `deltaRule_mem_tableOf`: proves unconditionally via `RcicSynTableBuild.deltaRule_lookup`
       that `deltaRule r (deltaAdmDb (enrichEnvWfT hEnv) hres hbody htr) ∈ tableOf hEnv`.
     * `deltaAdmDb_issued_obs_exchange`: transports `delta_issued_obs_exchange` along
       `deltaAdmDb_eps` to discharge the `hObs` premise of `es_delta_kept` on `deltaAdmDb`
       directly from `StepIH`.
   - **Exact-statement `CaseStep` closures on the `StepSuppliers.es_delta` telescope**:
     * `DeltaPorts` (**never mentions `dr`**) and `delta_caseStep_of_ports`: exact binder
       telescope of `StepSuppliers.es_delta` followed by `(ports : DeltaPorts ...)`, closing both
       proof-result and retained-result branches using `StepIH` (`Issues.delta_cl`).
     * `DeltaAdmObsPorts` (**never mentions `dr`, `hObs`, or `hDb_cl`**) and
       `delta_kept_caseStep_of_admObsPorts`: exact binder telescope of `StepSuppliers.es_delta`
       followed by `(ports : DeltaAdmObsPorts ...)`, discharging **both** `hR` (`Issues.delta_cl`)
       **and** `hObs` (`Issues.delta_obs_out`/`Issues.delta_obs_gate`) from `StepIH` and `hDb_cl`
       via `deltaAdmDb_closedWf_of_envWfT`.
     * `delta_proof_caseStep_of_ports`, `delta_kept_caseStep_of_ports`,
       `delta_kept_caseStep_of_obs_ih`, and `delta_kept_caseStep_tableOf`.
     * `delta_issued_cl_variants` and `delta_issued_pb_is_occurrence`: kernel-checked occurrence
       controls on `.cl` and `.pb` children emitted from `CvP.delta`.

2. **`StepSuppliers.delta_obs` and `AdmObsPlan.discharge`**:
   - `observation_issued_only_by_delta` and `observation_issues_nothing`: every
     `Issues issuer (.observation ...)` edge is `Issues.delta_obs_out` or `Issues.delta_obs_gate`
     from a `CvP.delta` node, and an `.observation` query issues no sub-queries (`StepIH` is
     vacuously empty).
   - `DeltaObsRoute` and `DeltaObsPorts` (completely `σ`-independent, using `hq.hom : LevelHom σ`
     from `Demand` + `LevelHom.eqN_map` to supply the `ψ`-side transport of `eqNRep` per
     `BELOWC_OBSERVATION_REQUESTS.md` §4), and `delta_obs_caseStep_of_ports` on the exact
     `StepSuppliers.delta_obs` binder telescope followed by `(ports : DeltaObsPorts ...)`.
   - `delta_obs_caseStep_of_completePlan`, `delta_obs_exchange_of_completePlan`
     (`AdmObsPlan.discharge` transported to `deltaAdmDb`), `delta_obs_caseStep_out_of_cert`, and
     `delta_obs_caseStep_gate_of_cert`.

3. **`StepSuppliers.es_iota_retained` (`RcicSynP2Iota.iota_erasure_from_answers`, `RcicSynIotaRoutePlan`, Nat/List/Vec instances)**:
   - **Issued ports proved from `Demand` + `StepIH`**:
     * `iota_issued_pbL` & `iota_issued_pbR`: extract `PBit σ ρ dl hlhs.reg.2` and
       `PBit σ ρ dr hlhs.reg.2` via `Issues.iota_pbL` / `Issues.iota_pbR`.
     * `iota_issued_cl_left` & `iota_issued_cl_right`: extract `CL tbl σ ρ dl hlhs` and
       `CL tbl σ ρ hrhs dr` via `Issues.occ_cl` at payload paths `(0, [2])`/`(0, [0])` and
       `(0, [1])`/`(0, [3])` + `below_iota`.
     * `iota_issued_pb_hlhs_of_reg_occ` & `iota_issued_pb_hrhs_of_reg_occ`: extract
       `qPL : PBit σ ρ hlhs hlhs.reg.2` and `qPR : PBit σ ρ hrhs hlhs.reg.2` from `StepIH` via
       `Issues.occ_pb` whenever `hlhs.reg.2` sits at a `P2Query.subAt` occurrence path `pReg`.
   - **Exact-statement `CaseStep` closures on the `StepSuppliers.es_iota_retained` telescope**:
     * `IotaRetainedPorts` (**never mentions `dl`, `dr`, `qCLL`, or `qCLR`**) and
       `iota_retained_caseStep_of_ports`: exact binder telescope of
       `StepSuppliers.es_iota_retained` followed by `(ports : IotaRetainedPorts ...)`, discharging
       `qCLL` and `qCLR` from `StepIH`.
     * `IotaRetainedSimulation` and `IotaRetainedRegOccPorts` (**never mentions `qPL`, `qPR`,
       `qCLL`, `qCLR`**) and `iota_retained_caseStep_of_reg_occ_ports`: exact binder telescope of
       `StepSuppliers.es_iota_retained` followed by `(ports : IotaRetainedRegOccPorts ...)`,
       discharging **all four** outer queries `qCLL`, `qCLR`, `qPL`, `qPR` from `StepIH`.
     * `iota_retained_caseStep_of_simulation` and `iota_retained_caseStep_same_endpoints`.
     * `iota_issued_cl_is_occurrence`, `iota_issued_pb_variants`, and `slot_not_issued`:
       kernel-checked occurrence controls on `.cl`, `.pb`, and `.slot` queries.
   - **Concrete Nat / `#7451` hit-bvar `esub` / List / Vec instances**:
     * `natSucc_iota_retained_caseStep`: unconditional `CaseStep` closure on
       `RcicSynNatSuccIota.H`.
     * `natIotaSiteEsub`, `natIotaPlan_esub_origins`, `nat_esub_slot_request_below`, `H_esub`,
       `s17_hL_esub_eps`, and `natSucc_esub_iota_retained_caseStep`: exercises `#7451`'s
       hit-bvar `esub` spine fix (`s16hL_esub`) in `RcicSynIotaRoutePlan` and closes `CaseStep`
       unconditionally on `H_esub`.
     * `s18_beta_witness` and `listCons_iota_retained_caseStep`: unconditional `CaseStep` closure
       on `RcicSynListConsIota.s18H`.
     * `IotaExpectedSlotPos`, `expectedIotaSlotCount`,
       `expectedIotaSlotCount_eq_planSlotCount_add_ctorParams`, `wSuccU1_expectedSlotCount` (`6`),
       `wConsNat_expectedSlotCount` (`9` vs `planSlotCount = 8`), and
       `wVcons_expectedSlotCount` (`11` vs `planSlotCount wVcons = 10` on `Vec`).
   - **What remains for a general ι rule/template decoder (`BELOWC_DEMAND_GRAMMAR_CONTINUATION.md` §7.4)**:
     1. Complete slot enumeration from `DerivedIota` (`IotaExpectedSlotPos`: `recArg`, `major`,
        `ctorParam`, `ctorField`, `rhsRecResult`) before reading, returning
        `originalApp | wrappedNeed | missingExpectedSlot` without dropping `ctorParams` or
        `filterMap`ping missing RHS recursive-result reads (`#7451` fixes `spineViews` to
        continue into the replacement at an `esub`/`lsub` hit `bvar` per A6 §11).
     2. Keeping constructor-side `lsC`/`ctorParams` distinct from the recursor-side level list
        and parameter prefix.
     3. General admission-to-`CRule`/template decoder (or supplied table-construction receipt)
        connecting `DerivedIota` to a `CRule ∈ tbl` with `CRoot` match and finite
        `RStar (RStep tbl)` β* simulation (`hmatchL`, `hcroot`, `hbeta`, `hmatchR`), since
        `CRule` has function fields (`nargs`, `rhs`) and cannot be selected by decidable equality.
     4. Typed global decoder for boxed local `RawQuery` slot requests from
        `RcicSynIotaRoutePlan` (converting heterogeneous boxed `.cl c.dl c.dr` into `.es`/`cts`
        legs and supplying `.slot` kind bits, which have no issuing row in `Issues` —
        `W-IOTA-SLOT-KIND-SOURCE`).

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-- Constructor tag of a `CvP`, nonzero on `delta` and `iota`.
    Used by `congrArg esParentTagDeltaIota` to refute foreign `.es` rows when inverting
    an `Issues` edge whose parent is a concrete `.es` node. -/
def cvpCtorTagDeltaIota {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat} :
    CvP E n Γ a b T → Nat
  | .delta .. => 1
  | .iota .. => 2
  | _ => 0

/-- `cvpCtorTagDeltaIota` lifted to the `.es` parent of an `Issues` edge. -/
def esParentTagDeltaIota : P2Query Eₐ → Nat
  | .es c _ _ _ => cvpCtorTagDeltaIota c
  | _ => 0

/-! ## §1 `StepSuppliers.es_delta`: issued ports, the §2.1 `D_b` adapter, and `CaseStep` closures -/

/-- `Issues.delta_cl` is unconditionally answered by `StepIH` whenever the parent `.es (CvP.delta ...)`
    query is demanded: yields `CL tbl σ ρ hb dr` (`hR` in `es_delta_kept`). -/
theorem delta_issued_cl
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ)) :
    CL tbl σ ρ hb dr := by
  let hnode := CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr
  have hwb : hb.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact ih_local Aw tbl hq ih (.cl hb dr S σ ρ) Issues.delta_cl rfl
    (lexDM_combMeas_mono Aw _ (lex_of_dm (dmStep_pair_below Aw hnode rfl hb dr hwb hwr)))

/-- Whenever `hb.reg.2` sits at a `P2Query.subAt` occurrence path `pReg` of the `CvP.delta` query,
    `StepIH` answers `PBit σ ρ hb hb.reg.2` via `Issues.occ_pb` at `(0, [0])` and `(0, pReg)`. -/
theorem delta_issued_reg_pb
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pReg : List Nat)
    (hocc : (P2Query.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ).subAt
      0 pReg = some (.ty hb.reg.2))
    (hq : Demand (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ)) :
    PBit σ ρ hb hb.reg.2 := by
  let hnode := CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr
  have hwb : hb.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwreg : hb.reg.2.wt Aw < hnode.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hb) hwb
  exact ih_local Aw tbl hq ih (.pb hb hb.reg.2 S σ ρ)
    (Issues.occ_pb (k₁ := 0) (k₂ := 0) (p₁ := [0]) (p₂ := pReg)
      rfl hocc hq.ap.1 (assumpPref_reg hq.ap.1))
    rfl
    (lexDM_combMeas_mono Aw _ (lex_of_dm (dmStep_pair_below Aw hnode rfl hb hb.reg.2 hwb hwreg)))

/-- When `dl = deltaCanonL hres hlen hwf hb`, `hb.reg.2` sits at payload path `(0, [1, 0])` of the
    `CvP.delta` query, so `StepIH` unconditionally yields `PBit σ ρ hb hb.reg.2`. -/
theorem delta_direct_const_issued_pb
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb
      (deltaCanonL hres hlen hwf hb) dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb
      (deltaCanonL hres hlen hwf hb) dr) S σ ρ)) :
    PBit σ ρ hb hb.reg.2 :=
  delta_issued_reg_pb Aw tbl hres hbody htr hlen hwf hb (deltaCanonL hres hlen hwf hb) dr
    S σ ρ [1, 0] rfl hq ih

/-- `deltaCanonL hres hlen hwf hb` preserves `AssumpPref` from `hb.AssumpPref`. -/
theorem deltaCanonL_ap
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (hap : hb.AssumpPref) :
    (deltaCanonL hres hlen hwf hb).AssumpPref :=
  assumpPref_reg hap

/-- Ranking adequacy (`BELOWC_DEMAND_GRAMMAR_CONTINUATION.md` §7.3): `delta_obs_before`
    generalized from `(enrichEnvWfT S.env).admW` to any admission-weight assignment `Aw`
    satisfying `AgreeOn E Aw (enrichEnvWfT S.env).admW`. -/
theorem delta_obs_before_of_agreeOn
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E n₀ Γ₀)
    (σ : Level → Level) (ρ : List Disp) (pos : ObsPos)
    (hag : AgreeOn E Aw (enrichEnvWfT S.env).admW) :
    Before Aw
      (.observation ((enrichEnvWfT S.env).defAdm hres hbody htr).hv id
        (instLevel (ls.map σ)) (fun l => σ (instLevel ls l)) pos S σ [])
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ) := by
  let hE := enrichEnvWfT S.env
  let a := hE.defAdm hres hbody htr
  let hnode := CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr
  refine before_of_same_prefix Aw rfl
    (lexDM_combMeas_mono Aw _ (lex_of_dm (dmStep_under_rule Aw hnode rfl ?_)))
  intro y hy
  have h1 : y ≤ a.hv.wt Aw := TyP.atoms_le Aw a.hv y hy
  have h2 : a.hv.wt Aw = a.hv.wt hE.admW := TyP.wt_congr a.hv (agreeOn_mono a.ext hag)
  have h3 : a.hv.wt hE.admW < hE.admW r := a.lt
  have h4 : Aw r = hE.admW r := hag r m hres
  have h5 : Aw r < dl.wt Aw := TyP.admW_lt_of_const Aw dl ⟨ls, rfl⟩
  simp only [CvP.wt]
  omega

/-- Every actual `outLevels` index `k` of `((enrichEnvWfT S.env).defAdm hres hbody htr).hv` is
    issued by `Issues.delta_obs_out` and answered by `StepIH`. -/
theorem delta_issued_obs_out_at
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E n₀ Γ₀)
    (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (hag : AgreeOn E Aw (enrichEnvWfT S.env).admW)
    (hap : ((enrichEnvWfT S.env).defAdm hres hbody htr).hv.AssumpPref)
    {k : Nat} {l : Level}
    (hk : (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.outLevels id)[k]? = some l) :
    eqN (instLevel (ls.map σ) l) (σ (instLevel ls l)) := by
  have hstep := ih_issue Aw tbl hq ih
    (.observation ((enrichEnvWfT S.env).defAdm hres hbody htr).hv id
      (instLevel (ls.map σ)) (fun l => σ (instLevel ls l)) (.out k) S σ [])
    (Issues.delta_obs_out hk hap)
    (delta_obs_before_of_agreeOn Aw hres hbody htr hlen hwf hb dl dr S σ ρ (.out k) hag)
  exact hstep l hk

/-- Every actual `gateLevels` index `k` of `((enrichEnvWfT S.env).defAdm hres hbody htr).hv` is
    issued by `Issues.delta_obs_gate` and answered by `StepIH`. -/
theorem delta_issued_obs_gate_at
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E n₀ Γ₀)
    (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (hag : AgreeOn E Aw (enrichEnvWfT S.env).admW)
    (hap : ((enrichEnvWfT S.env).defAdm hres hbody htr).hv.AssumpPref)
    {k : Nat} {l : Level}
    (hk : (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.gateLevels id)[k]? = some l) :
    levelIsZero (instLevel (ls.map σ) l) = levelIsZero (σ (instLevel ls l)) := by
  have hstep := ih_issue Aw tbl hq ih
    (.observation ((enrichEnvWfT S.env).defAdm hres hbody htr).hv id
      (instLevel (ls.map σ)) (fun l => σ (instLevel ls l)) (.gate k) S σ [])
    (Issues.delta_obs_gate hk hap)
    (delta_obs_before_of_agreeOn Aw hres hbody htr hlen hwf hb dl dr S σ ρ (.gate k) hag)
  exact hstep l hk

/-- `StepIH` answers every `l ∈ ((enrichEnvWfT S.env).defAdm hres hbody htr).hv.OutLevels` via
    `Issues.delta_obs_out`. -/
theorem delta_issued_obs_out
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E n₀ Γ₀)
    (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (hag : AgreeOn E Aw (enrichEnvWfT S.env).admW)
    (hap : ((enrichEnvWfT S.env).defAdm hres hbody htr).hv.AssumpPref) :
    ∀ l ∈ ((enrichEnvWfT S.env).defAdm hres hbody htr).hv.OutLevels,
      eqN (instLevel (ls.map σ) l) (σ (instLevel ls l)) := by
  intro l hl
  rcases List.getElem?_of_mem hl with ⟨k, hk⟩
  exact delta_issued_obs_out_at Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ hq ih hag hap hk

/-- `StepIH` answers every `l ∈ ((enrichEnvWfT S.env).defAdm hres hbody htr).hv.GateLevels` via
    `Issues.delta_obs_gate`. -/
theorem delta_issued_obs_gate
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E n₀ Γ₀)
    (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (hag : AgreeOn E Aw (enrichEnvWfT S.env).admW)
    (hap : ((enrichEnvWfT S.env).defAdm hres hbody htr).hv.AssumpPref) :
    ∀ l ∈ ((enrichEnvWfT S.env).defAdm hres hbody htr).hv.GateLevels,
      levelIsZero (instLevel (ls.map σ) l) = levelIsZero (σ (instLevel ls l)) := by
  intro l hl
  rcases List.getElem?_of_mem hl with ⟨k, hk⟩
  exact delta_issued_obs_gate_at Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ hq ih hag hap hk

/-- Combining `delta_issued_obs_out` and `delta_issued_obs_gate` via `obsLvlEq_eps_delta` yields
    the δ-exchange `LvlEq` on the receipt's admission derivation directly from `StepIH`. -/
theorem delta_issued_obs_exchange
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E n₀ Γ₀)
    (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (hag : AgreeOn E Aw (enrichEnvWfT S.env).admW)
    (hap : ((enrichEnvWfT S.env).defAdm hres hbody htr).hv.AssumpPref) :
    LvlEq (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.eps (instLevel (ls.map σ)) [])
      (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.eps (fun l => σ (instLevel ls l)) []) :=
  obsLvlEq_eps_delta ((enrichEnvWfT S.env).defAdm hres hbody htr).hv
    (delta_issued_obs_out Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ hq ih hag hap)
    (delta_issued_obs_gate Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ hq ih hag hap)

/-! ### §1.1 The §2.1 `D_b` adapter (`BELOWC_OBSERVATION_REQUESTS.md` §2.1) -/

/-- Cast a derivation's level arity from `0` to `a` along `ha : a = 0`. -/
def castArityZero {E : ResolvedEnv} {a : Nat} {Γ : LCtx} {b T : Expr Nat}
    (ha : a = 0) (D : TyP E 0 Γ b T) : TyP E a Γ b T :=
  ha.symm ▸ D

theorem castArityZero_eps {E : ResolvedEnv} {a : Nat} {Γ : LCtx} {b T : Expr Nat}
    (ha : a = 0) (D : TyP E 0 Γ b T) (σ : Level → Level) (ρ : List Disp) :
    (castArityZero ha D).eps σ ρ = D.eps σ ρ := by
  cases ha; rfl

theorem castArityZero_outLevels {E : ResolvedEnv} {a : Nat} {Γ : LCtx} {b T : Expr Nat}
    (ha : a = 0) (D : TyP E 0 Γ b T) (θ : Level → Level) :
    (castArityZero ha D).outLevels θ = D.outLevels θ := by
  cases ha; rfl

theorem castArityZero_gateLevels {E : ResolvedEnv} {a : Nat} {Γ : LCtx} {b T : Expr Nat}
    (ha : a = 0) (D : TyP E 0 Γ b T) (θ : Level → Level) :
    (castArityZero ha D).gateLevels θ = D.gateLevels θ := by
  cases ha; rfl

theorem castArityZero_closedWf {E : ResolvedEnv} {a : Nat} {Γ : LCtx} {b T : Expr Nat}
    (ha : a = 0) (D : TyP E 0 Γ b T) :
    (castArityZero ha D).ClosedWf ↔ D.ClosedWf := by
  cases ha; exact Iff.rfl

theorem castArityZero_deltaRule (r : Nat) {E : ResolvedEnv} {a : Nat} {b T : Expr Nat}
    (ha : a = 0) (D : TyP E 0 [] b T) :
    deltaRule r (castArityZero ha D) = deltaRule r D := by
  cases ha; rfl

/-- The prescribed `D_b` adapter (`BELOWC_OBSERVATION_REQUESTS.md` §2.1): from the selected
    admission `a := hE.defAdm hres hbody htr` (`a.hv : TyP a.E₀ 0 [] b m.mtype`,
    `a.ext : EnvExt a.E₀ E`, `a.arity : m.arity = 0`), weaken `a.hv` to `E` via `TyP.ewk`
    and cast its level arity `0` to `m.arity` along `a.arity.symm`. -/
def deltaAdmDb {E : ResolvedEnv} (hE : EnvWfP E)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) : TyP E m.arity [] b m.mtype :=
  let a := hE.defAdm hres hbody htr
  castArityZero a.arity (TyP.ewk a.E₀ E 0 [] b m.mtype a.ext a.hv)

theorem deltaAdmDb_eps {E : ResolvedEnv} (hE : EnvWfP E)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (σ : Level → Level) (ρ : List Disp) :
    (deltaAdmDb hE hres hbody htr).eps σ ρ = (hE.defAdm hres hbody htr).hv.eps σ ρ := by
  unfold deltaAdmDb
  rw [castArityZero_eps]
  rfl

theorem deltaAdmDb_outLevels {E : ResolvedEnv} (hE : EnvWfP E)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (θ : Level → Level) :
    (deltaAdmDb hE hres hbody htr).outLevels θ = (hE.defAdm hres hbody htr).hv.outLevels θ := by
  unfold deltaAdmDb
  rw [castArityZero_outLevels]
  rfl

theorem deltaAdmDb_gateLevels {E : ResolvedEnv} (hE : EnvWfP E)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (θ : Level → Level) :
    (deltaAdmDb hE hres hbody htr).gateLevels θ = (hE.defAdm hres hbody htr).hv.gateLevels θ := by
  unfold deltaAdmDb
  rw [castArityZero_gateLevels]
  rfl

theorem deltaAdmDb_closedWf {E : ResolvedEnv} (hE : EnvWfP E)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) :
    (deltaAdmDb hE hres hbody htr).ClosedWf ↔ (hE.defAdm hres hbody htr).hv.ClosedWf := by
  unfold deltaAdmDb
  exact castArityZero_closedWf _ _

theorem deltaAdmDb_deltaRule {E : ResolvedEnv} (hE : EnvWfP E)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) :
    deltaRule r (deltaAdmDb hE hres hbody htr) = deltaRule r (hE.defAdm hres hbody htr).hv := by
  unfold deltaAdmDb
  rw [castArityZero_deltaRule]
  rfl

/-- Every transparent admission derivation selected by `(enrichEnvWfT hEnv).defAdm` satisfies
    `TyP.ClosedWf` unconditionally (by the same `EnvWfT` tree induction as `deltaRule_lookup`). -/
theorem defAdm_closedWf : {E : ResolvedEnv} → (hEnv : EnvWfT E) →
    {r : Nat} → {m : CheckedMember} → {b : Expr Nat} →
    (hres : E.members r = some m) → (hbody : m.body = some b) →
    (htr : transparent m.mclass = true) →
    ((enrichEnvWfT hEnv).defAdm hres hbody htr).hv.ClosedWf
  | _, .empty, _, _, _, h, _, _ => Option.noConfusion h
  | _, .axiom E r' A u hE hfresh hA hcl hlvl, r, m, b, h, hb, htr => by
      cases hdec : Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm : ⟨.axiomM, 0, A, none⟩ = m :=
            Option.some.inj ((members_extend_self E r _).symm.trans h)
          subst hm
          exact Bool.noConfusion htr
      | isFalse hr =>
          simp only [enrichEnvWfT, EnvWfP.defAdm]
          rw [decRec_isFalse hr hdec]
          simp only [DefAdm.step, DefAdm.lift']
          exact defAdm_closedWf hE ((members_extend_ne E _ hr).symm.trans h) hb htr
  | _, .definition E r' A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, r, m, b, h, hb, htr => by
      cases hdec : Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm : ⟨.definitionM, 0, A, some v⟩ = m :=
            Option.some.inj ((members_extend_self E r _).symm.trans h)
          subst hm
          have hbv : v = b := Option.some.inj hb
          subst hbv
          simp only [enrichEnvWfT, EnvWfP.defAdm]
          rw [decRec_isTrue rfl hdec]
          simp only [eqRec_self, eqNdrec_self, optNoConf_self]
          exact closedWf_enrichHasTyT (envClosed_of_envWfT hE) (envExt_refl E)
            (memberSortP_of_envWfP (enrichEnvWfT hE)) (letCtxConvP_of_envWfT hE)
            (.nil E 0) hv
      | isFalse hr =>
          simp only [enrichEnvWfT, EnvWfP.defAdm]
          rw [decRec_isFalse hr hdec]
          simp only [DefAdm.step, DefAdm.lift']
          exact defAdm_closedWf hE ((members_extend_ne E _ hr).symm.trans h) hb htr
  | _, .thm E r' A p hE hfresh hA hp hclA hclp hlvlA hlvlp, r, m, b, h, hb, htr => by
      cases hdec : Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm : ⟨.theoremM, 0, A, some p⟩ = m :=
            Option.some.inj ((members_extend_self E r _).symm.trans h)
          subst hm
          exact Bool.noConfusion htr
      | isFalse hr =>
          simp only [enrichEnvWfT, EnvWfP.defAdm]
          rw [decRec_isFalse hr hdec]
          simp only [DefAdm.step, DefAdm.lift']
          exact defAdm_closedWf hE ((members_extend_ne E _ hr).symm.trans h) hb htr
  | _, .opaque E r' A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, r, m, b, h, hb, htr => by
      cases hdec : Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm : ⟨.opaqueM, 0, A, some v⟩ = m :=
            Option.some.inj ((members_extend_self E r _).symm.trans h)
          subst hm
          exact Bool.noConfusion htr
      | isFalse hr =>
          simp only [enrichEnvWfT, EnvWfP.defAdm]
          rw [decRec_isFalse hr hdec]
          simp only [DefAdm.step, DefAdm.lift']
          exact defAdm_closedWf hE ((members_extend_ne E _ hr).symm.trans h) hb htr
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, r, m, b, h, hb, htr => by
      simp only [enrichEnvWfT, EnvWfP.defAdm, DefAdm.lift']
      exact defAdm_closedWf hE
        ((enrichGroupMembersT (cvWalkHyp_of_envWfT hE)
          (memberSortP_of_envWfP (enrichEnvWfT hE)) hmem).body_old h hb) hb htr

/-- The §2.1 adapted admission derivation `deltaAdmDb (enrichEnvWfT hEnv) hres hbody htr`
    satisfies `ClosedWf` unconditionally (`hDb_cl` in `es_delta_kept`). -/
theorem deltaAdmDb_closedWf_of_envWfT {E : ResolvedEnv} (hEnv : EnvWfT E)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) :
    (deltaAdmDb (enrichEnvWfT hEnv) hres hbody htr).ClosedWf :=
  (deltaAdmDb_closedWf (enrichEnvWfT hEnv) hres hbody htr).mpr
    (defAdm_closedWf hEnv hres hbody htr)

/-- The `deltaRule` of the §2.1 adapted admission derivation `deltaAdmDb` is a member of
    `tableOf hEnv` (`hmem` in `es_delta_kept`), via `RcicSynTableBuild.deltaRule_lookup` and
    `deltaAdmDb_deltaRule`. -/
theorem deltaRule_mem_tableOf {E : ResolvedEnv} (hEnv : EnvWfT E)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) :
    deltaRule r (deltaAdmDb (enrichEnvWfT hEnv) hres hbody htr) ∈ tableOf hEnv := by
  rw [deltaAdmDb_deltaRule]
  rcases deltaRule_lookup hEnv hres hbody htr with ⟨e, he, hrule⟩
  rw [← hrule]
  exact List.mem_map.mpr ⟨e, he, rfl⟩

/-- Transporting `delta_issued_obs_exchange` along `deltaAdmDb_eps` yields the exact `hObs`
    premise of `RcicSynDeltaKeptES.es_delta_kept` for `D_b := deltaAdmDb (enrichEnvWfT S.env) hres hbody htr`
    directly from `StepIH`. -/
theorem deltaAdmDb_issued_obs_exchange
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E n₀ Γ₀)
    (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (hag : AgreeOn E Aw (enrichEnvWfT S.env).admW)
    (hap : ((enrichEnvWfT S.env).defAdm hres hbody htr).hv.AssumpPref) :
    LvlEq ((deltaAdmDb (enrichEnvWfT S.env) hres hbody htr).eps (instLevel (ls.map σ)) [])
      ((deltaAdmDb (enrichEnvWfT S.env) hres hbody htr).eps (fun l => σ (instLevel ls l)) []) := by
  rw [deltaAdmDb_eps, deltaAdmDb_eps]
  exact delta_issued_obs_exchange Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ hq ih hag hap

/-! ### §1.2 Zero-hypothesis and conditional `CaseStep` closures for `StepSuppliers.es_delta` -/

/-- **Zero-hypothesis closure** of the proof-result direct-const subcase of `StepSuppliers.es_delta`
    (`dl = deltaCanonL hres hlen hwf hb`, `levelIsZero (σ hb.reg.1) = true`):
    `StepIH` supplies both `PBit σ ρ hb hb.reg.2` (via `Issues.occ_pb` at `(0, [0])` / `(0, [1, 0])`)
    and `CL tbl σ ρ hb dr` (via `Issues.delta_cl`). -/
theorem es_delta_direct_const_proof
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ hb.reg.1) = true) :
    CaseStep Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb
      (deltaCanonL hres hlen hwf hb) dr) S σ ρ) := by
  intro hq ih
  have hpb : PBit σ ρ hb hb.reg.2 :=
    delta_direct_const_issued_pb Aw tbl hres hbody htr hlen hwf hb dr S σ ρ hq ih
  have hR : ConvMod (EStep tbl) LvlEq (hb.eps σ ρ) (dr.eps σ ρ) :=
    delta_issued_cl Aw tbl hres hbody htr hlen hwf hb (deltaCanonL hres hlen hwf hb) dr S σ ρ hq ih
  have hdl_star : (deltaCanonL hres hlen hwf hb).eps σ ρ = .star := by
    unfold deltaCanonL
    exact eps_const_proof hu
  have hhb_star : hb.eps σ ρ = .star := hpb.mpr hu
  rw [hhb_star] at hR
  simpa only [Goal, ES, CvP.dl, CvP.dr, hdl_star] using hR

/-- Proof-result branch of `StepSuppliers.es_delta` when `hb.reg.2` sits at a `P2Query.subAt`
    occurrence path `pReg`: `StepIH` supplies `PBit σ ρ hb hb.reg.2` (`Issues.occ_pb`) and
    `CL tbl σ ρ hb dr` (`Issues.delta_cl`), so only `CL tbl σ ρ dl (deltaCanonL hres hlen hwf hb)`
    and `pReg` are needed (**never assuming `PBit σ ρ hb hb.reg.2` or mentioning `dr`**). -/
theorem es_delta_proof_of_reg_occ
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
    CaseStep Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ) := by
  intro hq ih
  have hpb : PBit σ ρ hb hb.reg.2 :=
    delta_issued_reg_pb Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ pReg hocc hq ih
  have hR : ConvMod (EStep tbl) LvlEq (hb.eps σ ρ) (dr.eps σ ρ) :=
    delta_issued_cl Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ hq ih
  have hL_star : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) .star := by
    have h : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) ((deltaCanonL hres hlen hwf hb).eps σ ρ) := hL
    unfold deltaCanonL at h
    rw [eps_const_proof hu] at h
    exact h
  have hhb_star : hb.eps σ ρ = .star := hpb.mpr hu
  rw [hhb_star] at hR
  simpa only [Goal, ES, CvP.dl, CvP.dr] using hL_star.trans hR

/-- Proof-result branch of `StepSuppliers.es_delta` (`levelIsZero (σ hb.reg.1) = true`), using
    the exact `StepSuppliers.es_delta` binder telescope: discharges `CL tbl σ ρ hb dr` from
    `StepIH` via `delta_issued_cl`, and closes `CaseStep` from the two unissued ports
    `hL : Goal tbl (.cl dl (deltaCanonL hres hlen hwf hb) S σ ρ)` and
    `hpb : Goal tbl (.pb hb hb.reg.2 S σ ρ)`. -/
theorem delta_proof_caseStep_of_ports
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
    (hL : Goal tbl (.cl dl (deltaCanonL hres hlen hwf hb) S σ ρ))
    (hpb : Goal tbl (.pb hb hb.reg.2 S σ ρ)) :
    CaseStep Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ) := by
  intro hq ih
  have hR : ConvMod (EStep tbl) LvlEq (hb.eps σ ρ) (dr.eps σ ρ) :=
    delta_issued_cl Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ hq ih
  have hL_star : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) .star := by
    have h : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) ((deltaCanonL hres hlen hwf hb).eps σ ρ) := hL
    unfold deltaCanonL at h
    rw [eps_const_proof hu] at h
    exact h
  have hhb_star : hb.eps σ ρ = .star := hpb.mpr hu
  rw [hhb_star] at hR
  simpa only [Goal, ES, CvP.dl, CvP.dr] using hL_star.trans hR

/-- Retained-result branch of `StepSuppliers.es_delta` (`levelIsZero (σ hb.reg.1) = false`),
    using the exact `StepSuppliers.es_delta` binder telescope and `RcicSynDeltaKeptES.es_delta_kept`:
    discharges `hR : CL tbl σ ρ hb dr` from `StepIH` via `delta_issued_cl`, and takes the
    remaining premises of `es_delta_kept`. -/
theorem delta_kept_caseStep_of_ports
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hE : EnvWfT E) (D_b : TyP E m.arity [] b m.mtype) (hDb_cl : D_b.ClosedWf)
    (hρ : DispFor σ E n Γ ρ) (hu : levelIsZero (σ hb.reg.1) = false)
    (hmem : deltaRule r D_b ∈ tbl)
    (hObs : LvlEq (D_b.eps (instLevel (ls.map σ)) [])
      (D_b.eps (fun l => σ (instLevel ls l)) []))
    (hL : Goal tbl (.cl dl (deltaCanonL hres hlen hwf hb) S σ ρ))
    (hB : Goal tbl (.cl (deltaDbΓ hE Γ hres hbody hlen hwf D_b) hb S σ ρ)) :
    CaseStep Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ) := by
  intro hq ih
  have hR : CL tbl σ ρ hb dr :=
    delta_issued_cl Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ hq ih
  exact es_delta_kept tbl σ ρ hE hres hbody htr hlen hwf hb dl dr D_b hDb_cl hρ hu
    hmem hObs hL hB hR

/-- Residual-port package for `StepSuppliers.es_delta` covering both the proof-result and
    retained-result branches (**never mentioning `dr`**, since `CL tbl σ ρ hb dr` is supplied
    by `StepIH` through `Issues.delta_cl`). -/
inductive DeltaPorts (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
    {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (_htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (σ : Level → Level) (ρ : List Disp) : Type where
  | proof
      (hu : levelIsZero (σ hb.reg.1) = true)
      (leftCl : CL tbl σ ρ dl (deltaCanonL hres hlen hwf hb))
      (hbPb : PBit σ ρ hb hb.reg.2)
  | kept
      (hE : EnvWfT E)
      (D_b : TyP E m.arity [] b m.mtype)
      (hDb_cl : D_b.ClosedWf)
      (dispFor : DispFor σ E n Γ ρ)
      (hu : levelIsZero (σ hb.reg.1) = false)
      (ruleMem : deltaRule r D_b ∈ tbl)
      (obs : LvlEq (D_b.eps (instLevel (ls.map σ)) [])
        (D_b.eps (fun l => σ (instLevel ls l)) []))
      (leftCl : CL tbl σ ρ dl (deltaCanonL hres hlen hwf hb))
      (bodyCl : CL tbl σ ρ (deltaDbΓ hE Γ hres hbody hlen hwf D_b) hb)

/-- Exact `StepSuppliers.es_delta` statement closed under `DeltaPorts`:
    the binder telescope is copied verbatim from `RcicSynStepSkeleton.StepSuppliers.es_delta`,
    followed by a single `(ports : DeltaPorts ...)` binder. -/
theorem delta_caseStep_of_ports
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : DeltaPorts tbl hres hbody htr hlen hwf hb dl σ ρ) :
    CaseStep Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ) := by
  cases ports with
  | proof hu hL hpb =>
      exact delta_proof_caseStep_of_ports Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ hu hL hpb
  | kept hE D_b hDb_cl hρ hu hmem hObs hL hB =>
      exact delta_kept_caseStep_of_ports Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ
        hE D_b hDb_cl hρ hu hmem hObs hL hB

/-- Retained-result branch of `StepSuppliers.es_delta` at `S : ScopedCtx Eₐ E n₀ Γ₀` using the
    §2.1 adapted admission derivation `D_b := deltaAdmDb (enrichEnvWfT S.env) hres hbody htr`:
    - `hR : CL tbl σ ρ hb dr` is discharged from `StepIH` via `Issues.delta_cl`;
    - `hObs` is discharged from `StepIH` via `Issues.delta_obs_out` / `Issues.delta_obs_gate` +
      `obsLvlEq_eps_delta` + `deltaAdmDb_eps`;
    - `hDb_cl : D_b.ClosedWf` is discharged unconditionally via `deltaAdmDb_closedWf_of_envWfT`;
    leaving only `hag`, `hap`, `hρ`, `hmem`, `hL`, and `hB`. -/
theorem delta_kept_caseStep_of_obs_ih
    {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ hb.reg.1) = false)
    (hag : AgreeOn E Aw (enrichEnvWfT S.env).admW)
    (hap : ((enrichEnvWfT S.env).defAdm hres hbody htr).hv.AssumpPref)
    (hρ : DispFor σ E n Γ ρ)
    (hmem : deltaRule r (deltaAdmDb (enrichEnvWfT S.env) hres hbody htr) ∈ tbl)
    (hL : Goal tbl (.cl dl (deltaCanonL hres hlen hwf hb) S σ ρ))
    (hB : Goal tbl
      (.cl (deltaDbΓ S.env Γ hres hbody hlen hwf
        (deltaAdmDb (enrichEnvWfT S.env) hres hbody htr)) hb S σ ρ)) :
    CaseStep Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ) := by
  intro hq ih
  have hR : CL tbl σ ρ hb dr :=
    delta_issued_cl Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ hq ih
  have hObs :
      LvlEq ((deltaAdmDb (enrichEnvWfT S.env) hres hbody htr).eps (instLevel (ls.map σ)) [])
        ((deltaAdmDb (enrichEnvWfT S.env) hres hbody htr).eps (fun l => σ (instLevel ls l)) []) :=
    deltaAdmDb_issued_obs_exchange Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ hq ih hag hap
  exact es_delta_kept tbl σ ρ S.env hres hbody htr hlen hwf hb dl dr
    (deltaAdmDb (enrichEnvWfT S.env) hres hbody htr)
    (deltaAdmDb_closedWf_of_envWfT S.env hres hbody htr)
    hρ hu hmem hObs hL hB hR

/-- Residual-port structure for the retained-result branch of `StepSuppliers.es_delta` using the
    §2.1 adapted admission derivation `deltaAdmDb`: **never mentions `dr`, `hObs`, or `hDb_cl`**,
    since `hR` (`Issues.delta_cl`) and `hObs` (`Issues.delta_obs_out`/`Issues.delta_obs_gate`) are
    discharged from `StepIH`, and `hDb_cl` is proved by `deltaAdmDb_closedWf_of_envWfT`. -/
structure DeltaAdmObsPorts (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) : Prop where
  envEq : E₀ = E
  hu : levelIsZero (σ hb.reg.1) = false
  agreeOn : AgreeOn E Aw (enrichEnvWfT (envEq ▸ S.env)).admW
  admAp : ((enrichEnvWfT (envEq ▸ S.env)).defAdm hres hbody htr).hv.AssumpPref
  dispFor : DispFor σ E n Γ ρ
  ruleMem : deltaRule r (deltaAdmDb (enrichEnvWfT (envEq ▸ S.env)) hres hbody htr) ∈ tbl
  leftCl : CL tbl σ ρ dl (deltaCanonL hres hlen hwf hb)
  bodyCl : CL tbl σ ρ
    (deltaDbΓ (envEq ▸ S.env) Γ hres hbody hlen hwf
      (deltaAdmDb (enrichEnvWfT (envEq ▸ S.env)) hres hbody htr)) hb

/-- Exact `StepSuppliers.es_delta` statement closed under `DeltaAdmObsPorts`:
    the binder telescope is copied verbatim from `RcicSynStepSkeleton.StepSuppliers.es_delta`,
    followed by a single `(ports : DeltaAdmObsPorts ...)` binder. -/
theorem delta_kept_caseStep_of_admObsPorts
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
    CaseStep Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ) := by
  rcases ports with ⟨rfl, hu, hag, hap, hρ, hmem, hL, hB⟩
  exact delta_kept_caseStep_of_obs_ih Aw tbl hres hbody htr hlen hwf hb dl dr S σ ρ
    hu hag hap hρ hmem hL hB

/-- Specialization of `delta_kept_caseStep_of_obs_ih` to `tbl := tableOf S.env` and canonical
    display `S.can σ` on `S : ScopedCtx Eₐ E n Γ`: `hDb_cl`, `hρ` (from `S.canDispForHom`),
    `hmem` (from `deltaRule_mem_tableOf`), `hObs` (from `StepIH`), and `hR` (from `StepIH`) are
    all discharged automatically, leaving only `hag`, `hap`, `hL`, and `hB`. -/
theorem delta_kept_caseStep_tableOf
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level)
    (hu : levelIsZero (σ hb.reg.1) = false)
    (hag : AgreeOn E Aw (enrichEnvWfT S.env).admW)
    (hap : ((enrichEnvWfT S.env).defAdm hres hbody htr).hv.AssumpPref)
    (hL : Goal (tableOf S.env) (.cl dl (deltaCanonL hres hlen hwf hb) S σ (S.can σ)))
    (hB : Goal (tableOf S.env)
      (.cl (deltaDbΓ S.env Γ hres hbody hlen hwf
        (deltaAdmDb (enrichEnvWfT S.env) hres hbody htr)) hb S σ (S.can σ))) :
    CaseStep Aw (tableOf S.env)
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ (S.can σ)) := by
  intro hq ih
  exact delta_kept_caseStep_of_obs_ih Aw (tableOf S.env) hres hbody htr hlen hwf hb dl dr
    S σ (S.can σ) hu hag hap (S.canDispForHom hq.hom).1 (deltaRule_mem_tableOf S.env hres hbody htr)
    hL hB hq ih

/-! ### §1.3 Kernel-checked occurrence controls for `CvP.delta` -/

/-- Extract the `(hb, dr)` payload pair of a `.es (CvP.delta ...)` query as `DNode`s (`none` on
    every other query constructor or `CvP` constructor). -/
def deltaClNodes (q : P2Query Eₐ) : Option (DNode × DNode) := by
  cases q with
  | es h _ _ _ =>
      cases h with
      | delta _ _ _ _ _ _ _ _ _ _ _ _ hb _ dr => exact some (.ty hb, .ty dr)
      | _ => exact none
  | _ => exact none

/-- Extract the `(D₁, D₂)` payload pair of a `.cl D₁ D₂ ...` query as `DNode`s (`none` on
    every other query constructor). -/
def clPairNodes : P2Query Eₐ → Option (DNode × DNode)
  | .cl D₁ D₂ _ _ _ => some (.ty D₁, .ty D₂)
  | _ => none

/-- Extract the `(D, DT)` payload pair of a `.pb D DT ...` query as `DNode`s (`none` on
    every other query constructor). -/
def pbPairNodes : P2Query Eₐ → Option (DNode × DNode)
  | .pb D DT _ _ _ => some (.ty D, .ty DT)
  | _ => none

/-- Kernel-checked issuance control for `CvP.delta`: every `.cl` query issued by
    `.es (CvP.delta ...)` is either `delta_cl` (`(D₁, D₂) = (hb, dr)` as `DNode`s) or `occ_cl`
    (both endpoints occur at `subAt` payload paths of the parent). -/
theorem delta_issued_cl_variants
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true}
    {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
    {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e' T₁' T₂' : Expr Nat}
    {D₁ : TyP E' n' Γ' e' T₁'} {D₂ : TyP E' n' Γ' e' T₂'}
    {E₀' : ResolvedEnv} {n₀' : Nat} {Γ₀' : LCtx}
    {S' : ScopedCtx Eₐ E₀' n₀' Γ₀'} {σ' : Level → Level} {ρ' : List Disp}
    {q q' : P2Query Eₐ}
    (hi : Issues q q')
    (hq : q = .es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ)
    (hq' : q' = .cl D₁ D₂ S' σ' ρ') :
    (DNode.ty D₁ = DNode.ty hb ∧ DNode.ty D₂ = DNode.ty dr) ∨
      (∃ (k₁ k₂ : Nat) (p₁ p₂ : List Nat),
        q.subAt k₁ p₁ = some (.ty D₁) ∧ q.subAt k₂ p₂ = some (.ty D₂)) := by
  cases hi with
  | delta_cl =>
      have hd := congrArg deltaClNodes hq
      have hc := congrArg clPairNodes hq'
      have heq := Option.some.inj (hc.symm.trans hd)
      exact Or.inl ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
  | occ_cl h₁ h₂ _ _ =>
      have hc := Option.some.inj (congrArg clPairNodes hq')
      have e1 : DNode.ty _ = DNode.ty D₁ := congrArg Prod.fst hc
      have e2 : DNode.ty _ = DNode.ty D₂ := congrArg Prod.snd hc
      exact Or.inr ⟨_, _, _, _, e1 ▸ h₁, e2 ▸ h₂⟩
  | _ =>
      first
      | solve | cases congrArg clPairNodes hq'
      | solve | cases congrArg deltaClNodes hq

/-- Kernel-checked issuance control for `CvP.delta` `.pb` children: `CvP.delta` has no dedicated
    `.pb` row, so every `.pb` child it issues is an `occ_pb` occurrence pair. -/
theorem delta_issued_pb_is_occurrence
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true}
    {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
    {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e' T' : Expr Nat} {s' : Level}
    {D : TyP E' n' Γ' e' T'} {DT : TyP E' n' Γ' T' (.sort s')}
    {E₀' : ResolvedEnv} {n₀' : Nat} {Γ₀' : LCtx}
    {S' : ScopedCtx Eₐ E₀' n₀' Γ₀'} {σ' : Level → Level} {ρ' : List Disp}
    {q q' : P2Query Eₐ}
    (hi : Issues q q')
    (hq : q = .es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ)
    (hq' : q' = .pb D DT S' σ' ρ') :
    ∃ (k₁ k₂ : Nat) (p₁ p₂ : List Nat),
      q.subAt k₁ p₁ = some (.ty D) ∧ q.subAt k₂ p₂ = some (.ty DT) := by
  cases hi with
  | occ_pb h₁ h₂ _ _ =>
      have hc := Option.some.inj (congrArg pbPairNodes hq')
      have e1 : DNode.ty _ = DNode.ty D := congrArg Prod.fst hc
      have e2 : DNode.ty _ = DNode.ty DT := congrArg Prod.snd hc
      exact ⟨_, _, _, _, e1 ▸ h₁, e2 ▸ h₂⟩
  | _ =>
      first
      | solve | cases congrArg pbPairNodes hq'
      | solve | cases congrArg esParentTagDeltaIota hq

/-! ## §2 `StepSuppliers.delta_obs` and `AdmObsPlan.discharge` -/

/-- Test whether a `P2Query` is an `.es (CvP.delta ...)` query. -/
def isDeltaQuery (q : P2Query Eₐ) : Bool := by
  cases q with
  | es h _ _ _ =>
      cases h with
      | delta => exact true
      | _ => exact false
  | _ => exact false

/-- Every `Issues issuer (.observation ...)` edge comes from a `.es (CvP.delta ...)` issuer
    (`Issues.delta_obs_out` or `Issues.delta_obs_gate`) at empty observation display `ρ = []`. -/
theorem observation_issued_only_by_delta
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} {D : TyP E n Γ e T} {θ φ ψ : Level → Level} {pos : ObsPos}
    {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    {issuer : P2Query Eₐ}
    (hi : Issues issuer (.observation D θ φ ψ pos S σ ρ)) :
    isDeltaQuery issuer = true ∧ ρ = [] := by
  cases hi with
  | delta_obs_out _ _ => exact ⟨rfl, rfl⟩
  | delta_obs_gate _ _ => exact ⟨rfl, rfl⟩

/-- No named `Issues` row has an `.observation` query as its issuer: only the six generic
    `occ_*` occurrence rows apply, so every issued child has tag `.es`, `.cl`, `.eut`, `.pb`,
    `.bitCoh`, or `.head` (in particular `q'.tag ≠ .observation`, `STEP_SUPPLIERS.md` §1″:
    class (c) semantic producer). -/
theorem observation_issues_nothing
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T) (θ φ ψ : Level → Level) (pos : ObsPos)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    {q' : P2Query Eₐ}
    (hi : Issues (.observation D θ φ ψ pos S σ ρ) q') :
    q'.tag ≠ .observation ∧
      (q'.tag = .es ∨ q'.tag = .cl ∨ q'.tag = .eut ∨
        q'.tag = .pb ∨ q'.tag = .bitCoh ∨ q'.tag = .head) := by
  cases hi with
  | occ_es _ _ => exact ⟨fun h => P2Tag.noConfusion h, Or.inl rfl⟩
  | occ_cl _ _ _ _ => exact ⟨fun h => P2Tag.noConfusion h, Or.inr (Or.inl rfl)⟩
  | occ_eut _ _ _ _ => exact ⟨fun h => P2Tag.noConfusion h, Or.inr (Or.inr (Or.inl rfl))⟩
  | occ_pb _ _ _ _ => exact ⟨fun h => P2Tag.noConfusion h, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  | occ_bitCoh _ _ _ _ =>
      exact ⟨fun h => P2Tag.noConfusion h, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  | occ_head _ _ _ =>
      exact ⟨fun h => P2Tag.noConfusion h, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩

/-- `σ`-independent S7 §3 route for a single level observation at `pos` under `ls`:
    unlike `ObsCert σ ls l`, this route asks for **neither** `LevelHom σ` **nor** the `ψ`-side
    transport `eqN (σ (instLevel ls l)) (σ (instLevel ls l₀))` of `eqNRep`, because both are
    supplied inside `delta_obs_caseStep_of_ports` from `hq.hom : LevelHom σ` (via
    `eqN_instLevel_obs` and `LevelHom.eqN_map`, `BELOWC_OBSERVATION_REQUESTS.md` §4). -/
inductive DeltaObsRoute (ls : List Level) : ObsPos → Level → Type where
  /-- S7 §3 row 1: `l` is bounded below `ls.length`. -/
  | bounded {pos : ObsPos} {l : Level} :
      levelBounded ls.length l = true → DeltaObsRoute ls pos l
  /-- S7 §3 row 2 (`BELOWC_OBSERVATION_REQUESTS.md` §4): `l` is `eqN` to a bounded
      representative `l₀`; `hq.hom.eqN_map (eqN_instLevel_obs hl ls)` supplies the `ψ`-side
      transport. -/
  | eqNRep {pos : ObsPos} {l : Level} (l₀ : Level) :
      eqN l l₀ → levelBounded ls.length l₀ = true → DeltaObsRoute ls pos l
  /-- S7 §3 row 3: successor gate (`.succ l₀`) at a gate position. -/
  | succGate {k : Nat} (l₀ : Level) :
      DeltaObsRoute ls (.gate k) (.succ l₀)
  /-- S7 §3 row 3′: parameter-free `UniformType` gate. -/
  | uniformType {k : Nat} {l : Level} :
      levelBounded 0 l = true → UniformType l → DeltaObsRoute ls (.gate k) l
  /-- S7 §3 row 4: parameter-free `UniformProp` gate. -/
  | uniformProp {k : Nat} {l : Level} :
      levelBounded 0 l = true → UniformProp l → DeltaObsRoute ls (.gate k) l

/-- Combine a `σ`-independent `DeltaObsRoute ls pos l` with `hσ : LevelHom σ` (from `Demand.hom`)
    to build a supplying `ObsCert σ ls l`. -/
def DeltaObsRoute.toCert {σ : Level → Level} {ls : List Level} {pos : ObsPos} {l : Level}
    (hσ : LevelHom σ) : DeltaObsRoute ls pos l → ObsCert σ ls l
  | .bounded hb => .bounded hb hσ
  | .eqNRep l₀ hl hb =>
      .eqNRep l₀ hl hb (hσ.eqN_map (eqN_instLevel_obs hl ls)) hσ
  | .succGate l₀ => .succGate l₀ hσ
  | .uniformType hb hUT => .uniformType hb hUT hσ
  | .uniformProp hb hUP => .uniformProp hb hUP hσ

theorem DeltaObsRoute.supplyOut_isSome {σ : Level → Level} {ls : List Level} {k : Nat} {l : Level}
    (hσ : LevelHom σ) (r : DeltaObsRoute ls (.out k) l) :
    (r.toCert hσ).supplyOut.isSome = true := by
  cases r <;> rfl

theorem DeltaObsRoute.supplyGate_isSome {σ : Level → Level} {ls : List Level} {k : Nat} {l : Level}
    (hσ : LevelHom σ) (r : DeltaObsRoute ls (.gate k) l) :
    (r.toCert hσ).supplyGate.isSome = true := by
  cases r <;> rfl

/-- `σ`-independent residual-port package for `StepSuppliers.delta_obs` at position `pos`. -/
def DeltaObsPorts
    {E : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E n₀ Γ₀)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (ls : List Level) : ObsPos → Prop
  | .out k =>
      ∀ l, (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.outLevels id)[k]? = some l →
        Nonempty (DeltaObsRoute ls (.out k) l)
  | .gate k =>
      ∀ l, (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.gateLevels id)[k]? = some l →
        Nonempty (DeltaObsRoute ls (.gate k) l)

/-- Exact `StepSuppliers.delta_obs` statement closed under `DeltaObsPorts`:
    the binder telescope is copied verbatim from `RcicSynStepSkeleton.StepSuppliers.delta_obs`,
    followed by a single `(ports : DeltaObsPorts ...)` binder. Uses `hq.hom : LevelHom σ` from
    `Demand` to instantiate `DeltaObsRoute.toCert`. -/
theorem delta_obs_caseStep_of_ports
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
      (instLevel (ls.map σ)) (fun l => σ (instLevel ls l)) pos S σ []) := by
  intro hq _ih
  have hσ : LevelHom σ := hq.hom
  cases pos with
  | out k =>
      intro l hk
      rcases ports l hk with ⟨route⟩
      rcases Option.isSome_iff_exists.mp (route.supplyOut_isSome hσ) with ⟨p, -⟩
      exact p.down
  | gate k =>
      intro l hk
      rcases ports l hk with ⟨route⟩
      rcases Option.isSome_iff_exists.mp (route.supplyGate_isSome hσ) with ⟨p, -⟩
      exact p.down

/-- Exact `StepSuppliers.delta_obs` statement closed from a complete observation plan
    `p : AdmObsPlan ((enrichEnvWfT S.env).defAdm hres hbody htr) σ ls` (`hc : p.Complete`). -/
theorem delta_obs_caseStep_of_completePlan
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
      (instLevel (ls.map σ)) (fun l => σ (instLevel ls l)) pos S σ []) := by
  intro _hq _ih
  cases pos with
  | out k =>
      intro l hk
      have hmem : l ∈ p.Db.OutLevels := by
        rw [p.Db_eq]
        exact List.mem_iff_getElem?.mpr ⟨_, hk⟩
      exact p.supply_out hc hmem
  | gate k =>
      intro l hk
      have hmem : l ∈ p.Db.GateLevels := by
        rw [p.Db_eq]
        exact List.mem_iff_getElem?.mpr ⟨_, hk⟩
      exact p.supply_gate hc hmem

/-- `AdmObsPlan.discharge` transported to the §2.1 adapted admission derivation `deltaAdmDb`:
    a complete observation plan directly yields the `hObs` premise of `es_delta_kept`. -/
theorem delta_obs_exchange_of_completePlan {E : ResolvedEnv} (hE : EnvWfP E)
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) {σ : Level → Level}
    (p : AdmObsPlan (hE.defAdm hres hbody htr) σ ls) (hc : p.Complete) :
    LvlEq ((deltaAdmDb hE hres hbody htr).eps (instLevel (ls.map σ)) [])
      ((deltaAdmDb hE hres hbody htr).eps (fun l => σ (instLevel ls l)) []) := by
  rw [deltaAdmDb_eps, deltaAdmDb_eps, ← p.Db_eq]
  exact p.discharge hc

/-- Per-position `StepSuppliers.delta_obs` closure at `pos = .out k` from a single supplying
    certificate `c : ObsCert σ ls l`. -/
theorem delta_obs_caseStep_out_of_cert
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true}
    {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
    {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    (_hδ : Demand (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (k : Nat)
    (hcert : ∀ l, (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.outLevels id)[k]? = some l →
      ∃ c : ObsCert σ ls l, c.supplyOut.isSome = true) :
    CaseStep Aw tbl (.observation ((enrichEnvWfT S.env).defAdm hres hbody htr).hv id
      (instLevel (ls.map σ)) (fun l => σ (instLevel ls l)) (.out k) S σ []) := by
  intro _hq _ih l hk
  rcases hcert l hk with ⟨c, hc⟩
  rcases Option.isSome_iff_exists.mp hc with ⟨p, -⟩
  exact p.down

/-- Per-position `StepSuppliers.delta_obs` closure at `pos = .gate k` from a single supplying
    certificate `c : ObsCert σ ls l`. -/
theorem delta_obs_caseStep_gate_of_cert
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true}
    {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
    {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    (_hδ : Demand (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (k : Nat)
    (hcert : ∀ l, (((enrichEnvWfT S.env).defAdm hres hbody htr).hv.gateLevels id)[k]? = some l →
      ∃ c : ObsCert σ ls l, c.supplyGate.isSome = true) :
    CaseStep Aw tbl (.observation ((enrichEnvWfT S.env).defAdm hres hbody htr).hv id
      (instLevel (ls.map σ)) (fun l => σ (instLevel ls l)) (.gate k) S σ []) := by
  intro _hq _ih l hk
  rcases hcert l hk with ⟨c, hc⟩
  rcases Option.isSome_iff_exists.mp hc with ⟨p, -⟩
  exact p.down

/-! ## §3 `StepSuppliers.es_iota_retained`: issued ports, `CaseStep` closures, and Nat/List/Vec instances -/

/-- `Issues.iota_pbL` is unconditionally answered by `StepIH` whenever `.es (CvP.iota ...)`
    is demanded: yields `PBit σ ρ dl hlhs.reg.2`. -/
theorem iota_issued_pbL
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ)) :
    PBit σ ρ dl hlhs.reg.2 :=
  ih_local Aw tbl hq ih (.pb dl hlhs.reg.2 S σ ρ) Issues.iota_pbL rfl
    (lexDM_combMeas_mono Aw _ (iota_qL_below Aw w hlhs hrhs dl dr))

/-- `Issues.iota_pbR` is unconditionally answered by `StepIH` whenever `.es (CvP.iota ...)`
    is demanded: yields `PBit σ ρ dr hlhs.reg.2`. -/
theorem iota_issued_pbR
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ)) :
    PBit σ ρ dr hlhs.reg.2 :=
  ih_local Aw tbl hq ih (.pb dr hlhs.reg.2 S σ ρ) Issues.iota_pbR rfl
    (lexDM_combMeas_mono Aw _ (iota_qR_below Aw w hlhs hrhs dl dr))

/-- Same-site occurrence `Issues.occ_cl` at payload paths `(0, [2])` (`dl`) and `(0, [0])` (`hlhs`)
    is unconditionally answered by `StepIH` whenever `.es (CvP.iota ...)` is demanded: yields
    `CL tbl σ ρ dl hlhs` (`qCLL` in `RcicSynP2Iota.iota_erasure_from_answers`). -/
theorem iota_issued_cl_left
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ)) :
    CL tbl σ ρ dl hlhs :=
  ih_local Aw tbl hq ih (.cl dl hlhs S σ ρ)
    (Issues.occ_cl (k₁ := 0) (k₂ := 0) (p₁ := [2]) (p₂ := [0]) rfl rfl hq.ap.2.2.1 hq.ap.1)
    rfl
    (lexDM_combMeas_mono Aw _ (lex_of_dm (below_iota Aw w hlhs hrhs dl dr).2.2.2.2.1))

/-- Same-site occurrence `Issues.occ_cl` at payload paths `(0, [1])` (`hrhs`) and `(0, [3])` (`dr`)
    is unconditionally answered by `StepIH` whenever `.es (CvP.iota ...)` is demanded: yields
    `CL tbl σ ρ hrhs dr` (`qCLR` in `RcicSynP2Iota.iota_erasure_from_answers`). -/
theorem iota_issued_cl_right
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ)) :
    CL tbl σ ρ hrhs dr :=
  ih_local Aw tbl hq ih (.cl hrhs dr S σ ρ)
    (Issues.occ_cl (k₁ := 0) (k₂ := 0) (p₁ := [1]) (p₂ := [3]) rfl rfl hq.ap.2.1 hq.ap.2.2.2)
    rfl
    (lexDM_combMeas_mono Aw _ (lex_of_dm (below_iota Aw w hlhs hrhs dl dr).2.2.2.2.2))

/-- Whenever `hlhs.reg.2` sits at a `P2Query.subAt` occurrence path `pReg` of the `CvP.iota` query,
    `StepIH` answers `qPL : PBit σ ρ hlhs hlhs.reg.2` via `Issues.occ_pb` at `(0, [0])` and
    `(0, pReg)`. -/
theorem iota_issued_pb_hlhs_of_reg_occ
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pReg : List Nat)
    (hocc : (P2Query.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ).subAt
      0 pReg = some (.ty hlhs.reg.2))
    (hq : Demand (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ)) :
    PBit σ ρ hlhs hlhs.reg.2 := by
  let hnode := CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr
  have hwlhs : hlhs.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwreg : hlhs.reg.2.wt Aw < hnode.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hlhs) hwlhs
  exact ih_local Aw tbl hq ih (.pb hlhs hlhs.reg.2 S σ ρ)
    (Issues.occ_pb (k₁ := 0) (k₂ := 0) (p₁ := [0]) (p₂ := pReg)
      rfl hocc hq.ap.1 (assumpPref_reg hq.ap.1))
    rfl
    (lexDM_combMeas_mono Aw _ (lex_of_dm (dmStep_pair_below Aw hnode rfl hlhs hlhs.reg.2 hwlhs hwreg)))

/-- Whenever `hlhs.reg.2` sits at a `P2Query.subAt` occurrence path `pReg` of the `CvP.iota` query,
    `StepIH` answers `qPR : PBit σ ρ hrhs hlhs.reg.2` via `Issues.occ_pb` at `(0, [1])` and
    `(0, pReg)`. -/
theorem iota_issued_pb_hrhs_of_reg_occ
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pReg : List Nat)
    (hocc : (P2Query.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ).subAt
      0 pReg = some (.ty hlhs.reg.2))
    (hq : Demand (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ)) :
    PBit σ ρ hrhs hlhs.reg.2 := by
  let hnode := CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr
  have hwlhs : hlhs.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwrhs : hrhs.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwreg : hlhs.reg.2.wt Aw < hnode.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hlhs) hwlhs
  exact ih_local Aw tbl hq ih (.pb hrhs hlhs.reg.2 S σ ρ)
    (Issues.occ_pb (k₁ := 0) (k₂ := 0) (p₁ := [1]) (p₂ := pReg)
      rfl hocc hq.ap.2.1 (assumpPref_reg hq.ap.1))
    rfl
    (lexDM_combMeas_mono Aw _ (lex_of_dm (dmStep_pair_below Aw hnode rfl hrhs hlhs.reg.2 hwrhs hwreg)))

/-- Conditional `CaseStep` closure for `StepSuppliers.es_iota_retained` (exact binder telescope):
    discharges `qCLL : CL tbl σ ρ dl hlhs` and `qCLR : CL tbl σ ρ hrhs dr` from `StepIH` via
    `iota_issued_cl_left` and `iota_issued_cl_right`, and finishes via
    `RcicSynP2Iota.iota_erasure_from_answers` from the remaining simulation data. -/
theorem iota_retained_caseStep_of_simulation
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (_hrel : levelIsZero (σ hlhs.reg.1) = false)
    (qPL : Goal tbl (.pb hlhs hlhs.reg.2 S σ ρ))
    (qPR : Goal tbl (.pb hrhs hlhs.reg.2 S σ ρ))
    {el erhs er : ETm}
    (hmatchL : ConvMod (EStep tbl) LvlEq (hlhs.eps σ ρ) el)
    (hcroot : CRoot tbl el erhs)
    (hbeta : RStar (RStep tbl) erhs er)
    (hmatchR : ConvMod (EStep tbl) LvlEq er (hrhs.eps σ ρ)) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ) := by
  intro hq ih
  have qCLL : CL tbl σ ρ dl hlhs :=
    iota_issued_cl_left Aw tbl w hlhs hrhs dl dr S σ ρ hq ih
  have qCLR : CL tbl σ ρ hrhs dr :=
    iota_issued_cl_right Aw tbl w hlhs hrhs dl dr S σ ρ hq ih
  exact iota_erasure_from_answers w hlhs hrhs dl dr qCLL qCLR qPL qPR
    hmatchL hcroot hbeta hmatchR

/-- Residual-port structure for `StepSuppliers.es_iota_retained` (**never mentioning `dl`, `dr`,
    `qCLL`, or `qCLR`**, since `qCLL` and `qCLR` are supplied by `StepIH` via `Issues.occ_cl`). -/
structure IotaRetainedPorts (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (σ : Level → Level) (ρ : List Disp) : Type where
  qPL : PBit σ ρ hlhs hlhs.reg.2
  qPR : PBit σ ρ hrhs hlhs.reg.2
  el : ETm
  erhs : ETm
  er : ETm
  matchL : ConvMod (EStep tbl) LvlEq (hlhs.eps σ ρ) el
  croot : CRoot tbl el erhs
  beta : RStar (RStep tbl) erhs er
  matchR : ConvMod (EStep tbl) LvlEq er (hrhs.eps σ ρ)

/-- Exact `StepSuppliers.es_iota_retained` statement closed under `IotaRetainedPorts`:
    the binder telescope is copied verbatim from `RcicSynStepSkeleton.StepSuppliers.es_iota_retained`,
    followed by a single `(ports : IotaRetainedPorts ...)` binder. -/
theorem iota_retained_caseStep_of_ports
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (ports : IotaRetainedPorts tbl hlhs hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ) :=
  iota_retained_caseStep_of_simulation Aw tbl w hlhs hrhs dl dr S σ ρ hrel
    ports.qPL ports.qPR ports.matchL ports.croot ports.beta ports.matchR

/-- Pure S16 §4.5 simulation receipt for retained-result ι (**no outer query answers at all**:
    neither `qCLL`, `qCLR`, `qPL`, nor `qPR`). -/
structure IotaRetainedSimulation (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (σ : Level → Level) (ρ : List Disp) : Type where
  el : ETm
  erhs : ETm
  er : ETm
  matchL : ConvMod (EStep tbl) LvlEq (hlhs.eps σ ρ) el
  croot : CRoot tbl el erhs
  beta : RStar (RStep tbl) erhs er
  matchR : ConvMod (EStep tbl) LvlEq er (hrhs.eps σ ρ)

/-- Residual-port structure when `hlhs.reg.2` sits at a `P2Query.subAt` occurrence path `pReg`
    (e.g., `[0, 2]` whenever `hlhs` is a `TyP.app` node): **all four** outer queries `qCLL`,
    `qCLR`, `qPL`, `qPR` of `iota_erasure_from_answers` are discharged from `StepIH` inside
    `iota_retained_caseStep_of_reg_occ_ports`. -/
structure IotaRetainedRegOccPorts (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) : Type where
  pReg : List Nat
  regOcc : (P2Query.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ).subAt
    0 pReg = some (.ty hlhs.reg.2)
  sim : IotaRetainedSimulation tbl hlhs hrhs σ ρ

/-- Exact `StepSuppliers.es_iota_retained` statement closed under `IotaRetainedRegOccPorts`:
    **all four** outer queries `qCLL`, `qCLR`, `qPL`, `qPR` are discharged from `StepIH`
    (`Issues.occ_cl` + `Issues.occ_pb`). -/
theorem iota_retained_caseStep_of_reg_occ_ports
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (ports : IotaRetainedRegOccPorts tbl w hlhs hrhs dl dr S σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ) := by
  intro hq ih
  have qPL : PBit σ ρ hlhs hlhs.reg.2 :=
    iota_issued_pb_hlhs_of_reg_occ Aw tbl w hlhs hrhs dl dr S σ ρ ports.pReg ports.regOcc hq ih
  have qPR : PBit σ ρ hrhs hlhs.reg.2 :=
    iota_issued_pb_hrhs_of_reg_occ Aw tbl w hlhs hrhs dl dr S σ ρ ports.pReg ports.regOcc hq ih
  exact iota_retained_caseStep_of_simulation Aw tbl w hlhs hrhs dl dr S σ ρ hrel
    qPL qPR ports.sim.matchL ports.sim.croot ports.sim.beta ports.sim.matchR hq ih

/-- When the outer endpoints coincide with the premise typings (`dl = hlhs` and `dr = hrhs`, as in
    every `enrichConvT` ι node and in the landed Nat/List instances), **all four** outer query
    answers `qPL`, `qPR`, `qCLL`, `qCLR` of `RcicSynP2Iota.iota_erasure_from_answers` are
    discharged directly from `StepIH` (`iota_issued_pbL`, `iota_issued_pbR`,
    `iota_issued_cl_left`, `iota_issued_cl_right`), leaving only the simulation witnesses
    (`hmatchL`, `hcroot`, `hbeta`, `hmatchR`). -/
theorem iota_retained_caseStep_same_endpoints
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (hdl : dl = hlhs) (hdr : dr = hrhs)
    {el erhs er : ETm}
    (hmatchL : ConvMod (EStep tbl) LvlEq (hlhs.eps σ ρ) el)
    (hcroot : CRoot tbl el erhs)
    (hbeta : RStar (RStep tbl) erhs er)
    (hmatchR : ConvMod (EStep tbl) LvlEq er (hrhs.eps σ ρ)) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ) := by
  intro hq ih
  have qPL : Goal tbl (.pb hlhs hlhs.reg.2 S σ ρ) :=
    hdl ▸ iota_issued_pbL Aw tbl w hlhs hrhs dl dr S σ ρ hq ih
  have qPR : Goal tbl (.pb hrhs hlhs.reg.2 S σ ρ) :=
    hdr ▸ iota_issued_pbR Aw tbl w hlhs hrhs dl dr S σ ρ hq ih
  exact iota_retained_caseStep_of_simulation Aw tbl w hlhs hrhs dl dr S σ ρ hrel
    qPL qPR hmatchL hcroot hbeta hmatchR hq ih

/-! ### §3.1 Kernel-checked occurrence controls for `CvP.iota` and `.slot` -/

/-- Extract the `((dl, hlhs.reg.2), (dr, hlhs.reg.2))` `.pb` pairs of a `.es (CvP.iota ...)`
    query as `DNode`s (`none` on every other query constructor or `CvP` constructor). -/
def iotaPbNodes (q : P2Query Eₐ) : Option ((DNode × DNode) × (DNode × DNode)) := by
  cases q with
  | es h _ _ _ =>
      cases h with
      | iota _ _ _ _ _ _ _ hlhs _ dl dr =>
          exact some ((.ty dl, .ty hlhs.reg.2), (.ty dr, .ty hlhs.reg.2))
      | _ => exact none
  | _ => exact none

/-- Kernel-checked issuance control for `CvP.iota` `.cl` children: `CvP.iota` has no dedicated
    `.cl` row, so every `.cl` child it issues is an `occ_cl` occurrence pair. -/
theorem iota_issued_cl_is_occurrence
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    {w : DerivedIota E lhs rhs} {hlhs : TyP E n Γ lhs T} {hrhs : TyP E n Γ rhs T}
    {dl : TyP E n Γ lhs T} {dr : TyP E n Γ rhs T}
    {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e' T₁' T₂' : Expr Nat}
    {D₁ : TyP E' n' Γ' e' T₁'} {D₂ : TyP E' n' Γ' e' T₂'}
    {E₀' : ResolvedEnv} {n₀' : Nat} {Γ₀' : LCtx}
    {S' : ScopedCtx Eₐ E₀' n₀' Γ₀'} {σ' : Level → Level} {ρ' : List Disp}
    {q q' : P2Query Eₐ}
    (hi : Issues q q')
    (hq : q = .es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ)
    (hq' : q' = .cl D₁ D₂ S' σ' ρ') :
    ∃ (k₁ k₂ : Nat) (p₁ p₂ : List Nat),
      q.subAt k₁ p₁ = some (.ty D₁) ∧ q.subAt k₂ p₂ = some (.ty D₂) := by
  cases hi with
  | occ_cl h₁ h₂ _ _ =>
      have hc := Option.some.inj (congrArg clPairNodes hq')
      have e1 : DNode.ty _ = DNode.ty D₁ := congrArg Prod.fst hc
      have e2 : DNode.ty _ = DNode.ty D₂ := congrArg Prod.snd hc
      exact ⟨_, _, _, _, e1 ▸ h₁, e2 ▸ h₂⟩
  | _ =>
      first
      | solve | cases congrArg clPairNodes hq'
      | solve | cases congrArg esParentTagDeltaIota hq

/-- Kernel-checked issuance control for `CvP.iota` `.pb` children: every `.pb` query issued by
    `.es (CvP.iota ...)` is `iota_pbL` (`(dl, hlhs.reg.2)`), `iota_pbR` (`(dr, hlhs.reg.2)`),
    or an `occ_pb` occurrence pair. -/
theorem iota_issued_pb_variants
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    {w : DerivedIota E lhs rhs} {hlhs : TyP E n Γ lhs T} {hrhs : TyP E n Γ rhs T}
    {dl : TyP E n Γ lhs T} {dr : TyP E n Γ rhs T}
    {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e' T' : Expr Nat} {s' : Level}
    {D : TyP E' n' Γ' e' T'} {DT : TyP E' n' Γ' T' (.sort s')}
    {E₀' : ResolvedEnv} {n₀' : Nat} {Γ₀' : LCtx}
    {S' : ScopedCtx Eₐ E₀' n₀' Γ₀'} {σ' : Level → Level} {ρ' : List Disp}
    {q q' : P2Query Eₐ}
    (hi : Issues q q')
    (hq : q = .es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ)
    (hq' : q' = .pb D DT S' σ' ρ') :
    (DNode.ty D = DNode.ty dl ∧ DNode.ty DT = DNode.ty hlhs.reg.2) ∨
      (DNode.ty D = DNode.ty dr ∧ DNode.ty DT = DNode.ty hlhs.reg.2) ∨
      (∃ (k₁ k₂ : Nat) (p₁ p₂ : List Nat),
        q.subAt k₁ p₁ = some (.ty D) ∧ q.subAt k₂ p₂ = some (.ty DT)) := by
  cases hi with
  | iota_pbL =>
      have hiota := Option.some.inj (congrArg iotaPbNodes hq)
      have hpb := Option.some.inj (congrArg pbPairNodes hq')
      have heq := hpb.symm.trans (congrArg Prod.fst hiota)
      exact Or.inl ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
  | iota_pbR =>
      have hiota := Option.some.inj (congrArg iotaPbNodes hq)
      have hpb := Option.some.inj (congrArg pbPairNodes hq')
      have heq := hpb.symm.trans (congrArg Prod.snd hiota)
      exact Or.inr (Or.inl ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩)
  | occ_pb h₁ h₂ _ _ =>
      have hc := Option.some.inj (congrArg pbPairNodes hq')
      have e1 : DNode.ty _ = DNode.ty D := congrArg Prod.fst hc
      have e2 : DNode.ty _ = DNode.ty DT := congrArg Prod.snd hc
      exact Or.inr (Or.inr ⟨_, _, _, _, e1 ▸ h₁, e2 ▸ h₂⟩)
  | _ =>
      first
      | solve | cases congrArg pbPairNodes hq'
      | solve | cases congrArg iotaPbNodes hq

/-- No `Issues` row targets a `.slot` query (`W-IOTA-SLOT-KIND-SOURCE`). -/
theorem slot_not_issued
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {m : CheckedMember} {T : Expr Nat}
    (u uD : Level) (hres : E.members r = some m) (dSlot : TyP E n Γ T (.sort u))
    (ls : List Level) (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (issuer : P2Query Eₐ) :
    ¬ Issues issuer (.slot u uD hres dSlot ls S σ ρ) := by
  intro hi
  cases hi

/-! ### §3.2 Concrete Nat / `#7451` hit-bvar `esub` / List / Vec instances & §7.4 slot enumeration -/

/-- Concrete retained-ι `CaseStep` closure on the landed `Nat.succ` recursor instance
    (`RcicSynNatSuccIota.H` / `natSuccTable`): all four query answers are supplied by `StepIH`,
    and the `CRoot` (`natSucc_croot`) and 4-step RHS β* chain (`s17_beta_witness`) are supplied
    by the landed `RcicSynNatSuccIota` / `RcicSynP2Iota` lemmas. -/
theorem natSucc_iota_retained_caseStep
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) :
    CaseStep Aw natSuccTable (.es H S id []) :=
  iota_retained_caseStep_same_endpoints Aw natSuccTable (DerivedIota.of wSuccU1) hL hR hL hR
    S id [] (by rw [s17_hL_reg1]; rfl) rfl rfl
    s17_matchL natSucc_croot s17_beta_witness s17_matchR

/-- The `#7451` (batch 150) hit-bvar `esub`-wrapped Nat ι site (`s16hL_esub` from
    `RcicSynIotaRoutePlan`). -/
noncomputable def natIotaSiteEsub : IotaSite natEnvU 1 [] where
  T := .const 0 []
  w := wSuccU1
  d := DerivedIota.of wSuccU1
  hlhs := s16hL_esub
  hrhs := s16hR
  dl := s16hL_esub
  dr := s16hR

/-- PIN (`#7451`): `planIota` on the hit-bvar `esub`-wrapped Nat site preserves all six §4
    slot origins (`[.spine 0, .spine 1, .spine 2, .spine 3, .majorField 0, .rhsDirectRec 1]`). -/
theorem natIotaPlan_esub_origins :
    (planIota natIotaSiteEsub).slots.map (·.origin) =
      [.spine 0, .spine 1, .spine 2, .spine 3, .majorField 0, .rhsDirectRec 1] := by
  decide

/-- Every slot request derivation emitted on the `#7451` hit-bvar `esub` site sits strictly
    below `natIotaSiteEsub.N s16AwNat`. -/
theorem nat_esub_slot_request_below (j : Nat) {qs : List RawQuery}
    (hq : request_of_iota_slot (planIota natIotaSiteEsub) j = some qs) :
    ∀ q ∈ qs, ∀ d ∈ q.derivations,
      d.wt s16AwNat < natIotaSiteEsub.N s16AwNat :=
  iota_slot_request_below s16AwNat natIotaSiteEsub j hq

/-- The `CvP.iota` conversion node built from `#7451`'s hit-bvar `esub` LHS `s16hL_esub` and
    `s16hR`. -/
noncomputable def H_esub :
    CvP natEnvU 1 [] (iotaLhsOf wSuccU1) (iotaRhsOf wSuccU1) (.const 0 []) :=
  .iota natEnvU 1 [] (iotaLhsOf wSuccU1) (iotaRhsOf wSuccU1) (.const 0 [])
    (DerivedIota.of wSuccU1) s16hL_esub s16hR s16hL_esub s16hR

/-- `s16hL_esub.eps id []` reduces to `EL` (`ETm.inst 0 (s16hL.eps id []) (.bvar 0) = EL`). -/
theorem s17_hL_esub_eps : s16hL_esub.eps id [] = EL := rfl

/-- `s16hR.eps id []` reduces to `ER` (`s16hR` and `hR` share the same erased term). -/
theorem s17_s16hR_eps : s16hR.eps id [] = ER := rfl

/-- Unconditional `CaseStep` closure on the `#7451` hit-bvar `esub`-wrapped Nat retained-ι
    instance `H_esub`: all four outer query answers are supplied by `StepIH`, and the `CRoot`
    and 4-step β* chain are supplied by `natSucc_croot` and `s17_beta_witness`. -/
theorem natSucc_esub_iota_retained_caseStep
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) :
    CaseStep Aw natSuccTable (.es H_esub S id []) :=
  iota_retained_caseStep_same_endpoints Aw natSuccTable
    (DerivedIota.of wSuccU1) s16hL_esub s16hR s16hL_esub s16hR
    S id [] rfl rfl rfl
    (s17_hL_esub_eps ▸ .refl _) natSucc_croot s17_beta_witness (s17_s16hR_eps ▸ .refl _)

/-- The seven β steps of `RcicSynListConsIota` packaged as a finite `RStar (RStep listConsTable)`
    witness for `iota_erasure_from_answers`. -/
def s18_beta_witness :
    RStar (RStep listConsTable)
      (ETm.appN (listConsRule.rhs [.succ .zero, .succ .zero] [.succ .zero])
        [Aε, Mε, mnε, mcε, Aε, hε, tε]) s18ER :=
  .step s18Step1 (.step s18Step2 (.step s18Step3 (.step s18Step4
    (.step s18Step5 (.step s18Step6 (.step s18Step7 (.refl s18ER)))))))

/-- Concrete retained-ι `CaseStep` closure on the landed `List.cons` recursor instance
    (`RcicSynListConsIota.s18H` / `listConsTable`): all four query answers are supplied by
    `StepIH`, and the `CRoot` (`listCons_croot`) and 7-step RHS β* chain (`s18_beta_witness`)
    are supplied by the landed `RcicSynListConsIota` lemmas. -/
theorem listCons_iota_retained_caseStep
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) :
    CaseStep Aw listConsTable (.es s18H S id []) :=
  iota_retained_caseStep_same_endpoints Aw listConsTable
    (DerivedIota.of wConsNat) s18hL s18hR s18hL s18hR
    S id [] rfl rfl rfl
    (s18hL_eps_el ▸ .refl _) listCons_croot s18_beta_witness (s18hR_eps_er ▸ .refl _)

/-- Expected ι slot positions enumerated from `w : IotaWitness E` before reading the spines
    (`BELOWC_DEMAND_GRAMMAR_CONTINUATION.md` §7.4): includes `ctorParam (j : Fin w.ctorParams.length)`,
    which `RcicSynIotaRoutePlan.planIota` currently omits. -/
inductive IotaExpectedSlotPos {E : ResolvedEnv} (w : IotaWitness E) : Type where
  | recArg (j : Fin w.preMajor.length)
  | major
  | ctorParam (j : Fin w.ctorParams.length)
  | ctorField (j : Fin w.fields.length)
  | rhsRecResult (j : Fin (recResultIdxs w.kinds 0).length)
  deriving DecidableEq

/-- Full §7.4 expected ι slot count for `w : IotaWitness E` (including `w.ctorParams.length`). -/
def expectedIotaSlotCount {E : ResolvedEnv} (w : IotaWitness E) : Nat :=
  w.preMajor.length + 1 + w.ctorParams.length + w.fields.length + (recResultIdxs w.kinds 0).length

/-- The difference between `expectedIotaSlotCount w` (§7.4) and `planSlotCount w`
    (`RcicSynIotaRoutePlan`) is exactly `w.ctorParams.length`. -/
theorem expectedIotaSlotCount_eq_planSlotCount_add_ctorParams {E : ResolvedEnv}
    (w : IotaWitness E) :
    expectedIotaSlotCount w = planSlotCount w + w.ctorParams.length := by
  simp only [expectedIotaSlotCount, planSlotCount]
  omega

/-- On `Nat.succ` (`wSuccU1`, 0 constructor parameters), `expectedIotaSlotCount` and
    `planSlotCount` both equal `6`. -/
theorem wSuccU1_expectedSlotCount :
    expectedIotaSlotCount wSuccU1 = 6 ∧ planSlotCount wSuccU1 = 6 := ⟨rfl, rfl⟩

/-- On `List.cons` (`wConsNat`, 1 constructor parameter `A`), `expectedIotaSlotCount` is `9`
    (`BELOWC_OBSERVATION_REQUESTS.md` §2.4: nine natural/declaration pairs including separate
    `qA` and `qACtor`), while `planSlotCount` is `8`. -/
theorem wConsNat_expectedSlotCount :
    expectedIotaSlotCount wConsNat = 9 ∧ planSlotCount wConsNat = 8 := ⟨rfl, rfl⟩

/-- On indexed `Vec.vcons` (`wVcons`, 1 constructor parameter `A` and 1 index `k`),
    `expectedIotaSlotCount` is `11` (`S19_VEC_INDEXED_ES.md` §6: eleven occurrences), while
    `planSlotCount` is `10`. -/
theorem wVcons_expectedSlotCount :
    expectedIotaSlotCount wVcons = 11 ∧ planSlotCount wVcons = 10 := ⟨rfl, rfl⟩

end Rcic.Syn

#print axioms Rcic.Syn.cvpCtorTagDeltaIota
#print axioms Rcic.Syn.esParentTagDeltaIota
#print axioms Rcic.Syn.delta_issued_cl
#print axioms Rcic.Syn.delta_issued_reg_pb
#print axioms Rcic.Syn.delta_direct_const_issued_pb
#print axioms Rcic.Syn.deltaCanonL_ap
#print axioms Rcic.Syn.delta_obs_before_of_agreeOn
#print axioms Rcic.Syn.delta_issued_obs_out_at
#print axioms Rcic.Syn.delta_issued_obs_gate_at
#print axioms Rcic.Syn.delta_issued_obs_out
#print axioms Rcic.Syn.delta_issued_obs_gate
#print axioms Rcic.Syn.delta_issued_obs_exchange
#print axioms Rcic.Syn.castArityZero
#print axioms Rcic.Syn.castArityZero_eps
#print axioms Rcic.Syn.castArityZero_outLevels
#print axioms Rcic.Syn.castArityZero_gateLevels
#print axioms Rcic.Syn.castArityZero_closedWf
#print axioms Rcic.Syn.castArityZero_deltaRule
#print axioms Rcic.Syn.deltaAdmDb
#print axioms Rcic.Syn.deltaAdmDb_eps
#print axioms Rcic.Syn.deltaAdmDb_outLevels
#print axioms Rcic.Syn.deltaAdmDb_gateLevels
#print axioms Rcic.Syn.deltaAdmDb_closedWf
#print axioms Rcic.Syn.deltaAdmDb_deltaRule
#print axioms Rcic.Syn.defAdm_closedWf
#print axioms Rcic.Syn.deltaAdmDb_closedWf_of_envWfT
#print axioms Rcic.Syn.deltaRule_mem_tableOf
#print axioms Rcic.Syn.deltaAdmDb_issued_obs_exchange
#print axioms Rcic.Syn.es_delta_direct_const_proof
#print axioms Rcic.Syn.es_delta_proof_of_reg_occ
#print axioms Rcic.Syn.delta_proof_caseStep_of_ports
#print axioms Rcic.Syn.delta_kept_caseStep_of_ports
#print axioms Rcic.Syn.DeltaPorts
#print axioms Rcic.Syn.delta_caseStep_of_ports
#print axioms Rcic.Syn.delta_kept_caseStep_of_obs_ih
#print axioms Rcic.Syn.DeltaAdmObsPorts
#print axioms Rcic.Syn.delta_kept_caseStep_of_admObsPorts
#print axioms Rcic.Syn.delta_kept_caseStep_tableOf
#print axioms Rcic.Syn.deltaClNodes
#print axioms Rcic.Syn.clPairNodes
#print axioms Rcic.Syn.pbPairNodes
#print axioms Rcic.Syn.delta_issued_cl_variants
#print axioms Rcic.Syn.delta_issued_pb_is_occurrence
#print axioms Rcic.Syn.isDeltaQuery
#print axioms Rcic.Syn.observation_issued_only_by_delta
#print axioms Rcic.Syn.observation_issues_nothing
#print axioms Rcic.Syn.DeltaObsRoute
#print axioms Rcic.Syn.DeltaObsRoute.toCert
#print axioms Rcic.Syn.DeltaObsRoute.supplyOut_isSome
#print axioms Rcic.Syn.DeltaObsRoute.supplyGate_isSome
#print axioms Rcic.Syn.DeltaObsPorts
#print axioms Rcic.Syn.delta_obs_caseStep_of_ports
#print axioms Rcic.Syn.delta_obs_caseStep_of_completePlan
#print axioms Rcic.Syn.delta_obs_exchange_of_completePlan
#print axioms Rcic.Syn.delta_obs_caseStep_out_of_cert
#print axioms Rcic.Syn.delta_obs_caseStep_gate_of_cert
#print axioms Rcic.Syn.iota_issued_pbL
#print axioms Rcic.Syn.iota_issued_pbR
#print axioms Rcic.Syn.iota_issued_cl_left
#print axioms Rcic.Syn.iota_issued_cl_right
#print axioms Rcic.Syn.iota_issued_pb_hlhs_of_reg_occ
#print axioms Rcic.Syn.iota_issued_pb_hrhs_of_reg_occ
#print axioms Rcic.Syn.iota_retained_caseStep_of_simulation
#print axioms Rcic.Syn.IotaRetainedPorts
#print axioms Rcic.Syn.iota_retained_caseStep_of_ports
#print axioms Rcic.Syn.IotaRetainedSimulation
#print axioms Rcic.Syn.IotaRetainedRegOccPorts
#print axioms Rcic.Syn.iota_retained_caseStep_of_reg_occ_ports
#print axioms Rcic.Syn.iota_retained_caseStep_same_endpoints
#print axioms Rcic.Syn.iotaPbNodes
#print axioms Rcic.Syn.iota_issued_cl_is_occurrence
#print axioms Rcic.Syn.iota_issued_pb_variants
#print axioms Rcic.Syn.slot_not_issued
#print axioms Rcic.Syn.natSucc_iota_retained_caseStep
#print axioms Rcic.Syn.natIotaSiteEsub
#print axioms Rcic.Syn.natIotaPlan_esub_origins
#print axioms Rcic.Syn.nat_esub_slot_request_below
#print axioms Rcic.Syn.H_esub
#print axioms Rcic.Syn.s17_hL_esub_eps
#print axioms Rcic.Syn.s17_s16hR_eps
#print axioms Rcic.Syn.natSucc_esub_iota_retained_caseStep
#print axioms Rcic.Syn.s18_beta_witness
#print axioms Rcic.Syn.listCons_iota_retained_caseStep
#print axioms Rcic.Syn.IotaExpectedSlotPos
#print axioms Rcic.Syn.expectedIotaSlotCount
#print axioms Rcic.Syn.expectedIotaSlotCount_eq_planSlotCount_add_ctorParams
#print axioms Rcic.Syn.wSuccU1_expectedSlotCount
#print axioms Rcic.Syn.wConsNat_expectedSlotCount
#print axioms Rcic.Syn.wVcons_expectedSlotCount

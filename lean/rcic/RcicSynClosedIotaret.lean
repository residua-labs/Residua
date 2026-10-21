import rcic.RcicSynStepFieldsIotaRetained
import rcic.RcicSynTableNoHead
import rcic.RcicSynES
import rcic.RcicSynConst

/-!
# `es_iota_retained` — closed-port layer (swe-iotaret, SR-IOTARET)

The discharged surface of `StepSuppliers.es_iota_retained`
(`RcicSynStepFieldsIotaRetained`): every premise of the landed
`es_iota_retained_field` measured and either discharged below or named as
the residual boundary.

## Port table (premises of `es_iota_retained_field`)

| port | class | disposition |
|---|---|---|
| `hrel : levelIsZero (σ hlhs.reg.1) = false` | (a) | the field's own
  guard — `RcicSynStepSkeleton`'s supplier is invoked only on this
  `false` branch. |
| `qCLL`, `qCLR`, `qPL`, `qPR` | (b) | `StepIH`-answered, already landed
  inside `iota_retained_caseStep_of_reg_occ_ports` /
  `iota_retained_caseStep_same_endpoints` (`Issues.occ_cl`,
  `Issues.occ_pb`; `iota_issued_pb*`, `iota_issued_cl_*`). |
| `pReg`, `regOcc` | (c), subclasses | `hlhs.reg.2` sits in the query's
  own derivation forest whenever `hlhs`'s top node stores it:
  `.app`-headed `hlhs` (`iota_regOcc_app`, landed, path `[0,2]`) and
  `conv`-headed `hlhs` whose inner conversion is not a transport
  (`iota_regOcc_conv`, **this module**, path `[0, 1, hc.dchildren.length - 1]`
  via `CvP.dr_dchildren_getLast`). Free entirely when `dl = hlhs` and
  `dr = hrhs` (`es_iota_retained_closed_same_endpoints`).
  **Residual (d)** for transport-headed `hlhs` (`wk`/`esub`/`lsub`/`linst`/
  `ewk`/`cctx`) or a transport `hc`: `TyP.reg` (RcicConvPlus.lean:441–458)
  then wraps `D.reg.2` in a *fresh* transport node that is not a `subAt`
  descendant of the forest. The premise itself stays satisfiable
  (`iota_regOcc_app` inhabits the same shape on `.app`). |
| `sim : IotaRetainedSimulation tbl hlhs hrhs σ ρ`
  (`el`, `erhs`, `er`, `matchL`, `croot`, `beta`, `matchR`) | **(d)** |
  the S16 §4.5 decoder: needs a `CRule ∈ tbl` whose head is the recursor
  ref plus a template β* run to `hrhs.eps σ ρ`. **Kernel counterexample to
  a universal discharge:** `iotaRetained_no_croot_tableOf` proves no
  `CRoot` of the derived δ-only `tableOf hEnv` has a `w.recRef`-headed
  left side (every emitted head is a `.definitionM` member,
  `head_defM_build`; `w.hrecK` pins `w.recRef` to `.recursorM`) — so
  `sim.croot` cannot be produced from `EnvWfT`/`TableWF` data alone.
  **Non-vacuity:** the port is inhabited on the hand-built fixture tables
  (`iotaRetainedSimulation_natSucc`, `iotaRetainedSimulation_listCons`).
  The missing object is the ι-rule row of `buildTableSyntax`
  (W-IOTA-GENERATED-CHAIN-BOUND). |

Hence no theorem gives the field from `EnvWfT`/`TableWF` alone: the (d)
residual `sim` is reported, not hidden — `es_iota_retained_closed` is the
honest boundary `(pReg, regOcc, sim)`.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-! ## §1 the `regOcc` receipt on a `conv`-headed `hlhs` -/

/-- The last derivation child of a non-transport `CvP` node is its right
    endpoint typing `hc.dr` (`RcicConvPlus.lean:349`): every non-transport
    `dchildren` list ends in `.ty dr`, while the transports (`wk`, `esub`,
    `linst`, `ewk`, `cctx`) store no `dr` child at all. -/
theorem CvP.dr_dchildren_getLast {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (hc : CvP E n Γ a b T)
    (hnt : hc.isTransport = false) :
    hc.dchildren.getLast? = some (.ty hc.dr) := by
  cases hc <;> simp_all [CvP.isTransport, CvP.dchildren, CvP.dr]

/-- Index form of `CvP.dr_dchildren_getLast`, for `DNode.subAt` paths. -/
theorem CvP.dr_dchildren_last {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (hc : CvP E n Γ a b T)
    (hnt : hc.isTransport = false) :
    hc.dchildren[hc.dchildren.length - 1]? = some (.ty hc.dr) := by
  rw [← List.getLast?_eq_getElem?]
  exact CvP.dr_dchildren_getLast hc hnt

/-- The `regOcc` receipt on a `conv`-headed `hlhs` whose conversion `hc`
    is not a transport: `(TyP.conv .. h hc).reg = ⟨u, hc.dr⟩` and
    `hlhs.dchildren = [.ty h, .cv hc]`, so `hc.dr` resolves at payload
    path `[0, 1, hc.dchildren.length - 1]`.  Class (c): proved outright. -/
theorem iota_regOcc_conv
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs A T rhs : Expr Nat} {u : Level}
    (w : DerivedIota E lhs rhs)
    (h : TyP E n Γ lhs A) (hc : CvP E n Γ A T (.sort u))
    (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hnt : hc.isTransport = false) :
    (P2Query.es (CvP.iota E n Γ lhs rhs T w
        (TyP.conv E n Γ lhs A T u h hc) hrhs dl dr) S σ ρ).subAt
      0 [0, 1, hc.dchildren.length - 1] =
      some (.ty (TyP.conv E n Γ lhs A T u h hc).reg.2) := by
  show (hc.dchildren[hc.dchildren.length - 1]?).bind (fun d' => d'.subAt [])
    = some (.ty hc.dr)
  rw [CvP.dr_dchildren_last hc hnt]
  rfl

/-- `IotaRetainedRegOccPorts` for the conv-headed subclass: the receipt
    `iota_regOcc_conv` plus the (d) decoder `sim`. -/
def iotaRetainedRegOccPorts_of_conv
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs A T rhs : Expr Nat} {u : Level}
    (w : DerivedIota E lhs rhs)
    (h : TyP E n Γ lhs A) (hc : CvP E n Γ A T (.sort u))
    (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hnt : hc.isTransport = false)
    (sim : IotaRetainedSimulation tbl (TyP.conv E n Γ lhs A T u h hc)
      hrhs σ ρ) :
    IotaRetainedRegOccPorts tbl w (TyP.conv E n Γ lhs A T u h hc)
      hrhs dl dr S σ ρ :=
  ⟨[0, 1, hc.dchildren.length - 1],
    iota_regOcc_conv w h hc hrhs dl dr S σ ρ hnt, sim⟩

/-! ## §2 closed field theorems -/

/-- `es_iota_retained` on a `conv`-headed `hlhs` with non-transport
    conversion: `regOcc` is discharged (`iota_regOcc_conv`), so the only
    residual is the (d) decoder `sim`. -/
theorem es_iota_retained_closed_of_conv
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs A T rhs : Expr Nat} {u : Level}
    (w : DerivedIota E lhs rhs)
    (h : TyP E n Γ lhs A) (hc : CvP E n Γ A T (.sort u))
    (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ u) = false)
    (hnt : hc.isTransport = false)
    (sim : IotaRetainedSimulation tbl (TyP.conv E n Γ lhs A T u h hc)
      hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w
        (TyP.conv E n Γ lhs A T u h hc) hrhs dl dr) S σ ρ) :=
  es_iota_retained_field Aw tbl w (TyP.conv E n Γ lhs A T u h hc) hrhs
    dl dr S σ ρ hrel [0, 1, hc.dchildren.length - 1]
    (iota_regOcc_conv w h hc hrhs dl dr S σ ρ hnt) sim

/-- `es_iota_retained_closed_of_conv` at the reflexive-match residual
    `IotaRetainedRulePorts`. -/
theorem es_iota_retained_closed_of_conv_of_rulePorts
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs A T rhs : Expr Nat} {u : Level}
    (w : DerivedIota E lhs rhs)
    (h : TyP E n Γ lhs A) (hc : CvP E n Γ A T (.sort u))
    (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ u) = false)
    (hnt : hc.isTransport = false)
    (ports : IotaRetainedRulePorts tbl (TyP.conv E n Γ lhs A T u h hc)
      hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w
        (TyP.conv E n Γ lhs A T u h hc) hrhs dl dr) S σ ρ) :=
  es_iota_retained_closed_of_conv Aw tbl w h hc hrhs dl dr S σ ρ hrel hnt
    ports.toSimulation

/-- `es_iota_retained` on an `.app`-headed `hlhs`: `regOcc` discharged by
    the landed `iota_regOcc_app`; the only residual is the (d) decoder
    `sim`. -/
theorem es_iota_retained_closed_of_app
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f a A B rhs : Expr Nat} {u : Level}
    (w : DerivedIota E (.app f a) rhs)
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort u))
    (hrhs : TyP E n Γ rhs (instantiate0 a B))
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ rhs (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ u) = false)
    (sim : IotaRetainedSimulation tbl (TyP.app E n Γ f a A B u hf ha hT)
      hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ (.app f a) rhs (instantiate0 a B) w
        (TyP.app E n Γ f a A B u hf ha hT) hrhs dl dr) S σ ρ) :=
  es_iota_retained_field_of_app Aw tbl w hf ha hT hrhs dl dr S σ ρ hrel sim

/-- `es_iota_retained` with the premise typings stored as the endpoints
    (`dl = hlhs`, `dr = hrhs` — every `enrichConvT` ι node and every landed
    instance): `regOcc` is bypassed outright; the only residual is the (d)
    decoder `sim`. -/
theorem es_iota_retained_closed_same_endpoints
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (sim : IotaRetainedSimulation tbl hlhs hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs hlhs hrhs)
      S σ ρ) :=
  es_iota_retained_field_same_endpoints Aw tbl w hlhs hrhs hlhs hrhs S σ ρ
    hrel rfl rfl sim

/-- `es_iota_retained_closed_same_endpoints` at the reflexive-match
    residual `IotaRetainedRulePorts`. -/
theorem es_iota_retained_closed_same_endpoints_of_rulePorts
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (ports : IotaRetainedRulePorts tbl hlhs hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs hlhs hrhs)
      S σ ρ) :=
  es_iota_retained_closed_same_endpoints Aw tbl w hlhs hrhs S σ ρ hrel
    ports.toSimulation

/-- **RESIDUAL BOUNDARY (named, not discharged).**  `es_iota_retained` at
    arbitrary `dl`/`dr` owes exactly two residuals: the `hlhs.reg.2`
    occurrence receipt (`pReg`/`regOcc` — discharged on `.app`-headed and
    non-transport-`conv`-headed `hlhs`, bypassed at same endpoints) and the
    (d) decoder `sim` (`IotaRetainedSimulation`; `croot` is provably absent
    on the derived δ-only table, `iotaRetained_no_croot_tableOf`, and
    inhabited on the fixture tables, §3). -/
theorem es_iota_retained_closed
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (pReg : List Nat)
    (regOcc : (P2Query.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr)
        S σ ρ).subAt 0 pReg = some (.ty hlhs.reg.2))
    (sim : IotaRetainedSimulation tbl hlhs hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr)
      S σ ρ) :=
  es_iota_retained_field Aw tbl w hlhs hrhs dl dr S σ ρ hrel pReg regOcc sim

/-! ## §3 the (d) residual: non-vacuity witnesses and the δ-table tooth -/

/-- NON-VACUITY of `IotaRetainedSimulation`: the Nat-succ fixture's
    `natSucc_croot`/`s17_beta_witness` inhabit the (d) port under the
    reflexive specialization (`matchL`/`matchR` = `ConvMod.refl`). -/
noncomputable def iotaRetainedSimulation_natSucc :
    IotaRetainedSimulation natSuccTable hL hR id [] :=
  IotaRetainedRulePorts.toSimulation
    ⟨_, natSucc_croot, s17_beta_witness⟩

/-- NON-VACUITY of `IotaRetainedSimulation`: the List.cons fixture's
    `listCons_croot`/`s18_beta_witness`. -/
noncomputable def iotaRetainedSimulation_listCons :
    IotaRetainedSimulation listConsTable s18hL s18hR id [] :=
  IotaRetainedRulePorts.toSimulation
    ⟨_, listCons_croot, s18_beta_witness⟩

/-- TOOTH (kernel side): the recursor ref of any `IotaWitness` is a
    `NoHeadRule` head in the derived table `tableOf hEnv` — every emitted
    rule head resolves to a `.definitionM` member (`head_defM_build`),
    while `w.hrec`/`w.hrecK` pin `w.recRef` to `.recursorM`. -/
theorem iotaRecursor_noHeadRule_tableOf {E : ResolvedEnv}
    (hEnv : EnvWfT E) (w : IotaWitness E) :
    NoHeadRule (tableOf hEnv) w.recRef :=
  noHeadRule_tableOf_of_ne_defM hEnv w.hrec fun h =>
    MemberClass.noConfusion (w.hrecK.symm.trans h)

/-- KERNEL COUNTEREXAMPLE for a universal `sim.croot` discharge: on the
    derived δ-only table `tableOf hEnv`, no `CRoot` left side is headed by
    the recursor ref — the ι redex `appN (const w.recRef ls) args` never
    reduces.  The missing generator is the ι-rule row of `buildTableSyntax`
    (W-IOTA-GENERATED-CHAIN-BOUND). -/
theorem iotaRetained_no_croot_tableOf {E : ResolvedEnv} (hEnv : EnvWfT E)
    (w : IotaWitness E) {ls : List Level} {args : List ETm} {erhs : ETm} :
    ¬ CRoot (tableOf hEnv) (ETm.appN (.const w.recRef ls) args) erhs := by
  intro h
  generalize hx : ETm.appN (.const w.recRef ls) args = x at h
  have hnR := iotaRecursor_noHeadRule_tableOf hEnv w
  cases h with
  | bare hρ _ ls' args' _ =>
      obtain ⟨hhead, -, -⟩ := ETm.appN_const_inj hx
      exact hnR _ hρ hhead.symm
  | ctor hρ _ ls' _ args' _ _ _ =>
      obtain ⟨hhead, -, -⟩ := ETm.appN_const_inj hx
      exact hnR _ hρ hhead.symm

end Rcic.Syn

#print axioms Rcic.Syn.CvP.dr_dchildren_getLast
#print axioms Rcic.Syn.CvP.dr_dchildren_last
#print axioms Rcic.Syn.iota_regOcc_conv
#print axioms Rcic.Syn.iotaRetainedRegOccPorts_of_conv
#print axioms Rcic.Syn.es_iota_retained_closed_of_conv
#print axioms Rcic.Syn.es_iota_retained_closed_of_conv_of_rulePorts
#print axioms Rcic.Syn.es_iota_retained_closed_of_app
#print axioms Rcic.Syn.es_iota_retained_closed_same_endpoints
#print axioms Rcic.Syn.es_iota_retained_closed_same_endpoints_of_rulePorts
#print axioms Rcic.Syn.es_iota_retained_closed
#print axioms Rcic.Syn.iotaRetainedSimulation_natSucc
#print axioms Rcic.Syn.iotaRetainedSimulation_listCons
#print axioms Rcic.Syn.iotaRecursor_noHeadRule_tableOf
#print axioms Rcic.Syn.iotaRetained_no_croot_tableOf

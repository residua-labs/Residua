import rcic.RcicSynE
import rcic.RcicSynLevel
import rcic.RcicSynTableBuildI
import rcic.RcicSynTableCongrI
import rcic.RcicSynNatSuccIota
import rcic.RcicSynP2Iota
import rcic.RcicSynStepFieldsIotaRetained
import rcic.RcicSynStepFieldsDeltaIota
import rcic.RcicSynClosedIotaret
import rcic.RcicSynBelowPortsTableObstruction

/-!
# `RcicSynSRIotaRet` — sortRow row 6 `es_iota_retained` at `tableOfI`

Row 6's closer `es_iota_retained_closed` retains `pReg`/`regOcc`/`sim`
(`hrel` is the field's own telescope argument, supplied by the caller's
`levelIsZero` case split — `RcicSynStepSkeleton.lean:429`).  The (d) decoder
`sim : IotaRetainedSimulation` was refuted at the δ-only `tableOf`
(`iotaRetained_no_croot_tableOf`) but is inhabited at `tableOfI`.

## What this module proves (composition only)

§1 **Table monotonicity** — `CRoot`/`RStep`/`RStar`/`EStep`/`ConvMod` and the
   two residual structures are monotone under `tbl ⊆ tbl'`.
§2 **Producers** — `croot_of_iotaRule_mem`/`croot_of_rule_mem_bare`: a rule's
   membership + major/length data is a `CRoot` (the census's named missing
   lemma `croot_of_iotaRule_mem`).
§3 **Inhabitation at `tableOfI`** — `natSuccTable ⊆ tableOfI natEnvUWfT`
   (`tableOfI_nat`), so the landed `natSucc_croot`/`s17_beta_witness` port to
   `IotaRetainedRulePorts`/`IotaRetainedSimulation` at the real `tableOfI`,
   and the full row `CaseStep` is discharged on the Nat fixture
   (`es_iota_retained_tableOfI_nat`).
§4 **The named walls** — `esIotaRetainedWall` is the row's exact residual as
   ONE `Prop`: the regOcc+sim residual bundle `IotaRetainedRegOccPorts` at
   `tableOfI hW`.  `esIotaRetainedSimWall` is the same-endpoints residual
   (`Nonempty sim`), `esIotaRetainedPortsWall` the redex-aligned
   reflexive-match instance `Nonempty (IotaRetainedRulePorts …)` that
   `es_iota_retained_closed_same_endpoints_of_rulePorts` feeds directly.
   `es_iota_retained_tableOfI`/`_same_endpoints`/`_of_rulePorts` are the
   conditional fields; all three walls are inhabited on the Nat fixture.

The genuinely open remainder is the redex-aligned conditional: for
`hlhs : TyP E n Γ (iotaLhsOf w) T` the erased lhs is `w.recRef`-headed only
when the ctor's `iotaCtorSafe` gate emits its `iotaRuleOfCtor` row, and the
`beta` leg then needs the template run to land on `hrhs.eps σ ρ`
(W-IOTA-GENERATED-CHAIN-BOUND).  No unconditional `∀`-form of these walls
is stated or refuted here: the landed closers consume `ports`/`sim` only
per-instance at `DerivedIota`-aligned endpoints, so the unconditional
forms are nobody's lemma.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 monotonicity of the residual structures under `tbl ⊆ tbl'` -/

/-- `CRoot` is monotone in the rule table. -/
theorem cRoot_tbl_mono {tbl tbl' : List CRule} {a b : ETm}
    (hsub : ∀ ρ, ρ ∈ tbl → ρ ∈ tbl') (h : CRoot tbl a b) :
    CRoot tbl' a b := by
  cases h with
  | bare hρ hm ls args hn => exact .bare (hsub _ hρ) hm ls args hn
  | ctor hρ hm ls ls' args bs hn hb =>
      exact .ctor (hsub _ hρ) hm ls ls' args bs hn hb

/-- `RStep` is monotone in the rule table. -/
theorem rstep_tbl_mono {tbl tbl' : List CRule} {a b : ETm}
    (hsub : ∀ ρ, ρ ∈ tbl → ρ ∈ tbl') (h : RStep tbl a b) :
    RStep tbl' a b := by
  induction h with
  | beta M N => exact .beta M N
  | cr h => exact .cr (cRoot_tbl_mono hsub h)
  | appL a _ ih => exact .appL a ih
  | appR f _ ih => exact .appR f ih
  | lam _ ih => exact .lam ih
  | piL b _ ih => exact .piL b ih
  | piR a _ ih => exact .piR a ih

/-- `EStep` is monotone in the rule table. -/
theorem estep_tbl_mono {tbl tbl' : List CRule} {a b : ETm}
    (hsub : ∀ ρ, ρ ∈ tbl → ρ ∈ tbl') (h : EStep tbl a b) :
    EStep tbl' a b := by
  cases h with
  | inl h => exact .inl (rstep_tbl_mono hsub h)
  | inr h => exact .inr h

/-- `RStar` over `RStep` is monotone in the rule table. -/
theorem rstar_tbl_mono {tbl tbl' : List CRule} {a b : ETm}
    (hsub : ∀ ρ, ρ ∈ tbl → ρ ∈ tbl') (h : RStar (RStep tbl) a b) :
    RStar (RStep tbl') a b :=
  rstar_mono (fun h => rstep_tbl_mono hsub h) h

/-- `ConvMod` over `EStep` is monotone in the rule table. -/
theorem convMod_tbl_mono {tbl tbl' : List CRule} {a b : ETm}
    (hsub : ∀ ρ, ρ ∈ tbl → ρ ∈ tbl') (h : ConvMod (EStep tbl) LvlEq a b) :
    ConvMod (EStep tbl') LvlEq a b := by
  induction h with
  | refl a => exact .refl a
  | fwd h => exact .fwd (estep_tbl_mono hsub h)
  | bwd h => exact .bwd (estep_tbl_mono hsub h)
  | eqv h => exact .eqv h
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-- `IotaRetainedSimulation` is monotone in the rule table. -/
def iotaRetainedSimulation_tbl_mono {tbl tbl' : List CRule}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    {hlhs : TyP E n Γ lhs T} {hrhs : TyP E n Γ rhs T}
    {σ : Level → Level} {ρ : List Disp}
    (hsub : ∀ ρ, ρ ∈ tbl → ρ ∈ tbl')
    (s : IotaRetainedSimulation tbl hlhs hrhs σ ρ) :
    IotaRetainedSimulation tbl' hlhs hrhs σ ρ :=
  ⟨s.el, s.erhs, s.er, convMod_tbl_mono hsub s.matchL,
    cRoot_tbl_mono hsub s.croot, rstar_tbl_mono hsub s.beta,
    convMod_tbl_mono hsub s.matchR⟩

/-- `IotaRetainedRulePorts` is monotone in the rule table. -/
def iotaRetainedRulePorts_tbl_mono {tbl tbl' : List CRule}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    {hlhs : TyP E n Γ lhs T} {hrhs : TyP E n Γ rhs T}
    {σ : Level → Level} {ρ : List Disp}
    (hsub : ∀ ρ, ρ ∈ tbl → ρ ∈ tbl')
    (p : IotaRetainedRulePorts tbl hlhs hrhs σ ρ) :
    IotaRetainedRulePorts tbl' hlhs hrhs σ ρ :=
  ⟨p.erhs, cRoot_tbl_mono hsub p.croot, rstar_tbl_mono hsub p.beta⟩

/-! ## §2 `CRoot` producers from rule membership -/

/-- `croot_of_iotaRule_mem` (the census's named missing lemma): a rule row
    with `major = some (d, m)` produces a `CRoot` on every well-sized
    `args ++ [major]` spine.  At `tbl := tableOfI hW` the `iotaRulesOf`
    rows make this inhabitable where `tableOf` was refuted. -/
theorem croot_of_iotaRule_mem {tbl : List CRule} {ρ : CRule} {d : Nat}
    {m : List Level → Nat} (hρ : ρ ∈ tbl) (hm : ρ.major = some (d, m))
    (ls ls' : List Level) (args bs : List ETm)
    (hn : args.length = ρ.nargs ls) (hb : bs.length = m ls') :
    CRoot tbl (ETm.appN (.const ρ.head ls)
        (args ++ [ETm.appN (.const d ls') bs]))
      (ETm.appN (ρ.rhs ls ls') (args ++ bs)) :=
  .ctor hρ hm ls ls' args bs hn hb

/-- The `major = none` arm: every rule row also produces the bare `CRoot`. -/
theorem croot_of_rule_mem_bare {tbl : List CRule} {ρ : CRule}
    (hρ : ρ ∈ tbl) (hm : ρ.major = none) (ls : List Level) (args : List ETm)
    (hn : args.length = ρ.nargs ls) :
    CRoot tbl (ETm.appN (.const ρ.head ls) args)
      (ETm.appN (ρ.rhs ls []) args) :=
  .bare hρ hm ls args hn

/-- `croot_of_iotaRule_mem` pinned to the real `tableOfI hW`. -/
theorem croot_of_iotaRule_mem_tableOfI {E : ResolvedEnv}
    (hW : EnvWfT E) {ρ : CRule} {d : Nat} {m : List Level → Nat}
    (hρ : ρ ∈ tableOfI hW) (hm : ρ.major = some (d, m))
    (ls ls' : List Level) (args bs : List ETm)
    (hn : args.length = ρ.nargs ls) (hb : bs.length = m ls') :
    CRoot (tableOfI hW) (ETm.appN (.const ρ.head ls)
        (args ++ [ETm.appN (.const d ls') bs]))
      (ETm.appN (ρ.rhs ls ls') (args ++ bs)) :=
  croot_of_iotaRule_mem hρ hm ls ls' args bs hn hb

/-! ## §3 inhabitation at `tableOfI`: the Nat fixture -/

/-- `natSuccTable` is a sub-table of the real `tableOfI natEnvUWfT`
    (`tableOfI_nat` computes it to `[natZeroRule, natSuccRule]`). -/
theorem natSucc_mem_tableOfI (ρ : CRule) (hρ : ρ ∈ natSuccTable) :
    ρ ∈ tableOfI natEnvUWfT := by
  rw [tableOfI_nat]
  cases hρ with
  | head => exact .tail _ (.head _)
  | tail _ h => cases h

/-- The retained-simulation ports at the REAL `tableOfI`: the landed
    `natSucc_croot` + `s17_beta_witness`, transported by §1. -/
noncomputable def iotaRetainedRulePorts_tableOfI_nat :
    IotaRetainedRulePorts (tableOfI natEnvUWfT) hL hR id [] := by
  refine ⟨ETm.appN (natSuccRule.rhs [.succ .zero] []) [Pε, Zε, msε, Zε],
    ?_, ?_⟩
  · rw [hL_eps_el]
    exact cRoot_tbl_mono natSucc_mem_tableOfI natSucc_croot
  · rw [hR_eps_er]
    exact rstar_tbl_mono natSucc_mem_tableOfI s17_beta_witness

/-- The (d) decoder `sim` is inhabited at the real `tableOfI` — at
    `tableOf` the same statement is refuted
    (`natSucc_simulation_tableOf_refuted`). -/
noncomputable def iotaRetainedSimulation_tableOfI_nat :
    IotaRetainedSimulation (tableOfI natEnvUWfT) hL hR id [] :=
  iotaRetainedRulePorts_tableOfI_nat.toSimulation

/-- The fixture's level guard: `hL.reg.1` is `succ zero` (`s17_hL_reg1`). -/
theorem sri_hrel_nat : levelIsZero (id hL.reg.1) = false := by
  rw [s17_hL_reg1]
  rfl

/-- ROW 6 discharged on the concrete Nat instance at `tableOfI`: the field
    `es_iota_retained` evaluated on the admitted S17 conversion `H`. -/
theorem es_iota_retained_tableOfI_nat :
    CaseStep AwNat (tableOfI natEnvUWfT)
      (.es H natSucc_belowScope id []) :=
  es_iota_retained_closed_same_endpoints AwNat (tableOfI natEnvUWfT)
    (DerivedIota.of wSuccU1) hL hR natSucc_belowScope id []
    sri_hrel_nat iotaRetainedSimulation_tableOfI_nat

/-! ## §4 the row's residual as ONE named Prop -/

/-- ROW 6 RESIDUAL (the named wall, not discharged): `es_iota_retained` at
    `tableOfI hW` owes exactly the `IotaRetainedRegOccPorts` residual —
    `pReg`/`regOcc` (the `hlhs.reg.2` forest receipt, (c)-subclass) together
    with `sim` (the (d) decoder).  `hrel` is field data and is NOT in this
    Prop.  Inhabited on the Nat fixture (`esIotaRetainedWall_nat`). -/
def esIotaRetainedWall {E : ResolvedEnv} (hW : EnvWfT E)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {n : Nat} {Γ : LCtx}
    {lhs rhs T : Expr Nat} {Eₐ : ResolvedEnv}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T) (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Prop :=
  Nonempty (IotaRetainedRegOccPorts (tableOfI hW) w hlhs hrhs dl dr S σ ρ)

/-- The conditional field at `tableOfI hW`: `es_iota_retained` modulo
    exactly `esIotaRetainedWall`. -/
theorem es_iota_retained_tableOfI (Aw : Nat → Nat) {E : ResolvedEnv}
    (hW : EnvWfT E) {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat} {Eₐ : ResolvedEnv}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T) (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (hwall : esIotaRetainedWall hW w hlhs hrhs dl dr S σ ρ) :
    CaseStep Aw (tableOfI hW)
      (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ) := by
  obtain ⟨ports⟩ := hwall
  exact es_iota_retained_closed Aw (tableOfI hW) w hlhs hrhs dl dr S σ ρ
    hrel ports.pReg ports.regOcc ports.sim

/-- ROW 6 RESIDUAL at the canonical same-endpoints shape (`dl = hlhs`,
    `dr = hrhs`, every `enrichConvT` ι node): there `regOcc` is bypassed
    outright (`es_iota_retained_closed_same_endpoints`), so the exact
    remaining wall is the (d) decoder `sim` alone. -/
def esIotaRetainedSimWall {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (σ : Level → Level) (ρ : List Disp) : Prop :=
  Nonempty (IotaRetainedSimulation (tableOfI hW) hlhs hrhs σ ρ)

/-- The conditional field at `tableOfI hW`, same-endpoints shape. -/
theorem es_iota_retained_tableOfI_same_endpoints (Aw : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E) {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    {Eₐ : ResolvedEnv}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (hwall : esIotaRetainedSimWall hW hlhs hrhs σ ρ) :
    CaseStep Aw (tableOfI hW)
      (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs hlhs hrhs) S σ ρ) := by
  obtain ⟨sim⟩ := hwall
  exact es_iota_retained_closed_same_endpoints Aw (tableOfI hW) w hlhs
    hrhs S σ ρ hrel sim

/-- NON-VACUITY: the same-endpoints wall is inhabited on the Nat fixture —
    `sim` is `iotaRetainedSimulation_tableOfI_nat`. -/
theorem esIotaRetainedSimWall_nat :
    esIotaRetainedSimWall natEnvUWfT hL hR id [] :=
  ⟨iotaRetainedSimulation_tableOfI_nat⟩

/-- REDEX-ALIGNED INSTANCE (the (d) decoder the closer really feeds):
    `Nonempty (IotaRetainedRulePorts (tableOfI hW) hlhs hrhs σ ρ)` —
    `croot` at the erased ι-redex left plus the β* run to `hrhs.eps σ ρ`
    with reflexive `ConvMod` legs.  Stronger than `esIotaRetainedSimWall`
    (reflexive matches); inhabited on the Nat fixture
    (`esIotaRetainedPortsWall_nat`). -/
def esIotaRetainedPortsWall {E : ResolvedEnv} (hW : EnvWfT E)
    {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (σ : Level → Level) (ρ : List Disp) : Prop :=
  Nonempty (IotaRetainedRulePorts (tableOfI hW) hlhs hrhs σ ρ)

/-- Conditional field pin at `tableOfI hW` consuming exactly the
    redex-aligned `IotaRetainedRulePorts` instance — the form
    `es_iota_retained_closed_same_endpoints_of_rulePorts` feeds. -/
theorem es_iota_retained_tableOfI_of_rulePorts (Aw : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E) {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    {Eₐ : ResolvedEnv}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (hwall : esIotaRetainedPortsWall hW hlhs hrhs σ ρ) :
    CaseStep Aw (tableOfI hW)
      (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs hlhs hrhs) S σ ρ) := by
  obtain ⟨ports⟩ := hwall
  exact es_iota_retained_closed_same_endpoints_of_rulePorts Aw
    (tableOfI hW) w hlhs hrhs S σ ρ hrel ports

/-- NON-VACUITY: the redex-aligned ports wall is inhabited on the Nat
    fixture — `ports` is `iotaRetainedRulePorts_tableOfI_nat`. -/
theorem esIotaRetainedPortsWall_nat :
    esIotaRetainedPortsWall natEnvUWfT hL hR id [] :=
  ⟨iotaRetainedRulePorts_tableOfI_nat⟩

#print axioms Rcic.Syn.cRoot_tbl_mono
#print axioms Rcic.Syn.rstep_tbl_mono
#print axioms Rcic.Syn.estep_tbl_mono
#print axioms Rcic.Syn.rstar_tbl_mono
#print axioms Rcic.Syn.convMod_tbl_mono
#print axioms Rcic.Syn.iotaRetainedSimulation_tbl_mono
#print axioms Rcic.Syn.iotaRetainedRulePorts_tbl_mono
#print axioms Rcic.Syn.croot_of_iotaRule_mem
#print axioms Rcic.Syn.croot_of_rule_mem_bare
#print axioms Rcic.Syn.croot_of_iotaRule_mem_tableOfI
#print axioms Rcic.Syn.natSucc_mem_tableOfI
#print axioms Rcic.Syn.iotaRetainedRulePorts_tableOfI_nat
#print axioms Rcic.Syn.iotaRetainedSimulation_tableOfI_nat
#print axioms Rcic.Syn.sri_hrel_nat
#print axioms Rcic.Syn.es_iota_retained_tableOfI_nat
#print axioms Rcic.Syn.esIotaRetainedWall
#print axioms Rcic.Syn.es_iota_retained_tableOfI
#print axioms Rcic.Syn.esIotaRetainedSimWall
#print axioms Rcic.Syn.es_iota_retained_tableOfI_same_endpoints
#print axioms Rcic.Syn.esIotaRetainedSimWall_nat
#print axioms Rcic.Syn.esIotaRetainedPortsWall
#print axioms Rcic.Syn.es_iota_retained_tableOfI_of_rulePorts
#print axioms Rcic.Syn.esIotaRetainedPortsWall_nat

end Rcic.Syn

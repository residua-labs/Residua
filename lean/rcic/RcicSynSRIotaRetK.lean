import rcic.RcicSynStepFieldsIotaRetained

/-!
# `RcicSynSRIotaRetK` — row 6 `es_iota_retained`: the K-side retelling

cc 19:56Z item: at `tableOfK hW`, gated singleton-`Prop` large-eliminating
groups emit the bare nullary `iotaKRule` (`iotaRulesKOf`, sr4
`RcicSynTableK` — **unlanded**, `e7da62df44` on `glm/sr4-tablek`) *instead
of* the ctor-major `iotaRulesOf` emission. So `sim.croot`'s shape changes:
it is a **`CRoot.bare`** step (`ρ.major = none`), never `CRoot.ctor`.

## What this module states (all table-generic)

* `IotaBareRoot tbl el erhs` — `CRoot.bare`'s data packaged as a Prop:
  rule membership (`hmem`, the sole table-dependent input), `hbare`,
  levels/args/arity, and the erased-redex/RHS equations. `.toCRoot`
  projects it to `CRoot tbl el erhs`.
* `IotaRetainedKSim tbl hlhs hrhs σ ρ` — `IotaRetainedSimulation` with
  `croot` constrained to the bare shape. `.toSimulation` projects to the
  landed structure, so every `es_iota_retained_field*` theorem applies.
* Field theorems at generic `tbl`: `es_iota_retained_field_of_ksim`,
  `es_iota_retained_field_same_endpoints_of_ksim`,
  `es_iota_retained_field_of_app_of_ksim`.

## The exact inhabited boundary

`IotaBareRoot.hmem` — the bare K rule's membership — is the **only**
table-dependent input of the retelling. At `tbl := tableOfK hW` it is
estar's `mem_tableOfK_*`-family lemma on `iotaRulesKOf`, discharged at an
`iotaKGate` pass: `bare_mem_iotaRulesKOf` identifies every bare member as
THE K rule (`iotaKRuleOf_spec` gives its literal `iotaKRule rr nargs
nparams nindices nfields` shape, from which `hbare`/`hlen`/`hel`/`herhs`
are rule arithmetic). `matchL`/`beta`/`matchR`/`er`/`erhs` are the same
`ConvMod (EStep tbl)`/`RStar (RStep tbl)` legs as the ctor-major telling.
`tableOfK`/`iotaRulesKOf`/`tableWF_tableOfK`/`tableOfICompat_tableOfK`/
`eqK_es` are all unlanded (estar + glm-sr4 branches) — the dependency is
stated, not imported.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-- The bare-rule root receipt — `CRoot.bare`'s data packaged as a Prop.
    `hmem` is the sole table-dependent field; at `tableOfK` gated groups
    it is the `iotaRulesKOf`/`iotaKRule` membership (estar/sr4, unlanded). -/
structure IotaBareRoot (tbl : List CRule) (el erhs : ETm) : Type where
  /-- The bare rule itself (at `tableOfK`: `iotaKRule rr …`). -/
  rule : CRule
  /-- THE NAMED BOUNDARY: rule membership in the table. -/
  hmem : rule ∈ tbl
  /-- Bare shape: `iotaRulesKOf`'s K emission is `major = none` (and by
      `bare_mem_iotaRulesKOf` every bare member IS the K rule). -/
  hbare : rule.major = none
  ls : List Level
  args : List ETm
  hlen : args.length = rule.nargs ls
  hel : el = ETm.appN (.const rule.head ls) args
  herhs : erhs = ETm.appN (rule.rhs ls []) args

/-- `IotaBareRoot` projects to the landed `CRoot` step. -/
theorem IotaBareRoot.toCRoot {tbl : List CRule} {el erhs : ETm}
    (k : IotaBareRoot tbl el erhs) : CRoot tbl el erhs := by
  obtain ⟨rule, hmem, hbare, ls, args, hlen, hel, herhs⟩ := k
  cases hel; cases herhs
  exact CRoot.bare hmem hbare ls args hlen

/-- The K-side retained simulation: `IotaRetainedSimulation` with `croot`
    constrained to the bare (`major = none`) shape — the `iotaRulesKOf`
    emission at gated singleton-`Prop` large-eliminating groups. -/
structure IotaRetainedKSim (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (σ : Level → Level) (ρ : List Disp) : Type where
  el : ETm
  erhs : ETm
  er : ETm
  matchL : ConvMod (EStep tbl) LvlEq (hlhs.eps σ ρ) el
  kroot : IotaBareRoot tbl el erhs
  beta : RStar (RStep tbl) erhs er
  matchR : ConvMod (EStep tbl) LvlEq er (hrhs.eps σ ρ)

/-- A `IotaRetainedKSim` is a fortiori an `IotaRetainedSimulation`. -/
def IotaRetainedKSim.toSimulation {tbl : List CRule}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    {hlhs : TyP E n Γ lhs T} {hrhs : TyP E n Γ rhs T}
    {σ : Level → Level} {ρ : List Disp}
    (k : IotaRetainedKSim tbl hlhs hrhs σ ρ) :
    IotaRetainedSimulation tbl hlhs hrhs σ ρ :=
  ⟨_, _, _, k.matchL, k.kroot.toCRoot, k.beta, k.matchR⟩

/-- `es_iota_retained_field` on the K-side residual: general `dl`/`dr`,
    `hlhs.reg.2` occurrence receipt + the bare-rule simulation. -/
theorem es_iota_retained_field_of_ksim
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (pReg : List Nat)
    (regOcc : (P2Query.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ).subAt
      0 pReg = some (.ty hlhs.reg.2))
    (ksim : IotaRetainedKSim tbl hlhs hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ) :=
  es_iota_retained_field Aw tbl w hlhs hrhs dl dr S σ ρ hrel pReg regOcc
    ksim.toSimulation

/-- The K-side residual at coincident stored endpoints (`dl = hlhs`,
    `dr = hrhs`) — no `regOcc` receipt needed. -/
theorem es_iota_retained_field_same_endpoints_of_ksim
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (hdl : dl = hlhs) (hdr : dr = hrhs)
    (ksim : IotaRetainedKSim tbl hlhs hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ) :=
  es_iota_retained_field_same_endpoints Aw tbl w hlhs hrhs dl dr S σ ρ hrel
    hdl hdr ksim.toSimulation

/-- The K-side residual on an `.app`-headed `hlhs` (the canonical ι-site):
    `regOcc` discharged by `iota_regOcc_app`, only `ksim` remains. -/
theorem es_iota_retained_field_of_app_of_ksim
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
    (ksim : IotaRetainedKSim tbl (TyP.app E n Γ f a A B u hf ha hT)
      hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ (.app f a) rhs (instantiate0 a B) w
        (TyP.app E n Γ f a A B u hf ha hT) hrhs dl dr) S σ ρ) :=
  es_iota_retained_field_of_app Aw tbl w hf ha hT hrhs dl dr S σ ρ hrel
    ksim.toSimulation

#print axioms Rcic.Syn.IotaBareRoot.toCRoot
#print axioms Rcic.Syn.IotaRetainedKSim.toSimulation
#print axioms Rcic.Syn.es_iota_retained_field_of_ksim
#print axioms Rcic.Syn.es_iota_retained_field_same_endpoints_of_ksim
#print axioms Rcic.Syn.es_iota_retained_field_of_app_of_ksim

end Rcic.Syn

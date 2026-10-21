import rcic.RcicNativePiProbeRelBridge
import rcic.RcicNativePiProbeKObstruction
import rcic.RcicNativeReadbackCK

/-!
# Typed relation adapters for selected native iota under CK readback

The selected relation is exactly `ReadbackCKAudit.WhStepCK E`. Its landed
`ReadbackLaws`, `DetR`, and `NormalUniqueR` are used without a wrapper.
`ReadbackLaws.famApp_normal` retains its `EnvWfT` guard.

`NativeIotaForwardCKAtT` is the CK instance of the #7723 forward-observation
shape. The existing `NativeIotaForwardAtT` is explicitly indexed by
`WhStepK E n`; these are different propositions. This leaf does not change
that K-bound port or claim a readback comparison between K and CK.

The direct CK result composes selected native iota with landed determinism.
The separate relation adapter consumes the typed `LRSCoreS` endpoint facts;
its `FundConvAt` entry point uses the existing identity-substitution adapter.
The ordinary True iota controls have active sort and Pi observations.

The current CK Eq gap is also measured at the typed endpoint: at the
actual `ApproxT` model it refutes the selected `FundConvAt`, and hence
`FundamentalSAtT`. No global supplier of these facts is assumed.

Composition only. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.PiProbeRelIotaAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.PiProbeAlgebraAudit
open Rcic.Declarative.NativeValleys.PiProbeComputationAudit
open Rcic.Declarative.NativeValleys.PiProbeKObstructionAudit
open Rcic.Declarative.NativeValleys.PiProbeRelBridgeAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ## The exact readback, its selected step, and a direct baseline -/

/-- The #7723 observation obligation, explicitly selected at CK. -/
def NativeIotaForwardCKAtT {Γ : LCtx} {lhs rhs T : Expr Nat}
    (_hI : DerivedIota E lhs rhs) (_hlhs : HasTyT E n Γ lhs T)
    (_hrhs : HasTyT E n Γ rhs T) : Prop :=
  ProbeTransportT (WhStepCK E) E n Γ lhs rhs

/-- Native legacy iota is a context step of the exact CK core. -/
theorem whStepCK_of_native_iota {Γ : LCtx} {lhs rhs : Expr Nat}
    (hI : DerivedIota E lhs rhs) : WhStepCK E Γ lhs rhs :=
  .ctx (.iota (derivedIotaU_ofDerivedIota hI))

/-- CK determinism cancels the chosen context step at every normal endpoint.
This also supplies the zeta specialization used by the substitution adapter. -/
theorem redR_ctx_whStepCK_iff (hW : EnvWfT E) {Γ : LCtx} {M N X : Expr Nat}
    (hs : WhStepCtx E Γ M N) (hX : NormalR (WhStepCK E) Γ X) :
    RedR (WhStepCK E) Γ M X ↔ RedR (WhStepCK E) Γ N X := by
  constructor
  · exact redR_contract_of_source_unique (.ctx hs)
      (fun _ hs' => (detR_whStepCK hW Γ (.ctx hs) hs').symm) hX
  · exact fun hr => .step (.ctx hs) hr

theorem probeEquiv_ctx_whStepCK (hW : EnvWfT E) {Γ : LCtx} {M N : Expr Nat}
    (hs : WhStepCtx E Γ M N) : ProbeEquivT (WhStepCK E) E n Γ M N :=
  probeEquiv_of_readback_iffT (readbackLaws_whStepCK E)
    (fun _ hX => redR_ctx_whStepCK_iff hW hs hX)

/-- Direct selected-iota transport follows from the existing CK step and
determinism, without a fundamental-lemma premise. -/
theorem native_iota_forwardCK (hW : EnvWfT E) {Γ : LCtx} {lhs rhs T : Expr Nat}
    (hI : DerivedIota E lhs rhs) (hlhs : HasTyT E n Γ lhs T)
    (hrhs : HasTyT E n Γ rhs T) : NativeIotaForwardCKAtT hI hlhs hrhs :=
  (probeEquiv_ctx_whStepCK hW (.iota (derivedIotaU_ofDerivedIota hI))).1

/-- The reverse observation direction is plain readback expansion. -/
theorem native_iota_reverseCK {Γ : LCtx} {lhs rhs : Expr Nat}
    (hI : DerivedIota E lhs rhs) : ProbeTransportT (WhStepCK E) E n Γ rhs lhs := by
  constructor
  · rintro ⟨u, hr⟩
    exact ⟨u, .step (whStepCK_of_native_iota hI) hr⟩
  · intro A B hr _
    exact ⟨A, B, .step (whStepCK_of_native_iota hI) hr, ⟨.refl _ _⟩, ⟨.refl _ _⟩⟩

theorem native_iota_motive_iff_forwardCK {Γ : LCtx} {lhs rhs T : Expr Nat}
    (hI : DerivedIota E lhs rhs) (hlhs : HasTyT E n Γ lhs T)
    (hrhs : HasTyT E n Γ rhs T) :
    ConvProbeMotiveT (WhStepCK E) (.iota Γ lhs rhs T hI hlhs hrhs) ↔
      NativeIotaForwardCKAtT hI hlhs hrhs :=
  ⟨fun h => h.1, fun h => ⟨h, native_iota_reverseCK hI⟩⟩

/-! ## The typed endpoint adapters -/

/-- Both endpoint suppliers are consumed by the common bridge. Normal
uniqueness pins its Pi witness to the specified source observation. -/
theorem native_iota_forwardCK_of_lrSCoreS (hW : EnvWfT E)
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (hI : DerivedIota E lhs rhs) (hlhs : HasTyT E n Γ lhs T)
    (hrhs : HasTyT E n Γ rhs T)
    (hsort : ∀ u, RedR (WhStepCK E) Γ lhs (.sort u) →
      LRSCoreS (WhStepCK E) E n Γ lhs rhs T (sortCode u))
    (hpi : ∀ A B, RedR (WhStepCK E) Γ lhs (.pi A B) →
      CtxWfT E n (.assumption A :: Γ) →
      LRSCoreS (WhStepCK E) E n Γ lhs rhs T (.pi .bot [])) :
    NativeIotaForwardCKAtT hI hlhs hrhs :=
  probeTransport_of_lrSCoreS_probesT (readbackLaws_whStepCK E)
    (normalUniqueR_whStepCK hW) hsort hpi

/-- The selected `FundConvAt` is instantiated only through the existing
identity adapter. Model coverage is local to the two observations consumed. -/
theorem native_iota_forwardCK_of_fundConvAt (hW : EnvWfT E)
    {M : CtxModelT E} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {ρ : EnvT}
    (hId : RelSubstIdT M (WhStepCK E) n Γ ρ) {lhs rhs T : Expr Nat}
    (hI : DerivedIota E lhs rhs) (hlhs : HasTyT E n Γ lhs T)
    (hrhs : HasTyT E n Γ rhs T) (hF : FundConvAt M (WhStepCK E) n Γ lhs rhs T)
    (hsort : ∀ u, RedR (WhStepCK E) Γ lhs (.sort u) →
      M.Ap ρ lhs (sortCode u) ∨ M.Ap ρ rhs (sortCode u))
    (hpi : ∀ A B, RedR (WhStepCK E) Γ lhs (.pi A B) →
      CtxWfT E n (.assumption A :: Γ) →
      M.Ap ρ lhs (.pi .bot []) ∨ M.Ap ρ rhs (.pi .bot [])) :
    NativeIotaForwardCKAtT hI hlhs hrhs :=
  native_iota_forwardCK_of_lrSCoreS hW hI hlhs hrhs
    (fun u hr => fundConvAt_ctx_of_id hΓ hId hF (sortCode u) (hsort u hr))
    (fun A B hr hΓA => fundConvAt_ctx_of_id hΓ hId hF (.pi .bot []) (hpi A B hr hΓA))

/-! ## Active typed ordinary-iota controls -/

theorem truePiIota_readbackCK : RedR (WhStepCK trueEnvU) [] truePiIotaLhs mixPi :=
  .step (whStepCK_of_native_iota truePiIotaNative) (.refl _)

/-- This endpoint fact comes from the existing Pi diagonal and relation
expansion; no native fundamental iota case is reconstructed. -/
theorem truePiIota_endpointS :
    LRSCoreS (WhStepCK trueEnvU) trueEnvU 0 [] truePiIotaLhs mixPi
      (.sort truePiIotaLevel) (.pi .bot []) :=
  lrSCoreS_expand_red (readbackLaws_whStepCK trueEnvU) truePiIota_readbackCK
    (.pi .bot []) (lrSCoreS_pi_self .nil (.sort _ .zero))

theorem truePiIota_no_sort_readbackCK (u : Level) :
    ¬ RedR (WhStepCK trueEnvU) [] truePiIotaLhs (.sort u) := by
  intro hr
  obtain ⟨v, hv⟩ :=
    (native_iota_forwardCK trueEnvUWfT truePiIotaNative truePiIotaLhsTy truePiIotaRhsTy).sorts
      ⟨u, hr⟩
  exact Expr.noConfusion (redR_pi_eq (readbackLaws_whStepCK trueEnvU) hv)

/-- The relation adapter has an active Pi source and an explicit endpoint
fact; its universal sort clause is discharged by the measured exclusion. -/
theorem truePiIota_forwardCK_of_relS :
    NativeIotaForwardCKAtT truePiIotaNative truePiIotaLhsTy truePiIotaRhsTy :=
  native_iota_forwardCK_of_lrSCoreS trueEnvUWfT truePiIotaNative truePiIotaLhsTy truePiIotaRhsTy
    (fun u hr => (truePiIota_no_sort_readbackCK u hr).elim)
    (fun _ _ _ _ => truePiIota_endpointS)

theorem truePiIota_rel_adapter_nonvacuity :
    Nonempty (EnvWfT trueEnvU) ∧ Nonempty (CtxWfT trueEnvU 0 []) ∧
    Nonempty (HasTyT trueEnvU 0 [] truePiIotaLhs (.sort truePiIotaLevel)) ∧
    Nonempty (HasTyT trueEnvU 0 [] mixPi (.sort truePiIotaLevel)) ∧
    Nonempty (ConvT trueEnvU 0 [] truePiIotaLhs mixPi (.sort truePiIotaLevel)) ∧
    RedR (WhStepCK trueEnvU) [] truePiIotaLhs mixPi ∧
    LRSCoreS (WhStepCK trueEnvU) trueEnvU 0 [] truePiIotaLhs mixPi
      (.sort truePiIotaLevel) (.pi .bot []) ∧
    NativeIotaForwardCKAtT truePiIotaNative truePiIotaLhsTy truePiIotaRhsTy ∧
    ∃ A B, RedR (WhStepCK trueEnvU) [] mixPi (.pi A B) ∧
      Nonempty (TyConvT trueEnvU 0 [] (.sort .zero) A) ∧
      Nonempty (TyConvT trueEnvU 0 [.assumption (.sort .zero)] (.sort .zero) B) :=
  ⟨⟨trueEnvUWfT⟩, ⟨.nil⟩, ⟨truePiIotaLhsTy⟩, ⟨truePiIotaRhsTy⟩,
    ⟨truePiIotaAtSort⟩, truePiIota_readbackCK, truePiIota_endpointS,
    truePiIota_forwardCK_of_relS,
    truePiIota_forwardCK_of_relS.pis truePiIota_readbackCK
      (.assumption _ _ _ .nil (.sort _ .zero))⟩

/-- The landed sort-valued True iota has an active universe observation. -/
theorem trueSortIota_readbackCK :
    RedR (WhStepCK trueEnvU) [] (iotaLhsOf wTrueRecU) (.sort .zero) :=
  .step (whStepCK_of_native_iota (.of wTrueRecU)) (.refl _)

theorem trueSortIota_endpointS :
    LRSCoreS (WhStepCK trueEnvU) trueEnvU 0 [] (iotaLhsOf wTrueRecU) (.sort .zero)
      (.sort (.succ .zero)) .prop := by
  rw [lrSCoreS_prop_iff]
  exact ⟨⟨.succ .zero, .refl _⟩, .zero, .zero, trueSortIota_readbackCK, .refl _⟩

/-- Here the relation adapter consumes an inhabited sort endpoint. CK
normal uniqueness excludes any competing Pi observation of this source. -/
theorem trueSortIota_forwardCK_of_relS :
    NativeIotaForwardCKAtT (.of wTrueRecU)
      (trueEnvUL_tyS1 (n := 0) (Γ := [])) (.sort [] .zero) := by
  refine native_iota_forwardCK_of_lrSCoreS trueEnvUWfT (.of wTrueRecU)
    trueEnvUL_tyS1 (.sort [] .zero) ?_ ?_
  · intro u hr
    have heq : Expr.sort u = (.sort .zero : Expr Nat) :=
      normalUniqueR_whStepCK trueEnvUWfT [] hr
        ((readbackLaws_whStepCK trueEnvU).sort_normal [] u)
        trueSortIota_readbackCK ((readbackLaws_whStepCK trueEnvU).sort_normal [] .zero)
    have hu := Expr.sort.inj heq
    subst u
    simpa only [sortCode_zero] using trueSortIota_endpointS
  · intro A B hr _
    have heq : Expr.pi A B = (.sort .zero : Expr Nat) :=
      normalUniqueR_whStepCK trueEnvUWfT [] hr
        ((readbackLaws_whStepCK trueEnvU).pi_normal [] A B)
        trueSortIota_readbackCK ((readbackLaws_whStepCK trueEnvU).sort_normal [] .zero)
    exact Expr.noConfusion heq

/-- All typing and the native conversion are imported from the original
True control. The output is obtained by applying the relation adapter. -/
theorem trueSortIota_rel_adapter_nonvacuity :
    Nonempty (EnvWfT trueEnvU) ∧ Nonempty (CtxWfT trueEnvU 0 []) ∧
    Nonempty (HasTyT trueEnvU 0 [] (iotaLhsOf wTrueRecU) (.sort (.succ .zero))) ∧
    Nonempty (HasTyT trueEnvU 0 [] (.sort .zero) (.sort (.succ .zero))) ∧
    Nonempty (ConvT trueEnvU 0 [] (iotaLhsOf wTrueRecU) (.sort .zero) (.sort (.succ .zero))) ∧
    RedR (WhStepCK trueEnvU) [] (iotaLhsOf wTrueRecU) (.sort .zero) ∧
    LRSCoreS (WhStepCK trueEnvU) trueEnvU 0 [] (iotaLhsOf wTrueRecU) (.sort .zero)
      (.sort (.succ .zero)) .prop ∧
    NativeIotaForwardCKAtT (.of wTrueRecU)
      (trueEnvUL_tyS1 (n := 0) (Γ := [])) (.sort [] .zero) ∧
    ∃ u, RedR (WhStepCK trueEnvU) [] (.sort .zero) (.sort u) :=
  ⟨⟨trueEnvUWfT⟩, ⟨.nil⟩, ⟨trueEnvUL_tyS1⟩, ⟨.sort [] .zero⟩,
    ⟨trueEnvU_ci⟩, trueSortIota_readbackCK, trueSortIota_endpointS,
    trueSortIota_forwardCK_of_relS,
    trueSortIota_forwardCK_of_relS.sorts ⟨.zero, trueSortIota_readbackCK⟩⟩

/-! ## The exact typed supplier at the existing Eq gap -/

/-- The admitted Eq conversion cannot supply even its typed sort endpoint. -/
theorem not_lrSCoreS_whStepCK_eqGap_sort (n : Nat) :
    ¬ LRSCoreS (WhStepCK eqEnvT) eqEnvT n eqGapCtx (.sort .zero) eqGapRedex
      (.sort (.succ .zero)) .sort := by
  intro h
  obtain ⟨_, _, _, _, hr⟩ := (lrSCoreS_sort_iff _ _ _ _).mp h
  exact Expr.noConfusion (whRedCK_eqGapRedex_eq hr)

theorem not_lrSCoreS_whStepCK_eqGap_prop (n : Nat) :
    ¬ LRSCoreS (WhStepCK eqEnvT) eqEnvT n eqGapCtx (.sort .zero) eqGapRedex
      (.sort (.succ .zero)) .prop :=
  fun h => not_lrSCoreS_whStepCK_eqGap_sort n ((lrSCoreS_prop_iff_sort _ _ _ _).mp h)

/-- The concrete Eq context is let-free. -/
theorem lookupValue_eqGapCtx_none (i : Nat) : lookupValue eqGapCtx i = none := by
  cases i with
  | zero => rfl
  | succ i =>
      cases i with
      | zero => rfl
      | succ i =>
          cases i with
          | zero => rfl
          | succ i => simp [eqGapCtx, lookupValue]

/-- At the bottom variable environment, the identity relation package is
inhabited for the actual Eq context, for every model and readback. -/
theorem relSubstIdT_eqGap_bot (M : CtxModelT eqEnvT) (R : Readback) (n : Nat) :
    RelSubstIdT M R n eqGapCtx EnvT.bot := by
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  have hT := typedSubstT_id (envClosed_of_envWfT pinEqGroupWfT) hΓ
  refine ⟨hT, hT, ?_, ?_, ?_⟩
  · intro i A hA
    exact ⟨by simpa only [substT_id] using
      (ConvT.refl eqGapCtx (.bvar i) A (.bvar eqGapCtx i A hA))⟩
  · intro i A _ c hc
    have hc' : c = .bot := hc.elim id id
    subst c
    exact ⟨lrSCoreS_bot _ _ _ _, lrSCoreS_bot _ _ _ _,
      lrSCoreS_bot _ _ _ _, lrSCoreS_bot _ _ _ _⟩
  · intro i v A hv _
    rw [lookupValue_eqGapCtx_none] at hv
    exact Option.noConfusion hv

/-- The current typed model really observes the source sort, so the
selected `FundConvAt` fails for CK at this native conversion. -/
theorem not_fundConvAt_approxT_whStepCK_eqGap (n : Nat) :
    ¬ FundConvAt (ctxModelT_approxT eqEnvT) (WhStepCK eqEnvT) n eqGapCtx
      (.sort .zero) eqGapRedex (.sort (.succ .zero)) := by
  intro hF
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  apply not_lrSCoreS_whStepCK_eqGap_prop n
  exact fundConvAt_ctx_of_id hΓ
    (relSubstIdT_eqGap_bot (ctxModelT_approxT eqEnvT) (WhStepCK eqEnvT) n) hF .prop
    (Or.inl (approxT_sort_code eqEnvT EnvT.bot .zero))

/-- The exact typed global supplier is therefore unavailable as well. -/
theorem not_fundamentalSAtT_approxT_whStepCK_eqEnvT (n : Nat) :
    ¬ FundamentalSAtT (ctxModelT_approxT eqEnvT) (WhStepCK eqEnvT) n := by
  intro hF
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  obtain ⟨hc⟩ := eqGap_conv n
  exact not_fundConvAt_approxT_whStepCK_eqGap n (hF.2 hΓ hc)

/-- The existing environment-typing guard is satisfied on both sides of
the same identity substitution; no stronger future package is assumed. -/
theorem relSubstTypedAtT_eqGap_bot (n : Nat) :
    RelSubstTypedAtT (ctxModelT_approxT eqEnvT) (WhStepCK eqEnvT) n eqGapCtx
      EnvT.bot EnvT.bot SubstT.id SubstT.id eqGapCtx :=
  ⟨relSubstIdT_eqGap_bot (ctxModelT_approxT eqEnvT) (WhStepCK eqEnvT) n,
    envTypedAtT_bot eqGapCtx, envTypedAtT_bot eqGapCtx⟩

/-- The typed Eq counterexample includes the admitted environment, native
context and conversion, identity relation package, typed model environment,
and the actual source compact which forces the impossible endpoint. -/
theorem eqGap_typed_supplier_counterexample (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    Nonempty (ConvT eqEnvT n eqGapCtx (.sort .zero) eqGapRedex (.sort (.succ .zero))) ∧
    RelSubstIdT (ctxModelT_approxT eqEnvT) (WhStepCK eqEnvT) n eqGapCtx EnvT.bot ∧
    EnvTypedAtT (ctxModelT_approxT eqEnvT) eqGapCtx EnvT.bot ∧
    ApproxT eqEnvT EnvT.bot (.sort .zero) .prop ∧
    ¬ FundConvAt (ctxModelT_approxT eqEnvT) (WhStepCK eqEnvT) n eqGapCtx
      (.sort .zero) eqGapRedex (.sort (.succ .zero)) :=
  ⟨⟨pinEqGroupWfT⟩, eqGapCtx_wf n, eqGap_conv n,
    relSubstIdT_eqGap_bot (ctxModelT_approxT eqEnvT) (WhStepCK eqEnvT) n,
    envTypedAtT_bot eqGapCtx, approxT_sort_code eqEnvT EnvT.bot .zero,
    not_fundConvAt_approxT_whStepCK_eqGap n⟩

-- BEGIN RCIC_PI_PROBE_REL_IOTA_ROOTS
#print axioms NativeIotaForwardCKAtT
#print axioms whStepCK_of_native_iota
#print axioms redR_ctx_whStepCK_iff
#print axioms probeEquiv_ctx_whStepCK
#print axioms native_iota_forwardCK
#print axioms native_iota_reverseCK
#print axioms native_iota_motive_iff_forwardCK
#print axioms native_iota_forwardCK_of_lrSCoreS
#print axioms native_iota_forwardCK_of_fundConvAt
#print axioms truePiIota_readbackCK
#print axioms truePiIota_endpointS
#print axioms truePiIota_no_sort_readbackCK
#print axioms truePiIota_forwardCK_of_relS
#print axioms truePiIota_rel_adapter_nonvacuity
#print axioms trueSortIota_readbackCK
#print axioms trueSortIota_endpointS
#print axioms trueSortIota_forwardCK_of_relS
#print axioms trueSortIota_rel_adapter_nonvacuity
#print axioms not_lrSCoreS_whStepCK_eqGap_sort
#print axioms not_lrSCoreS_whStepCK_eqGap_prop
#print axioms lookupValue_eqGapCtx_none
#print axioms relSubstIdT_eqGap_bot
#print axioms not_fundConvAt_approxT_whStepCK_eqGap
#print axioms not_fundamentalSAtT_approxT_whStepCK_eqEnvT
#print axioms relSubstTypedAtT_eqGap_bot
#print axioms eqGap_typed_supplier_counterexample
-- END RCIC_PI_PROBE_REL_IOTA_ROOTS

end Rcic.Declarative.NativeValleys.PiProbeRelIotaAudit

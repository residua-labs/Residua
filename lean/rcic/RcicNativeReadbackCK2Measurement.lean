import rcic.RcicNativeReadbackCK2NativeControls
import rcic.RcicNativeReadbackCK2IndexDet
import rcic.RcicNativeReadbackCK2ModelObstruction

/-!
# CK2 measurement and local adapter controls

Both candidates satisfy the complete structural readback contract.  The
native-index candidate handles all four native controls.  The one-sided
weak-head candidate handles the original beta gap and transparent delta
at the actual index head, but its binder and eta failures are established
in `RcicNativeReadbackCK2Index`.

The active local adapter controls below have actual sort readbacks and
non-bottom model observations in the admitted Eq environment.  They are
not an inhabitant of the unchanged global Fundamental supplier: that
supplier is refuted for both candidates by the imported obstruction.
No conditional action is advertised as a supplied global input.

Composition only.  `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2Audit
open Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2IndexDetAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit
open Rcic.Declarative.NativeValleys.PiProbeAlgebraAudit
open Rcic.Declarative.NativeValleys.PiProbeComputationAudit
open Rcic.Declarative.NativeValleys.PiProbeCongruenceAudit
open Rcic.Declarative.NativeValleys.PiProbeModelBoundaryAudit
open Rcic.Declarative.NativeValleys.PiProbeRelAppAudit

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

/-- Whole-core contract, with no source-typing restriction in determinism. -/
theorem native_core_contract (hW : EnvWfT E) (n : Nat) :
    DetR (WhStepCK2 E n) ∧ NormalUniqueR (WhStepCK2 E n) ∧
      ReadbackLaws E (WhStepCK2 E n) :=
  ⟨detR_whStepCK2 hW, normalUniqueR_whStepCK2 hW, readbackLaws_whStepCK2 E n⟩

/-- The same contract for the complete index-context grammar. -/
theorem index_core_contract (hW : EnvWfT E) :
    DetR (WhStepIndexCK2 E) ∧ NormalUniqueR (WhStepIndexCK2 E) ∧
      ReadbackLaws E (WhStepIndexCK2 E) :=
  ⟨detR_whStepIndexCK2 hW, normalUniqueR_whStepIndexCK2 hW,
    readbackLaws_whStepIndexCK2 E⟩

/-- All the native controls are actual readbacks in the entire new core. -/
theorem native_controls_readback (n : Nat) :
    RedR (WhStepCK2 eqEnvT n) binderEqCtx binderIndexRedex (.sort .zero) ∧
    RedR (WhStepCK2 eqEnvT n) etaEqCtx etaIndexRedex (.sort .zero) ∧
    RedR (WhStepCK2 deltaEqEnv n) deltaHeadEqCtx
      (deltaRedex (.const 66 [])) (.sort .zero) ∧
    RedR (WhStepCK2 deltaEqEnv n) deltaUnderBinderEqCtx
      (deltaRedex deltaBinderIndex) (.sort .zero) :=
  ⟨redR_single (.native (kNativeHead_binder n)),
    redR_single (.native (kNativeHead_eta n)),
    redR_single (.native (kNativeHead_delta n)),
    redR_single (.native (kNativeHead_delta_under_binder n))⟩

/-- Candidate (b)'s delta control is a full recursor readback: one index
delta step and then the original syntactic K step. -/
theorem index_delta_readback :
    RedR (WhStepIndexCK2 deltaEqEnv) deltaHeadEqCtx
      (deltaRedex (.const 66 [])) (.sort .zero) := by
  refine .step (.index
    (w := eqConvW deltaEqExtends indexFn indexId (.const 66 [])
      binderIndexMot (.sort .zero))
    (Or.inl ⟨rfl, rfl, rfl⟩) not_isCtorSpine_bvar
    (delta_index_schedule deltaHeadEqCtx)) ?_
  exact .step (.ck (.kStar
    (w := eqConvW deltaEqExtends indexFn indexId indexId binderIndexMot (.sort .zero))
    ⟨rfl, rfl, rfl⟩ not_isCtorSpine_bvar rfl)) (.refl _)

/-- These are the two actual-source reads.  The full `FundConvAt`
obligation retains all related substitutions and is treated separately
in `RcicNativeReadbackCK2Gap`. -/
theorem eqGap_actual_reads (n : Nat) :
    RedR (WhStepCK2 eqEnvT n) eqGapCtx eqGapRedex (.sort .zero) ∧
    RedR (WhStepIndexCK2 eqEnvT) eqGapCtx eqGapRedex (.sort .zero) :=
  ⟨redR_whStepCK2_eqGap n, redR_whStepIndexCK2_eqGap⟩

/-- A supplied actual sort read and normal uniqueness prove the complete
local realization guard at this endpoint.  The model seed is non-bottom. -/
theorem eqGap_realized_of_read {R : Readback}
    (hL : ReadbackLaws eqEnvT R) (hNU : NormalUniqueR R)
    (hr : RedR R eqGapCtx eqGapRedex (.sort .zero)) :
    ProbeRealizedAtT R eqEnvT n eqGapCtx eqGapRedex := by
  constructor
  · intro u hu
    have he := hNU eqGapCtx hu (fun e hs => hL.sort_normal _ _ e hs)
      hr (fun e hs => hL.sort_normal _ _ e hs)
    obtain rfl := Expr.sort.inj he
    exact eqRec_model_minor_backward (approxT_sort_code eqEnvT _ .zero)
  · intro A B hp _
    have he := hNU eqGapCtx hp (fun e hs => hL.pi_normal _ _ _ e hs)
      hr (fun e hs => hL.sort_normal _ _ e hs)
    exact (Expr.noConfusion he : False).elim

/-- The formerly stuck source has actual, non-vacuous local realization
under both repaired relations. -/
theorem eqGap_realized_both (n : Nat) :
    ProbeRealizedAtT (WhStepCK2 eqEnvT n) eqEnvT n eqGapCtx eqGapRedex ∧
    ProbeRealizedAtT (WhStepIndexCK2 eqEnvT) eqEnvT n eqGapCtx eqGapRedex :=
  ⟨eqGap_realized_of_read (readbackLaws_whStepCK2 eqEnvT n)
      (normalUniqueR_whStepCK2 pinEqGroupWfT) (redR_whStepCK2_eqGap n),
    eqGap_realized_of_read (readbackLaws_whStepIndexCK2 eqEnvT)
      (normalUniqueR_whStepIndexCK2 pinEqGroupWfT) redR_whStepIndexCK2_eqGap⟩

/-- The existing cancellation and probe-algebra lemmas consume the new
determinism theorem, without any Fundamental or model transport premise. -/
theorem probeEquiv_of_stepCK2 (hW : EnvWfT E) {a b : Expr Nat}
    (hs : WhStepCK2 E n Γ a b) : ProbeEquivT (WhStepCK2 E n) E n Γ a b :=
  probeEquiv_of_readback_iffT (readbackLaws_whStepCK2 E n)
    (fun _ hn => ⟨redR_contract_of_source_unique hs
      (fun _ ht => (detR_whStepCK2 hW Γ hs ht).symm) hn,
      fun hr => .step hs hr⟩)

/-- All original context computations retain their specified probes. -/
theorem probeEquiv_ctxCK2 (hW : EnvWfT E) {a b : Expr Nat}
    (hs : WhStepCtx E Γ a b) : ProbeEquivT (WhStepCK2 E n) E n Γ a b :=
  probeEquiv_of_stepCK2 hW (.ctx hs)

/-- The chosen native iota adapter survives at the new readback.  Its
forward and reverse actions follow from the same actual context step. -/
theorem native_iota_probeCK2 (hW : EnvWfT E) {lhs rhs : Expr Nat}
    (hi : DerivedIota E lhs rhs) :
    ProbeEquivT (WhStepCK2 E n) E n Γ lhs rhs :=
  probeEquiv_ctxCK2 hW (.iota (derivedIotaU_ofDerivedIota hi))

def actionFnType : Expr Nat := .pi (.sort (.succ .zero)) (.sort (.succ .zero))
def actionFn : Expr Nat := .lam (.sort (.succ .zero)) (.sort .zero)
def actionExpandedFn : Expr Nat := .app (.lam actionFnType (.bvar 0)) actionFn

def actionFnTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ actionFn actionFnType :=
  .lam _ _ _ _ _ (.sort _ _) (.sort _ _)

/-- A non-reflexive native function-conversion input to the head action. -/
def actionHeadConv (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ConvT E n Γ actionExpandedFn actionFn actionFnType :=
  .beta _ _ _ _ _ _ (.pi _ _ _ _ _ (.sort _ _) (.sort _ _))
    (.bvar _ 0 _ rfl) (actionFnTy E n Γ)

/-- The head action is open in every typed argument to this function. -/
theorem action_headCK2 (hW : EnvWfT E) :
    AppHeadActionT (WhStepCK2 E n) (actionHeadConv E n Γ) := by
  intro a _
  exact probeEquiv_of_stepCK2 hW (.appHead (.ctx (.beta _ _ _)))

/-- The argument action is open in every native argument conversion. -/
theorem action_argCK2 (hW : EnvWfT E) (hΓ : CtxWfT E n Γ) :
    AppArgActionT (WhStepCK2 E n) (actionFnTy E n Γ) := by
  intro a b _
  exact probeEquiv_transT hW hΓ (probeEquiv_ctxCK2 hW (.beta _ _ _))
    (probeEquiv_symmT (probeEquiv_ctxCK2 hW (.beta _ _ _)))

/-- A substitution-edge input with a proper beta value edge. -/
theorem action_mixedCK2 (hW : EnvWfT E) :
    MixedSubstEdgesT (WhStepCK2 E n) E n Γ
      (.app actionFn (.sort .zero)) (.sort .zero) (.bvar 0) (.bvar 0) :=
  ⟨probeEquiv_reflT _ _, probeEquiv_ctxCK2 hW (.beta _ _ _)⟩

/-- Local actions, typing, realization and a non-bottom observed result
coexist in the actual admitted Eq environment.  This is deliberately a
local witness, not a global adapter-input package. -/
theorem action_nonvacuityCK2 (n : Nat) :
    AppHeadActionT (WhStepCK2 eqEnvT n) (actionHeadConv eqEnvT n []) ∧
    AppArgActionT (WhStepCK2 eqEnvT n) (actionFnTy eqEnvT n []) ∧
    Nonempty (HasTyT eqEnvT n [] (.app actionFn (.sort .zero)) (.sort (.succ .zero))) ∧
    RedR (WhStepCK2 eqEnvT n) [] (.app actionFn (.sort .zero)) (.sort .zero) ∧
    ApproxT eqEnvT (ctxEnvT eqEnvT []) (.app actionFn (.sort .zero)) .prop ∧
    CTyS eqEnvT .prop .sort ∧ CptT.prop ≠ .bot ∧
    ProbeRealizedAtT (WhStepCK2 eqEnvT n) eqEnvT n [] (.app actionFn (.sort .zero)) :=
  ⟨action_headCK2 pinEqGroupWfT, action_argCK2 pinEqGroupWfT .nil,
    ⟨.app _ _ _ _ _ (actionFnTy eqEnvT n []) (.sort _ _)⟩,
    redR_single (.ctx (.beta _ _ _)),
    approxT_app_empty_demand (fun h => CptT.noConfusion h)
      (approxT_sort_code eqEnvT _ .zero),
    by rw [CTyS]; exact Or.inr TyCodeCT.prop,
    (fun h => CptT.noConfusion h),
    probeRealizedAt_constantSortAppT (readbackLaws_whStepCK2 eqEnvT n)
      (normalUniqueR_whStepCK2 pinEqGroupWfT) [] _ _ .zero⟩

/-- Neither repaired relation admits the original global supplier in
the actual Eq environment.  Adding other adapter inputs cannot inhabit
this already necessary conjunct of the requested Fundamental assembly. -/
theorem neither_original_fundamental (n : Nat) :
    (¬ FundamentalSAtT (ctxModelT_approxT eqEnvT) (WhStepCK2 eqEnvT n) n) ∧
    (¬ FundamentalSAtT (ctxModelT_approxT eqEnvT) (WhStepIndexCK2 eqEnvT) n) :=
  ⟨not_fundamentalSAtT_whStepCK2_eqEnv n,
    ReadbackCK2ModelObstructionAudit.not_fundamentalSAtT_whStepIndexCK2_eqEnv n⟩

-- BEGIN RCIC_NATIVE_READBACK_CK2_MEASUREMENT_ROOTS
#print axioms native_core_contract
#print axioms index_core_contract
#print axioms native_controls_readback
#print axioms index_delta_readback
#print axioms eqGap_actual_reads
#print axioms eqGap_realized_of_read
#print axioms eqGap_realized_both
#print axioms probeEquiv_of_stepCK2
#print axioms probeEquiv_ctxCK2
#print axioms native_iota_probeCK2
#print axioms actionFnType
#print axioms actionFn
#print axioms actionExpandedFn
#print axioms actionFnTy
#print axioms actionHeadConv
#print axioms action_headCK2
#print axioms action_argCK2
#print axioms action_mixedCK2
#print axioms action_nonvacuityCK2
#print axioms neither_original_fundamental
-- END RCIC_NATIVE_READBACK_CK2_MEASUREMENT_ROOTS

end Rcic.Declarative.NativeValleys.ReadbackCK2MeasurementAudit

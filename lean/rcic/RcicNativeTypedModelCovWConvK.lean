import rcic.RcicNativeTypedModelCovWNativeFollowupSeal

/-!
# Typed legacy K alignment with declarative conversion

The four CK2 gates do not type the full recursor occurrence.  This module
keeps them verbatim and supplies the additional, explicit legacy occurrence
data used by the landed irrelevance/application/iota composition.  No native
conversion of the K source to its target is assumed. `closure_claim = 0`.
-/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit ReadbackCK2IndexAudit
open TypedModelCovWMatrixAudit TypedModelCovWNativeAudit

/-- Actual occurrence data in addition to the unchanged four CK2 gates.
The alignment is native typing data; it is not the desired K conversion. -/
structure CovWConvKData (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (w : IotaWitness E) (x T : Expr Nat) where
  canon : KCanonW w x
  nonconstructor : ¬ IsCtorSpine E x
  index : KIndexConvAt E n Γ w
  common : KCommonAt E n Γ w x
  canonical : ctorMajor w = ctorMajorRec w
  align : ∀ {A : Expr Nat}, HasTyT E n Γ x A → TyConvT E n Γ A (majorFamily w)
  source : HasTyT E n Γ (recCall (.const w.recRef w.ls) w.preMajor x) T
  constructor : HasTyT E n Γ (iotaLhsOf w) T
  target : HasTyT E n Γ (iotaRhsOf w) T

/-- The bridge constructs irr, application congruence and legacy iota. -/
theorem covWConv_K_sound {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {w : IotaWitness E} {x T : Expr Nat} (h : CovWConvKData E n Γ w x T) :
    Nonempty (ConvT E n Γ
      (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w) T) := by
  obtain ⟨⟨hP⟩, ⟨hx⟩, ⟨hc⟩⟩ := h.common
  have hc' : HasTyT E n Γ (ctorMajor w) (majorFamily w) := h.canonical ▸ hc
  exact ⟨convT_iotaStarK_alignAt h.align hx hc' hP
    (.iota Γ _ _ T (.of w) h.constructor h.target) h.source⟩

theorem covWConv_K_native {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {w : IotaWitness E} {x T : Expr Nat} (h : CovWConvKData E n Γ w x T) :
    WhStepCK2 E n Γ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w) :=
  .native (.intro h.canon h.nonconstructor h.index h.common)

/-- Variable occurrence inversion supplies the alignment function without choice. -/
theorem covWConv_K_bvar_data {E : ResolvedEnv} {n i : Nat} {Γ : LCtx}
    {w : IotaWitness E} {T : Expr Nat}
    (hk : KCanonW w (.bvar i)) (hi : KIndexConvAt E n Γ w)
    (hc : KCommonAt E n Γ w (.bvar i))
    (ha : ctorMajor w = ctorMajorRec w)
    (hs : HasTyT E n Γ (recCall (.const w.recRef w.ls) w.preMajor (.bvar i)) T)
    (hl : HasTyT E n Γ (iotaLhsOf w) T)
    (hr : HasTyT E n Γ (iotaRhsOf w) T) :
    Nonempty (CovWConvKData E n Γ w (.bvar i) T) := by
  obtain ⟨hx⟩ := hc.2.1
  exact ⟨⟨hk, not_isCtorSpine_bvar, hi, hc, ha,
    fun h => tyConvT_bvar_align h hx, hs, hl, hr⟩⟩

/-- The eta-index call is retained by the derived rule. -/
theorem covWConv_etaIndex_K_data (n : Nat) :
    Nonempty (CovWConvKData eqEnvT n etaEqCtx covWMatrixKWitness (.bvar 0)
      (.sort (.succ .zero))) := by
  obtain ⟨hk, hn, hi, hc⟩ := covWMatrix_K_native_gates n
  obtain ⟨hcanon⟩ := hc.2.2
  apply covWConv_K_bvar_data hk hi hc rfl
  · exact etaIndexRecTy n (.bvar etaEqCtx 0 _ rfl)
  · exact etaIndexRecTy n hcanon
  · exact .sort _ _

theorem covWConv_etaIndex_sound (n : Nat) :
    Nonempty (ConvT eqEnvT n etaEqCtx etaIndexRedex (.sort .zero)
      (.sort (.succ .zero))) := by
  obtain ⟨h⟩ := covWConv_etaIndex_K_data n
  exact covWConv_K_sound h

/-- An arbitrary minor is admitted by the original four gates. -/
def covWConvBadMinor : Expr Nat := .const 999 []
def covWConvBadKSource : Expr Nat :=
  recCall (.const 65 [.succ (.succ .zero)])
    [indexFn, .bvar 1, etaIndexMot, covWConvBadMinor, etaIndex] (.bvar 0)
def covWConvBadKWitness : IotaWitness eqEnvT :=
  eqConvW (fun _ _ h => h) indexFn (.bvar 1) etaIndex etaIndexMot covWConvBadMinor

theorem covWConv_bad_K_gates (n : Nat) :
    KCanonW covWConvBadKWitness (.bvar 0) ∧
    (¬ IsCtorSpine eqEnvT (.bvar 0)) ∧
    KIndexConvAt eqEnvT n etaEqCtx covWConvBadKWitness ∧
    KCommonAt eqEnvT n etaEqCtx covWConvBadKWitness (.bvar 0) := by
  obtain ⟨hi, hc⟩ := eqKGate_of_indexConv (fun _ _ h => h)
    etaIndexMot covWConvBadMinor (indexFnTy eqEnvT n etaEqCtx)
    (etaIndexParamTy n) (etaIndexTy n) (.bvar etaEqCtx 0 _ rfl) (etaIndexConv n)
  exact ⟨Or.inl ⟨rfl, rfl, rfl⟩, not_isCtorSpine_bvar, hi, hc⟩

theorem covWConv_bad_K_native (n : Nat) :
    WhStepCK2 eqEnvT n etaEqCtx covWConvBadKSource covWConvBadMinor := by
  obtain ⟨hk, hn, hi, hc⟩ := covWConv_bad_K_gates n
  exact .native (.intro (w := covWConvBadKWitness) hk hn hi hc)

theorem covWConv_bad_minor_untyped (n : Nat) (Γ : LCtx) (T : Expr Nat) :
    ¬ Nonempty (HasTyT eqEnvT n Γ covWConvBadMinor T) := by
  rintro ⟨h⟩
  have hc := hasTyT_constsIn h
  change ∃ m, eqEnvT.members 999 = some m at hc
  obtain ⟨m, hm⟩ := hc
  cases hm

/-- All gates and native admission are inhabited; the unsorted complete
occurrence is exactly the missing premise, not a typed counterexample. -/
theorem covWConv_four_gates_do_not_imply_conversion (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n etaEqCtx) ∧
    WhStepCK2 eqEnvT n etaEqCtx covWConvBadKSource covWConvBadMinor ∧
    (∀ T, ¬ Nonempty (ConvT eqEnvT n etaEqCtx covWConvBadKSource covWConvBadMinor T)) := by
  refine ⟨⟨pinEqGroupWfT⟩, ⟨etaEqCtxWf n⟩, covWConv_bad_K_native n, ?_⟩
  intro T h
  obtain ⟨hc⟩ := h
  exact covWConv_bad_minor_untyped n etaEqCtx T
    ⟨(convEnds pinEqGroupWfT (etaEqCtxWf n) hc).2.1⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_K_ROOTS
#print axioms CovWConvKData
#print axioms covWConv_K_sound
#print axioms covWConv_K_native
#print axioms covWConv_K_bvar_data
#print axioms covWConv_etaIndex_K_data
#print axioms covWConv_etaIndex_sound
#print axioms covWConv_bad_K_gates
#print axioms covWConv_bad_K_native
#print axioms covWConv_bad_minor_untyped
#print axioms covWConv_four_gates_do_not_imply_conversion
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_K_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

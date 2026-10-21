import rcic.RcicNativeTypedModelKGControls
import rcic.RcicNativeTypedModelKGuard

/-!
# The imported KG agreement at the six native controls

This leaf consumes the renamed `TypedModelKAudit.KG` API and the existing
`TypedModelKGuardAudit` API.  It defines neither guard nor model again.

At the concrete native `WhStepCK2`, KG rejects apart and delta under a binder;
it accepts the beta gap, beta under a binder, head delta and neutral eta.
Conjoining the unchanged native `KIndexConvAt` preserves these six outcomes.
The beta-under-binder acceptance is the imported eta-shaped control; it does
not establish general congruence underneath binders.

The missing closure port below is only one composition instance: head delta
followed by eta.  Its two premises hold and its conclusion is refuted.
These controls do not assert completeness for all native conversions.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2Audit
open Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit
open Rcic.Declarative.NativeValleys.TypedModelKAudit
open Rcic.Declarative.NativeValleys.TypedModelKGuardAudit

/-- The exact six KG agreement measurements, in the order apart, index beta,
beta under a binder, head delta, delta under a binder, and eta.  The beta
readback law is the imported theorem at this concrete native readback. -/
theorem kg_six_agreement_controls (n : Nat) :
    (¬ KG.KIdxAgree eqEnvT (WhStepCK2 eqEnvT n) n
      apartCtx idPiProp apartRight) ∧
    KG.KIdxAgree eqEnvT (WhStepCK2 eqEnvT n) n eqGapCtx (.bvar 1)
      (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)) ∧
    KG.KIdxAgree eqEnvT (WhStepCK2 eqEnvT n) n
      binderEqCtx indexId indexBinderBeta ∧
    KG.KIdxAgree deltaEqEnv (WhStepCK2 deltaEqEnv n) n
      deltaHeadEqCtx indexId (.const 66 []) ∧
    (¬ KG.KIdxAgree deltaEqEnv (WhStepCK2 deltaEqEnv n) n
      deltaUnderBinderEqCtx indexId deltaBinderIndex) ∧
    KG.KIdxAgree eqEnvT (WhStepCK2 eqEnvT n) n
      etaEqCtx (.bvar 1) etaIndex :=
  ⟨KG.not_kIdxAgree_apart n,
    KG.kIdxAgree_eqGap (WhStepCK2 eqEnvT n) n (readbackLaws_whStepCK2 eqEnvT n),
    KG.kIdxAgree_binder (WhStepCK2 eqEnvT n) n,
    KG.kIdxAgree_deltaHead (WhStepCK2 deltaEqEnv n) n deltaHeadEqCtx,
    KG.not_kIdxAgree_deltaBinder n deltaUnderBinderEqCtx,
    KG.kIdxAgree_etaIndex (WhStepCK2 eqEnvT n) n⟩

/-- The same six measurements after adjoining the original native index
certificate at each exact legacy witness.  The apart entry refutes the
conjunction; it does not assert native nonconvertibility of the apart indices. -/
theorem kg_six_native_conjunction_controls (n : Nat) :
    (¬ (KIndexConvAt eqEnvT n apartCtx
        (eqConvW (fun _ _ h => h) (.sort .zero) idPiProp apartRight
          apartMot (.sort .zero)) ∧
      KG.KIdxAgree eqEnvT (WhStepCK2 eqEnvT n) n
        apartCtx idPiProp apartRight)) ∧
    (KIndexConvAt eqEnvT n eqGapCtx eqGapW ∧
      KG.KIdxAgree eqEnvT (WhStepCK2 eqEnvT n) n eqGapCtx (.bvar 1)
        (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1))) ∧
    (KIndexConvAt eqEnvT n binderEqCtx
        (eqConvW (fun _ _ h => h) indexFn indexId indexBinderBeta
          binderIndexMot (.sort .zero)) ∧
      KG.KIdxAgree eqEnvT (WhStepCK2 eqEnvT n) n
        binderEqCtx indexId indexBinderBeta) ∧
    (KIndexConvAt deltaEqEnv n deltaHeadEqCtx
        (eqConvW deltaEqExtends indexFn indexId (.const 66 [])
          binderIndexMot (.sort .zero)) ∧
      KG.KIdxAgree deltaEqEnv (WhStepCK2 deltaEqEnv n) n
        deltaHeadEqCtx indexId (.const 66 [])) ∧
    (¬ (KIndexConvAt deltaEqEnv n deltaUnderBinderEqCtx
        (eqConvW deltaEqExtends indexFn indexId deltaBinderIndex
          binderIndexMot (.sort .zero)) ∧
      KG.KIdxAgree deltaEqEnv (WhStepCK2 deltaEqEnv n) n
        deltaUnderBinderEqCtx indexId deltaBinderIndex)) ∧
    (KIndexConvAt eqEnvT n etaEqCtx
        (eqConvW (fun _ _ h => h) indexFn (.bvar 1) etaIndex
          etaIndexMot (.sort .zero)) ∧
      KG.KIdxAgree eqEnvT (WhStepCK2 eqEnvT n) n
        etaEqCtx (.bvar 1) etaIndex) := by
  obtain ⟨ha, hg, hb, hd, hdb, he⟩ := kg_six_agreement_controls n
  refine ⟨(fun h => ha h.2), ⟨(kIndexGuardAt_eqGap n).1, hg⟩,
    ⟨(kIndexGuardAt_binder n).1, hb⟩,
    ⟨(kIndexGuardAt_delta n).1, hd⟩, (fun h => hdb h.2), ?_⟩
  exact ⟨(eqKGate_of_indexConv (fun _ _ h => h) etaIndexMot (.sort .zero)
    (indexFnTy eqEnvT n etaEqCtx) (etaIndexParamTy n) (etaIndexTy n)
    (.bvar etaEqCtx 0 _ rfl) (etaIndexConv n)).1, he⟩

/-- The six measurements use admitted environments, well-formed native
contexts and actual native typings of the complete recursor terms.  The
beta-gap typing is obtained from its imported native conversion by the
existing endpoint theorem, without reconstructing that derivation. -/
theorem kg_six_native_typing_controls (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (EnvWfT deltaEqEnv) ∧
    (Nonempty (CtxWfT eqEnvT n apartCtx) ∧
      Nonempty (HasTyT eqEnvT n apartCtx apartRec (.sort (.succ .zero)))) ∧
    (Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
      Nonempty (HasTyT eqEnvT n eqGapCtx eqGapRedex (.sort (.succ .zero)))) ∧
    (Nonempty (CtxWfT eqEnvT n binderEqCtx) ∧
      Nonempty (HasTyT eqEnvT n binderEqCtx binderIndexRedex (.sort (.succ .zero)))) ∧
    (Nonempty (CtxWfT deltaEqEnv n deltaHeadEqCtx) ∧
      Nonempty (HasTyT deltaEqEnv n deltaHeadEqCtx
        (deltaRedex (.const 66 [])) (.sort (.succ .zero)))) ∧
    (Nonempty (CtxWfT deltaEqEnv n deltaUnderBinderEqCtx) ∧
      Nonempty (HasTyT deltaEqEnv n deltaUnderBinderEqCtx
        (deltaRedex deltaBinderIndex) (.sort (.succ .zero)))) ∧
    (Nonempty (CtxWfT eqEnvT n etaEqCtx) ∧
      Nonempty (HasTyT eqEnvT n etaEqCtx etaIndexRedex (.sort (.succ .zero)))) := by
  obtain ⟨hΓg⟩ := eqGapCtx_wf n
  obtain ⟨cg⟩ := eqGap_conv n
  exact ⟨⟨pinEqGroupWfT⟩, ⟨deltaEqEnvWf⟩,
    ⟨⟨apartCtx_wf n⟩, apartRec_typed n⟩,
    ⟨⟨hΓg⟩, (convT_endpoints pinEqGroupWfT hΓg cg).2⟩,
    ⟨⟨binderEqCtxWf n⟩,
      ⟨binderIndexRecTy n binderEqCtx (.bvar binderEqCtx 0 _ rfl)⟩⟩,
    ⟨⟨deltaHeadEqCtxWf n⟩,
      ⟨deltaRecTy n deltaHeadEqCtx (deltaConstTy n deltaHeadEqCtx)
        (.bvar deltaHeadEqCtx 0 _ rfl)⟩⟩,
    ⟨⟨deltaUnderBinderEqCtxWf n⟩,
      ⟨deltaRecTy n deltaUnderBinderEqCtx (deltaBinderTy n deltaUnderBinderEqCtx)
        (.bvar deltaUnderBinderEqCtx 0 _ rfl)⟩⟩,
    ⟨⟨etaEqCtxWf n⟩, ⟨etaIndexRecTy n (.bvar etaEqCtx 0 _ rfl)⟩⟩⟩

/-- The rejected delta-under-binder conjunction nevertheless has its native
index certificate, native common typing and full native K head.  Its context
and complete source term also have actual native typing derivations. -/
theorem kg_deltaBinder_native_obstruction (n : Nat) :
    Nonempty (EnvWfT deltaEqEnv) ∧
    Nonempty (CtxWfT deltaEqEnv n deltaUnderBinderEqCtx) ∧
    Nonempty (HasTyT deltaEqEnv n deltaUnderBinderEqCtx
      (deltaRedex deltaBinderIndex) (.sort (.succ .zero))) ∧
    Nonempty (ConvT deltaEqEnv n deltaUnderBinderEqCtx
      deltaBinderIndex indexId indexFn) ∧
    KIndexConvAt deltaEqEnv n deltaUnderBinderEqCtx
      (eqConvW deltaEqExtends indexFn indexId deltaBinderIndex
        binderIndexMot (.sort .zero)) ∧
    KCommonAt deltaEqEnv n deltaUnderBinderEqCtx
      (eqConvW deltaEqExtends indexFn indexId deltaBinderIndex
        binderIndexMot (.sort .zero)) (.bvar 0) ∧
    KNativeHead deltaEqEnv n deltaUnderBinderEqCtx
      (deltaRedex deltaBinderIndex) (.sort .zero) ∧
    (¬ (KIndexConvAt deltaEqEnv n deltaUnderBinderEqCtx
        (eqConvW deltaEqExtends indexFn indexId deltaBinderIndex
          binderIndexMot (.sort .zero)) ∧
      KG.KIdxAgree deltaEqEnv (WhStepCK2 deltaEqEnv n) n
        deltaUnderBinderEqCtx indexId deltaBinderIndex)) := by
  obtain ⟨hi, hc⟩ := eqKGate_of_indexConv deltaEqExtends binderIndexMot (.sort .zero)
    (indexFnTy deltaEqEnv n deltaUnderBinderEqCtx)
    (indexIdTy deltaEqEnv n deltaUnderBinderEqCtx)
    (deltaBinderTy n deltaUnderBinderEqCtx) (.bvar deltaUnderBinderEqCtx 0 _ rfl)
    (deltaBinderIndexConv n deltaUnderBinderEqCtx)
  exact ⟨⟨deltaEqEnvWf⟩, ⟨deltaUnderBinderEqCtxWf n⟩,
    ⟨deltaRecTy n deltaUnderBinderEqCtx (deltaBinderTy n deltaUnderBinderEqCtx)
      (.bvar deltaUnderBinderEqCtx 0 _ rfl)⟩,
    ⟨deltaBinderIndexConv n deltaUnderBinderEqCtx⟩, hi, hc,
    kNativeHead_delta_under_binder n,
    fun h => KG.not_kIdxAgree_deltaBinder n deltaUnderBinderEqCtx h.2⟩

/-- The two imported additional guards cross on the admitted fixtures: KG
accepts neutral eta where the strict semantic guard fails, while the strict
semantic guard accepts delta under a binder where KG fails. -/
theorem kg_and_strict_guard_cross_controls (n : Nat) :
    (KG.KIdxAgree eqEnvT (WhStepCK2 eqEnvT n) n etaEqCtx (.bvar 1) etaIndex ∧
      ¬ KIndexGuardAt eqEnvT n etaEqCtx
        (eqConvW (fun _ _ h => h) indexFn (.bvar 1) etaIndex
          etaIndexMot (.sort .zero))) ∧
    (KIndexGuardAt deltaEqEnv n deltaUnderBinderEqCtx
        (eqConvW deltaEqExtends indexFn indexId deltaBinderIndex
          binderIndexMot (.sort .zero)) ∧
      ¬ KG.KIdxAgree deltaEqEnv (WhStepCK2 deltaEqEnv n) n
        deltaUnderBinderEqCtx indexId deltaBinderIndex) :=
  ⟨⟨KG.kIdxAgree_etaIndex (WhStepCK2 eqEnvT n) n, not_kIndexGuardAt_eta n⟩,
    ⟨kIndexGuardAt_delta_under_binder n,
      KG.not_kIdxAgree_deltaBinder n deltaUnderBinderEqCtx⟩⟩

/-- The checked constant agrees with its eta expansion, using its imported
native function typing. -/
theorem kg_deltaConst_eta (R : Readback) (n : Nat) (Γ : LCtx) :
    KG.KIdxAgree deltaEqEnv R n Γ (.const 66 []) deltaBinderIndex :=
  .etaL (A := .sort .zero) (B := .sort .zero) (f := .const 66 [])
    (deltaConstTy n Γ)

/-- Only the composition instance required by the delta-under-binder control:
head delta from `indexId` to the constant, followed by eta of that constant.
This is a named missing closure port, not a new agreement relation. -/
def KGDeltaEtaCompositionAt (n : Nat) : Prop :=
  KG.KIdxAgree deltaEqEnv (WhStepCK2 deltaEqEnv n) n
      deltaUnderBinderEqCtx indexId (.const 66 []) →
  KG.KIdxAgree deltaEqEnv (WhStepCK2 deltaEqEnv n) n
      deltaUnderBinderEqCtx (.const 66 []) deltaBinderIndex →
  KG.KIdxAgree deltaEqEnv (WhStepCK2 deltaEqEnv n) n
      deltaUnderBinderEqCtx indexId deltaBinderIndex

/-- Both premises of the single missing composition instance are inhabited;
the imported endpoint rejection refutes even this restricted closure port. -/
theorem not_kgDeltaEtaCompositionAt (n : Nat) :
    ¬ KGDeltaEtaCompositionAt n := by
  intro h
  exact KG.not_kIdxAgree_deltaBinder n deltaUnderBinderEqCtx
    (h (KG.kIdxAgree_deltaHead (WhStepCK2 deltaEqEnv n) n deltaUnderBinderEqCtx)
      (kg_deltaConst_eta (WhStepCK2 deltaEqEnv n) n deltaUnderBinderEqCtx))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_K_GUARD_ROOTS
#print axioms kg_six_agreement_controls
#print axioms kg_six_native_conjunction_controls
#print axioms kg_six_native_typing_controls
#print axioms kg_deltaBinder_native_obstruction
#print axioms kg_and_strict_guard_cross_controls
#print axioms kg_deltaConst_eta
#print axioms KGDeltaEtaCompositionAt
#print axioms not_kgDeltaEtaCompositionAt
-- END RCIC_NATIVE_TYPED_MODEL_COV_K_GUARD_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovKGuardAudit

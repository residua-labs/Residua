import rcic.RcicNativeTypedModelCovWConvHo
import rcic.RcicNativeTypedModelCovWConvAndK
import rcic.RcicNativeTypedModelCovWConvLocal

/-! Actual native and semantic premises for the remeasured controls.
The M result below is a shared strictly typed positive observation, not full
observation equality. Apart retention is explicitly an unsupplied goal.
The realization interface records typed closing substitutions and all demands;
it does not assert substitution or conversion invariance. closure_claim = 0. -/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit
open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelKAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelCovTAudit TypedModelCovWAudit TypedModelCovWIrrelAudit
open TypedModelCovWMatrixAudit TypedModelCovWNativeAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit ReadbackCK2IndexAudit
open ReadbackCK2ModelObstructionAudit

structure CovWConvRealized (E : ResolvedEnv) (arity stage : Nat) (Γ : LCtx)
    (ρ : EnvWConvR) (σ : SubstT) : Prop where
  typing : TypedSubstT E arity [] σ Γ
  observed : ∀ i c, ρ i c → ApproxTKWConvStage E arity stage [] EnvWConvR.bot (σ i) c

theorem covWConv_realized_bot {E : ResolvedEnv} {arity stage : Nat} {Γ : LCtx}
    {σ : SubstT} (ht : TypedSubstT E arity [] σ Γ) :
    CovWConvRealized E arity stage Γ EnvWConvR.bot σ := by
  refine ⟨ht, ?_⟩
  intro i c hc
  cases hc
  exact ⟨.bot _ _ _, by
    simp [covWConvCoarse, covWConvRawErase, TypedModelCovWIrrelAudit.covWIrrelErase,
      covTObservationBudget]⟩

theorem covWConv_realized_nil (E : ResolvedEnv) (arity stage : Nat) :
    CovWConvRealized E arity stage [] EnvWConvR.bot SubstT.id :=
  covWConv_realized_bot (covWNative_realized_nil E arity stage).typing

theorem covWConv_M_realized (n stage : Nat) :
    CovWConvRealized eqEnvT n stage etaEqCtx EnvWConvR.bot covWMatrixKSubst :=
  covWConv_realized_bot (covWMatrixKSubst_typed n)

theorem covWConv_prop_demand_typed (E : ResolvedEnv) :
    CTySConv E (.sort (LevelCode.ofLevel .zero))
      (.sort (LevelCode.ofLevel (.succ .zero))) := by
  refine ⟨.sort .zero, .sort (.succ .zero), rfl, rfl, ?_⟩
  refine .sortTy (.sort .zero (.succ .zero) (fun _ => rfl)) ?_
  change CTyS E .prop .sort
  rw [CTyS]
  exact Or.inr .prop

theorem covWConv_prop_demand_nonbottom :
    CptWConv.sort (LevelCode.ofLevel .zero) ≠ .bot := by
  intro h
  cases h

/-- All explicitly defined typing/observation/realization guards of the
closed W fixtures have actual witnesses. Both terms still observe only bot. -/
theorem covWConv_Ho_guards_inhabited (n stage : Nat) :
    CovWConvRealized covUHoEnv n stage [] EnvWConvR.bot SubstT.id ∧
    CovWConvObservation covUHoEnv n [] EnvWConvR.bot (.sort (.succ .zero))
      (.sort (LevelCode.ofLevel (.succ .zero))) ∧
    CTySConv covUHoEnv (.sort (LevelCode.ofLevel .zero))
      (.sort (LevelCode.ofLevel (.succ .zero))) ∧
    CptWConv.sort (LevelCode.ofLevel .zero) ≠ .bot :=
  ⟨covWConv_realized_nil _ _ _, covWConv_observation_of (.sort _ _ _),
    covWConv_prop_demand_typed _, covWConv_prop_demand_nonbottom⟩

/-- M retains its native conversion and a shared strict nonbottom demand.
No all-observation equality is hidden in this control. -/
theorem covWConv_M_shared_typed (n : Nat) (ρ : EnvWConvR) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n etaEqCtx) ∧
    Nonempty (HasTyT eqEnvT n etaEqCtx etaIndexRedex (.sort (.succ .zero))) ∧
    Nonempty (HasTyT eqEnvT n etaEqCtx covWMatrixMajorCtorCall (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n etaEqCtx etaIndexRedex covWMatrixMajorCtorCall
      (.sort (.succ .zero))) ∧
    CovWConvObservation eqEnvT n etaEqCtx ρ (.sort (.succ .zero))
      (.sort (LevelCode.ofLevel (.succ .zero))) ∧
    CTySConv eqEnvT (.sort (LevelCode.ofLevel .zero))
      (.sort (LevelCode.ofLevel (.succ .zero))) ∧
    CovWConvObservation eqEnvT n etaEqCtx ρ etaIndexRedex
      (.sort (LevelCode.ofLevel .zero)) ∧
    CovWConvObservation eqEnvT n etaEqCtx ρ covWMatrixMajorCtorCall
      (.sort (LevelCode.ofLevel .zero)) := by
  refine ⟨⟨pinEqGroupWfT⟩, ⟨etaEqCtxWf n⟩, ⟨covWMatrixMajorNeutralCall_ty n⟩,
    ⟨covWMatrixMajorCtorCall_ty n⟩, ⟨covWMatrixMajorCongr n⟩,
    covWConv_observation_of (.sort _ _ _), covWConv_prop_demand_typed _,
    covWConv_observation_of (covWConv_etaIndex_K_observed n ρ), ?_⟩
  exact covWConv_observation_of (covWConv_eqIota_observed n ρ)

/-- RI keeps the legacy conversion, both typings, the type observation and
strict positive demand; the unchanged raw exclusion is recorded separately. -/
theorem covWConv_RI_inhabited (n : Nat) :
    CovWMatrixNativePair trueEnvU n (iotaLhsOf wTrueRecU) (.sort .zero)
      (.sort (.succ .zero)) (.succ (.succ .zero)) ∧
    CovWConvRealized trueEnvU n 1 [] EnvWConvR.bot SubstT.id ∧
    CovWConvObservation trueEnvU n [] EnvWConvR.bot (.sort (.succ .zero))
      (.sort (LevelCode.ofLevel (.succ .zero))) ∧
    CTySConv trueEnvU (.sort (LevelCode.ofLevel .zero))
      (.sort (LevelCode.ofLevel (.succ .zero))) ∧
    CovWConvObservation trueEnvU n [] EnvWConvR.bot (iotaLhsOf wTrueRecU)
      (.sort (LevelCode.ofLevel .zero)) ∧
    ¬ CovWIrrelRawObservation trueEnvU n EnvWIrrel.bot (iotaLhsOf wTrueRecU) .prop :=
  ⟨covWMatrix_raw_true_iota_native n, covWConv_realized_nil _ _ _,
    covWConv_observation_of (.sort _ _ _), covWConv_prop_demand_typed _,
    (covWConv_trueIota_positive n _).1,
    covWMatrix_raw_true_iota_source_excluded n EnvWIrrel.bot⟩

/-- This exact full-grammar control remains unsupplied. -/
def CovWConvApartRetention (n : Nat) : Prop :=
  ∀ (ρ : EnvWConvR) (c : CptWConvR),
    ApproxTKWConv eqEnvT n apartCtx ρ apartRec c → c = .bot

theorem covWConv_apart_inhabited (n : Nat) (ρ : EnvWConvR) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n apartCtx) ∧
    Nonempty (HasTyT eqEnvT n apartCtx apartRec (.sort (.succ .zero))) ∧
    CovWConvObservation eqEnvT n apartCtx ρ apartRec .bot :=
  ⟨⟨pinEqGroupWfT⟩, ⟨apartCtx_wf n⟩, apartRec_typed n, ⟨.bot, rfl, .bot _ _ _⟩⟩

/-- An explicit consumer, not a separation supplier: the extra K occurrence
data cannot evade the unchanged native index gate. -/
theorem covWConv_apart_direct_K_blocked (n : Nat)
    (hsep : CovWNativeApartIndexSeparation n)
    {w : IotaWitness eqEnvT} {x T : Expr Nat}
    (hs : recCall (.const w.recRef w.ls) w.preMajor x = apartRec) :
    ¬ Nonempty (CovWConvKData eqEnvT n apartCtx w x T) := by
  rintro ⟨hk⟩
  apply covWNative_apart_direct_K_blocked n hsep (iotaRhsOf w)
  rw [← hs]
  exact .intro hk.canon hk.nonconstructor hk.index hk.common


/-- The concrete W head equality also supplies every finite binder test.
The test holes are written at their displayed binder depth. -/
theorem covWConv_Ho_beta_binder_tests (n : Nat) (Γ : LCtx) (ρ : EnvWConvR)
    (D : Expr Nat) (rows : List (List CptWConvR × CptWConvR)) :
    (∀ s ∈ rows, CovWConvObservation covUHoEnv n (.assumption D :: Γ)
      (EnvWConvR.cons (demandWConvR s.1) ρ) covWNativeHoBetaSource (covWConvCode s.2)) ↔
    (∀ s ∈ rows, CovWConvObservation covUHoEnv n (.assumption D :: Γ)
      (EnvWConvR.cons (demandWConvR s.1) ρ) covWMatrixIotaSource (covWConvCode s.2)) := by
  constructor
  · intro h s hs
    exact (covWConv_Ho_beta_all_observations n _ _ _).mp (h s hs)
  · intro h s hs
    exact (covWConv_Ho_beta_all_observations n _ _ _).mpr (h s hs)

theorem covWConv_Ho_zeta_binder_tests (n : Nat) (Γ : LCtx) (ρ : EnvWConvR)
    (D : Expr Nat) (rows : List (List CptWConvR × CptWConvR)) :
    (∀ s ∈ rows, CovWConvObservation covUHoEnv n (.assumption D :: Γ)
      (EnvWConvR.cons (demandWConvR s.1) ρ) covWNativeHoLetSource (covWConvCode s.2)) ↔
    (∀ s ∈ rows, CovWConvObservation covUHoEnv n (.assumption D :: Γ)
      (EnvWConvR.cons (demandWConvR s.1) ρ) covWMatrixIotaSource (covWConvCode s.2)) := by
  constructor
  · intro h s hs
    exact (covWConv_Ho_zeta_all_observations n _ _ _).mp (h s hs)
  · intro h s hs
    exact (covWConv_Ho_zeta_all_observations n _ _ _).mpr (h s hs)

#print axioms covWConv_Ho_beta_binder_tests
#print axioms covWConv_Ho_zeta_binder_tests

#print axioms CovWConvRealized
#print axioms covWConv_realized_bot
#print axioms covWConv_realized_nil
#print axioms covWConv_M_realized
#print axioms covWConv_prop_demand_typed
#print axioms covWConv_prop_demand_nonbottom
#print axioms covWConv_Ho_guards_inhabited
#print axioms covWConv_M_shared_typed
#print axioms covWConv_RI_inhabited
#print axioms CovWConvApartRetention
#print axioms covWConv_apart_inhabited
#print axioms covWConv_apart_direct_K_blocked

end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

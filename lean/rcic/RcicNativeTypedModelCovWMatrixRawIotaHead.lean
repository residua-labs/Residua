import rcic.RcicNativeTypedModelCovWMatrixCore
import rcic.RcicNativeTypedModelCovWMatrixKHead

/-!
# Legacy ordinary iota at a raw observation head

Raw observations have no proposition-recursion rule. An actual admitted,
closed legacy True constructor-major iota step therefore has a bottom-only
source, while its `Sort 0` RHS supplies the strict nonbottom observation
`prop`. Its native conversion, typing, finite valuation and raw realizer
are supplied. The same raw head exclusion applies to Eq, and hence to the
actual native K example from KHead. This module does not transfer raw
absence to the guarded relation. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelKAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelAudit.TypingFin TypedModelW6IotaAudit
open TypedModelCovWAudit TypedModelCovTAudit TypedModelCovVAudit TypedModelCovWIrrelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2InputsAudit ReadbackCK2IndexAudit

/-- Every raw proposition-recursion constant is bottom-only. -/
theorem covWMatrix_raw_prop_const_only_bot {E : ResolvedEnv} {n : Nat}
    (w : IotaWitnessS E) (hP : PropFamilyS w)
    {ρ : EnvWIrrel} {r : Nat} {ls : List Level} {c : CptWIrrel}
    (hr : r = w.recRef) (h : ApproxTWIrrel E n ρ (.const r ls) c) : c = .bot := by
  cases h with
  | bot => rfl
  | const _ _ _ hrigid _ =>
      subst r
      exact (not_rigidConst_of_recursor w hrigid).elim
  | delta hd _ =>
      subst r
      exact (not_deltaConst_of_recursor w hd).elim
  | recursor _ hnp _ _ _ =>
      exact (hnp ((propFamilyS_iff_recRef_eq hr).mpr hP)).elim

theorem covWMatrix_raw_app_only_bot {E : ResolvedEnv} {n : Nat}
    {ρ : EnvWIrrel} {f a : Expr Nat} {c : CptWIrrel}
    (hf : ∀ u, ApproxTWIrrel E n ρ f u → u = .bot)
    (h : ApproxTWIrrel E n ρ (.app f a) c) : c = .bot := by
  cases h with
  | bot => rfl
  | app hfun _ _ => cases hf _ hfun
  | appSpine hfun _ _ => cases hf _ hfun

theorem covWMatrix_raw_foldApps_only_bot {E : ResolvedEnv} {n : Nat}
    {ρ : EnvWIrrel} (args : List (Expr Nat)) : ∀ f : Expr Nat,
    (∀ u, ApproxTWIrrel E n ρ f u → u = .bot) →
    ∀ c, ApproxTWIrrel E n ρ (foldApps f args) c → c = .bot := by
  induction args with
  | nil => intro f hf c hc; exact hf c hc
  | cons a args ih =>
      intro f hf c hc
      exact ih (.app f a) (fun _ h => covWMatrix_raw_app_only_bot hf h) c hc

theorem covWMatrix_raw_eq_rec_only_bot {n : Nat} {ρ : EnvWIrrel}
    {ls : List Level} {c : CptWIrrel}
    (h : ApproxTWIrrel eqEnvT n ρ (.const 65 ls) c) : c = .bot := by
  obtain ⟨w, hr⟩ := eqRec_structured_exists
  exact covWMatrix_raw_prop_const_only_bot w (eqRec_model_schema w hr).1 hr.symm h

theorem covWMatrix_raw_legacy_iota_source_only_bot {n : Nat} {ρ : EnvWIrrel}
    {c : CptWIrrel} (h : ApproxTWIrrel eqEnvT n ρ (iotaLhsOf eqGapW) c) :
    c = .bot := by
  change ApproxTWIrrel eqEnvT n ρ
    (foldApps (.const 65 [.succ (.succ .zero)])
      [.bvar 2, .bvar 1, eqGapMot, .sort .zero,
        .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1), ctorMajor eqGapW]) c at h
  exact covWMatrix_raw_foldApps_only_bot _ _
    (fun _ hh => covWMatrix_raw_eq_rec_only_bot hh) c h

theorem covWMatrix_raw_legacy_iota_source_excluded (n : Nat) (ρ : EnvWIrrel) :
    ¬ CovWIrrelRawObservation eqEnvT n ρ (iotaLhsOf eqGapW) .prop := by
  rintro ⟨d, he, hd⟩
  have hb := covWMatrix_raw_legacy_iota_source_only_bot hd
  subst d
  cases he

theorem covWMatrix_raw_legacy_iota_rhs_observed (n : Nat) (ρ : EnvWIrrel) :
    CovWIrrelRawObservation eqEnvT n ρ (iotaRhsOf eqGapW) .prop :=
  ⟨.prop, rfl, .sort ρ .zero⟩

theorem covWMatrix_raw_legacy_iota_type_observed (n : Nat) (ρ : EnvWIrrel) :
    CovWIrrelRawObservation eqEnvT n ρ (.sort (.succ .zero)) .sort :=
  ⟨.sort, rfl, .sort ρ (.succ .zero)⟩

theorem covWMatrix_raw_true_iota_source_only_bot {n : Nat} {ρ : EnvWIrrel}
    {c : CptWIrrel} (h : ApproxTWIrrel trueEnvU n ρ (iotaLhsOf wTrueRecU) c) :
    c = .bot := by
  change ApproxTWIrrel trueEnvU n ρ
    (foldApps (.const 2 [.succ (.succ .zero)])
      [kMot, .sort .zero, .const 1 []]) c at h
  exact covWMatrix_raw_foldApps_only_bot _ _
    (fun _ hh => covWMatrix_raw_prop_const_only_bot covVTrueWitness rfl rfl hh) c h

theorem covWMatrix_raw_true_iota_source_excluded (n : Nat) (ρ : EnvWIrrel) :
    ¬ CovWIrrelRawObservation trueEnvU n ρ (iotaLhsOf wTrueRecU) .prop := by
  rintro ⟨d, he, hd⟩
  have hb := covWMatrix_raw_true_iota_source_only_bot hd
  subst d
  cases he

/-- This is the legacy `ConvT.iota` generator at an actual closed constructor
major, with both native endpoint typings supplied. -/
theorem covWMatrix_raw_true_iota_native (n : Nat) :
    CovWMatrixNativePair trueEnvU n (iotaLhsOf wTrueRecU) (.sort .zero)
      (.sort (.succ .zero)) (.succ (.succ .zero)) where
  envWf := ⟨trueEnvUWfT⟩
  ctxWf := ⟨.nil⟩
  leftTy := ⟨trueEnvUL_tyS1⟩
  rightTy := ⟨.sort [] .zero⟩
  typeTy := ⟨.sort [] (.succ .zero)⟩
  conversion := ⟨.iota [] _ _ _ (.of wTrueRecU) trueEnvUL_tyS1 (.sort [] .zero)⟩

theorem covWMatrix_raw_true_iota_step (n : Nat) :
    WhStepCK2 trueEnvU n [] (iotaLhsOf wTrueRecU) (.sort .zero) :=
  .ctx (.iota (.ofU wTrueRecU))

/-- Every premise of the closed raw strict-typed failure is inhabited. -/
theorem covWMatrix_raw_true_iota_failure (n : Nat) :
    CovWMatrixRawClosedFailure trueEnvU n 1 (iotaLhsOf wTrueRecU) (.sort .zero)
      (.sort (.succ .zero)) (.succ (.succ .zero)) .prop .sort where
  native := covWMatrix_raw_true_iota_native n
  typedSubst := (covWIrrel_realized_nil trueEnvU n 1).typing
  realized := by
    intro i c hc
    cases hc
    exact ⟨.bot _ _, by simp [covWIrrelErase, covTObservationBudget]⟩
  erasedValuation := envTypedFinAtT_nil _ _
  erasedCoherence := fun _ _ hv => Option.noConfusion hv
  typeObserved := ⟨.sort, rfl, .sort EnvWIrrel.bot (.succ .zero)⟩
  demand := by
    rw [CTyS]
    exact Or.inr .prop
  nonbottom := fun h => CptT.noConfusion h
  rightObserved := ⟨.prop, rfl, .sort EnvWIrrel.bot .zero⟩
  leftAbsent := covWMatrix_raw_true_iota_source_excluded n EnvWIrrel.bot

theorem covWMatrix_raw_true_iota_not_invariant (n : Nat) :
    ¬ CovWMatrixRawTypedInvariant trueEnvU n EnvWIrrel.bot (.sort (.succ .zero))
      (iotaLhsOf wTrueRecU) (.sort .zero) :=
  covWMatrix_rawClosedFailure_refutes (covWMatrix_raw_true_iota_failure n)

theorem covWMatrix_raw_K_source_only_bot {n : Nat} {ρ : EnvWIrrel}
    {c : CptWIrrel} (h : ApproxTWIrrel eqEnvT n ρ etaIndexRedex c) : c = .bot := by
  change ApproxTWIrrel eqEnvT n ρ
    (foldApps (.const 65 [.succ (.succ .zero)])
      [indexFn, .bvar 1, etaIndexMot, .sort .zero, etaIndex, .bvar 0]) c at h
  exact covWMatrix_raw_foldApps_only_bot _ _
    (fun _ hh => covWMatrix_raw_eq_rec_only_bot hh) c h

theorem covWMatrix_raw_K_source_excluded (n : Nat) (ρ : EnvWIrrel) :
    ¬ CovWIrrelRawObservation eqEnvT n ρ etaIndexRedex .prop := by
  rintro ⟨d, he, hd⟩
  have hb := covWMatrix_raw_K_source_only_bot hd
  subst d
  cases he

/-- The same actual closing substitution as KHead realizes the raw bottom
valuation. No substituted-source exclusion is claimed. -/
theorem covWMatrix_raw_K_realized (n stage : Nat) :
    TypedSubstT eqEnvT n [] covWMatrixKSubst etaEqCtx ∧
    (∀ i c, EnvWIrrel.bot i c →
      ApproxTWIrrel eqEnvT n EnvWIrrel.bot (covWMatrixKSubst i) c ∧
      covTObservationBudget (covWIrrelErase c) ≤ stage) := by
  refine ⟨covWMatrixKSubst_typed n, ?_⟩
  intro i c hc
  cases hc
  exact ⟨.bot _ _, by simp [covWIrrelErase, covTObservationBudget]⟩

theorem covWMatrix_raw_K_erased_valuation :
    EnvTypedFinAtT (⟨ApproxTW eqEnvT⟩ : CtxModelT eqEnvT)
      etaEqCtx (covWIrrelEnvErase EnvWIrrel.bot) := by
  rw [covWIrrel_env_erase_bot]
  exact envTypedFinAtT_bot _ (fun ρ e => ApproxTW.bot ρ e) etaEqCtx

theorem covWMatrix_raw_K_erased_coherence :
    CtxEnvM (⟨ApproxTW eqEnvT⟩ : CtxModelT eqEnvT)
      etaEqCtx (covWIrrelEnvErase EnvWIrrel.bot) := by
  intro i v hv
  cases i with
  | zero => cases hv
  | succ i =>
      cases i with
      | zero => cases hv
      | succ i => simp [etaEqCtx, lookupValue] at hv

theorem covWMatrix_raw_K_not_invariant (n : Nat) :
    ¬ CovWMatrixRawTypedInvariant eqEnvT n EnvWIrrel.bot (.sort (.succ .zero))
      etaIndexRedex (.sort .zero) := by
  intro h
  exact covWMatrix_raw_K_source_excluded n EnvWIrrel.bot
    ((h .sort .prop (covWMatrix_raw_legacy_iota_type_observed n EnvWIrrel.bot)
      covWMatrix_K_compact_typed).mpr
        ⟨.prop, rfl, .sort EnvWIrrel.bot .zero⟩)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_RAW_IOTA_HEAD_ROOTS
#print axioms covWMatrix_raw_prop_const_only_bot
#print axioms covWMatrix_raw_app_only_bot
#print axioms covWMatrix_raw_foldApps_only_bot
#print axioms covWMatrix_raw_eq_rec_only_bot
#print axioms covWMatrix_raw_legacy_iota_source_only_bot
#print axioms covWMatrix_raw_legacy_iota_source_excluded
#print axioms covWMatrix_raw_legacy_iota_rhs_observed
#print axioms covWMatrix_raw_legacy_iota_type_observed
#print axioms covWMatrix_raw_true_iota_source_only_bot
#print axioms covWMatrix_raw_true_iota_source_excluded
#print axioms covWMatrix_raw_true_iota_native
#print axioms covWMatrix_raw_true_iota_step
#print axioms covWMatrix_raw_true_iota_failure
#print axioms covWMatrix_raw_true_iota_not_invariant
#print axioms covWMatrix_raw_K_source_only_bot
#print axioms covWMatrix_raw_K_source_excluded
#print axioms covWMatrix_raw_K_realized
#print axioms covWMatrix_raw_K_erased_valuation
#print axioms covWMatrix_raw_K_erased_coherence
#print axioms covWMatrix_raw_K_not_invariant
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_RAW_IOTA_HEAD_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit

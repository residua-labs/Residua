import rcic.RcicNativeTypedModelCovWNativeFixtures
import rcic.RcicNativeTypedModelCovWIrrelRecControl

/-! # Fresh native-aligned Nat recursion control
The schema reads only the two empty minor rows. The closed native realizer
supplies the constructor observation using actual argument typing.
Raw observations are retained unchanged. `closure_claim = 0`. -/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelAudit.TypingFin TypedModelKAudit TypedModelKFragmentAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open TypedModelCovPAudit TypedModelCovQAudit TypedModelCovRAudit TypedModelCovSAudit
open TypedModelCovTAudit TypedModelCovWAudit TypedModelCovWEtaAudit TypedModelCovWIrrelAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem covWNativeRec_minor (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative natEnvU n Γ ρ covTRecMinor covWIrrelRecMinorCode := by
  refine .lam (.bot _ _ _) ?_ ?_ ?_
  · intro row hrow c hc
    obtain rfl := List.mem_singleton.mp hrow
    exact (List.not_mem_nil _ hc).elim
  · exact ⟨([], .lam [([], .prop)]), List.mem_singleton_self _, CptWIrrel.noConfusion⟩
  · intro row hrow
    obtain rfl := List.mem_singleton.mp hrow
    refine .lam (.bot _ _ _) ?_ ?_ ?_
    · intro inner hinner c hc
      obtain rfl := List.mem_singleton.mp hinner
      exact (List.not_mem_nil _ hc).elim
    · exact ⟨([], .prop), List.mem_singleton_self _, CptWIrrel.noConfusion⟩
    · intro inner hinner
      obtain rfl := List.mem_singleton.mp hinner
      exact .sort _ _ .zero

/-- The schema observes only the minor's two empty-demand graph rows. -/
theorem covWNativeRec_schema (n : Nat) (Γ : LCtx) :
    ApproxTKWNative natEnvU n Γ
      (EnvWIrrel.pushArgs
        (([[], [], [covWIrrelRecMinorCode]] ++ [[]]).map demandWIrrel) EnvWIrrel.bot)
      (instantiateLevels [.succ (.succ .zero)] covWNatSucc.schema) .prop := by
  change ApproxTKWNative natEnvU n Γ
    (EnvWIrrel.pushArgs
      (([[], [], [covWIrrelRecMinorCode]] ++ [[]]).map demandWIrrel) EnvWIrrel.bot)
    (.app (.app (.bvar 1) (.bvar 0))
      (.app (.app (.app (.app (.const 3 [.succ (.succ .zero)]) (.bvar 3))
        (.bvar 2)) (.bvar 1)) (.bvar 0))) .prop
  apply ApproxTKWNative.app (s := ([], .prop))
  · apply ApproxTKWNative.app (s := ([], .lam [([], .prop)]))
    · exact .bvar (List.mem_singleton_self _)
    · exact List.mem_singleton_self _
    · intro c hc
      exact (List.not_mem_nil _ hc).elim
  · exact List.mem_singleton_self _
  · intro c hc
    exact (List.not_mem_nil _ hc).elim

theorem covWNativeRec_const (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative natEnvU n Γ ρ (.const 3 [.succ (.succ .zero)])
      (curryStepWIrrel [[], [], [covWIrrelRecMinorCode], [covWIrrelRecMajorCode]] .prop) := by
  apply ApproxTKWNative.recursor (w := covWNatSucc) [.succ (.succ .zero)]
    not_propFamilyS_covWNatSucc
    (us_pre := [[], [], [covWIrrelRecMinorCode]]) (us_fields := [[]]) rfl rfl
  exact covWNativeRec_schema n _

/-- Four raw applications consume exactly the displayed finite rows. -/
theorem covWNativeRec_call (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) (a : Expr Nat)
    (ha : ApproxTKWNative natEnvU n Γ ρ a covWIrrelRecMajorCode) :
    ApproxTKWNative natEnvU n Γ ρ
      (recCall (.const 3 [.succ (.succ .zero)])
        [covTRecMotive, .sort .zero, covTRecMinor] a) .prop := by
  have h1 : ApproxTKWNative natEnvU n Γ ρ
      (.app (.const 3 [.succ (.succ .zero)]) covTRecMotive)
      (curryStepWIrrel [[], [covWIrrelRecMinorCode], [covWIrrelRecMajorCode]] .prop) :=
    .app (covWNativeRec_const n Γ ρ) (List.mem_singleton_self _)
      (fun _ h => (List.not_mem_nil _ h).elim)
  have h2 : ApproxTKWNative natEnvU n Γ ρ
      (.app (.app (.const 3 [.succ (.succ .zero)]) covTRecMotive) (.sort .zero))
      (curryStepWIrrel [[covWIrrelRecMinorCode], [covWIrrelRecMajorCode]] .prop) :=
    .app h1 (List.mem_singleton_self _)
      (fun _ h => (List.not_mem_nil _ h).elim)
  have h3 : ApproxTKWNative natEnvU n Γ ρ
      (.app (.app (.app (.const 3 [.succ (.succ .zero)]) covTRecMotive)
        (.sort .zero)) covTRecMinor)
      (curryStepWIrrel [[covWIrrelRecMajorCode]] .prop) := by
    refine .app h2 (List.mem_singleton_self _) ?_
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact covWNativeRec_minor n Γ ρ
  refine .app h3 (List.mem_singleton_self _) ?_
  intro c hc
  obtain rfl := List.mem_singleton.mp hc
  exact ha

theorem covWNativeRec_type (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) (i : Nat)
    (hi : ρ i covWIrrelRecMajorCode) :
    ApproxTKWNative natEnvU n Γ ρ (covTRecTypeAt i) .prop :=
  covWNativeRec_call n Γ ρ (.bvar i) (.bvar hi)

theorem covWNativeRec_major_observed (n : Nat) :
    ApproxTKWNativeStage natEnvU n 1 [] EnvWIrrel.bot covURecMajor covWIrrelRecMajorCode := by
  refine ⟨covWNative_guarded_appSpine_bot (covWEtaNatFn_ty n [])
    (hasTyT_natEnvU_zero n _) (covWNative_succ_observed n [] EnvWIrrel.bot), ?_⟩
  simp [covTObservationBudget, covWIrrelRecMajorCode, covWIrrelErase, covWIrrelEraseArgs]

theorem covWNativeRec_env_realized (n : Nat) :
    CovWNativeRealized natEnvU n 1 covTRecCtx covWIrrelRecEnv covURecSubst := by
  refine ⟨covURecSubst_typed n, ?_⟩
  intro i c hc
  cases i with
  | zero =>
      change c = covWIrrelRecMajorCode at hc
      subst c
      exact covWNativeRec_major_observed n
  | succ i =>
      change c = .bot at hc
      subst c
      exact ⟨.bot _ _ _, by simp [covTObservationBudget, covWIrrelErase]⟩

theorem covWNativeRec_instance_observed (n : Nat) :
    ApproxTKWNativeStage natEnvU n 1 [] EnvWIrrel.bot covURecInstance .prop :=
  ⟨covWNativeRec_call n [] EnvWIrrel.bot covURecMajor (covWNativeRec_major_observed n).1,
    by simp [covTObservationBudget, covWIrrelErase]⟩

/-- Native evidence, both new observations, and the concrete nonbottom realizer
are supplied independently. No forward-substitution theorem is assumed. -/
theorem covWNative_nat_rec_instance_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧
    Nonempty (CtxWfT natEnvU n covTRecCtx) ∧
    Nonempty (HasTyT natEnvU n covTRecCtx (covTRecTypeAt 0) (.sort (.succ .zero))) ∧
    CovWNativeRealized natEnvU n 1 covTRecCtx covWIrrelRecEnv covURecSubst ∧
    ApproxTKWNative natEnvU n covTRecCtx covWIrrelRecEnv (covTRecTypeAt 0) .prop ∧
    Nonempty (HasTyT natEnvU n [] covURecInstance (.sort (.succ .zero))) ∧
    Nonempty (ConvT natEnvU n [] covURecInstance (.sort .zero) (.sort (.succ .zero))) ∧
    ApproxTWIrrel natEnvU n EnvWIrrel.bot covURecInstance .prop ∧
    ApproxTKWNativeStage natEnvU n 1 [] EnvWIrrel.bot covURecInstance .prop ∧
    RedR (WhStepCK2 natEnvU n) [] covURecInstance (.sort .zero) ∧
    ApproxTKWNative natEnvU n [] EnvWIrrel.bot (.sort .zero) .prop :=
  ⟨⟨natEnvUWfT⟩, ⟨covTRecCtx_wf n⟩,
    ⟨covTRecTypeAt_hasTy n covTRecCtx 0 (.bvar _ 0 _ rfl)⟩,
    covWNativeRec_env_realized n, covWNativeRec_type n _ _ 0 rfl,
    ⟨covURecInstance_hasTy n⟩, ⟨covURecInstance_conv n⟩,
    covWIrrelRecInstance_raw n EnvWIrrel.bot, covWNativeRec_instance_observed n,
    covURecInstance_read n, .sort _ _ .zero⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_REC_CONTROL_ROOTS
#print axioms covWNativeRec_minor
#print axioms covWNativeRec_schema
#print axioms covWNativeRec_const
#print axioms covWNativeRec_call
#print axioms covWNativeRec_type
#print axioms covWNativeRec_major_observed
#print axioms covWNativeRec_env_realized
#print axioms covWNativeRec_instance_observed
#print axioms covWNative_nat_rec_instance_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_REC_CONTROL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

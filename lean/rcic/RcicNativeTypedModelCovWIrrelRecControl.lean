import rcic.RcicNativeTypedModelCovWIrrelAligned
import rcic.RcicNativeTypedModelCovURecInstance

/-!
# A fresh Nat-recursion control with proof-erasing compacts

The admitted successor schema is observed directly in the new raw grammar.
Its minor consumes two empty demands, and its constructor demand retains
the witness's actual constructor universe vector. The closed major is
`succ zero`; its field observation is bottom. No observation embedding or
substitution-closure theorem supplies the new closed result.

The concrete native typing, conversion and readback are retained from the
existing instance. A new finite realizer supplies the open recursor's
successor demand. These are local controls, not a normalization theorem.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit TypedModelKFragmentAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open TypedModelCovPAudit TypedModelCovQAudit TypedModelCovRAudit TypedModelCovSAudit
open TypedModelCovTAudit TypedModelCovWAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def covWIrrelRecMinorCode : CptWIrrel := .lam [([], .lam [([], .prop)])]

def covWIrrelRecMajorCode : CptWIrrel := .spine 2 [] [.bot]

def covWIrrelRecEnv : EnvWIrrel
  | 0, c => c = covWIrrelRecMajorCode
  | _ + 1, c => c = .bot

theorem covWIrrelRec_minor_code_erase :
    covWIrrelErase covWIrrelRecMinorCode = covTRecMinorCode := rfl

theorem covWIrrelRec_major_code_erase :
    covWIrrelErase covWIrrelRecMajorCode = covTRecMajorCode := rfl

/-- The recursor constructor uses its actual witness-level vector. -/
theorem covWIrrelRec_ctor_demand :
    ctorDemandWIrrel covWNatSucc.ctorRef covWNatSucc.lsC covWNatSucc.nparams [[]] =
      [covWIrrelRecMajorCode] := rfl

theorem covWIrrelRecMinor_raw (n : Nat) (ρ : EnvWIrrel) :
    ApproxTWIrrel natEnvU n ρ covTRecMinor covWIrrelRecMinorCode := by
  refine .lam (.bot _ _) ?_ ?_ ?_
  · intro row hrow c hc
    obtain rfl := List.mem_singleton.mp hrow
    exact (List.not_mem_nil _ hc).elim
  · exact ⟨([], .lam [([], .prop)]), List.mem_singleton_self _, CptWIrrel.noConfusion⟩
  · intro row hrow
    obtain rfl := List.mem_singleton.mp hrow
    refine .lam (.bot _ _) ?_ ?_ ?_
    · intro inner hinner c hc
      obtain rfl := List.mem_singleton.mp hinner
      exact (List.not_mem_nil _ hc).elim
    · exact ⟨([], .prop), List.mem_singleton_self _, CptWIrrel.noConfusion⟩
    · intro inner hinner
      obtain rfl := List.mem_singleton.mp hinner
      exact .sort _ .zero

/-- The schema observes only the minor's two empty-demand graph rows. -/
theorem covWIrrelRec_schema_raw (n : Nat) :
    ApproxTWIrrel natEnvU n
      (EnvWIrrel.pushArgs
        (([[], [], [covWIrrelRecMinorCode]] ++ [[]]).map demandWIrrel) EnvWIrrel.bot)
      (instantiateLevels [.succ (.succ .zero)] covWNatSucc.schema) .prop := by
  change ApproxTWIrrel natEnvU n
    (EnvWIrrel.pushArgs
      (([[], [], [covWIrrelRecMinorCode]] ++ [[]]).map demandWIrrel) EnvWIrrel.bot)
    (.app (.app (.bvar 1) (.bvar 0))
      (.app (.app (.app (.app (.const 3 [.succ (.succ .zero)]) (.bvar 3))
        (.bvar 2)) (.bvar 1)) (.bvar 0))) .prop
  apply ApproxTWIrrel.app (s := ([], .prop))
  · apply ApproxTWIrrel.app (s := ([], .lam [([], .prop)]))
    · exact .bvar (List.mem_singleton_self _)
    · exact List.mem_singleton_self _
    · intro c hc
      exact (List.not_mem_nil _ hc).elim
  · exact List.mem_singleton_self _
  · intro c hc
    exact (List.not_mem_nil _ hc).elim

theorem covWIrrelRec_const_raw (n : Nat) (ρ : EnvWIrrel) :
    ApproxTWIrrel natEnvU n ρ (.const 3 [.succ (.succ .zero)])
      (curryStepWIrrel [[], [], [covWIrrelRecMinorCode], [covWIrrelRecMajorCode]] .prop) := by
  apply ApproxTWIrrel.recursor (w := covWNatSucc) [.succ (.succ .zero)]
    not_propFamilyS_covWNatSucc
    (us_pre := [[], [], [covWIrrelRecMinorCode]]) (us_fields := [[]]) rfl rfl
  exact covWIrrelRec_schema_raw n

/-- Four raw applications consume exactly the displayed finite rows. -/
theorem covWIrrelRec_call_raw (n : Nat) (ρ : EnvWIrrel) (a : Expr Nat)
    (ha : ApproxTWIrrel natEnvU n ρ a covWIrrelRecMajorCode) :
    ApproxTWIrrel natEnvU n ρ
      (recCall (.const 3 [.succ (.succ .zero)])
        [covTRecMotive, .sort .zero, covTRecMinor] a) .prop := by
  have h1 : ApproxTWIrrel natEnvU n ρ
      (.app (.const 3 [.succ (.succ .zero)]) covTRecMotive)
      (curryStepWIrrel [[], [covWIrrelRecMinorCode], [covWIrrelRecMajorCode]] .prop) :=
    .app (covWIrrelRec_const_raw n ρ) (List.mem_singleton_self _)
      (fun _ h => (List.not_mem_nil _ h).elim)
  have h2 : ApproxTWIrrel natEnvU n ρ
      (.app (.app (.const 3 [.succ (.succ .zero)]) covTRecMotive) (.sort .zero))
      (curryStepWIrrel [[covWIrrelRecMinorCode], [covWIrrelRecMajorCode]] .prop) :=
    .app h1 (List.mem_singleton_self _)
      (fun _ h => (List.not_mem_nil _ h).elim)
  have h3 : ApproxTWIrrel natEnvU n ρ
      (.app (.app (.app (.const 3 [.succ (.succ .zero)]) covTRecMotive)
        (.sort .zero)) covTRecMinor)
      (curryStepWIrrel [[covWIrrelRecMajorCode]] .prop) := by
    refine .app h2 (List.mem_singleton_self _) ?_
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact covWIrrelRecMinor_raw n ρ
  refine .app h3 (List.mem_singleton_self _) ?_
  intro c hc
  obtain rfl := List.mem_singleton.mp hc
  exact ha

theorem covWIrrelRecTypeAt_raw (n : Nat) (ρ : EnvWIrrel) (i : Nat)
    (hi : ρ i covWIrrelRecMajorCode) :
    ApproxTWIrrel natEnvU n ρ (covTRecTypeAt i) .prop :=
  covWIrrelRec_call_raw n ρ (.bvar i) (.bvar hi)

theorem covWIrrelRecTypeAt_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) (i : Nat)
    (hi : ρ i covWIrrelRecMajorCode) :
    ApproxTKWIrrel natEnvU n Γ ρ (covTRecTypeAt i) .prop :=
  .free (kFreeT_natEnvU _) (covWIrrelRecTypeAt_raw n ρ i hi)

/-- Bottom is admitted in the actual Nat argument slot without a proof
classification hypothesis. The successor head is a fresh raw constant. -/
theorem covWIrrelRecMajor_raw (n : Nat) (ρ : EnvWIrrel) :
    ApproxTWIrrel natEnvU n ρ covURecMajor covWIrrelRecMajorCode :=
  .appSpine (.const ρ 2 [] rigidConst_natEnvU_succ not_propCtorT_natEnvU_succ)
    (.bot _ _) (fun _ => rfl)

theorem covWIrrelRecMajor_observed (n : Nat) :
    ApproxTKWIrrelStage natEnvU n 1 [] EnvWIrrel.bot covURecMajor covWIrrelRecMajorCode :=
  ⟨.free (kFreeT_natEnvU _) (covWIrrelRecMajor_raw n EnvWIrrel.bot),
    by simp [covTObservationBudget, covWIrrelRecMajorCode, covWIrrelErase,
      covWIrrelEraseArgs]⟩

theorem covWIrrelRecEnv_realized (n : Nat) :
    CovWIrrelRealized natEnvU n 1 covTRecCtx covWIrrelRecEnv covURecSubst := by
  refine ⟨covURecSubst_typed n, ?_⟩
  intro i c hc
  cases i with
  | zero =>
      change c = covWIrrelRecMajorCode at hc
      subst c
      exact covWIrrelRecMajor_observed n
  | succ i =>
      change c = .bot at hc
      subst c
      exact ⟨.bot _ _ _, by simp [covTObservationBudget, covWIrrelErase]⟩

/-- This closed supply is constructed from the schema and major directly. -/
theorem covWIrrelRecInstance_raw (n : Nat) (ρ : EnvWIrrel) :
    ApproxTWIrrel natEnvU n ρ covURecInstance .prop :=
  covWIrrelRec_call_raw n ρ covURecMajor (covWIrrelRecMajor_raw n ρ)

theorem covWIrrelRecInstance_observed (n : Nat) :
    ApproxTKWIrrelStage natEnvU n 1 [] EnvWIrrel.bot covURecInstance .prop :=
  ⟨.free (kFreeT_natEnvU _) (covWIrrelRecInstance_raw n EnvWIrrel.bot),
    by simp [covTObservationBudget, covWIrrelErase]⟩

theorem covWIrrelRecInstance_erased (n : Nat) :
    CovWIrrelRawObservation natEnvU n EnvWIrrel.bot covURecInstance .prop ∧
    CovWIrrelObservation natEnvU n [] EnvWIrrel.bot covURecInstance .prop :=
  ⟨⟨.prop, rfl, covWIrrelRecInstance_raw n EnvWIrrel.bot⟩,
    covWIrrel_observation_of (covWIrrelRecInstance_observed n).1⟩

/-- The open demand and its concrete closed instance have all their native
typing and new realization premises, along with the retained native readback. -/
theorem covWIrrel_nat_rec_instance_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧
    Nonempty (CtxWfT natEnvU n covTRecCtx) ∧
    Nonempty (HasTyT natEnvU n covTRecCtx (covTRecTypeAt 0) (.sort (.succ .zero))) ∧
    CovWIrrelRealized natEnvU n 1 covTRecCtx covWIrrelRecEnv covURecSubst ∧
    ApproxTKWIrrel natEnvU n covTRecCtx covWIrrelRecEnv (covTRecTypeAt 0) .prop ∧
    Nonempty (HasTyT natEnvU n [] covURecInstance (.sort (.succ .zero))) ∧
    Nonempty (ConvT natEnvU n [] covURecInstance (.sort .zero) (.sort (.succ .zero))) ∧
    ApproxTWIrrel natEnvU n EnvWIrrel.bot covURecInstance .prop ∧
    ApproxTKWIrrelStage natEnvU n 1 [] EnvWIrrel.bot covURecInstance .prop ∧
    RedR (WhStepCK2 natEnvU n) [] covURecInstance (.sort .zero) ∧
    ApproxTKWIrrel natEnvU n [] EnvWIrrel.bot (.sort .zero) .prop :=
  ⟨⟨natEnvUWfT⟩, ⟨covTRecCtx_wf n⟩,
    ⟨covTRecTypeAt_hasTy n covTRecCtx 0 (.bvar _ 0 _ rfl)⟩,
    covWIrrelRecEnv_realized n, covWIrrelRecTypeAt_observed n _ _ 0 rfl,
    ⟨covURecInstance_hasTy n⟩, ⟨covURecInstance_conv n⟩,
    covWIrrelRecInstance_raw n EnvWIrrel.bot, covWIrrelRecInstance_observed n,
    covURecInstance_read n, .free (kFreeT_sort natEnvU .zero) (.sort _ .zero)⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_REC_CONTROL_ROOTS
#print axioms covWIrrelRecMinorCode
#print axioms covWIrrelRecMajorCode
#print axioms covWIrrelRecEnv
#print axioms covWIrrelRec_minor_code_erase
#print axioms covWIrrelRec_major_code_erase
#print axioms covWIrrelRec_ctor_demand
#print axioms covWIrrelRecMinor_raw
#print axioms covWIrrelRec_schema_raw
#print axioms covWIrrelRec_const_raw
#print axioms covWIrrelRec_call_raw
#print axioms covWIrrelRecTypeAt_raw
#print axioms covWIrrelRecTypeAt_observed
#print axioms covWIrrelRecMajor_raw
#print axioms covWIrrelRecMajor_observed
#print axioms covWIrrelRecEnv_realized
#print axioms covWIrrelRecInstance_raw
#print axioms covWIrrelRecInstance_observed
#print axioms covWIrrelRecInstance_erased
#print axioms covWIrrel_nat_rec_instance_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_REC_CONTROL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

import rcic.RcicNativeTypedModelCovWIrrelFunctionRepairBoundary

/-!
# The function-field boundary already occurs in the raw grammar

The admitted nonproof function position retains the original finite
compact of `G succ` using only raw constant and spine application rules.
The eta, beta, and let sources cannot supply that compact in the raw
grammar, because their actual K-free certificates lift any proposed raw
derivation into the already excluded complete guarded grammar.

The boundary uses original erased compacts. Its raw realizer and its
finite valuation in the erased raw model are supplied directly; native
typing, conversions, and reductions are actual admitted data.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelAudit.TypingFin
open TypedModelCovTAudit TypedModelCovWAudit TypedModelCovWEtaAudit
open ReadbackCKAudit ReadbackCK2Audit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem covWFunction_raw_target (n : Nat) (ρ : EnvWIrrel) :
    ApproxTWIrrel covWFunctionEnv n ρ covWFunctionTarget covWFunctionFineR :=
  .appSpine
    (.const ρ 4 [] covWFunction_g_rigid covWFunction_g_not_propCtor)
    (.const ρ 2 [] covWFunction_succ_rigid covWFunction_succ_not_propCtor)
    (fun hp => (covWFunction_g_nonproof_position n hp).elim)

theorem covWFunction_raw_type (n : Nat) (ρ : EnvWIrrel) :
    ApproxTWIrrel covWFunctionEnv n ρ (.sort .zero) .prop :=
  .sort ρ .zero

theorem covWFunction_raw_arrow (n : Nat) (ρ : EnvWIrrel) :
    ApproxTWIrrel covWFunctionEnv n ρ covWFunctionArrow covWFunctionArrowCodeR := by
  refine .pi (.const ρ 0 [] covWFunction_nat_rigid covWFunction_nat_not_propCtor) ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact .const _ 0 [] covWFunction_nat_rigid covWFunction_nat_not_propCtor

theorem covWFunction_raw_target_observation (n : Nat) (ρ : EnvWIrrel) :
    CovWIrrelRawObservation covWFunctionEnv n ρ covWFunctionTarget covWFunctionFine :=
  ⟨covWFunctionFineR, rfl, covWFunction_raw_target n ρ⟩

theorem covWFunction_raw_type_observation (n : Nat) (ρ : EnvWIrrel) :
    CovWIrrelRawObservation covWFunctionEnv n ρ (.sort .zero) .prop :=
  ⟨.prop, rfl, covWFunction_raw_type n ρ⟩

theorem covWFunction_raw_eta_absent (n : Nat) (ρ : EnvWIrrel) :
    ¬ CovWIrrelRawObservation covWFunctionEnv n ρ covWFunctionEtaSource covWFunctionFine := by
  rintro ⟨d, hd, h⟩
  exact covWFunction_erased_eta_absent n [] ρ
    ⟨d, hd, .free covWFunction_kFree.2.1 h⟩

theorem covWFunction_raw_beta_absent (n : Nat) (ρ : EnvWIrrel) :
    ¬ CovWIrrelRawObservation covWFunctionEnv n ρ covWFunctionBetaSource covWFunctionFine := by
  rintro ⟨d, hd, h⟩
  exact covWFunction_erased_beta_absent n [] ρ
    ⟨d, hd, .free covWFunction_kFree.2.2 h⟩

theorem covWFunction_raw_let_absent (n : Nat) (ρ : EnvWIrrel) :
    ¬ CovWIrrelRawObservation covWFunctionEnv n ρ covWFunctionLetSource covWFunctionFine := by
  rintro ⟨d, hd, h⟩
  exact covWFunction_erased_let_absent n [] ρ
    ⟨d, hd, .free covWFunction_let_kFree h⟩

theorem covWFunction_raw_all_fine_decorations_absent (n : Nat) (ρ : EnvWIrrel)
    (d : CptWIrrel) (hd : covWIrrelErase d = covWFunctionFine) :
    (¬ ApproxTWIrrel covWFunctionEnv n ρ covWFunctionEtaSource d) ∧
    (¬ ApproxTWIrrel covWFunctionEnv n ρ covWFunctionBetaSource d) ∧
    (¬ ApproxTWIrrel covWFunctionEnv n ρ covWFunctionLetSource d) :=
  ⟨fun h => covWFunction_raw_eta_absent n ρ ⟨d, hd, h⟩,
   fun h => covWFunction_raw_beta_absent n ρ ⟨d, hd, h⟩,
   fun h => covWFunction_raw_let_absent n ρ ⟨d, hd, h⟩⟩

/-- The raw finite realizer is supplied independently of guarded eta. -/
theorem covWFunction_raw_realized (n : Nat) :
    TypedSubstT covWFunctionEnv n [] SubstT.id [] ∧
    (∀ i c, EnvWIrrel.bot i c →
      ApproxTWIrrel covWFunctionEnv n EnvWIrrel.bot (SubstT.id i) c ∧
      covTObservationBudget (covWIrrelErase c) ≤ 2) := by
  refine ⟨(covWIrrel_realized_nil covWFunctionEnv n 2).typing, ?_⟩
  intro i c hc
  cases hc
  exact ⟨.bot _ _, by simp [covWIrrelErase, covTObservationBudget]⟩

structure CovWFunctionRawFailureAt (n : Nat) : Prop where
  envWf : Nonempty (EnvWfT covWFunctionEnv)
  ctxWf : Nonempty (CtxWfT covWFunctionEnv n [])
  typedSubst : TypedSubstT covWFunctionEnv n [] SubstT.id []
  rawRealized : ∀ i c, EnvWIrrel.bot i c →
    ApproxTWIrrel covWFunctionEnv n EnvWIrrel.bot (SubstT.id i) c ∧
    covTObservationBudget (covWIrrelErase c) ≤ 2
  erasedValuation : EnvTypedFinAtT
    (⟨ApproxTW covWFunctionEnv⟩ : CtxModelT covWFunctionEnv) []
    (covWIrrelEnvErase EnvWIrrel.bot)
  erasedCoherence : CtxEnvM
    (⟨ApproxTW covWFunctionEnv⟩ : CtxModelT covWFunctionEnv) []
    (covWIrrelEnvErase EnvWIrrel.bot)
  arrowTy : Nonempty (HasTyT covWFunctionEnv n [] covWFunctionArrow
    (.sort (.imax (.succ .zero) (.succ .zero))))
  succTy : Nonempty (HasTyT covWFunctionEnv n [] covWFunctionSucc covWFunctionArrow)
  etaSourceTy : Nonempty (HasTyT covWFunctionEnv n [] covWFunctionEtaSource (.sort .zero))
  betaSourceTy : Nonempty (HasTyT covWFunctionEnv n [] covWFunctionBetaSource (.sort .zero))
  letSourceTy : Nonempty (HasTyT covWFunctionEnv n [] covWFunctionLetSource (.sort .zero))
  targetTy : Nonempty (HasTyT covWFunctionEnv n [] covWFunctionTarget (.sort .zero))
  typeTy : Nonempty (HasTyT covWFunctionEnv n [] (.sort .zero) (.sort (.succ .zero)))
  etaConversion : Nonempty
    (ConvT covWFunctionEnv n [] covWFunctionEtaSource covWFunctionTarget (.sort .zero))
  betaConversion : Nonempty
    (ConvT covWFunctionEnv n [] covWFunctionBetaSource covWFunctionTarget (.sort .zero))
  letConversion : Nonempty
    (ConvT covWFunctionEnv n [] covWFunctionLetSource covWFunctionTarget (.sort .zero))
  betaStep : WhStepCK2 covWFunctionEnv n [] covWFunctionBetaSource covWFunctionTarget
  letStep : WhStepCK2 covWFunctionEnv n [] covWFunctionLetSource covWFunctionTarget
  nativeNonproof : ¬ CovWIrrelProofPosition covWFunctionEnv n 4 [] 0
  targetRaw : ApproxTWIrrel covWFunctionEnv n EnvWIrrel.bot
    covWFunctionTarget covWFunctionFineR
  typeRaw : ApproxTWIrrel covWFunctionEnv n EnvWIrrel.bot (.sort .zero) .prop
  arrowRaw : ApproxTWIrrel covWFunctionEnv n EnvWIrrel.bot
    covWFunctionArrow covWFunctionArrowCodeR
  targetObservation : CovWIrrelRawObservation covWFunctionEnv n EnvWIrrel.bot
    covWFunctionTarget covWFunctionFine
  typeObservation : CovWIrrelRawObservation covWFunctionEnv n EnvWIrrel.bot
    (.sort .zero) .prop
  demand : CTyS covWFunctionEnv covWFunctionFine .prop
  nonbottom : covWFunctionFine ≠ .bot
  etaNoFine : ¬ CovWIrrelRawObservation covWFunctionEnv n EnvWIrrel.bot
    covWFunctionEtaSource covWFunctionFine
  betaNoFine : ¬ CovWIrrelRawObservation covWFunctionEnv n EnvWIrrel.bot
    covWFunctionBetaSource covWFunctionFine
  letNoFine : ¬ CovWIrrelRawObservation covWFunctionEnv n EnvWIrrel.bot
    covWFunctionLetSource covWFunctionFine

theorem covWFunction_raw_inhabited (n : Nat) : CovWFunctionRawFailureAt n where
  envWf := ⟨covWFunctionEnv_wf⟩
  ctxWf := ⟨.nil⟩
  typedSubst := (covWFunction_raw_realized n).1
  rawRealized := (covWFunction_raw_realized n).2
  erasedValuation := envTypedFinAtT_nil _ _
  erasedCoherence := fun _ _ hv => Option.noConfusion hv
  arrowTy := ⟨covWFunction_arrow_ty n []⟩
  succTy := ⟨covWFunction_succ_ty n []⟩
  etaSourceTy := ⟨covWFunction_eta_source_ty n []⟩
  betaSourceTy := ⟨covWFunction_beta_source_ty n []⟩
  letSourceTy := ⟨covWFunction_let_source_ty n []⟩
  targetTy := ⟨covWFunction_target_ty n []⟩
  typeTy := ⟨.sort [] .zero⟩
  etaConversion := ⟨covWFunction_eta_conv n []⟩
  betaConversion := ⟨covWFunction_beta_conv n []⟩
  letConversion := ⟨covWFunction_let_conv n []⟩
  betaStep := covWFunction_beta_step n []
  letStep := covWFunction_let_step n []
  nativeNonproof := covWFunction_g_nonproof_position n
  targetRaw := covWFunction_raw_target n EnvWIrrel.bot
  typeRaw := covWFunction_raw_type n EnvWIrrel.bot
  arrowRaw := covWFunction_raw_arrow n EnvWIrrel.bot
  targetObservation := covWFunction_raw_target_observation n EnvWIrrel.bot
  typeObservation := covWFunction_raw_type_observation n EnvWIrrel.bot
  demand := covWFunction_fine_typed
  nonbottom := covWFunction_fine_nonbottom
  etaNoFine := covWFunction_raw_eta_absent n EnvWIrrel.bot
  betaNoFine := covWFunction_raw_beta_absent n EnvWIrrel.bot
  letNoFine := covWFunction_raw_let_absent n EnvWIrrel.bot

theorem covWFunction_raw_same_stage (n : Nat) :
    ApproxTWIrrel covWFunctionEnv n EnvWIrrel.bot covWFunctionTarget covWFunctionFineR ∧
    covTObservationBudget covWFunctionFine ≤ 2 ∧
    ApproxTWIrrel covWFunctionEnv n EnvWIrrel.bot (.sort .zero) .prop ∧
    covTObservationBudget .prop ≤ 2 := by
  refine ⟨covWFunction_raw_target n EnvWIrrel.bot, ?_,
    covWFunction_raw_type n EnvWIrrel.bot, ?_⟩
  all_goals simp [covWFunctionFine, covWFunctionAtom, covTObservationBudget]

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_FUNCTION_RAW_BOUNDARY_ROOTS
#print axioms covWFunction_raw_target
#print axioms covWFunction_raw_type
#print axioms covWFunction_raw_arrow
#print axioms covWFunction_raw_target_observation
#print axioms covWFunction_raw_type_observation
#print axioms covWFunction_raw_eta_absent
#print axioms covWFunction_raw_beta_absent
#print axioms covWFunction_raw_let_absent
#print axioms covWFunction_raw_all_fine_decorations_absent
#print axioms covWFunction_raw_realized
#print axioms CovWFunctionRawFailureAt
#print axioms covWFunction_raw_inhabited
#print axioms covWFunction_raw_same_stage
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_FUNCTION_RAW_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

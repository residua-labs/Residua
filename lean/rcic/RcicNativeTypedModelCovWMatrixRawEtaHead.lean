import rcic.RcicNativeTypedModelCovWMatrixFunctionCells

/-!
# Native eta at the head fails for the unchanged raw grammar

The successor lambda has a strictly typed nonbottom graph observation.
Bare successor has only bottom or its rigid constant spine in the raw
grammar, so it cannot supply any decoration of that graph. The native
eta constructor relates these exact endpoints at the actual arrow type.

The generic failure record lists its absent endpoint first. The public
invariant refutation is in the native eta order, lambda to successor.
Both observations fit the displayed stage bound, and the native closing
realizer and erased finite valuation are inhabited. The final guarded
control supplies this one shared graph; it does not assert equality of
all guarded observations. No grammar or field discipline is changed.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelAudit.TypingFin TypedModelCovTAudit TypedModelCovWIrrelAudit

def covWMatrixRawEtaGraph : CptT := .lam [([.bot], .spine 2 [.bot])]

/-- Direct inversion of the raw constant rules, including recursor exclusion. -/
theorem covWMatrix_raw_rigid_const_shape {E : ResolvedEnv} {n r : Nat}
    {ρ : EnvWIrrel} {ls : List Level} {c : CptWIrrel}
    (hr : RigidConst E r) (h : ApproxTWIrrel E n ρ (.const r ls) c) :
    c = .bot ∨ c = .spine r ls [] := by
  cases h with
  | bot => exact Or.inl rfl
  | const => exact Or.inr rfl
  | delta hd _ => exact (not_rigidConst_of_deltaConst hd hr).elim
  | @recursor _ w => exact (not_rigidConst_of_recursor w hr).elim

theorem covWMatrix_raw_successor_no_graph (n : Nat) (ρ : EnvWIrrel)
    (rows : List (List CptWIrrel × CptWIrrel)) :
    ¬ ApproxTWIrrel covWFunctionEnv n ρ covWFunctionSucc (.lam rows) := by
  intro h
  rcases covWMatrix_raw_rigid_const_shape covWFunction_succ_rigid h with hb | hs
  · cases hb
  · cases hs

theorem covWMatrix_raw_successor_erased_no_graph (n : Nat) (ρ : EnvWIrrel)
    (rows : List (List CptT × CptT)) :
    ¬ CovWIrrelRawObservation covWFunctionEnv n ρ covWFunctionSucc (.lam rows) := by
  rintro ⟨d, he, hd⟩
  rcases covWMatrix_raw_rigid_const_shape covWFunction_succ_rigid hd with rfl | rfl
  · cases he
  · cases he

theorem covWMatrix_raw_eta_lambda_graph (n : Nat) (ρ : EnvWIrrel) :
    ApproxTWIrrel covWFunctionEnv n ρ covWFunctionEta covWFunctionGraphR := by
  refine .lam (.const ρ 0 [] covWFunction_nat_rigid covWFunction_nat_not_propCtor)
    ?_ ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · exact ⟨([.bot], .spine 2 [] [.bot]), List.mem_singleton.mpr rfl,
      fun h => CptWIrrel.noConfusion h⟩
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact .appSpine
      (.const _ 2 [] covWFunction_succ_rigid covWFunction_succ_not_propCtor)
      (.bot _ _) (fun _ => rfl)

theorem covWMatrix_raw_eta_lambda_observed (n : Nat) (ρ : EnvWIrrel) :
    CovWIrrelRawObservation covWFunctionEnv n ρ covWFunctionEta covWMatrixRawEtaGraph :=
  ⟨covWFunctionGraphR, rfl, covWMatrix_raw_eta_lambda_graph n ρ⟩

theorem covWMatrix_raw_eta_arrow_observed (n : Nat) (ρ : EnvWIrrel) :
    CovWIrrelRawObservation covWFunctionEnv n ρ covWFunctionArrow covWFunctionArrowCode :=
  ⟨covWFunctionArrowCodeR, rfl, covWFunction_raw_arrow n ρ⟩

theorem covWMatrix_raw_eta_graph_typed :
    CTyS covWFunctionEnv covWMatrixRawEtaGraph covWFunctionArrowCode :=
  covWFunction_graph_typedR

/-- The absent-side-first record contains the reverse of the displayed eta
conversion; both native directions are actual derivations. -/
theorem covWMatrix_raw_eta_head_failure (n : Nat) :
    CovWMatrixRawClosedFailure covWFunctionEnv n 3 covWFunctionSucc covWFunctionEta
      covWFunctionArrow (.imax (.succ .zero) (.succ .zero))
      covWMatrixRawEtaGraph covWFunctionArrowCode where
  native := {
    envWf := ⟨covWFunctionEnv_wf⟩
    ctxWf := ⟨.nil⟩
    leftTy := ⟨covWFunction_succ_ty n []⟩
    rightTy := ⟨covWFunction_eta_ty n []⟩
    typeTy := ⟨covWFunction_arrow_ty n []⟩
    conversion := ⟨.symm [] covWFunctionEta covWFunctionSucc covWFunctionArrow
      (covWMatrix_eta_hole_conversion n)⟩ }
  typedSubst := (covWFunction_raw_realized n).1
  realized := by
    intro i d hd
    cases hd
    exact ⟨.bot _ _, by simp [covWIrrelErase, covTObservationBudget]⟩
  erasedValuation := envTypedFinAtT_nil _ _
  erasedCoherence := fun _ _ hv => Option.noConfusion hv
  typeObserved := covWMatrix_raw_eta_arrow_observed n EnvWIrrel.bot
  demand := covWMatrix_raw_eta_graph_typed
  nonbottom := fun h => CptT.noConfusion h
  rightObserved := covWMatrix_raw_eta_lambda_observed n EnvWIrrel.bot
  leftAbsent := covWMatrix_raw_successor_erased_no_graph n EnvWIrrel.bot _

theorem covWMatrix_raw_eta_head_inhabited (n : Nat) :
    Nonempty (ConvT covWFunctionEnv n [] covWFunctionEta covWFunctionSucc covWFunctionArrow) ∧
    CovWMatrixRawClosedFailure covWFunctionEnv n 3 covWFunctionSucc covWFunctionEta
      covWFunctionArrow (.imax (.succ .zero) (.succ .zero))
      covWMatrixRawEtaGraph covWFunctionArrowCode ∧
    covTObservationBudget covWMatrixRawEtaGraph ≤ 3 ∧
    covTObservationBudget covWFunctionArrowCode ≤ 3 := by
  refine ⟨⟨covWMatrix_eta_hole_conversion n⟩, covWMatrix_raw_eta_head_failure n, ?_, ?_⟩
  all_goals simp [covTObservationBudget, covWMatrixRawEtaGraph, covWFunctionArrowCode]

theorem covWMatrix_raw_eta_head_not_invariant (n : Nat) :
    ¬ CovWMatrixRawTypedInvariant covWFunctionEnv n EnvWIrrel.bot covWFunctionArrow
      covWFunctionEta covWFunctionSucc := by
  intro h
  exact covWMatrix_raw_successor_erased_no_graph n EnvWIrrel.bot _
    ((h covWFunctionArrowCode covWMatrixRawEtaGraph
      (covWMatrix_raw_eta_arrow_observed n EnvWIrrel.bot)
      covWMatrix_raw_eta_graph_typed).mp
        (covWMatrix_raw_eta_lambda_observed n EnvWIrrel.bot))

/-- Guarded eta supplies this same strict graph on both endpoints. This is
one common observation, not a theorem about every guarded observation. -/
theorem covWMatrix_guarded_eta_head_shared_graph (n : Nat) :
    CovWIrrelObservation covWFunctionEnv n [] EnvWIrrel.bot covWFunctionEta covWMatrixRawEtaGraph ∧
    CovWIrrelObservation covWFunctionEnv n [] EnvWIrrel.bot covWFunctionSucc covWMatrixRawEtaGraph ∧
    CovWIrrelObservation covWFunctionEnv n [] EnvWIrrel.bot covWFunctionArrow covWFunctionArrowCode ∧
    CTyS covWFunctionEnv covWMatrixRawEtaGraph covWFunctionArrowCode :=
  ⟨covWIrrel_observation_of (covWFunction_eta_graphR n [] EnvWIrrel.bot),
    covWIrrel_observation_of (covWFunction_succ_graphR n [] EnvWIrrel.bot),
    covWIrrel_observation_of (covWFunction_arrow_observedR n [] EnvWIrrel.bot),
    covWMatrix_raw_eta_graph_typed⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_RAW_ETA_HEAD_ROOTS
#print axioms covWMatrixRawEtaGraph
#print axioms covWMatrix_raw_rigid_const_shape
#print axioms covWMatrix_raw_successor_no_graph
#print axioms covWMatrix_raw_successor_erased_no_graph
#print axioms covWMatrix_raw_eta_lambda_graph
#print axioms covWMatrix_raw_eta_lambda_observed
#print axioms covWMatrix_raw_eta_arrow_observed
#print axioms covWMatrix_raw_eta_graph_typed
#print axioms covWMatrix_raw_eta_head_failure
#print axioms covWMatrix_raw_eta_head_inhabited
#print axioms covWMatrix_raw_eta_head_not_invariant
#print axioms covWMatrix_guarded_eta_head_shared_graph
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_RAW_ETA_HEAD_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit

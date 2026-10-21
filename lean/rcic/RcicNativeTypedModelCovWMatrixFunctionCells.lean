import rcic.RcicNativeTypedModelCovWMatrixCore
import rcic.RcicNativeTypedModelCovWIrrelFunctionRawBoundary

/-!
# Concrete beta, zeta, and eta failures in the invariance matrix

The beta and zeta examples are literal head generators. The eta example
is the native eta generator on successor, composed with the actual
application-argument context `G [-]`. The declared argument of `G` is the
nonproof function type `Nat -> Nat`, so that example also occupies the
rigid-function-argument cell. It is not an eta-at-head counterexample.

All failures use the original erased compact `spine 4 [spine 2 []]`,
with an actual observed type code `prop` and a strict nonbottom demand.
Both raw and complete guarded failures are instantiated below. The final
binder-demand result is a finite factorization obstruction, a separate
obligation from a syntactic context position. These examples do not
establish a complete matrix or preclude a future field discipline.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelAudit.TypingFin TypedModelCovWAudit TypedModelCovTAudit
open TypedModelCovWTypedAudit TypedModelCovWEtaAudit TypedModelCovWIrrelAudit

theorem covWMatrix_beta_head_shape :
    CovWTypedBetaHead covWFunctionBetaSource covWFunctionTarget :=
  ⟨covWFunctionArrow, covWFunctionBody, covWFunctionSucc, rfl, rfl⟩

theorem covWMatrix_zeta_head_shape :
    CovWTypedLetHead covWFunctionLetSource covWFunctionTarget :=
  ⟨covWFunctionArrow, covWFunctionSucc, covWFunctionBody, rfl, rfl⟩

/-- This is the eta generator before application congruence. -/
def covWMatrix_eta_hole_conversion (n : Nat) :
    ConvT covWFunctionEnv n [] covWFunctionEta covWFunctionSucc covWFunctionArrow :=
  .eta [] covWFunctionSucc (.const 0 []) (.const 0 []) (covWFunction_succ_ty n [])

theorem covWMatrix_eta_argument_shape :
    covWFunctionEtaSource = .app covWFunctionG covWFunctionEta ∧
    covWFunctionTarget = .app covWFunctionG covWFunctionSucc := ⟨rfl, rfl⟩

/-- Actual native composition at this argument occurrence. -/
def covWMatrix_eta_argument_conversion (n : Nat) :
    ConvT covWFunctionEnv n [] covWFunctionEtaSource covWFunctionTarget (.sort .zero) :=
  .app [] covWFunctionG covWFunctionG covWFunctionEta covWFunctionSucc
    covWFunctionArrow (.sort .zero)
    (.refl [] covWFunctionG covWFunctionGType (covWFunction_g_ty n []))
    (covWMatrix_eta_hole_conversion n)

theorem covWMatrix_rigid_function_position (n : Nat) :
    RigidConst covWFunctionEnv 4 ∧
    CovWIrrelPosition covWFunctionEnv n 4 [] 0 [] covWFunctionArrow (.sort .zero) ∧
    ¬ CovWIrrelProofPosition covWFunctionEnv n 4 [] 0 :=
  ⟨covWFunction_g_rigid, covWFunction_g_position n, covWFunction_g_nonproof_position n⟩

theorem covWMatrix_beta_native (n : Nat) :
    CovWMatrixNativePair covWFunctionEnv n covWFunctionBetaSource covWFunctionTarget
      (.sort .zero) (.succ .zero) where
  envWf := ⟨covWFunctionEnv_wf⟩
  ctxWf := ⟨.nil⟩
  leftTy := ⟨covWFunction_beta_source_ty n []⟩
  rightTy := ⟨covWFunction_target_ty n []⟩
  typeTy := ⟨.sort [] .zero⟩
  conversion := ⟨covWFunction_beta_conv n []⟩

theorem covWMatrix_zeta_native (n : Nat) :
    CovWMatrixNativePair covWFunctionEnv n covWFunctionLetSource covWFunctionTarget
      (.sort .zero) (.succ .zero) where
  envWf := ⟨covWFunctionEnv_wf⟩
  ctxWf := ⟨.nil⟩
  leftTy := ⟨covWFunction_let_source_ty n []⟩
  rightTy := ⟨covWFunction_target_ty n []⟩
  typeTy := ⟨.sort [] .zero⟩
  conversion := ⟨covWFunction_let_conv n []⟩

theorem covWMatrix_eta_argument_native (n : Nat) :
    CovWMatrixNativePair covWFunctionEnv n covWFunctionEtaSource covWFunctionTarget
      (.sort .zero) (.succ .zero) where
  envWf := ⟨covWFunctionEnv_wf⟩
  ctxWf := ⟨.nil⟩
  leftTy := ⟨covWFunction_eta_source_ty n []⟩
  rightTy := ⟨covWFunction_target_ty n []⟩
  typeTy := ⟨.sort [] .zero⟩
  conversion := ⟨covWMatrix_eta_argument_conversion n⟩

theorem covWMatrix_beta_head_failure (n : Nat) :
    CovWMatrixClosedFailure covWFunctionEnv n 2 covWFunctionBetaSource covWFunctionTarget
      (.sort .zero) (.succ .zero) covWFunctionFine .prop where
  native := covWMatrix_beta_native n
  realized := covWIrrel_realized_nil _ _ _
  erasedValuation := envTypedFinAtT_nil _ _
  erasedCoherence := fun _ _ hv => Option.noConfusion hv
  typeObserved := covWFunction_erased_type_observed n [] EnvWIrrel.bot
  demand := covWFunction_fine_typed
  nonbottom := covWFunction_fine_nonbottom
  rightObserved := covWFunction_erased_target_observed n [] EnvWIrrel.bot
  leftAbsent := covWFunction_erased_beta_absent n [] EnvWIrrel.bot

theorem covWMatrix_zeta_head_failure (n : Nat) :
    CovWMatrixClosedFailure covWFunctionEnv n 2 covWFunctionLetSource covWFunctionTarget
      (.sort .zero) (.succ .zero) covWFunctionFine .prop where
  native := covWMatrix_zeta_native n
  realized := covWIrrel_realized_nil _ _ _
  erasedValuation := envTypedFinAtT_nil _ _
  erasedCoherence := fun _ _ hv => Option.noConfusion hv
  typeObserved := covWFunction_erased_type_observed n [] EnvWIrrel.bot
  demand := covWFunction_fine_typed
  nonbottom := covWFunction_fine_nonbottom
  rightObserved := covWFunction_erased_target_observed n [] EnvWIrrel.bot
  leftAbsent := covWFunction_erased_let_absent n [] EnvWIrrel.bot

theorem covWMatrix_eta_argument_failure (n : Nat) :
    CovWMatrixClosedFailure covWFunctionEnv n 2 covWFunctionEtaSource covWFunctionTarget
      (.sort .zero) (.succ .zero) covWFunctionFine .prop where
  native := covWMatrix_eta_argument_native n
  realized := covWIrrel_realized_nil _ _ _
  erasedValuation := envTypedFinAtT_nil _ _
  erasedCoherence := fun _ _ hv => Option.noConfusion hv
  typeObserved := covWFunction_erased_type_observed n [] EnvWIrrel.bot
  demand := covWFunction_fine_typed
  nonbottom := covWFunction_fine_nonbottom
  rightObserved := covWFunction_erased_target_observed n [] EnvWIrrel.bot
  leftAbsent := covWFunction_erased_eta_absent n [] EnvWIrrel.bot

theorem covWMatrix_beta_head_raw_failure (n : Nat) :
    CovWMatrixRawClosedFailure covWFunctionEnv n 2 covWFunctionBetaSource covWFunctionTarget
      (.sort .zero) (.succ .zero) covWFunctionFine .prop where
  native := covWMatrix_beta_native n
  typedSubst := (covWFunction_raw_realized n).1
  realized := (covWFunction_raw_realized n).2
  erasedValuation := envTypedFinAtT_nil _ _
  erasedCoherence := fun _ _ hv => Option.noConfusion hv
  typeObserved := covWFunction_raw_type_observation n EnvWIrrel.bot
  demand := covWFunction_fine_typed
  nonbottom := covWFunction_fine_nonbottom
  rightObserved := covWFunction_raw_target_observation n EnvWIrrel.bot
  leftAbsent := covWFunction_raw_beta_absent n EnvWIrrel.bot

theorem covWMatrix_zeta_head_raw_failure (n : Nat) :
    CovWMatrixRawClosedFailure covWFunctionEnv n 2 covWFunctionLetSource covWFunctionTarget
      (.sort .zero) (.succ .zero) covWFunctionFine .prop where
  native := covWMatrix_zeta_native n
  typedSubst := (covWFunction_raw_realized n).1
  realized := (covWFunction_raw_realized n).2
  erasedValuation := envTypedFinAtT_nil _ _
  erasedCoherence := fun _ _ hv => Option.noConfusion hv
  typeObserved := covWFunction_raw_type_observation n EnvWIrrel.bot
  demand := covWFunction_fine_typed
  nonbottom := covWFunction_fine_nonbottom
  rightObserved := covWFunction_raw_target_observation n EnvWIrrel.bot
  leftAbsent := covWFunction_raw_let_absent n EnvWIrrel.bot

theorem covWMatrix_eta_argument_raw_failure (n : Nat) :
    CovWMatrixRawClosedFailure covWFunctionEnv n 2 covWFunctionEtaSource covWFunctionTarget
      (.sort .zero) (.succ .zero) covWFunctionFine .prop where
  native := covWMatrix_eta_argument_native n
  typedSubst := (covWFunction_raw_realized n).1
  realized := (covWFunction_raw_realized n).2
  erasedValuation := envTypedFinAtT_nil _ _
  erasedCoherence := fun _ _ hv => Option.noConfusion hv
  typeObserved := covWFunction_raw_type_observation n EnvWIrrel.bot
  demand := covWFunction_fine_typed
  nonbottom := covWFunction_fine_nonbottom
  rightObserved := covWFunction_raw_target_observation n EnvWIrrel.bot
  leftAbsent := covWFunction_raw_eta_absent n EnvWIrrel.bot

theorem covWMatrix_beta_head_not_invariant (n : Nat) :
    ¬ CovWMatrixTypedInvariant covWFunctionEnv n [] EnvWIrrel.bot (.sort .zero)
      covWFunctionBetaSource covWFunctionTarget :=
  covWMatrix_closedFailure_refutes (covWMatrix_beta_head_failure n)

theorem covWMatrix_zeta_head_not_invariant (n : Nat) :
    ¬ CovWMatrixTypedInvariant covWFunctionEnv n [] EnvWIrrel.bot (.sort .zero)
      covWFunctionLetSource covWFunctionTarget :=
  covWMatrix_closedFailure_refutes (covWMatrix_zeta_head_failure n)

theorem covWMatrix_eta_argument_not_invariant (n : Nat) :
    ¬ CovWMatrixTypedInvariant covWFunctionEnv n [] EnvWIrrel.bot (.sort .zero)
      covWFunctionEtaSource covWFunctionTarget :=
  covWMatrix_closedFailure_refutes (covWMatrix_eta_argument_failure n)

theorem covWMatrix_beta_head_raw_not_invariant (n : Nat) :
    ¬ CovWMatrixRawTypedInvariant covWFunctionEnv n EnvWIrrel.bot (.sort .zero)
      covWFunctionBetaSource covWFunctionTarget :=
  covWMatrix_rawClosedFailure_refutes (covWMatrix_beta_head_raw_failure n)

theorem covWMatrix_zeta_head_raw_not_invariant (n : Nat) :
    ¬ CovWMatrixRawTypedInvariant covWFunctionEnv n EnvWIrrel.bot (.sort .zero)
      covWFunctionLetSource covWFunctionTarget :=
  covWMatrix_rawClosedFailure_refutes (covWMatrix_zeta_head_raw_failure n)

theorem covWMatrix_eta_argument_raw_not_invariant (n : Nat) :
    ¬ CovWMatrixRawTypedInvariant covWFunctionEnv n EnvWIrrel.bot (.sort .zero)
      covWFunctionEtaSource covWFunctionTarget :=
  covWMatrix_rawClosedFailure_refutes (covWMatrix_eta_argument_raw_failure n)

/-- This is an instantiated finite binder-factorization failure, separately
from the syntactic positions of the invariance matrix. -/
theorem covWMatrix_function_binder_factorization_failure (n : Nat) :
    CovWMatrixClosedFailure covWFunctionEnv n 2 covWFunctionBetaSource covWFunctionTarget
      (.sort .zero) (.succ .zero) covWFunctionFine .prop ∧
    ¬ ∃ (a : CptWIrrel) (us : List CptWIrrel),
      ApproxTKWIrrel covWFunctionEnv n [] EnvWIrrel.bot covWFunctionArrow a ∧
      (∀ u ∈ us, CTyS covWFunctionEnv (covWIrrelErase u) (covWIrrelErase a)) ∧
      (∀ u ∈ us, ApproxTKWIrrel covWFunctionEnv n [] EnvWIrrel.bot covWFunctionSucc u) ∧
      ApproxTKWIrrel covWFunctionEnv n [.assumption covWFunctionArrow]
        (EnvWIrrel.cons (demandWIrrel us) EnvWIrrel.bot) covWFunctionBody covWFunctionFineR :=
  ⟨covWMatrix_beta_head_failure n, covWFunction_repaired_no_typed_factor n⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_FUNCTION_CELLS_ROOTS
#print axioms covWMatrix_beta_head_shape
#print axioms covWMatrix_zeta_head_shape
#print axioms covWMatrix_eta_hole_conversion
#print axioms covWMatrix_eta_argument_shape
#print axioms covWMatrix_eta_argument_conversion
#print axioms covWMatrix_rigid_function_position
#print axioms covWMatrix_beta_native
#print axioms covWMatrix_zeta_native
#print axioms covWMatrix_eta_argument_native
#print axioms covWMatrix_beta_head_failure
#print axioms covWMatrix_zeta_head_failure
#print axioms covWMatrix_eta_argument_failure
#print axioms covWMatrix_beta_head_raw_failure
#print axioms covWMatrix_zeta_head_raw_failure
#print axioms covWMatrix_eta_argument_raw_failure
#print axioms covWMatrix_beta_head_not_invariant
#print axioms covWMatrix_zeta_head_not_invariant
#print axioms covWMatrix_eta_argument_not_invariant
#print axioms covWMatrix_beta_head_raw_not_invariant
#print axioms covWMatrix_zeta_head_raw_not_invariant
#print axioms covWMatrix_eta_argument_raw_not_invariant
#print axioms covWMatrix_function_binder_factorization_failure
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_FUNCTION_CELLS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit

import rcic.RcicNativeTypedModelCovWNativeExpansionBoundary
import rcic.RcicNativeTypedModelCovWNativeAliasControl

/-!
# Full function-observation equality fails in an application context

The two functions are an actual native eta pair. Both have only bottom
observations, at every context and valuation; their entire observation sets
agree, not only their strictly typed subsets. Applying both functions to the
same constructor proof distinguishes them. This composes the Ho prefix and
beta-alias exclusions, and supplies actual occurrence typings and the native
eta/application conversion. closure_claim = 0.
-/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelCovTAudit TypedModelCovWIrrelAudit TypedModelCovWMatrixAudit

def covWNativeHoArrow : Expr Nat := .pi (.const 63 []) (.sort (.succ .zero))

def covWNativeHo_prefix_arrow_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covWNativeHoPrefix covWNativeHoArrow := by
  apply HasTyT.conv Γ covWNativeHoPrefix _ covWNativeHoArrow _
    (covWNativeHo_prefix_ty n Γ)
  exact .pi Γ (.const 63 []) (.const 63 []) (.app covUHoMotive (.bvar 0))
    (.sort (.succ .zero)) .zero (.succ (.succ .zero))
    (.refl _ _ _ (.const Γ 63 [] covUHoFam rfl rfl rfl))
    (.beta _ _ _ _ _ _ (.const _ 63 [] covUHoFam rfl rfl rfl)
      (.sort _ _) (.bvar _ 0 _ rfl))

def covWNativeHo_eta_conv (n : Nat) (Γ : LCtx) :
    ConvT covUHoEnv n Γ covWNativeHoBetaFn covWNativeHoPrefix covWNativeHoArrow :=
  .eta _ _ _ _ (covWNativeHo_prefix_arrow_ty n Γ)

def covWNativeHo_eta_context_conv (n : Nat) (Γ : LCtx) :
    ConvT covUHoEnv n Γ covWNativeHoBetaSource covWMatrixIotaSource
      (.sort (.succ .zero)) :=
  .app _ _ _ _ _ _ _ (covWNativeHo_eta_conv n Γ)
    (.refl _ _ _ (covWMatrixIotaMajor_ty n Γ))

theorem covWNativeHo_functions_all_tagged (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (c : CptWIrrel) :
    ApproxTKWNative covUHoEnv n Γ ρ covWNativeHoBetaFn c ↔
    ApproxTKWNative covUHoEnv n Γ ρ covWNativeHoPrefix c := by
  constructor
  · intro h
    obtain rfl := covWNativeHo_beta_fn_only_bot h
    exact .bot _ _ _
  · intro h
    obtain rfl := covWNativeHo_prefix_only_bot h
    exact .bot _ _ _

theorem covWNativeHo_functions_all_public (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (c : CptT) :
    CovWNativeObservation covUHoEnv n Γ ρ covWNativeHoBetaFn c ↔
    CovWNativeObservation covUHoEnv n Γ ρ covWNativeHoPrefix c := by
  constructor
  · rintro ⟨d, he, hd⟩
    exact ⟨d, he, (covWNativeHo_functions_all_tagged n Γ ρ d).mp hd⟩
  · rintro ⟨d, he, hd⟩
    exact ⟨d, he, (covWNativeHo_functions_all_tagged n Γ ρ d).mpr hd⟩

theorem covWNativeHo_functions_typed_equal (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) :
    CovWNativeTypedInvariant covUHoEnv n Γ ρ covWNativeHoArrow
      covWNativeHoBetaFn covWNativeHoPrefix :=
  fun _ _ c _ => covWNativeHo_functions_all_public n Γ ρ c

def covWNativeHoFunctionContext : CovWNativeContext :=
  .appFunction .hole covWMatrixIotaMajor

theorem covWNativeHo_function_context_not_equal (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) :
    ¬ CovWNativeTypedInvariant covUHoEnv n Γ ρ (.sort (.succ .zero))
      (covWNativeFill covWNativeHoFunctionContext covWNativeHoBetaFn)
      (covWNativeFill covWNativeHoFunctionContext covWNativeHoPrefix) :=
  covWNativeHo_beta_not_typed_equal n Γ ρ

theorem covWNativeHo_arrow_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covUHoEnv n Γ ρ covWNativeHoArrow (.pi .bot [([], .sort)]) :=
  covWNative_type_sort_row (.sort _ _ (.succ .zero))

theorem covWNativeHo_arrow_demand :
    CTyS covUHoEnv (covWIrrelErase (.lam [([], .prop)]))
      (covWIrrelErase (.pi .bot [([], .sort)])) :=
  covWNative_empty_graph_typed_sort_pi .prop

theorem covWNativeHo_eta_function_failure_inhabited (n : Nat) :
    Nonempty (EnvWfT covUHoEnv) ∧ Nonempty (CtxWfT covUHoEnv n []) ∧
    Nonempty (HasTyT covUHoEnv n [] covWNativeHoArrow
      (.sort (.imax .zero (.succ (.succ .zero))))) ∧
    Nonempty (HasTyT covUHoEnv n [] covWNativeHoBetaFn covWNativeHoArrow) ∧
    Nonempty (HasTyT covUHoEnv n [] covWNativeHoPrefix covWNativeHoArrow) ∧
    Nonempty (ConvT covUHoEnv n [] covWNativeHoBetaFn covWNativeHoPrefix covWNativeHoArrow) ∧
    Nonempty (HasTyT covUHoEnv n [] covWMatrixIotaMajor (.const 63 [])) ∧
    CovWNativeOccurrence covUHoEnv n [] covWNativeHoBetaFn covWMatrixIotaMajor
      (.const 63 []) (.sort (.succ .zero)) ∧
    CovWNativeOccurrence covUHoEnv n [] covWNativeHoPrefix covWMatrixIotaMajor
      (.const 63 []) (.sort (.succ .zero)) ∧
    CovWMatrixNativePair covUHoEnv n covWNativeHoBetaSource covWMatrixIotaSource
      (.sort (.succ .zero)) (.succ (.succ .zero)) ∧
    Nonempty (ConvT covUHoEnv n [] covWNativeHoBetaSource covWMatrixIotaSource
      (.sort (.succ .zero))) ∧
    CovWNativeRealized covUHoEnv n 1 [] EnvWIrrel.bot SubstT.id ∧
    ApproxTKWNative covUHoEnv n [] EnvWIrrel.bot covWNativeHoArrow
      (.pi .bot [([], .sort)]) ∧
    CTyS covUHoEnv (covWIrrelErase (.lam [([], .prop)]))
      (covWIrrelErase (.pi .bot [([], .sort)])) ∧
    (covWIrrelErase (.lam [([], .prop)]) ≠ .bot) ∧
    (∀ ρ c, CovWNativeObservation covUHoEnv n [] ρ covWNativeHoBetaFn c ↔
      CovWNativeObservation covUHoEnv n [] ρ covWNativeHoPrefix c) ∧
    CovWNativeObservation covUHoEnv n [] EnvWIrrel.bot (.sort (.succ .zero)) .sort ∧
    CTyS covUHoEnv .prop .sort ∧
    (CptT.prop ≠ .bot) ∧
    CovWNativeObservation covUHoEnv n [] EnvWIrrel.bot covWMatrixIotaSource .prop ∧
    ¬ CovWNativeObservation covUHoEnv n [] EnvWIrrel.bot covWNativeHoBetaSource .prop :=
  ⟨⟨covUHoEnv_wf⟩, ⟨.nil⟩,
    ⟨.pi [] (.const 63 []) .zero (.sort (.succ .zero)) (.succ (.succ .zero))
      (.const [] 63 [] covUHoFam rfl rfl rfl) (.sort _ _)⟩,
    ⟨covWNativeHo_beta_fn_ty n []⟩, ⟨covWNativeHo_prefix_arrow_ty n []⟩,
    ⟨covWNativeHo_eta_conv n []⟩, ⟨covWMatrixIotaMajor_ty n []⟩,
    ⟨⟨covWNativeHo_beta_fn_ty n []⟩, ⟨covWMatrixIotaMajor_ty n []⟩⟩,
    ⟨⟨covWNativeHo_prefix_arrow_ty n []⟩, ⟨covWMatrixIotaMajor_ty n []⟩⟩,
    covWNativeHo_beta_pair n, ⟨covWNativeHo_eta_context_conv n []⟩,
    covWNative_realized_nil covUHoEnv n 1,
    covWNativeHo_arrow_observed n [] EnvWIrrel.bot, covWNativeHo_arrow_demand,
    (by intro h; cases h),
    covWNativeHo_functions_all_public n [],
    covWNative_observation_of (.sort [] EnvWIrrel.bot (.succ .zero)),
    covWMatrix_iota_compact_typed, (by intro h; cases h),
    covWNative_observation_of (covWNative_iota_source_prop n [] EnvWIrrel.bot),
    covWNativeHo_beta_prop_absent n [] EnvWIrrel.bot⟩

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_ETA_FUNCTION_BOUNDARY_ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoArrow
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_prefix_arrow_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_eta_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_eta_context_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_functions_all_tagged
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_functions_all_public
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_functions_typed_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoFunctionContext
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_function_context_not_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_arrow_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_arrow_demand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_eta_function_failure_inhabited
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_ETA_FUNCTION_BOUNDARY_ROOTS

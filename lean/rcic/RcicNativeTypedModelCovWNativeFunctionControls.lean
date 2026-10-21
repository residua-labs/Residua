import rcic.RcicNativeTypedModelCovWNativeCore
import rcic.RcicNativeTypedModelCovWIrrelFunctionRepairBoundary

/-!
# Actual function fields in G, including the beta and let bodies

The selected native domain is Nat -> Nat. Its atomic rigid compact is
rejected, and a strictly typed successor graph is retained. G succ, G eta,
the beta source, and the let source all supply the same nonbottom result
with that graph as its field. The lambda body uses actual native typing of
its variable argument in the extended context, so no raw `.free` bypass or
compact-prefix classifier is used.

These are direct local controls. They do not claim equality of every typed
observation of the four terms. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelCovTAudit
open TypedModelCovWAudit TypedModelCovWTypedAudit TypedModelCovWIrrelAudit
open TypedModelCovWEtaAudit ReadbackCKAudit ReadbackCK2Audit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def covWNativeFunctionResult : CptWIrrel := .spine 4 [] [covWFunctionGraphR]

theorem covWNativeFunction_nat_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covWFunctionEnv n Γ ρ (.const 0 []) (.spine 0 [] []) :=
  .const Γ ρ 0 [] covWFunction_nat_rigid covWFunction_nat_not_propCtor

theorem covWNativeFunction_succ_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covWFunctionEnv n Γ ρ covWFunctionSucc covWFunctionAtomR :=
  .const Γ ρ 2 [] covWFunction_succ_rigid covWFunction_succ_not_propCtor

theorem covWNativeFunction_arrow_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covWFunctionEnv n Γ ρ covWFunctionArrow covWFunctionArrowCodeR := by
  refine .pi (covWNativeFunction_nat_observed n Γ ρ) ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact covWNativeFunction_nat_observed n _ _

theorem covWNativeFunction_succ_graph (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covWFunctionEnv n Γ ρ covWFunctionSucc covWFunctionGraphR := by
  refine .eta (covWFunction_succ_ty n Γ) (covWNativeFunction_nat_observed n Γ ρ) ?_ ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · exact ⟨_, List.mem_singleton.mpr rfl, fun h => CptWIrrel.noConfusion h⟩
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact covWNative_guarded_appSpine_bot
      (covWFunction_succ_ty n (.assumption (.const 0 []) :: Γ))
      (.bvar _ 0 _ rfl) (covWNativeFunction_succ_observed n _ _)

theorem covWNativeFunction_eta_graph (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covWFunctionEnv n Γ ρ covWFunctionEta covWFunctionGraphR := by
  refine .lam (covWNativeFunction_nat_observed n Γ ρ) ?_ ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · exact ⟨_, List.mem_singleton.mpr rfl, fun h => CptWIrrel.noConfusion h⟩
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact covWNative_guarded_appSpine_bot
      (covWFunction_succ_ty n (.assumption (.const 0 []) :: Γ))
      (.bvar _ 0 _ rfl) (covWNativeFunction_succ_observed n _ _)

/-- The argument has its actual native type in this exact context. -/
theorem covWNativeFunction_graph_field {n : Nat} {Γ : LCtx}
    (hΓ : CtxWfT covWFunctionEnv n Γ) {x : Expr Nat}
    (hx : HasTyT covWFunctionEnv n Γ x covWFunctionArrow) :
    CovWNativeFieldAt covWFunctionEnv n Γ covWFunctionG x
      covWFunctionArrow (.sort .zero) covWFunctionGraphR := by
  refine ⟨⟨⟨covWFunction_g_ty n Γ⟩, ⟨hx⟩⟩, ?_, ?_⟩
  · intro hp
    exact (covWIrrel_natArrow_notProp covWFunctionEnv_wf covWFunctionEnv_inScope
      hΓ rfl hp).elim
  · intro _
    exact Or.inr ⟨_, rfl⟩

theorem covWNativeFunction_apply_graph (n : Nat) (Γ : LCtx)
    (hΓ : CtxWfT covWFunctionEnv n Γ) (ρ : EnvWIrrel) {x : Expr Nat}
    (hx : HasTyT covWFunctionEnv n Γ x covWFunctionArrow)
    (ho : ApproxTKWNative covWFunctionEnv n Γ ρ x covWFunctionGraphR) :
    ApproxTKWNative covWFunctionEnv n Γ ρ (.app covWFunctionG x)
      covWNativeFunctionResult := by
  refine .appSpine
    (.const Γ ρ 4 [] covWFunction_g_rigid covWFunction_g_not_propCtor) ho ?_ ?_
  · intro hp
    exact (covWFunction_g_nonproof_position n hp).elim
  · exact ⟨covWFunctionArrow, .sort .zero, covWNativeFunction_graph_field hΓ hx⟩

theorem covWNativeFunction_target_graph (n : Nat) (Γ : LCtx)
    (hΓ : CtxWfT covWFunctionEnv n Γ) (ρ : EnvWIrrel) :
    ApproxTKWNative covWFunctionEnv n Γ ρ covWFunctionTarget covWNativeFunctionResult :=
  covWNativeFunction_apply_graph n Γ hΓ ρ (covWFunction_succ_ty n Γ)
    (covWNativeFunction_succ_graph n Γ ρ)

theorem covWNativeFunction_eta_target_graph (n : Nat) (Γ : LCtx)
    (hΓ : CtxWfT covWFunctionEnv n Γ) (ρ : EnvWIrrel) :
    ApproxTKWNative covWFunctionEnv n Γ ρ covWFunctionEtaSource covWNativeFunctionResult :=
  covWNativeFunction_apply_graph n Γ hΓ ρ (covWFunction_eta_ty n Γ)
    (covWNativeFunction_eta_graph n Γ ρ)

theorem covWNativeFunction_beta_graph (n : Nat) (Γ : LCtx)
    (hΓ : CtxWfT covWFunctionEnv n Γ) (ρ : EnvWIrrel) :
    ApproxTKWNative covWFunctionEnv n Γ ρ covWFunctionBetaSource covWNativeFunctionResult := by
  refine .app (g := [([covWFunctionGraphR], covWNativeFunctionResult)])
    (s := ([covWFunctionGraphR], covWNativeFunctionResult)) ?_
    (List.mem_singleton.mpr rfl) ?_
  · refine .lam (covWNativeFunction_arrow_observed n Γ ρ) ?_ ?_ ?_
    · intro s hs u hu
      obtain rfl := List.mem_singleton.mp hs
      obtain rfl := List.mem_singleton.mp hu
      exact covWFunction_graph_typedR
    · exact ⟨_, List.mem_singleton.mpr rfl, fun h => CptWIrrel.noConfusion h⟩
    · intro s hs
      obtain rfl := List.mem_singleton.mp hs
      exact covWNativeFunction_apply_graph n _
        (.assumption Γ covWFunctionArrow (.imax (.succ .zero) (.succ .zero))
          hΓ (covWFunction_arrow_ty n Γ)) _
        (.bvar _ 0 _ rfl) (.bvar (List.mem_singleton.mpr rfl))
  · intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact covWNativeFunction_succ_graph n Γ ρ

theorem covWNativeFunction_let_graph (n : Nat) (Γ : LCtx)
    (hΓ : CtxWfT covWFunctionEnv n Γ) (ρ : EnvWIrrel) :
    ApproxTKWNative covWFunctionEnv n Γ ρ covWFunctionLetSource covWNativeFunctionResult :=
  .letE (covWNativeFunction_beta_graph n Γ hΓ ρ)

theorem covWNativeFunction_result_typed :
    CTyS covWFunctionEnv (covWIrrelErase covWNativeFunctionResult) .prop := by
  rw [CTyS]
  exact Or.inr (.spine (m := covWFunctionGMember) rfl rfl)

/-- The old atomic field fails at the actual displayed Nat-arrow domain.
This is an exact occurrence statement, not a native typing uniqueness claim. -/
theorem covWNativeFunction_old_atom_rejected (n : Nat) (Γ : LCtx) (x : Expr Nat) :
    ¬ CovWNativeFieldAt covWFunctionEnv n Γ covWFunctionG x
      covWFunctionArrow (.sort .zero) covWFunctionAtomR := by
  intro h
  exact covWNative_fieldAt_no_function_atom h (.refl Γ covWFunctionArrow)

theorem covWNativeFunction_four_graph_controls (n : Nat) :
    Nonempty (EnvWfT covWFunctionEnv) ∧ Nonempty (CtxWfT covWFunctionEnv n []) ∧
    CovWNativeRealized covWFunctionEnv n 4 [] EnvWIrrel.bot SubstT.id ∧
    Nonempty (HasTyT covWFunctionEnv n [] covWFunctionTarget (.sort .zero)) ∧
    Nonempty (HasTyT covWFunctionEnv n [] covWFunctionEtaSource (.sort .zero)) ∧
    Nonempty (HasTyT covWFunctionEnv n [] covWFunctionBetaSource (.sort .zero)) ∧
    Nonempty (HasTyT covWFunctionEnv n [] covWFunctionLetSource (.sort .zero)) ∧
    Nonempty (ConvT covWFunctionEnv n [] covWFunctionEtaSource covWFunctionTarget (.sort .zero)) ∧
    Nonempty (ConvT covWFunctionEnv n [] covWFunctionBetaSource covWFunctionTarget (.sort .zero)) ∧
    Nonempty (ConvT covWFunctionEnv n [] covWFunctionLetSource covWFunctionTarget (.sort .zero)) ∧
    CovWNativeObservation covWFunctionEnv n [] EnvWIrrel.bot (.sort .zero) .prop ∧
    CTyS covWFunctionEnv (covWIrrelErase covWNativeFunctionResult) .prop ∧
    covWNativeFunctionResult ≠ .bot ∧
    ApproxTKWNative covWFunctionEnv n [] EnvWIrrel.bot covWFunctionTarget covWNativeFunctionResult ∧
    ApproxTKWNative covWFunctionEnv n [] EnvWIrrel.bot covWFunctionEtaSource covWNativeFunctionResult ∧
    ApproxTKWNative covWFunctionEnv n [] EnvWIrrel.bot covWFunctionBetaSource covWNativeFunctionResult ∧
    ApproxTKWNative covWFunctionEnv n [] EnvWIrrel.bot covWFunctionLetSource covWNativeFunctionResult :=
  ⟨⟨covWFunctionEnv_wf⟩, ⟨.nil⟩, covWNative_realized_nil covWFunctionEnv n 4,
    ⟨covWFunction_target_ty n []⟩, ⟨covWFunction_eta_source_ty n []⟩,
    ⟨covWFunction_beta_source_ty n []⟩, ⟨covWFunction_let_source_ty n []⟩,
    ⟨covWFunction_eta_conv n []⟩, ⟨covWFunction_beta_conv n []⟩,
    ⟨covWFunction_let_conv n []⟩, covWNative_observation_of (.sort [] EnvWIrrel.bot .zero),
    covWNativeFunction_result_typed, (by intro h; cases h),
    covWNativeFunction_target_graph n [] .nil EnvWIrrel.bot,
    covWNativeFunction_eta_target_graph n [] .nil EnvWIrrel.bot,
    covWNativeFunction_beta_graph n [] .nil EnvWIrrel.bot,
    covWNativeFunction_let_graph n [] .nil EnvWIrrel.bot⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_FUNCTION_CONTROLS_ROOTS
#print axioms covWNativeFunctionResult
#print axioms covWNativeFunction_nat_observed
#print axioms covWNativeFunction_succ_observed
#print axioms covWNativeFunction_arrow_observed
#print axioms covWNativeFunction_succ_graph
#print axioms covWNativeFunction_eta_graph
#print axioms covWNativeFunction_graph_field
#print axioms covWNativeFunction_apply_graph
#print axioms covWNativeFunction_target_graph
#print axioms covWNativeFunction_eta_target_graph
#print axioms covWNativeFunction_beta_graph
#print axioms covWNativeFunction_let_graph
#print axioms covWNativeFunction_result_typed
#print axioms covWNativeFunction_old_atom_rejected
#print axioms covWNativeFunction_four_graph_controls
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_FUNCTION_CONTROLS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

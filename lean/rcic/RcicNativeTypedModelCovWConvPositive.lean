import rcic.RcicNativeTypedModelCovWConvCore
import rcic.RcicNativeFamModelK
import rcic.RcicNativeTypedModelCovWBasicK
import rcic.RcicAndHeadStepNoGo

/-!
Positive controls built in the new observation grammar.  Legacy True,
Eq and And calls use their actual iota endpoint typings.  The neutral
True and eta-index Eq calls use the additional checked K occurrence data.

The displayed common codes are positive observations.  They do not assert
equality of every observation of the compared terms.  In particular, this
file supplies the original And iota control. The separate AndK module
extracts canonical field typings and supplies the complete aligned And K
certificate; neither module infers all-observation equality from these codes.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelKAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelKFragmentAudit TypedModelKIndexFreeAudit TypedModelKGuardAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit ReadbackCK2IndexAudit
open TypedModelCovWAudit TypedModelCovWMatrixAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem covWConv_positive_empty_application
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {f x : Expr Nat} {c : CptWConvR}
    (h : ApproxTKWConv E n Γ ρ f (.lam [([], c)])) :
    ApproxTKWConv E n Γ ρ (.app f x) c :=
  .app h (List.mem_singleton.mpr rfl)
    (fun u hu => (List.not_mem_nil u hu).elim)

private theorem covWConv_positive_empty_lambda
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {A b : Expr Nat} {c : CptWConvR} (hc : c ≠ .bot)
    (h : ApproxTKWConv E n (.assumption A :: Γ)
      (EnvWConvR.cons (demandWConvR []) ρ) b c) :
    ApproxTKWConv E n Γ ρ (.lam A b) (.lam [([], c)]) := by
  refine .lam (.bot _ _ _) ?_
    ⟨([], c), List.mem_singleton.mpr rfl, hc⟩ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil u hu).elim
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact h

theorem covWConv_empty_pi_observed (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvWConvR) (A B : Expr Nat) :
    ApproxTKWConv E n Γ ρ (.pi A B) (.pi .bot []) :=
  .pi (.bot _ _ _)
    (fun _ hs => (List.not_mem_nil _ hs).elim)
    (fun _ hs => (List.not_mem_nil _ hs).elim)

/-- Public observations also expand along a checked legacy iota step. -/
theorem covWConv_iota_observation_expand
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {lhs rhs T : Expr Nat} {c : CptWConv}
    (hi : DerivedIota E lhs rhs)
    (hl : HasTyT E n Γ lhs T) (hr : HasTyT E n Γ rhs T)
    (h : CovWConvObservation E n Γ ρ rhs c) :
    CovWConvObservation E n Γ ρ lhs c := by
  obtain ⟨d, hd, ho⟩ := h
  exact ⟨d, hd, covWConv_iota_expand hi hl hr ho⟩

/-- The all-code expansion direction uses actual checked K occurrence data. -/
theorem covWConv_K_observation_expand
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {w : IotaWitness E} {x T : Expr Nat} {c : CptWConv}
    (hk : CovWConvKData E n Γ w x T)
    (h : CovWConvObservation E n Γ ρ (iotaRhsOf w) c) :
    CovWConvObservation E n Γ ρ
      (recCall (.const w.recRef w.ls) w.preMajor x) c := by
  obtain ⟨d, hd, ho⟩ := h
  exact ⟨d, hd, covWConv_K_expand hk ho⟩

/-! ## True: legacy constructor call and aligned neutral-major K call -/

/-- Extract the actual complete-call typing from the landed conversion. -/
def covWConv_true_call_ty {n : Nat} {Γ : LCtx} {x : Expr Nat}
    (hΓ : CtxWfT trueEnvU n Γ)
    (hx : HasTyT trueEnvU n Γ x (.const 0 [])) :
    HasTyT trueEnvU n Γ (kRec x) (.sort (.succ .zero)) :=
  (convEnds trueEnvUWfT hΓ (kRec_conv_sort hx)).2.1

def covWConv_trueIota_left_ty (n : Nat) :
    HasTyT trueEnvU n [] (iotaLhsOf wTrueRecU) (.sort (.succ .zero)) :=
  covWConv_true_call_ty .nil trueEnvUtt_ty

theorem covWConv_trueIota_observed (n : Nat) (ρ : EnvWConvR) :
    ApproxTKWConv trueEnvU n [] ρ (iotaLhsOf wTrueRecU) (.sort .zero) :=
  .iota wTrueRecU (covWConv_trueIota_left_ty n)
    (.sort _ .zero) (.sort _ _ .zero)

theorem covWConv_trueK_data (n : Nat) :
    Nonempty (CovWConvKData trueEnvU n kVarCtx wTrueRecU (.bvar 0)
      (.sort (.succ .zero))) := by
  apply covWConv_K_bvar_data (w := wTrueRecU) (Or.inl ⟨rfl, rfl, rfl⟩)
    (covW_trueK_index n).1 (covW_trueK_common n) rfl
  · exact covWConv_true_call_ty (kVarCtx_wf n) (kVar_ty n)
  · exact covWConv_true_call_ty (kVarCtx_wf n) trueEnvUtt_ty
  · exact .sort _ .zero

theorem covWConv_trueK_observed (n : Nat) (ρ : EnvWConvR) :
    ApproxTKWConv trueEnvU n kVarCtx ρ (kRec (.bvar 0)) (.sort .zero) := by
  obtain ⟨hk⟩ := covWConv_trueK_data n
  exact .recursorPropK wTrueRecU (.bvar 0) hk (.sort _ _ .zero)

theorem covWConv_trueK_conversion (n : Nat) :
    Nonempty (ConvT trueEnvU n kVarCtx (kRec (.bvar 0)) (.sort .zero)
      (.sort (.succ .zero))) := by
  obtain ⟨hk⟩ := covWConv_trueK_data n
  exact covWConv_K_sound hk

/-! ## Eq: legacy constructor call and the eta-index neutral-major call -/

theorem covWConv_eqIota_observed (n : Nat) (ρ : EnvWConvR) :
    ApproxTKWConv eqEnvT n etaEqCtx ρ
      (iotaLhsOf covWMatrixKWitness) (.sort .zero) := by
  obtain ⟨hk⟩ := covWConv_etaIndex_K_data n
  exact .iota covWMatrixKWitness hk.constructor hk.target (.sort _ _ .zero)

theorem covWConv_etaIndex_K_observed (n : Nat) (ρ : EnvWConvR) :
    ApproxTKWConv eqEnvT n etaEqCtx ρ etaIndexRedex (.sort .zero) := by
  obtain ⟨hk⟩ := covWConv_etaIndex_K_data n
  exact .recursorPropK covWMatrixKWitness (.bvar 0) hk (.sort _ _ .zero)

/-! ## And: the actual original legacy iota witness -/

theorem covWConv_andIota_rhs_observed (ρ : EnvWConvR) :
    ApproxTKWConv andEnvU 0 mixAndCtx ρ mixAndRhs (.pi .bot []) := by
  apply covWConv_positive_empty_application
  apply covWConv_positive_empty_application
  apply covWConv_positive_empty_lambda (by intro h; cases h)
  apply covWConv_positive_empty_lambda (by intro h; cases h)
  exact covWConv_empty_pi_observed _ _ _ _ _ _

theorem covWConv_andIota_observed (ρ : EnvWConvR) :
    ApproxTKWConv andEnvU 0 mixAndCtx ρ mixAndLhs (.pi .bot []) :=
  .iota mixAndW mixAndLhsTy mixAndRhsTy (covWConv_andIota_rhs_observed ρ)

/-! ## Externally visible nonbottom controls

These statements record common codes only.  The expansion lemmas above
quantify over every code in the right-to-left direction; no converse
observation theorem is assumed or inferred from a single common code.
-/

theorem covWConv_trueIota_positive (n : Nat) (ρ : EnvWConvR) :
    CovWConvObservation trueEnvU n [] ρ (iotaLhsOf wTrueRecU)
      (.sort (LevelCode.ofLevel .zero)) ∧
    CovWConvObservation trueEnvU n [] ρ (.sort .zero)
      (.sort (LevelCode.ofLevel .zero)) :=
  ⟨covWConv_observation_of (covWConv_trueIota_observed n ρ),
    covWConv_observation_of (.sort _ _ .zero)⟩

theorem covWConv_eqIota_positive (n : Nat) (ρ : EnvWConvR) :
    CovWConvObservation eqEnvT n etaEqCtx ρ (iotaLhsOf covWMatrixKWitness)
      (.sort (LevelCode.ofLevel .zero)) ∧
    CovWConvObservation eqEnvT n etaEqCtx ρ (.sort .zero)
      (.sort (LevelCode.ofLevel .zero)) :=
  ⟨covWConv_observation_of (covWConv_eqIota_observed n ρ),
    covWConv_observation_of (.sort _ _ .zero)⟩

theorem covWConv_andIota_positive (ρ : EnvWConvR) :
    CovWConvObservation andEnvU 0 mixAndCtx ρ mixAndLhs (.pi .bot []) ∧
    CovWConvObservation andEnvU 0 mixAndCtx ρ mixAndRhs (.pi .bot []) ∧
    CovWConvObservation andEnvU 0 mixAndCtx ρ mixPi (.pi .bot []) :=
  ⟨covWConv_observation_of (covWConv_andIota_observed ρ),
    covWConv_observation_of (covWConv_andIota_rhs_observed ρ),
    covWConv_observation_of (covWConv_empty_pi_observed _ _ _ _ _ _)⟩

theorem covWConv_trueK_positive (n : Nat) (ρ : EnvWConvR) :
    Nonempty (CovWConvKData trueEnvU n kVarCtx wTrueRecU (.bvar 0)
      (.sort (.succ .zero))) ∧
    CovWConvObservation trueEnvU n kVarCtx ρ (kRec (.bvar 0))
      (.sort (LevelCode.ofLevel .zero)) ∧
    CovWConvObservation trueEnvU n kVarCtx ρ (.sort .zero)
      (.sort (LevelCode.ofLevel .zero)) :=
  ⟨covWConv_trueK_data n,
    covWConv_observation_of (covWConv_trueK_observed n ρ),
    covWConv_observation_of (.sort _ _ .zero)⟩

theorem covWConv_etaIndex_K_positive (n : Nat) (ρ : EnvWConvR) :
    Nonempty (CovWConvKData eqEnvT n etaEqCtx covWMatrixKWitness (.bvar 0)
      (.sort (.succ .zero))) ∧
    CovWConvObservation eqEnvT n etaEqCtx ρ etaIndexRedex
      (.sort (LevelCode.ofLevel .zero)) ∧
    CovWConvObservation eqEnvT n etaEqCtx ρ (.sort .zero)
      (.sort (LevelCode.ofLevel .zero)) :=
  ⟨covWConv_etaIndex_K_data n,
    covWConv_observation_of (covWConv_etaIndex_K_observed n ρ),
    covWConv_observation_of (.sort _ _ .zero)⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_POSITIVE_ROOTS
#print axioms covWConv_iota_observation_expand
#print axioms covWConv_K_observation_expand
#print axioms covWConv_true_call_ty
#print axioms covWConv_trueIota_positive
#print axioms covWConv_eqIota_positive
#print axioms covWConv_andIota_positive
#print axioms covWConv_trueK_data
#print axioms covWConv_trueK_conversion
#print axioms covWConv_trueK_positive
#print axioms covWConv_etaIndex_K_positive
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_POSITIVE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

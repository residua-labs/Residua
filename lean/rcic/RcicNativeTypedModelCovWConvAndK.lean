import rcic.RcicNativeTypedModelCovWConvPositive

/-!
The canonical And K occurrence has all three required endpoint typings.
The selector typings are extracted from the transparent, already checked
constructor typing by application inversion; they are not rebuilt here.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelKAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelKFragmentAudit TypedModelKIndexFreeAudit TypedModelKGuardAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit ReadbackCK2IndexAudit
open TypedModelCovWAudit TypedModelCovWMatrixAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def covWConvAndField0 : Expr Nat :=
  covWAndCanonWitness.fields.getD 0 (.sort .zero)

def covWConvAndField1 : Expr Nat :=
  covWAndCanonWitness.fields.getD 1 (.sort .zero)

private def covWConvAndCtorPrefix : Expr Nat :=
  foldApps (.const 1 []) [.bvar 4, .bvar 3]

private def covWConvAndCtorOne : Expr Nat :=
  .app covWConvAndCtorPrefix covWConvAndField0

/-- Inversion computes on the public constructor typing's last application. -/
def covWConv_andK_field1_ty :
    HasTyT andEnvU 0 mixAndCtx covWConvAndField1 (.bvar 3) := by
  let hi := hasTyTInv_app covW_andK_canon_typed
    (show ctorMajorRec covWAndCanonWitness =
      .app covWConvAndCtorOne covWConvAndField1 from rfl)
  exact hi.2.2.2.1

/-- The preceding application supplies the first actual canonical field. -/
def covWConv_andK_field0_ty :
    HasTyT andEnvU 0 mixAndCtx covWConvAndField0 (.bvar 4) := by
  let hi := hasTyTInv_app covW_andK_canon_typed
    (show ctorMajorRec covWAndCanonWitness =
      .app covWConvAndCtorOne covWConvAndField1 from rfl)
  let hj := hasTyTInv_app hi.2.2.1
    (show covWConvAndCtorOne =
      .app covWConvAndCtorPrefix covWConvAndField0 from rfl)
  exact hj.2.2.2.1

/-- The complete recursor occurrence is retyped by the actual motive beta. -/
def covWConv_andK_call_ty {x : Expr Nat}
    (hx : HasTyT andEnvU 0 mixAndCtx x mixAndFamApp) :
    HasTyT andEnvU 0 mixAndCtx
      (recCall (.const 2 [.succ (.succ .zero)]) mixAndSpine x)
      (.sort (.succ .zero)) :=
  .conv _ _ _ _ (.succ (.succ .zero))
    (.app _ _ _ _ _ mixAndRecTy hx)
    (.beta _ mixAndFamApp (.sort (.succ .zero)) x
      (.sort (.succ (.succ .zero))) .zero mixAndFamTy (.sort _ _) hx)

/-- The actual canonical fields inhabit the two domains of the actual minor. -/
def covWConv_andK_target_ty :
    HasTyT andEnvU 0 mixAndCtx (iotaRhsOf covWAndCanonWitness)
      (.sort (.succ .zero)) := by
  let ht : HasTyT andEnvU 0 mixAndCtx
      (.app (.app mixAndMin covWConvAndField0) covWConvAndField1)
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
    .app _ _ _ _ _
      (.app _ _ _ _ _ mixAndMinTyNat covWConv_andK_field0_ty)
      covWConv_andK_field1_ty
  exact .conv _ _ _ _ _ ht
    (.sorts _ (.imax (.succ .zero) (.succ .zero)) (.succ .zero) (fun _ => rfl))

theorem covWConv_andK_data :
    Nonempty (CovWConvKData andEnvU 0 mixAndCtx covWAndCanonWitness
      (.bvar 0) (.sort (.succ .zero))) := by
  apply covWConv_K_bvar_data (w := covWAndCanonWitness)
    covW_andK_canon covW_andK_index.1 covW_andK_common rfl
  · exact covWConv_andK_call_ty mixTyH
  · exact covWConv_andK_call_ty covW_andK_canon_typed
  · exact covWConv_andK_target_ty

theorem covWConv_andK_conversion :
    Nonempty (ConvT andEnvU 0 mixAndCtx mixAndRedex
      (iotaRhsOf covWAndCanonWitness) (.sort (.succ .zero))) := by
  obtain ⟨hk⟩ := covWConv_andK_data
  exact covWConv_K_sound hk

theorem covWConv_andK_native :
    WhStepCK2 andEnvU 0 mixAndCtx mixAndRedex
      (iotaRhsOf covWAndCanonWitness) := by
  obtain ⟨hk⟩ := covWConv_andK_data
  exact covWConv_K_native hk

private theorem covWConv_andK_empty_application
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {f x : Expr Nat} {c : CptWConvR}
    (h : ApproxTKWConv E n Γ ρ f (.lam [([], c)])) :
    ApproxTKWConv E n Γ ρ (.app f x) c :=
  .app h (List.mem_singleton.mpr rfl)
    (fun u hu => (List.not_mem_nil u hu).elim)

private theorem covWConv_andK_empty_lambda
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

theorem covWConv_andK_rhs_observed (ρ : EnvWConvR) :
    ApproxTKWConv andEnvU 0 mixAndCtx ρ
      (iotaRhsOf covWAndCanonWitness) (.pi .bot []) := by
  apply covWConv_andK_empty_application
  apply covWConv_andK_empty_application
  apply covWConv_andK_empty_lambda (by intro h; cases h)
  apply covWConv_andK_empty_lambda (by intro h; cases h)
  exact covWConv_empty_pi_observed _ _ _ _ _ _

theorem covWConv_andK_observed (ρ : EnvWConvR) :
    ApproxTKWConv andEnvU 0 mixAndCtx ρ mixAndRedex (.pi .bot []) := by
  obtain ⟨hk⟩ := covWConv_andK_data
  exact .recursorPropK covWAndCanonWitness (.bvar 0) hk
    (covWConv_andK_rhs_observed ρ)

/-- Common positive codes; no equality of all observations is asserted. -/
theorem covWConv_andK_positive (ρ : EnvWConvR) :
    Nonempty (CovWConvKData andEnvU 0 mixAndCtx covWAndCanonWitness
      (.bvar 0) (.sort (.succ .zero))) ∧
    CovWConvObservation andEnvU 0 mixAndCtx ρ mixAndRedex (.pi .bot []) ∧
    CovWConvObservation andEnvU 0 mixAndCtx ρ
      (iotaRhsOf covWAndCanonWitness) (.pi .bot []) ∧
    CovWConvObservation andEnvU 0 mixAndCtx ρ mixPi (.pi .bot []) :=
  ⟨covWConv_andK_data,
    covWConv_observation_of (covWConv_andK_observed ρ),
    covWConv_observation_of (covWConv_andK_rhs_observed ρ),
    covWConv_observation_of (covWConv_empty_pi_observed _ _ _ _ _ _)⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_AND_K_ROOTS
#print axioms covWConv_andK_field0_ty
#print axioms covWConv_andK_field1_ty
#print axioms covWConv_andK_call_ty
#print axioms covWConv_andK_target_ty
#print axioms covWConv_andK_data
#print axioms covWConv_andK_conversion
#print axioms covWConv_andK_native
#print axioms covWConv_andK_rhs_observed
#print axioms covWConv_andK_observed
#print axioms covWConv_andK_positive
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_AND_K_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

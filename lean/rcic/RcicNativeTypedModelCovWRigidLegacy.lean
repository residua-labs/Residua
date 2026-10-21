import rcic.RcicNativeTypedModelCovWRigidTransport

/-! Legacy positive controls survive by the general grammar transport.
Eq has no newly admitted rigid recursor, so the two grammars coincide in
all contexts made solely of assumptions. -/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit

open FamModelAudit FamModelKAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelKFragmentAudit TypedModelKIndexFreeAudit TypedModelKGuardAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit ReadbackCK2IndexAudit
open TypedModelCovWAudit TypedModelCovWMatrixAudit
open TypedModelCovWNativeAudit TypedModelCovWConvAudit

theorem covWRigid_eq_no_recursors (r : Nat) : ¬ CovWRigidRecursor eqEnvT r := by
  rintro ⟨m, hm, hk, hw⟩
  by_cases h65 : r = 65
  · subst r
    exact hw covWMatrixKWitness rfl
  · rw [eqEnvT_mem] at hm
    simp only [h65, if_false] at hm
    by_cases h64 : r = 64
    · simp only [h64, if_true] at hm
      cases hm
      cases hk
    · simp only [h64, if_false] at hm
      by_cases h63 : r = 63
      · simp only [h63, if_true] at hm
        cases hm
        cases hk
      · simp only [h63, if_false] at hm
        cases hm

theorem covWRigid_eq_observations_iff {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {e : Expr Nat} {c : CptWConv}
    (hN : CovWRigidLocalFree Γ) :
    CovWRigidObservation eqEnvT n Γ ρ e c ↔ CovWConvObservation eqEnvT n Γ ρ e c := by
  constructor
  · rintro ⟨d, hd, ho⟩
    exact ⟨d, hd, covWRigid_to_conv covWRigid_eq_no_recursors ho hN⟩
  · exact covWRigid_observations_of_conv hN

theorem covWRigid_etaEq_localFree : CovWRigidLocalFree etaEqCtx :=
  covWRigid_localFree_cons _ (covWRigid_localFree_cons _ covWRigid_localFree_nil)

theorem covWRigid_trueVar_localFree : CovWRigidLocalFree kVarCtx :=
  covWRigid_localFree_cons _ covWRigid_localFree_nil

theorem covWRigid_mixAnd_localFree : CovWRigidLocalFree mixAndCtx :=
  covWRigid_localFree_cons _ (covWRigid_localFree_cons _
    (covWRigid_localFree_cons _ (covWRigid_localFree_cons _
      (covWRigid_localFree_cons _ covWRigid_localFree_nil))))

theorem covWRigid_trueIota_observed (n : Nat) (ρ : EnvWConvR) :
    ApproxTKWRigid trueEnvU n [] ρ (iotaLhsOf wTrueRecU) (.sort .zero) :=
  covWRigid_of_conv (covWConv_trueIota_observed n ρ) covWRigid_localFree_nil

theorem covWRigid_trueK_observed (n : Nat) (ρ : EnvWConvR) :
    ApproxTKWRigid trueEnvU n kVarCtx ρ (kRec (.bvar 0)) (.sort .zero) :=
  covWRigid_of_conv (covWConv_trueK_observed n ρ) covWRigid_trueVar_localFree

theorem covWRigid_eqIota_observed (n : Nat) (ρ : EnvWConvR) :
    ApproxTKWRigid eqEnvT n etaEqCtx ρ
      (iotaLhsOf covWMatrixKWitness) (.sort .zero) :=
  covWRigid_of_conv (covWConv_eqIota_observed n ρ) covWRigid_etaEq_localFree

theorem covWRigid_etaIndex_K_observed (n : Nat) (ρ : EnvWConvR) :
    ApproxTKWRigid eqEnvT n etaEqCtx ρ etaIndexRedex (.sort .zero) :=
  covWRigid_of_conv (covWConv_etaIndex_K_observed n ρ) covWRigid_etaEq_localFree

theorem covWRigid_andIota_observed (ρ : EnvWConvR) :
    ApproxTKWRigid andEnvU 0 mixAndCtx ρ mixAndLhs (.pi .bot []) :=
  covWRigid_of_conv (covWConv_andIota_observed ρ) covWRigid_mixAnd_localFree

theorem covWRigid_andK_observed (ρ : EnvWConvR) :
    ApproxTKWRigid andEnvU 0 mixAndCtx ρ mixAndRedex (.pi .bot []) :=
  covWRigid_of_conv (covWConv_andK_observed ρ) covWRigid_mixAnd_localFree

/-- The inhabited M fixture retains its common strict universe observation.
Equality of all typed observations is a stronger, separately measured goal. -/
theorem covWRigid_M_shared_typed (n : Nat) (ρ : EnvWConvR) :
    CovWRigidObservation eqEnvT n etaEqCtx ρ (.sort (.succ .zero))
      (.sort (LevelCode.ofLevel (.succ .zero))) ∧
    CTySConv eqEnvT (.sort (LevelCode.ofLevel .zero))
      (.sort (LevelCode.ofLevel (.succ .zero))) ∧
    CovWRigidObservation eqEnvT n etaEqCtx ρ etaIndexRedex
      (.sort (LevelCode.ofLevel .zero)) ∧
    CovWRigidObservation eqEnvT n etaEqCtx ρ
      (iotaLhsOf covWMatrixKWitness) (.sort (LevelCode.ofLevel .zero)) :=
  ⟨covWRigid_observation_of (.sort _ _ _), covWConv_prop_demand_typed _,
    covWRigid_observation_of (covWRigid_etaIndex_K_observed n ρ),
    covWRigid_observation_of (covWRigid_eqIota_observed n ρ)⟩

end Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit

-- BEGIN COVWRIGID GENERATED MISSING AXIOM ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_eq_no_recursors
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_eq_observations_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_etaEq_localFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_trueVar_localFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_mixAnd_localFree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_trueIota_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_trueK_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_eqIota_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_etaIndex_K_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_andIota_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_andK_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_M_shared_typed
-- END COVWRIGID GENERATED MISSING AXIOM ROOTS

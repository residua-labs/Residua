import rcic.RcicNativeTypedModelCovWNativeFixtures
import rcic.RcicNativeTypedModelCovWIrrelControls

/-!
# Code-free identity and total positive candidates after proof-field erasure

Every displayed observation is supplied directly in the new grammar and
then exposed at its original erased compact. The landed candidate/native
evidence is reused independently. No general observation embedding or
conversion-invariance theorem is asserted. closure_claim = 0.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelCovWIrrelAudit
open FamModelAudit FamModelKAudit FamModelLRSAudit
open PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelAudit.TypingFin TypedModelKAudit
open TypedModelKFragmentAudit TypedModelKControlAudit TypedModelKGuardAudit
open TypedModelKFailureAudit TypedModelKObstructionAudit TypedModelKTypedBetaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit ReadbackCK2IndexAudit
open ReadbackCK2NativeControlAudit ReadbackCK2ModelObstructionAudit
open TypedModelCovPAudit TypedModelCovQAudit TypedModelCovRAudit
open TypedModelCovSAudit TypedModelCovTAudit TypedModelCovVAudit TypedModelCovWAudit
open TypedModelCovZMeasureAudit TypedModelCovXAudit TypedModelCovXEtaAudit
open TypedModelCovYEtaAudit TypedModelCovZAudit TypedModelCovNormEscapeAudit
open TypedModelCovRelBoundaryAudit TypedModelCovNormConvCasesAudit PiProbeModelBoundaryAudit

open TypedModelCovWEtaAudit

theorem covWNative_identity_tower_observed (n j : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    CovWNativeObservation covZRigidIdEnv n Γ ρ (covQIdentityTowerApp j)
      (.spine 0 [.bot, .bot]) :=
  by
  have hf : HasTyT covZRigidIdEnv n Γ (.app (.const 0 []) (covQArrowTower j))
      (.pi (covQArrowTower j) (covQArrowTower j)) := by
    simpa only [covQ_identity_body_inst] using
      (HasTyT.app Γ (.const 0 []) (covQArrowTower j) (.sort (.succ .zero))
        (.pi (.bvar 0) (.bvar 1)) (covZRigidIdHead_hasTy n Γ)
        (covQArrowTower_hasTy covZRigidIdEnv n j Γ))
  exact covWNative_observation_of (covWNative_guarded_appSpine_bot hf
    (covQArrowTowerWitness_hasTy covZRigidIdEnv n j Γ)
    (covWNative_guarded_appSpine_bot (covZRigidIdHead_hasTy n Γ)
      (covQArrowTower_hasTy covZRigidIdEnv n j Γ)
      (covWNative_neutral_observed covPIdentity_neutral_head n Γ ρ)))

theorem covWNative_identity_uniform_control (n : Nat) :
    Nonempty (EnvWfT covZRigidIdEnv) ∧ Nonempty (CtxWfT covZRigidIdEnv n []) ∧
    Nonempty (HasTyT covZRigidIdEnv n [] (.const 0 []) cexPolyIdTy) ∧
    CovWNativeObservation covZRigidIdEnv n [] EnvWIrrel.bot (.const 0 []) (.spine 0 []) ∧
    covRIdentityRelation covZRigidIdEnv n []
      (.const 0 []) (.const 0 []) (.spine 0 []) ∧
    ∀ j, Nonempty (HasTyT covZRigidIdEnv n [] (covQIdentityTowerApp j)
        (covQArrowTower j)) ∧
      CovWNativeObservation covZRigidIdEnv n [] EnvWIrrel.bot (covQIdentityTowerApp j)
        (.spine 0 [.bot, .bot]) ∧
      CandidateCov covZRigidIdEnv (WhStepCK2 covZRigidIdEnv n) [] false
        (covRTowerRelation covZRigidIdEnv n [] j) ∧
      CovRJoint covZRigidIdEnv n [] (covRTowerSyntax covZRigidIdEnv j)
        (fun _ => false) (covRBaseVal covZRigidIdEnv)
        (covQIdentityTowerApp j) (covQIdentityTowerApp j) (.spine 0 [.bot, .bot]) := by
  obtain ⟨hW, hΓ, ht, ho, hrel, htower⟩ := covW_identity_uniform_control n
  refine ⟨hW, hΓ, ht,
    covWNative_observation_of (covWNative_neutral_observed covPIdentity_neutral_head n [] EnvWIrrel.bot),
    hrel, ?_⟩
  intro j
  obtain ⟨ht, ho, hc, hj⟩ := htower j
  exact ⟨ht, covWNative_identity_tower_observed n j [] EnvWIrrel.bot, hc, hj⟩

/-- The total positive PER accepts the same actual rigid proof observation,
with the independent native proof-irrelevance conversion retained. -/
theorem covWNative_proof_total_control (n : Nat) :
    Nonempty (EnvWfT covPProofEnv) ∧ Nonempty (CtxWfT covPProofEnv n []) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 0 []) (.sort .zero)) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 3 []) (.const 0 [])) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 1 []) (.const 0 [])) ∧
    Nonempty (ConvT covPProofEnv n [] (.const 3 []) (.const 1 []) (.const 0 [])) ∧
    IsPropCTP covPProofEnv (.spine 0 []) ∧
    CovWNativeObservation covPProofEnv n [] EnvWIrrel.bot (.const 0 []) (.spine 0 []) ∧
    CovWNativeObservation covPProofEnv n [] EnvWIrrel.bot (.const 3 []) (.spine 3 []) ∧
    CovWNativeObservation covPProofEnv n [] EnvWIrrel.bot (.const 1 []) .bot ∧
    CandidateCovS covPProofEnv (WhStepCK2 covPProofEnv n) [] true covSTotalRel ∧
    covSTotalRel (.const 3 []) (.const 1 []) (.spine 3 []) := by
  obtain ⟨hW, hΓ, hT, hp, hq, hc, hpos, hA, ho, hbot, hC, hrel⟩ :=
    covW_proof_total_control n
  exact ⟨hW, hΓ, hT, hp, hq, hc, hpos,
    covWNative_observation_of (covWNative_rigid_observed
      covPProof_true_rigid covPProof_true_not_propCtor n [] EnvWIrrel.bot),
    covWNative_observation_of (covWNative_rigid_observed
      covPProof_head_rigid covPProof_head_not_propCtor n [] EnvWIrrel.bot),
    ⟨.bot, rfl, .bot _ _ _⟩, hC, hrel⟩

/-- Actual True-constructor supply. This theorem makes no universal assertion
about all observations introduced by eta. -/
theorem covWNative_trueIntro_supply (n : Nat) :
    Nonempty (EnvWfT trueEnvU) ∧ Nonempty (CtxWfT trueEnvU n []) ∧
    Nonempty (HasTyT trueEnvU n [] (.const 0 []) (.sort .zero)) ∧
    Nonempty (HasTyT trueEnvU n [] (.const 1 []) (.const 0 [])) ∧
    CovWNativeObservation trueEnvU n [] EnvWIrrel.bot (.const 1 []) .bot ∧
    CandidateCovS trueEnvU (WhStepCK2 trueEnvU n) [] true covSTotalRel := by
  obtain ⟨hW, hΓ, hT, hp, ho, hC, _⟩ := covW_trueIntro_control n
  exact ⟨hW, hΓ, hT, hp, ⟨.bot, rfl, .bot _ _ _⟩, hC⟩

/-- Abel--Coquand native evidence and the displayed finite observations.
The old universal bottom-only result is not relabelled as a new-model fact. -/
theorem covWNative_abelCoquand_supply (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] AbelCoquand.top (.sort .zero)) ∧
    Nonempty (HasTyT emptyEnv n [] AbelCoquand.delta AbelCoquand.top) ∧
    Nonempty (HasTyT emptyEnv n [] covPAbelCoquandId AbelCoquand.top) ∧
    Nonempty (ConvT emptyEnv n [] AbelCoquand.delta covPAbelCoquandId
      AbelCoquand.top) ∧
    CovWNativeObservation emptyEnv n [] EnvWIrrel.bot AbelCoquand.top (.pi .bot []) ∧
    CovWNativeObservation emptyEnv n [] EnvWIrrel.bot AbelCoquand.delta .bot ∧
    CovWNativeObservation emptyEnv n [] EnvWIrrel.bot covPAbelCoquandId .bot ∧
    CandidateCovS emptyEnv (WhStepCK2 emptyEnv n) [] true covSTotalRel := by
  obtain ⟨hW, hΓ, hT, hp, hq, hc, hA, ho, hbot, hC, _⟩ :=
    covW_abelCoquand_control n
  exact ⟨hW, hΓ, hT, hp, hq, hc,
    covWNative_observation_of (covWNative_pi_nil emptyEnv n [] EnvWIrrel.bot _ _),
    ⟨.bot, rfl, .bot _ _ _⟩, ⟨.bot, rfl, .bot _ _ _⟩, hC⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_CONTROLS_ROOTS
#print axioms covWNative_identity_tower_observed
#print axioms covWNative_identity_uniform_control
#print axioms covWNative_proof_total_control
#print axioms covWNative_trueIntro_supply
#print axioms covWNative_abelCoquand_supply
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_CONTROLS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

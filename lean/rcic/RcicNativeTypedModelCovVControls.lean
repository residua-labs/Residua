import rcic.RcicNativeTypedModelCovVFixtures
import rcic.RcicNativeTypedModelCovSKControls
import rcic.RcicNativeTypedModelCovSProofAction
import rcic.RcicNativeTypedModelCovRIdentity

/-!
# Concrete controls for native-eligible proposition recursion

The guarded Eq success and both guard failures survive. The code-free rigid
identity and every finite tower retain actual observations. Total positive
PERs accept the actual neutral proof and the nonbottom proof-demand action;
the Abel--Coquand proofs retain their bottom-only observations. Native
certificates and relation witnesses below are supplied, not assumed.

The candidate definitions remain the landed R/S definitions. These local
controls do not supply a general interpretation or a fundamental case.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovVAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelAudit.TypingFin TypedModelKAudit
open TypedModelKFragmentAudit TypedModelKControlAudit TypedModelKGuardAudit
open TypedModelKFailureAudit TypedModelKObstructionAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit ReadbackCK2IndexAudit
open ReadbackCK2NativeControlAudit ReadbackCK2ModelObstructionAudit
open TypedModelCovPAudit TypedModelCovQAudit TypedModelCovRAudit
open TypedModelCovSAudit TypedModelCovTAudit TypedModelCovZMeasureAudit
open TypedModelCovXAudit TypedModelCovNormConvCasesAudit PiProbeModelBoundaryAudit

theorem covV_sort_observed (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (l : Level) : ApproxTKN E n Γ ρ (.sort l) (sortCode l) :=
  .free (kFreeT_sort E l) (.sort ρ l)

theorem covV_rigid_observed {E : ResolvedEnv} {r : Nat}
    (hr : RigidConst E r) (hn : ¬ PropCtorT E r)
    (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKN E n Γ ρ (.const r []) (.spine r []) :=
  .free (kFreeT_rigid_const hr []) (.const ρ r [] hr hn)

theorem covV_neutral_observed {E : ResolvedEnv} {r : Nat}
    (hh : NeutralHeadP E r) (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKN E n Γ ρ (.const r []) (.spine r []) := by
  apply covV_rigid_observed (neutralHeadP_rigid hh) ?_ n Γ ρ
  rintro ⟨m, fam, fm, hm, hctor, _⟩
  exact neutralHeadP_not_constructor hh hm hctor

/-- The actual guarded K observation retains its independent native and DI
guards. Native-eligible model recursion does not replace either guard. -/
theorem covV_K_eqGap_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    Nonempty (HasTyT eqEnvT n eqGapCtx eqGapRedex (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n eqGapCtx eqGapRedex (.sort .zero)
      (.sort (.succ .zero))) ∧
    KIndexGuardAt eqEnvT n eqGapCtx eqGapW ∧
    KNativeHead eqEnvT n eqGapCtx eqGapRedex (.sort .zero) ∧
    ApproxTKN eqEnvT n eqGapCtx EnvT.bot eqGapRedex .prop ∧
    ApproxTKN eqEnvT n eqGapCtx EnvT.bot (.sort .zero) .prop := by
  obtain ⟨hW, hΓ, ht, _, hc, hg, hk, _, _, _⟩ := covS_K_eqGap_control n
  exact ⟨hW, hΓ, ht, hc, hg, hk,
    covV_approxTK_of_native_heads covV_eq_native_heads
      (approxTK_eqGap_prop n EnvT.bot),
    covV_sort_observed eqEnvT n eqGapCtx EnvT.bot .zero⟩

theorem covV_K_apart_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n apartCtx) ∧
    Nonempty (HasTyT eqEnvT n apartCtx apartRec (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n apartCtx apartRec apartRec (.sort (.succ .zero))) ∧
    ApproxTKN eqEnvT n apartCtx EnvT.bot apartRec .bot ∧
    (∀ ρ c, ApproxTKN eqEnvT n apartCtx ρ apartRec c → c = .bot) ∧
    ¬ ApproxTKN eqEnvT n apartCtx EnvT.bot apartRec .prop := by
  obtain ⟨hW, hΓ, ht, hc, _, _, _, _⟩ := covS_K_apart_control n
  exact ⟨hW, hΓ, ht, hc, .bot _ _ _,
    fun _ _ h => approxTK_apartRec_bot (approxTKN_forget h),
    fun h => not_approxTK_apartRec_prop (approxTKN_forget h)⟩

theorem covV_K_eta_guard_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n etaEqCtx) ∧
    Nonempty (HasTyT eqEnvT n etaEqCtx etaIndexRedex (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n etaEqCtx etaIndexRedex (.sort .zero)
      (.sort (.succ .zero))) ∧
    KNativeHead eqEnvT n etaEqCtx etaIndexRedex (.sort .zero) ∧
    ApproxTKN eqEnvT n etaEqCtx EnvT.bot etaIndexRedex .bot ∧
    ApproxTKN eqEnvT n etaEqCtx EnvT.bot (.sort .zero) .prop ∧
    (∀ ρ c, ApproxTKN eqEnvT n etaEqCtx ρ etaIndexRedex c → c = .bot) ∧
    ¬ KIndexGuardAt eqEnvT n etaEqCtx
      (eqConvW (fun _ _ h => h) indexFn (.bvar 1) etaIndex etaIndexMot (.sort .zero)) := by
  obtain ⟨hW, hΓ, ht, _, hc, hk, _, _, _, hg, _⟩ := covS_K_eta_guard_control n
  exact ⟨hW, hΓ, ht, hc, hk, .bot _ _ _,
    covV_sort_observed eqEnvT n etaEqCtx EnvT.bot .zero,
    fun _ _ h => covS_K_eta_observation_bot (approxTKN_forget h), hg⟩

theorem covV_K_prefix_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    (∃ A B, Nonempty (HasTyT eqEnvT n eqGapCtx eqGapPrefix (.pi A B))) ∧
    ApproxTKN eqEnvT n eqGapCtx EnvT.bot eqGapPrefix .bot ∧
    (∀ ρ c, ApproxTKN eqEnvT n eqGapCtx ρ eqGapPrefix c → c = .bot) ∧
    ApproxTKN eqEnvT n eqGapCtx EnvT.bot eqGapRedex .prop := by
  obtain ⟨hW, hΓ, ht, _, _, _, _⟩ := covS_K_prefix_control n
  exact ⟨hW, hΓ, ht, .bot _ _ _,
    fun _ _ h => approxTK_eqGapPrefix_bot (approxTKN_forget h),
    covV_approxTK_of_native_heads covV_eq_native_heads
      (approxTK_eqGap_prop n EnvT.bot)⟩

theorem covV_identity_tower_observed (n j : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKN covZRigidIdEnv n Γ ρ (covQIdentityTowerApp j)
      (.spine 0 [.bot, .bot]) :=
  .appSpine (.appSpine (covV_neutral_observed covPIdentity_neutral_head n Γ ρ)
    (.bot _ _ _)) (.bot _ _ _)

/-- One unchanged code-free witness and actual observations of all tower
instances; the supplied candidate is used in both real applications. -/
theorem covV_identity_uniform_control (n : Nat) :
    Nonempty (EnvWfT covZRigidIdEnv) ∧ Nonempty (CtxWfT covZRigidIdEnv n []) ∧
    Nonempty (HasTyT covZRigidIdEnv n [] (.const 0 []) cexPolyIdTy) ∧
    ApproxTKN covZRigidIdEnv n [] EnvT.bot (.const 0 []) (.spine 0 []) ∧
    covRIdentityRelation covZRigidIdEnv n []
      (.const 0 []) (.const 0 []) (.spine 0 []) ∧
    ∀ j, Nonempty (HasTyT covZRigidIdEnv n [] (covQIdentityTowerApp j)
        (covQArrowTower j)) ∧
      ApproxTKN covZRigidIdEnv n [] EnvT.bot (covQIdentityTowerApp j)
        (.spine 0 [.bot, .bot]) ∧
      CandidateCov covZRigidIdEnv (WhStepCK2 covZRigidIdEnv n) [] false
        (covRTowerRelation covZRigidIdEnv n [] j) ∧
      CovRJoint covZRigidIdEnv n [] (covRTowerSyntax covZRigidIdEnv j)
        (fun _ => false) (covRBaseVal covZRigidIdEnv)
        (covQIdentityTowerApp j) (covQIdentityTowerApp j) (.spine 0 [.bot, .bot]) := by
  refine ⟨⟨covZRigidIdEnvWfT⟩, ⟨.nil⟩, ⟨covZRigidIdHead_hasTy n []⟩,
    covV_neutral_observed covPIdentity_neutral_head n [] EnvT.bot,
    covR_rigidIdentity_realization n [], ?_⟩
  intro j
  exact ⟨covQIdentityTowerApp_hasTy n j [],
    covV_identity_tower_observed n j [] EnvT.bot,
    covRTower_isCandidate _ n [] j, covR_identity_tower_joint n j []⟩

/-- The real nonbottom observation of a body-free proof remains accepted
by the total positive PER. Native irrelevance is independently supplied. -/
theorem covV_proof_total_control (n : Nat) :
    Nonempty (EnvWfT covPProofEnv) ∧ Nonempty (CtxWfT covPProofEnv n []) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 0 []) (.sort .zero)) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 3 []) (.const 0 [])) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 1 []) (.const 0 [])) ∧
    Nonempty (ConvT covPProofEnv n [] (.const 3 []) (.const 1 []) (.const 0 [])) ∧
    IsPropCTP covPProofEnv (.spine 0 []) ∧
    ApproxTKN covPProofEnv n [] EnvT.bot (.const 0 []) (.spine 0 []) ∧
    ApproxTKN covPProofEnv n [] EnvT.bot (.const 3 []) (.spine 3 []) ∧
    ApproxTKN covPProofEnv n [] EnvT.bot (.const 1 []) .bot ∧
    CandidateCovS covPProofEnv (WhStepCK2 covPProofEnv n) [] true covSTotalRel ∧
    covSTotalRel (.const 3 []) (.const 1 []) (.spine 3 []) := by
  obtain ⟨hW, hΓ, hT, hp, hq, hc, hpos, _⟩ := covSProof_total_control n
  exact ⟨hW, hΓ, hT, hp, hq, hc, hpos,
    covV_rigid_observed covPProof_true_rigid covPProof_true_not_propCtor n [] EnvT.bot,
    covV_rigid_observed covPProof_head_rigid covPProof_head_not_propCtor n [] EnvT.bot,
    .bot _ _ _, covSTotal_isCandidate _ (WhStepCK2 covPProofEnv n) [] true, trivial⟩

theorem covV_trueIntro_control (n : Nat) :
    Nonempty (EnvWfT trueEnvU) ∧ Nonempty (CtxWfT trueEnvU n []) ∧
    Nonempty (HasTyT trueEnvU n [] (.const 0 []) (.sort .zero)) ∧
    Nonempty (HasTyT trueEnvU n [] (.const 1 []) (.const 0 [])) ∧
    ApproxTKN trueEnvU n [] EnvT.bot (.const 1 []) .bot ∧
    CandidateCovS trueEnvU (WhStepCK2 trueEnvU n) [] true covSTotalRel ∧
    ∀ ρ c, ApproxTKN trueEnvU n [] ρ (.const 1 []) c →
      covSTotalRel (.const 1 []) (.const 1 []) c ∧ c = .bot := by
  obtain ⟨hW, hΓ, hT, hp, _⟩ := covS_trueIntro_control n
  refine ⟨hW, hΓ, hT, hp, .bot _ _ _,
    covSTotal_isCandidate _ (WhStepCK2 trueEnvU n) [] true, ?_⟩
  intro ρ c h
  exact covS_trueIntro_all_observations n [] ρ ρ c (Or.inl (approxTKN_forget h))

theorem covV_abelCoquand_control (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] AbelCoquand.top (.sort .zero)) ∧
    Nonempty (HasTyT emptyEnv n [] AbelCoquand.delta AbelCoquand.top) ∧
    Nonempty (HasTyT emptyEnv n [] covPAbelCoquandId AbelCoquand.top) ∧
    Nonempty (ConvT emptyEnv n [] AbelCoquand.delta covPAbelCoquandId
      AbelCoquand.top) ∧
    ApproxTKN emptyEnv n [] EnvT.bot AbelCoquand.top (.pi .bot []) ∧
    ApproxTKN emptyEnv n [] EnvT.bot AbelCoquand.delta .bot ∧
    ApproxTKN emptyEnv n [] EnvT.bot covPAbelCoquandId .bot ∧
    CandidateCovS emptyEnv (WhStepCK2 emptyEnv n) [] true covSTotalRel ∧
    ∀ ρ ρ' c, (ApproxTKN emptyEnv n [] ρ AbelCoquand.delta c ∨
      ApproxTKN emptyEnv n [] ρ' covPAbelCoquandId c) →
      covSTotalRel AbelCoquand.delta covPAbelCoquandId c ∧ c = .bot := by
  obtain ⟨hW, hΓ, hT, hp, hq, hc, _⟩ := covS_abelCoquand_control n
  refine ⟨hW, hΓ, hT, hp, hq, hc,
    covV_approxTK_of_native_heads covV_empty_native_heads
      (approxTK_pi_bot_nil emptyEnv n [] EnvT.bot _ _),
    .bot _ _ _, .bot _ _ _,
    covSTotal_isCandidate _ (WhStepCK2 emptyEnv n) [] true, ?_⟩
  intro ρ ρ' c h
  exact covS_abelCoquand_all_observations n [] ρ ρ' c
    (h.elim (fun h => Or.inl (approxTKN_forget h))
      (fun h => Or.inr (approxTKN_forget h)))

theorem covV_proof_demand_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKN covSProofFnEnv n Γ ρ (.app (.const 4 []) (.const 3 []))
      (.spine 4 [.spine 3 []]) :=
  .appSpine (covV_neutral_observed covSProofFn_neutral n Γ ρ)
    (covV_neutral_observed covSProofFn_argument_neutral n Γ ρ)

theorem covV_proof_demand_control (n : Nat) :
    Nonempty (EnvWfT covSProofFnEnv) ∧ Nonempty (CtxWfT covSProofFnEnv n []) ∧
    Nonempty (HasTyT covSProofFnEnv n [] (.const 3 []) (.const 0 [])) ∧
    Nonempty (HasTyT covSProofFnEnv n [] (.const 1 []) (.const 0 [])) ∧
    Nonempty (ConvT covSProofFnEnv n [] (.const 3 []) (.const 1 []) (.const 0 [])) ∧
    Nonempty (HasTyT covSProofFnEnv n [] (.app (.const 4 []) (.const 3 []))
      (.sort .zero)) ∧
    Nonempty (ConvT covSProofFnEnv n [] (.app (.const 4 []) (.const 3 []))
      (.app (.const 4 []) (.const 1 [])) (.sort .zero)) ∧
    ApproxTKN covSProofFnEnv n [] EnvT.bot (.const 3 []) (.spine 3 []) ∧
    ApproxTKN covSProofFnEnv n [] EnvT.bot (.app (.const 4 []) (.const 3 []))
      (.spine 4 [.spine 3 []]) ∧
    CandidateCovS covSProofFnEnv (WhStepCK2 covSProofFnEnv n) [] true covSTotalRel ∧
    CovXCompactAction covSProofFnEnv (.spine 4 []) [.spine 3 []]
      (.spine 4 [.spine 3 []]) ∧
    covRCodeRel covSProofFnEnv .prop (.app (.const 4 []) (.const 3 []))
      (.app (.const 4 []) (.const 1 [])) (.spine 4 [.spine 3 []]) ∧
    ¬ BotDemandT [.spine 3 []] := by
  obtain ⟨hW, hΓ, _, _, hp, hq, hc, hfp, _, hfc, _, _, _, _, hD,
    _, _, _, ha, hout, _, _, hnb⟩ := covSProofFn_nonbottom_demand_control n
  exact ⟨hW, hΓ, hp, hq, hc, hfp, hfc,
    covV_neutral_observed covSProofFn_argument_neutral n [] EnvT.bot,
    covV_proof_demand_observed n [] EnvT.bot, hD, ha, hout, hnb⟩

theorem covV_nat_rec_instance_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧
    Nonempty (HasTyT natEnvU n [] covURecInstance (.sort (.succ .zero))) ∧
    ApproxTKN natEnvU n [] EnvT.bot covURecInstance .prop ∧
    RedR (WhStepCK2 natEnvU n) [] covURecInstance (.sort .zero) :=
  ⟨⟨natEnvUWfT⟩, ⟨covURecInstance_hasTy n⟩,
    covV_approxTK_of_native_heads covV_nat_native_heads (covURecInstance_observed n).1,
    covURecInstance_read n⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_V_CONTROLS_ROOTS
#print axioms covV_sort_observed
#print axioms covV_rigid_observed
#print axioms covV_neutral_observed
#print axioms covV_K_eqGap_control
#print axioms covV_K_apart_control
#print axioms covV_K_eta_guard_control
#print axioms covV_K_prefix_control
#print axioms covV_identity_tower_observed
#print axioms covV_identity_uniform_control
#print axioms covV_proof_total_control
#print axioms covV_trueIntro_control
#print axioms covV_abelCoquand_control
#print axioms covV_proof_demand_observed
#print axioms covV_proof_demand_control
#print axioms covV_nat_rec_instance_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_V_CONTROLS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovVAudit

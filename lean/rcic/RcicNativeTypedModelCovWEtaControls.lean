import rcic.RcicNativeTypedModelCovWEtaAligned
import rcic.RcicNativeTypedModelCovWControls
import rcic.RcicNativeTypedModelCovWBasicK

/-!
# Positive controls in the typed eta observation grammar

Each displayed observation and realizer image inhabits `ApproxTKWEta`.
The embedding preserves the finite compact and its existing stage bound.
Native typing, conversion, and candidate evidence is retained explicitly.

These positive supplies do not transfer any universal bottom-only statement
from `ApproxTKW`: the new eta constructor requires a fresh proof of each such
negative control. In particular, the old proper-prefix exclusion is not
claimed here. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
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

/-- A retained native fixture together with its actual eta-model observations
and its actual closing substitution at the same finite information budget. -/
def CovWEtaFixtureAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (σ : SubstT) (x y A : Expr Nat) (c a : CptT) : Prop :=
  CovWFixtureAt E n Γ ρ σ x y A c a ∧
  ApproxTKWEtaStage E n covTFixtureStage Γ ρ x c ∧
  ApproxTKWEtaStage E n covTFixtureStage Γ ρ A a ∧
  CovWEtaRealized E n covTFixtureStage Γ ρ σ

theorem covWEta_fixture_of_old {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : EnvT} {σ : SubstT} {x y A : Expr Nat} {c a : CptT}
    (h : CovWFixtureAt E n Γ ρ σ x y A c a) :
    CovWEtaFixtureAt E n Γ ρ σ x y A c a :=
  ⟨h, covWEta_stage_of_old h.2.1, covWEta_stage_of_old h.2.2.1,
    covWEta_realized_of_old h.2.2.2⟩

theorem covWEta_fixture_natSucc_eta (n : Nat) :
    CovWEtaFixtureAt natEnvU n [] EnvT.bot SubstT.id
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      covXNatEtaEmptyRow covYNatArrowCode :=
  covWEta_fixture_of_old (covW_fixture_natSucc_eta n)

theorem covWEta_fixture_alias_in_pi (n : Nat) :
    ∃ A B, CovWEtaFixtureAt eqEnvT n eqGapCtx EnvT.bot covUEqSubst
      covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
      covNormAliasIdentityCpt (.pi .bot []) := by
  obtain ⟨A, B, h⟩ := covW_fixture_alias_in_pi n
  exact ⟨A, B, covWEta_fixture_of_old h⟩

theorem covWEta_fixture_polyPropLam (n : Nat) :
    CovWEtaFixtureAt eqEnvT n [] EnvT.bot SubstT.id
      covXPolyPropLam covXPolyPropLam covXPolyPropLamTy
      (.lam [([], .prop)]) covSPolyPropCode :=
  covWEta_fixture_of_old (covW_fixture_polyPropLam n)

theorem covWEta_fixture_alias_extension (n : Nat) :
    ∃ A B,
      Nonempty (CtxWfT eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx)) ∧
      CovWEtaFixtureAt eqEnvT n eqGapCtx EnvT.bot covUEqSubst
        idPiProp idPiProp (eqGapDirectAlias A B) (.pi .bot []) .bot := by
  obtain ⟨A, B, hΓ, h⟩ := covW_fixture_alias_extension n
  exact ⟨A, B, hΓ, covWEta_fixture_of_old h⟩

theorem covWEta_fixture_nat_coverage (n : Nat) :
    CovWEtaFixtureAt natEnvU n [] EnvT.bot SubstT.id
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covYNatArrowCode :=
  covWEta_fixture_of_old (covW_fixture_nat_coverage n)

theorem covWEta_fixture_nat_shape (n : Nat) :
    CovWEtaFixtureAt natEnvU n [] EnvT.bot SubstT.id
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covYNatArrowCode :=
  covWEta_fixture_of_old (covW_fixture_nat_shape n)

theorem covWEta_fixture_eq_anchor (n : Nat) :
    CovWEtaFixtureAt eqEnvT n eqGapCtx EnvT.bot covUEqSubst
      idPiProp idPiProp (.sort .zero) (.pi .bot []) .prop :=
  covWEta_fixture_of_old (covW_fixture_eq_anchor n)

theorem covWEta_fixture_nat_anchor (n : Nat) :
    CovWEtaFixtureAt natEnvU n [] EnvT.bot SubstT.id
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) (.spine 0 []) :=
  covWEta_fixture_of_old (covW_fixture_nat_anchor n)

theorem covWEta_sort_observed (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (l : Level) : ApproxTKWEta E n Γ ρ (.sort l) (sortCode l) :=
  covWEta_of_old (covW_sort_observed E n Γ ρ l)

theorem covWEta_rigid_observed {E : ResolvedEnv} {r : Nat}
    (hr : RigidConst E r) (hn : ¬ PropCtorT E r)
    (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta E n Γ ρ (.const r []) (.spine r []) :=
  covWEta_of_old (covW_rigid_observed hr hn n Γ ρ)

theorem covWEta_neutral_observed {E : ResolvedEnv} {r : Nat}
    (hh : NeutralHeadP E r) (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta E n Γ ρ (.const r []) (.spine r []) :=
  covWEta_of_old (covW_neutral_observed hh n Γ ρ)

/-- The actual guarded Eq success retains both native guards and its precise
nonbottom observation; no premise is replaced by eta. -/
theorem covWEta_K_eqGap_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    Nonempty (HasTyT eqEnvT n eqGapCtx eqGapRedex (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n eqGapCtx eqGapRedex (.sort .zero)
      (.sort (.succ .zero))) ∧
    KIndexGuardAt eqEnvT n eqGapCtx eqGapW ∧
    KNativeHead eqEnvT n eqGapCtx eqGapRedex (.sort .zero) ∧
    ApproxTKWEta eqEnvT n eqGapCtx EnvT.bot eqGapRedex .prop ∧
    ApproxTKWEta eqEnvT n eqGapCtx EnvT.bot (.sort .zero) .prop := by
  obtain ⟨hW, hΓ, ht, hc, hg, hk, ho, hs⟩ := covW_K_eqGap_control n
  exact ⟨hW, hΓ, ht, hc, hg, hk, covWEta_of_old ho, covWEta_of_old hs⟩

theorem covWEta_trueK_control (n : Nat) :
    Nonempty (EnvWfT trueEnvU) ∧ Nonempty (CtxWfT trueEnvU n kVarCtx) ∧
    Nonempty (NativeSpineHead.Step trueEnvU n kVarCtx
      (kRec (.bvar 0)) (.sort .zero) (.sort (.succ .zero))) ∧
    Nonempty (ConvT trueEnvU n kVarCtx (.sort .zero)
      (kRec (.bvar 0)) (.sort (.succ .zero))) ∧
    KIndexGuardAt trueEnvU n kVarCtx wTrueRecU ∧
    KCommonAt trueEnvU n kVarCtx wTrueRecU (.bvar 0) ∧
    ApproxTKWEta trueEnvU n kVarCtx EnvT.bot (kRec (.bvar 0)) .prop ∧
    RedR (WhStepCK2 trueEnvU n) kVarCtx (kRec (.bvar 0)) (.sort .zero) := by
  obtain ⟨hW, hΓ, hs, hc, hi, hcommon, ho, hr⟩ := covW_trueK_control n
  exact ⟨hW, hΓ, hs, hc, hi, hcommon, covWEta_of_old ho, hr⟩

theorem covWEta_andK_control :
    Nonempty (EnvWfT andEnvU) ∧ Nonempty (CtxWfT andEnvU 0 mixAndCtx) ∧
    Nonempty (NativeSpineHead.Step andEnvU 0 mixAndCtx mixAndRedex mixAndRhs
      (.app mixAndMot mixAndMkApp)) ∧
    Nonempty (ConvT andEnvU 0 mixAndCtx mixAndRedex mixPi
      (.sort (.imax (.succ .zero) (.succ .zero)))) ∧
    KIndexGuardAt andEnvU 0 mixAndCtx covWAndCanonWitness ∧
    KCommonAt andEnvU 0 mixAndCtx covWAndCanonWitness (.bvar 0) ∧
    ApproxTKWEta andEnvU 0 mixAndCtx EnvT.bot mixAndRedex (.pi .bot []) ∧
    RedR (WhStepCK2 andEnvU 0) mixAndCtx mixAndRedex mixPi := by
  obtain ⟨hW, hΓ, hs, hc, hi, hcommon, ho, hr⟩ := covW_andK_control
  exact ⟨hW, hΓ, hs, hc, hi, hcommon, covWEta_of_old ho, hr⟩

theorem covWEta_identity_tower_observed (n j : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covZRigidIdEnv n Γ ρ (covQIdentityTowerApp j)
      (.spine 0 [.bot, .bot]) :=
  covWEta_of_old (covW_identity_tower_observed n j Γ ρ)

theorem covWEta_identity_uniform_control (n : Nat) :
    Nonempty (EnvWfT covZRigidIdEnv) ∧ Nonempty (CtxWfT covZRigidIdEnv n []) ∧
    Nonempty (HasTyT covZRigidIdEnv n [] (.const 0 []) cexPolyIdTy) ∧
    ApproxTKWEta covZRigidIdEnv n [] EnvT.bot (.const 0 []) (.spine 0 []) ∧
    covRIdentityRelation covZRigidIdEnv n []
      (.const 0 []) (.const 0 []) (.spine 0 []) ∧
    ∀ j, Nonempty (HasTyT covZRigidIdEnv n [] (covQIdentityTowerApp j)
        (covQArrowTower j)) ∧
      ApproxTKWEta covZRigidIdEnv n [] EnvT.bot (covQIdentityTowerApp j)
        (.spine 0 [.bot, .bot]) ∧
      CandidateCov covZRigidIdEnv (WhStepCK2 covZRigidIdEnv n) [] false
        (covRTowerRelation covZRigidIdEnv n [] j) ∧
      CovRJoint covZRigidIdEnv n [] (covRTowerSyntax covZRigidIdEnv j)
        (fun _ => false) (covRBaseVal covZRigidIdEnv)
        (covQIdentityTowerApp j) (covQIdentityTowerApp j) (.spine 0 [.bot, .bot]) := by
  obtain ⟨hW, hΓ, ht, ho, hrel, htower⟩ := covW_identity_uniform_control n
  refine ⟨hW, hΓ, ht, covWEta_of_old ho, hrel, ?_⟩
  intro j
  obtain ⟨ht, ho, hc, hj⟩ := htower j
  exact ⟨ht, covWEta_of_old ho, hc, hj⟩

/-- The total positive PER accepts the same actual rigid proof observation,
with the independent native proof-irrelevance conversion retained. -/
theorem covWEta_proof_total_control (n : Nat) :
    Nonempty (EnvWfT covPProofEnv) ∧ Nonempty (CtxWfT covPProofEnv n []) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 0 []) (.sort .zero)) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 3 []) (.const 0 [])) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 1 []) (.const 0 [])) ∧
    Nonempty (ConvT covPProofEnv n [] (.const 3 []) (.const 1 []) (.const 0 [])) ∧
    IsPropCTP covPProofEnv (.spine 0 []) ∧
    ApproxTKWEta covPProofEnv n [] EnvT.bot (.const 0 []) (.spine 0 []) ∧
    ApproxTKWEta covPProofEnv n [] EnvT.bot (.const 3 []) (.spine 3 []) ∧
    ApproxTKWEta covPProofEnv n [] EnvT.bot (.const 1 []) .bot ∧
    CandidateCovS covPProofEnv (WhStepCK2 covPProofEnv n) [] true covSTotalRel ∧
    covSTotalRel (.const 3 []) (.const 1 []) (.spine 3 []) := by
  obtain ⟨hW, hΓ, hT, hp, hq, hc, hpos, hA, ho, hbot, hC, hrel⟩ :=
    covW_proof_total_control n
  exact ⟨hW, hΓ, hT, hp, hq, hc, hpos, covWEta_of_old hA,
    covWEta_of_old ho, covWEta_of_old hbot, hC, hrel⟩

/-- Actual True-constructor supply. This theorem makes no universal assertion
about all observations introduced by eta. -/
theorem covWEta_trueIntro_supply (n : Nat) :
    Nonempty (EnvWfT trueEnvU) ∧ Nonempty (CtxWfT trueEnvU n []) ∧
    Nonempty (HasTyT trueEnvU n [] (.const 0 []) (.sort .zero)) ∧
    Nonempty (HasTyT trueEnvU n [] (.const 1 []) (.const 0 [])) ∧
    ApproxTKWEta trueEnvU n [] EnvT.bot (.const 1 []) .bot ∧
    CandidateCovS trueEnvU (WhStepCK2 trueEnvU n) [] true covSTotalRel := by
  obtain ⟨hW, hΓ, hT, hp, ho, hC, _⟩ := covW_trueIntro_control n
  exact ⟨hW, hΓ, hT, hp, covWEta_of_old ho, hC⟩

/-- Abel--Coquand native evidence and the displayed finite observations.
The old universal bottom-only result is not relabelled as a new-model fact. -/
theorem covWEta_abelCoquand_supply (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] AbelCoquand.top (.sort .zero)) ∧
    Nonempty (HasTyT emptyEnv n [] AbelCoquand.delta AbelCoquand.top) ∧
    Nonempty (HasTyT emptyEnv n [] covPAbelCoquandId AbelCoquand.top) ∧
    Nonempty (ConvT emptyEnv n [] AbelCoquand.delta covPAbelCoquandId
      AbelCoquand.top) ∧
    ApproxTKWEta emptyEnv n [] EnvT.bot AbelCoquand.top (.pi .bot []) ∧
    ApproxTKWEta emptyEnv n [] EnvT.bot AbelCoquand.delta .bot ∧
    ApproxTKWEta emptyEnv n [] EnvT.bot covPAbelCoquandId .bot ∧
    CandidateCovS emptyEnv (WhStepCK2 emptyEnv n) [] true covSTotalRel := by
  obtain ⟨hW, hΓ, hT, hp, hq, hc, hA, ho, hbot, hC, _⟩ :=
    covW_abelCoquand_control n
  exact ⟨hW, hΓ, hT, hp, hq, hc, covWEta_of_old hA,
    covWEta_of_old ho, covWEta_of_old hbot, hC⟩

theorem covWEta_proof_demand_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covSProofFnEnv n Γ ρ (.app (.const 4 []) (.const 3 []))
      (.spine 4 [.spine 3 []]) :=
  covWEta_of_old (covW_proof_demand_observed n Γ ρ)

theorem covWEta_proof_demand_control (n : Nat) :
    Nonempty (EnvWfT covSProofFnEnv) ∧ Nonempty (CtxWfT covSProofFnEnv n []) ∧
    Nonempty (HasTyT covSProofFnEnv n [] (.const 3 []) (.const 0 [])) ∧
    Nonempty (HasTyT covSProofFnEnv n [] (.const 1 []) (.const 0 [])) ∧
    Nonempty (ConvT covSProofFnEnv n [] (.const 3 []) (.const 1 []) (.const 0 [])) ∧
    Nonempty (HasTyT covSProofFnEnv n [] (.app (.const 4 []) (.const 3 []))
      (.sort .zero)) ∧
    Nonempty (ConvT covSProofFnEnv n [] (.app (.const 4 []) (.const 3 []))
      (.app (.const 4 []) (.const 1 [])) (.sort .zero)) ∧
    ApproxTKWEta covSProofFnEnv n [] EnvT.bot (.const 3 []) (.spine 3 []) ∧
    ApproxTKWEta covSProofFnEnv n [] EnvT.bot (.app (.const 4 []) (.const 3 []))
      (.spine 4 [.spine 3 []]) ∧
    CandidateCovS covSProofFnEnv (WhStepCK2 covSProofFnEnv n) [] true covSTotalRel ∧
    CovXCompactAction covSProofFnEnv (.spine 4 []) [.spine 3 []]
      (.spine 4 [.spine 3 []]) ∧
    covRCodeRel covSProofFnEnv .prop (.app (.const 4 []) (.const 3 []))
      (.app (.const 4 []) (.const 1 [])) (.spine 4 [.spine 3 []]) ∧
    ¬ BotDemandT [.spine 3 []] := by
  obtain ⟨hW, hΓ, hp, hq, hc, hfp, hfc, ho, hfo, hD, ha, hout, hnb⟩ :=
    covW_proof_demand_control n
  exact ⟨hW, hΓ, hp, hq, hc, hfp, hfc, covWEta_of_old ho,
    covWEta_of_old hfo, hD, ha, hout, hnb⟩

theorem covWEta_nat_rec_instance_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧
    Nonempty (HasTyT natEnvU n [] covURecInstance (.sort (.succ .zero))) ∧
    ApproxTKWEta natEnvU n [] EnvT.bot covURecInstance .prop ∧
    RedR (WhStepCK2 natEnvU n) [] covURecInstance (.sort .zero) := by
  obtain ⟨hW, ht, ho, hr⟩ := covW_nat_rec_instance_control n
  exact ⟨hW, ht, covWEta_of_old ho, hr⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_CONTROLS_ROOTS
#print axioms CovWEtaFixtureAt
#print axioms covWEta_fixture_of_old
#print axioms covWEta_fixture_natSucc_eta
#print axioms covWEta_fixture_alias_in_pi
#print axioms covWEta_fixture_polyPropLam
#print axioms covWEta_fixture_alias_extension
#print axioms covWEta_fixture_nat_coverage
#print axioms covWEta_fixture_nat_shape
#print axioms covWEta_fixture_eq_anchor
#print axioms covWEta_fixture_nat_anchor
#print axioms covWEta_sort_observed
#print axioms covWEta_rigid_observed
#print axioms covWEta_neutral_observed
#print axioms covWEta_K_eqGap_control
#print axioms covWEta_trueK_control
#print axioms covWEta_andK_control
#print axioms covWEta_identity_tower_observed
#print axioms covWEta_identity_uniform_control
#print axioms covWEta_proof_total_control
#print axioms covWEta_trueIntro_supply
#print axioms covWEta_abelCoquand_supply
#print axioms covWEta_proof_demand_observed
#print axioms covWEta_proof_demand_control
#print axioms covWEta_nat_rec_instance_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_CONTROLS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit

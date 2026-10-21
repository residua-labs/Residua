import rcic.RcicNativeTypedModelCovSCandidate
import rcic.RcicNativeTypedModelKFailure

/-!
# Total positive PERs and the unchanged saturated K consumers

The K guard is native index conversion together with independent DI index
agreement. Neither field consumes proposition-code bottom collapse. The
positive Eq gap remains observed; the apart source and the neutral-eta
source remain blocked by that independent agreement condition. Proper Eq
prefixes remain bottom-only by arity/saturation, not by positive candidates.

The fresh false-tag sort candidate here is the named unchanged-data
embedding. Its Eq-gap edge is supplied through actual CK2 readback. No new
ordinary-arrow operator, observation rule, index guard, or general native
K supplier is asserted. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovSAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelKGuardAudit
open TypedModelKFailureAudit TypedModelKObstructionAudit TypedModelCovRAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit ReadbackCK2IndexAudit
open ReadbackCK2NativeControlAudit ReadbackCK2ModelObstructionAudit

/-- This actual positive K readback consumes candidate readback closure;
it does not consume a proposition-collapse field. -/
theorem covS_K_eqGap_readback (n : Nat) {p : Bool} {S : CovSRel}
    (hS : CandidateCovS eqEnvT (WhStepCK2 eqEnvT n) eqGapCtx p S)
    (y : Expr Nat) (c : CptT) :
    S eqGapRedex y c ↔ S (.sort .zero) y c :=
  hS.readback (redR_whStepCK2_eqGap n)

theorem covS_K_eqGap_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    Nonempty (HasTyT eqEnvT n eqGapCtx eqGapRedex (.sort (.succ .zero))) ∧
    Nonempty (HasTyT eqEnvT n eqGapCtx (.sort .zero) (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n eqGapCtx eqGapRedex (.sort .zero) (.sort (.succ .zero))) ∧
    KIndexGuardAt eqEnvT n eqGapCtx eqGapW ∧
    KNativeHead eqEnvT n eqGapCtx eqGapRedex (.sort .zero) ∧
    ApproxTK eqEnvT n eqGapCtx EnvT.bot eqGapRedex .prop ∧
    ApproxTK eqEnvT n eqGapCtx EnvT.bot (.sort .zero) .prop ∧
    (CptT.prop ≠ .bot) ∧
    CandidateCovS eqEnvT (WhStepCK2 eqEnvT n) eqGapCtx false
      (covRCodeRel eqEnvT .sort) ∧
    covRCodeRel eqEnvT .sort eqGapRedex (.sort .zero) .prop := by
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  obtain ⟨hc⟩ := eqGap_conv n
  have he := convEnds pinEqGroupWfT hΓ hc
  have hS := candidateCovS_of_R_false
    (covRSort_isCandidate eqEnvT (WhStepCK2 eqEnvT n) eqGapCtx)
  have hrel := (covS_K_eqGap_readback n hS (.sort .zero) .prop).mpr
    (covRSort_accepts_prop eqEnvT (.sort .zero) (.sort .zero))
  exact ⟨⟨pinEqGroupWfT⟩, ⟨hΓ⟩, ⟨he.2.1⟩, ⟨he.1⟩,
    ⟨.symm _ _ _ _ hc⟩, kIndexGuardAt_eqGap n, guarded_kNativeHead_eqGap n,
    approxTK_eqGap_prop n EnvT.bot,
    approxTK_sort_code eqEnvT n eqGapCtx EnvT.bot .zero,
    (fun h => CptT.noConfusion h), hS, hrel⟩

/-- The negative result concerns the actual model observation. It is not
misreported as rejection by a compact-only candidate leaf. -/
theorem covS_K_apart_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n apartCtx) ∧
    Nonempty (HasTyT eqEnvT n apartCtx apartRec (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n apartCtx apartRec apartRec (.sort (.succ .zero))) ∧
    ApproxTK eqEnvT n apartCtx EnvT.bot apartRec .bot ∧
    (∀ ρ c, ApproxTK eqEnvT n apartCtx ρ apartRec c → c = .bot) ∧
    (¬ ApproxTK eqEnvT n apartCtx EnvT.bot apartRec .prop) ∧
    CandidateCovS eqEnvT (WhStepCK2 eqEnvT n) apartCtx false
      (covRCodeRel eqEnvT .sort) ∧
    covRCodeRel eqEnvT .sort apartRec apartRec .bot := by
  obtain ⟨ht⟩ := apartRec_typed n
  have hS := candidateCovS_of_R_false
    (covRSort_isCandidate eqEnvT (WhStepCK2 eqEnvT n) apartCtx)
  exact ⟨⟨pinEqGroupWfT⟩, ⟨apartCtx_wf n⟩, ⟨ht⟩,
    ⟨.refl _ _ _ ht⟩, .bot _ _ _, fun _ _ h => approxTK_apartRec_bot h,
    not_approxTK_apartRec_prop, hS, hS.bot _ _⟩

/-- Native eta supplies a K head but not the stronger DI guard. Complete
application inversion excludes all other nonbottom model alternatives. -/
theorem covS_K_eta_observation_bot {n : Nat} {ρ : EnvT} {c : CptT}
    (h : ApproxTK eqEnvT n etaEqCtx ρ etaIndexRedex c) : c = .bot := by
  rcases approxTK_eqRec_bvar_inv (by decide) h with hb | ⟨w, hr, hp, hk, hi⟩
  · exact hb
  · exact (not_indexAgreementDI_eta hr hp hk hi.2).elim

/-- Every native, observation and candidate premise in the guard boundary
is inhabited. Total positive propositions do not fill the separate DI port. -/
theorem covS_K_eta_guard_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n etaEqCtx) ∧
    Nonempty (HasTyT eqEnvT n etaEqCtx etaIndexRedex (.sort (.succ .zero))) ∧
    Nonempty (HasTyT eqEnvT n etaEqCtx (.sort .zero) (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n etaEqCtx etaIndexRedex (.sort .zero) (.sort (.succ .zero))) ∧
    KNativeHead eqEnvT n etaEqCtx etaIndexRedex (.sort .zero) ∧
    ApproxTK eqEnvT n etaEqCtx EnvT.bot etaIndexRedex .bot ∧
    ApproxTK eqEnvT n etaEqCtx EnvT.bot (.sort .zero) .prop ∧
    (∀ ρ c, ApproxTK eqEnvT n etaEqCtx ρ etaIndexRedex c → c = .bot) ∧
    (¬ KIndexGuardAt eqEnvT n etaEqCtx
      (eqConvW (fun _ _ h => h) indexFn (.bvar 1) etaIndex etaIndexMot (.sort .zero))) ∧
    CandidateCovS eqEnvT (WhStepCK2 eqEnvT n) etaEqCtx false
      (covRCodeRel eqEnvT .sort) ∧
    covRCodeRel eqEnvT .sort etaIndexRedex (.sort .zero) .bot := by
  obtain ⟨hW, ⟨hΓ⟩, ⟨hc⟩, hK⟩ := native_eta_control n
  have he := convEnds pinEqGroupWfT hΓ hc
  have hS := candidateCovS_of_R_false
    (covRSort_isCandidate eqEnvT (WhStepCK2 eqEnvT n) etaEqCtx)
  exact ⟨hW, ⟨hΓ⟩, ⟨he.1⟩, ⟨he.2.1⟩, ⟨hc⟩, hK, .bot _ _ _,
    approxTK_sort_code eqEnvT n etaEqCtx EnvT.bot .zero,
    fun _ _ h => covS_K_eta_observation_bot h, not_kIndexGuardAt_eta n,
    hS, hS.bot _ _⟩

/-- Prefix bottomness and the failure of old raw application inversion
are model-side facts. The native prefix type and positive saturated
observation are supplied together with an actual S candidate. -/
theorem covS_K_prefix_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    (∃ A B, Nonempty (HasTyT eqEnvT n eqGapCtx eqGapPrefix (.pi A B))) ∧
    ApproxTK eqEnvT n eqGapCtx EnvT.bot eqGapPrefix .bot ∧
    (∀ ρ c, ApproxTK eqEnvT n eqGapCtx ρ eqGapPrefix c → c = .bot) ∧
    ApproxTK eqEnvT n eqGapCtx EnvT.bot eqGapRedex .prop ∧
    CandidateCovS eqEnvT (WhStepCK2 eqEnvT n) eqGapCtx false covSTotalRel ∧
    covSTotalRel eqGapPrefix eqGapPrefix .bot ∧
    ¬ CtxModelTLaws (ctxModelT_approxTK eqEnvT n eqGapCtx) := by
  obtain ⟨A, B, ht, _⟩ := eqGapAlias_native_beta_control n
  exact ⟨⟨pinEqGroupWfT⟩, eqGapCtx_wf n, ⟨A, B, ht⟩,
    .bot _ _ _, fun _ _ h => approxTK_eqGapPrefix_bot h,
    approxTK_eqGap_prop n EnvT.bot,
    covSTotal_isCandidate eqEnvT (WhStepCK2 eqEnvT n) eqGapCtx false,
    trivial, not_ctxModelTLaws_approxTK_eqGap n⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_S_K_CONTROLS_ROOTS
#print axioms covS_K_eqGap_readback
#print axioms covS_K_eqGap_control
#print axioms covS_K_apart_control
#print axioms covS_K_eta_observation_bot
#print axioms covS_K_eta_guard_control
#print axioms covS_K_prefix_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_S_K_CONTROLS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovSAudit

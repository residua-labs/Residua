import rcic.RcicNativeTypedModelCovNormTyCases

/-!
# Syntactic lambda applications: both residual arms are supplied

A lambda has no spine observation.  Neither saturated computation has a
lambda-headed source.  These two independent shape arguments supply the
exact residual record, so the existing application step closes from its
two genuine native children.  The identity applied to `Sort 0` is a full
non-bottom native/model/related-substitution control. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovNormTyCasesAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit TypedModelAudit TypedModelKAudit
open TypedModelCovRelAudit TypedModelCovNormSubstAudit
open TypedModelKFragmentAudit ReadbackCKAudit ReadbackCK2Audit
open TypedModelAudit.TypingFin

variable {E : ResolvedEnv} {C : CovTyping E} {R : Readback} {n : Nat}

/-- The saturated branch always has a constant-headed application source;
its exact witness is incompatible with a syntactic lambda head. -/
theorem cov_no_saturated_app_lam {Ξ : LCtx} {ρ : EnvT}
    {A body arg : Expr Nat} {c : CptT} :
    ¬ SaturatedComputationTK E n Ξ ρ (.app (.lam A body) arg) c := by
  rintro (⟨w, he, _, _⟩ | ⟨w, x, he, _, _, _, _, _, _⟩)
  · simp only [iotaLhsOfS, recCall_eq_app] at he
    exact F8EtaK.foldApps_const_ne_lam_any (Expr.app.inj he).1.symm
  · simp only [recCall_eq_app] at he
    exact F8EtaK.foldApps_const_ne_lam_any (Expr.app.inj he).1.symm

/-- Both exact residual fields are proved, without a model realization or
an assumed relation at the application output. -/
theorem covAppResiduals_lam (C : CovTyping E) (R : Readback) (n : Nat)
    (Ξ Γ : LCtx) (A body arg T : Expr Nat) :
    CovAppResiduals C R n Ξ Γ (.lam A body) arg T := by
  constructor
  · intro Δ ρ ρ' σ σ' _ _ r args u h
    have noSpine : ∀ θ, ApproxTK E n Ξ θ (.lam A body) (.spine r args) → False := by
      intro θ hf
      rcases approxT_lam_inv (approxTK_forget hf) with hbot | ⟨_, _, he, _⟩
      · exact CptT.noConfusion hbot
      · exact CptT.noConfusion he
    exact (h.elim (fun h => noSpine ρ h.1) (fun h => noSpine ρ' h.1)).elim
  · intro Δ ρ ρ' σ σ' _ _ c h
    exact (h.elim cov_no_saturated_app_lam cov_no_saturated_app_lam).elim

/-- Full application-constructor step for every syntactic lambda function.
The reused supplier obtains exactly the function and argument child IHs. -/
theorem fundCov_appLam_step_approxTK (hL : ReadbackLaws E R)
    (hW : EnvWfT E) (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E)
    (hι : IotaSubstT E) {Ξ Γ : LCtx} {A body arg D B : Expr Nat}
    (hf : HasTyT E n Γ (.lam A body) (.pi D B))
    (ha : HasTyT E n Γ arg D) :
    FundTyCovStep C (ctxModelT_approxTK E n Ξ) R n
      (HasTyT.app Γ (.lam A body) arg D B hf ha) :=
  fundCov_app_step_approxTK hL hW hcl hst hι hf ha
    (covAppResiduals_lam C R n Ξ Γ A body arg (instantiate0 arg B))

/-- A complete motive for this concrete application follows by the landed
semantic beta contraction, the actual K-free sort observation, and the
already proved sort motive.  No generated native derivation is an IH. -/
theorem fundCov_identitySortApp (C : CovTyping E) (n : Nat) (Ξ Γ : LCtx) :
    FundTyAtCov C (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n Γ
      (.app idSort1 (.sort .zero)) (.sort (.succ .zero)) := by
  apply fundTyAtCov_of_contract (readbackLaws_whStepCK2 E n)
    (dst := .sort .zero)
  · intro ρ c hc
    apply ApproxTK.free (kFreeT_sort E .zero)
    exact covConv_beta_fwd (covModelSubstFactorT_approxT E) ρ
      (.sort (.succ .zero)) (.bvar 0) (.sort .zero) (approxTK_forget hc)
  · intro Δ σ
    exact redR_single (.ctx (.beta _ _ _))
  · exact fundCov_sort (covAtomicModelLaws_approxTK E n Ξ) .zero

/-- The exact residual supplier and the concrete full motive are realized
in the admitted Nat environment at a non-bottom compact. -/
theorem covApp_native_control (C : CovTyping natEnvU) (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    CovAppResiduals C (WhStepCK2 natEnvU n) n [] [] idSort1 (.sort .zero)
      (.sort (.succ .zero)) ∧
    Nonempty (HasTyT natEnvU n [] (.app idSort1 (.sort .zero)) (.sort (.succ .zero))) ∧
    RelSubstAtCov C (ctxModelT_approxTK natEnvU n []) (WhStepCK2 natEnvU n) n
      [] EnvT.bot EnvT.bot SubstT.id SubstT.id [] ∧
    ApproxTK natEnvU n [] EnvT.bot (.app idSort1 (.sort .zero)) .prop ∧
    LRSCoreCov C (WhStepCK2 natEnvU n) n []
      (.app idSort1 (.sort .zero)) (.app idSort1 (.sort .zero))
      (.sort (.succ .zero)) .prop ∧ (.prop : CptT) ≠ .bot := by
  have hSub := relSubstAtCov_nil C (ctxModelT_approxTK natEnvU n [])
    (WhStepCK2 natEnvU n) n [] EnvT.bot EnvT.bot SubstT.id SubstT.id
  have hm : ApproxTK natEnvU n [] EnvT.bot (.app idSort1 (.sort .zero)) .prop := by
    refine .app (.free (kFreeT_natEnvU _) (approxT_idSort1_polyIdOut0 natEnvU EnvT.bot))
      (List.mem_singleton.mpr rfl) ?_
    intro u hu
    rcases List.mem_singleton.mp hu with rfl
    exact approxTK_sort_code natEnvU n [] EnvT.bot .zero
  refine ⟨⟨natEnvUWfT⟩, ⟨.nil⟩,
    covAppResiduals_lam C _ n [] [] (.sort (.succ .zero)) (.bvar 0) _ _,
    ⟨.app [] idSort1 (.sort .zero) (.sort (.succ .zero)) (.sort (.succ .zero))
      (.lam [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)
        (.sort (.succ .zero)) (.sort _ _) (.bvar _ 0 _ rfl)) (.sort _ _)⟩,
    hSub, hm, ?_, fun h => CptT.noConfusion h⟩
  simpa only [substT_id] using
    fundCov_identitySortApp C n [] [] .nil hSub .prop (Or.inl hm)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_NORM_APP_CASES_ROOTS
#print axioms cov_no_saturated_app_lam
#print axioms covAppResiduals_lam
#print axioms fundCov_appLam_step_approxTK
#print axioms fundCov_identitySortApp
#print axioms covApp_native_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_NORM_APP_CASES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovNormTyCasesAudit

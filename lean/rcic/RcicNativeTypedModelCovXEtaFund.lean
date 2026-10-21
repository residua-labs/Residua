import rcic.RcicNativeTypedModelCovXInterface
import rcic.RcicNativeTypedModelCovXEtaFactor

/-!
# Complete successor eta Fundamental supplier

The old successor eta conversion motive was kernel-refuted. The new motive
is supplied here for every target context, related substitution and compact
observed at either endpoint. Both views are actual finite witnesses, and the
eta-left-only lambda tables are covered by the proved observational theorem.
This local supplier does not assert that every native type has a finite view.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCK2Audit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit
open TypedModelCovNormConvCasesAudit TypedModelCovXAudit

/-- The function child has a complete motive at every actually observed
successor compact. Its application output is the proved native spine action. -/
theorem fundTyAtCovX_natSucc (n : Nat) (Ξ Γ : LCtx) :
    FundTyAtCovX (C2 natEnvU) (ctxModelT_approxTK natEnvU n Ξ)
      (WhStepCK2 natEnvU n) n Γ (.const 2 []) (.pi (.const 0 []) (.const 0 [])) := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  have hshape : c = .bot ∨ c = .spine 2 [] :=
    hc.elim
      (fun h => approxT_rigid_const_inv rigidConst_natEnvU_succ (approxTK_forget h))
      (fun h => approxT_rigid_const_inv rigidConst_natEnvU_succ (approxTK_forget h))
  change LRSCoreCovX (C2 natEnvU) (WhStepCK2 natEnvU n) n Δ
    (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 [])) c
  rcases hshape with hb | rfl
  · exact Or.inl hb
  · exact lrSCoreCovX_of_view (C2 natEnvU) (covXNatArrowView n Δ)
      (covX_natArrow_spine_of_action n Δ _ _ (covX_natSucc_spine_action n Δ))

/-- The complete concrete eta conversion supplier, including observations
available only at the lambda endpoint. No native or semantic port is assumed. -/
theorem fundConvAtCovX_eta_natSucc (n : Nat) (Ξ Γ : LCtx) :
    FundConvAtCovX (C2 natEnvU) (ctxModelT_approxTK natEnvU n Ξ)
      (WhStepCK2 natEnvU n) n Γ
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  change LRSCoreCovX (C2 natEnvU) (WhStepCK2 natEnvU n) n Δ
    (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
    (.const 2 []) (.pi (.const 0 []) (.const 0 [])) c
  exact lrSCoreCovX_of_view (C2 natEnvU) (covXNatArrowView n Δ)
    (covX_natSucc_eta_observed n Ξ Δ ρ ρ' c hc)

/-- The new supplier and the old refutation coexist at exactly the same
model, native eta edge, type, context and compact-typing instance. -/
theorem covX_natSucc_eta_motive_changed (n : Nat) :
    FundConvAtCovX (C2 natEnvU) (ctxModelT_approxTK natEnvU n [])
      (WhStepCK2 natEnvU n) n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) ∧
    ¬ FundConvAtCov (C2 natEnvU) (ctxModelT_approxTK natEnvU n [])
      (WhStepCK2 natEnvU n) n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) :=
  ⟨fundConvAtCovX_eta_natSucc n [] [], not_fundConvAtCov_eta_natSucc (C2 natEnvU) n⟩

/-- The complete motive has an actual guarded related substitution and
non-bottom observations on both relevant compact shapes. This is a supply,
not an implication with an uninhabited substitution premise. -/
theorem covX_natSucc_eta_fund_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    RelSubstAtCovX (C2 natEnvU) (ctxModelT_approxTK natEnvU n [])
      (WhStepCK2 natEnvU n) n [] EnvT.bot EnvT.bot SubstT.id SubstT.id [] ∧
    Nonempty (ConvT natEnvU n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 2 []) (.spine 2 []) ∧
    ApproxTK natEnvU n [] EnvT.bot
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      covXNatEtaEmptyRow ∧
    FundTyAtCovX (C2 natEnvU) (ctxModelT_approxTK natEnvU n [])
      (WhStepCK2 natEnvU n) n [] (.const 2 []) (.pi (.const 0 []) (.const 0 [])) ∧
    FundConvAtCovX (C2 natEnvU) (ctxModelT_approxTK natEnvU n [])
      (WhStepCK2 natEnvU n) n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) ∧
    (.spine 2 [] : CptT) ≠ .bot ∧ covXNatEtaEmptyRow ≠ .bot := by
  obtain ⟨hW, hΓ, _, _, hc, _, hobs, _⟩ := covX_natSucc_eta_control n
  exact ⟨hW, hΓ,
    relSubstAtCovX_nil (C2 natEnvU) _ (WhStepCK2 natEnvU n) n []
      EnvT.bot EnvT.bot SubstT.id SubstT.id,
    hc, hobs, covX_natSucc_eta_empty_row_observed n [] EnvT.bot,
    fundTyAtCovX_natSucc n [] [], fundConvAtCovX_eta_natSucc n [] [],
    fun h => CptT.noConfusion h, fun h => CptT.noConfusion h⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_ETA_FUND_ROOTS
#print axioms fundTyAtCovX_natSucc
#print axioms fundConvAtCovX_eta_natSucc
#print axioms covX_natSucc_eta_motive_changed
#print axioms covX_natSucc_eta_fund_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_ETA_FUND_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit

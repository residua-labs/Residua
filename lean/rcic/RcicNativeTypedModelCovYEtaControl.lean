import rcic.RcicNativeTypedModelCovYEtaCoverage

/-!
# Successor eta at the finite type-code relation

The native action proof is imported from the earlier extensional candidate.
Only its fixed Nat domain and codomain leaves are transported to the new
finite type-code relation. Every actual endpoint-OR observation is supplied
at one actual type code, including lambda tables present only on the left.
No global native type-view supply is used. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCK2Audit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit
open TypedModelCovXAudit TypedModelCovXEtaAudit TypedModelCovYAudit

/-- Local composition from the already proved Nat-arrow actions. The new
actual type-code gate and its coverage are explicit additional inputs. -/
theorem lrSCoreCovY_natArrow_of_covX_actions (n : Nat) (Γ : LCtx)
    (x y : Expr Nat) (c : CptT)
    (ht : (C2 natEnvU).ty c covYNatArrowCode)
    (hcov : CovYActionCoverage (C2 natEnvU) c (.spine 0 []) [([], .spine 0 [])])
    (hx : LRSCoreCovXAt (C2 natEnvU) (covXNatArrowView n Γ) x y c) :
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Γ x y
      (.pi (.const 0 []) (.const 0 [])) c covYNatArrowCode := by
  rw [covYNatArrowCode, lrSCoreCovY_pi_iff]
  refine ⟨ht, Or.inr ⟨.const 0 [], .const 0 [], .refl _, hcov, ?_⟩⟩
  intro ds out ha row hr hs N N' hN hN' hc hd
  obtain rfl := List.mem_singleton.mp hr
  have hold : ∀ u ∈ ds, LRSCoreCovXAt (C2 natEnvU) (covXNatView n Γ) N N' u := by
    intro u hu
    have hh := hd u hu
    rw [LRSCoreCovY.eq_def] at hh
    exact hh.2
  have ho := hx.2 ds out ha N N' hN hN' hc hold
  constructor
  · exact lrSCoreCovY_of_old_leaf (C2 natEnvU)
      (fun d g he => CptT.noConfusion he) hs.2 ho.1
  · exact lrSCoreCovY_of_old_leaf (C2 natEnvU)
      (fun d g he => CptT.noConfusion he) hs.2 ho.2

/-- Complete successor eta point supplier for every observed compact on
either side, at the same finite semantic type code. -/
theorem covY_natSucc_eta_observed (n : Nat) (Ξ Γ : LCtx) (ρ ρ' : EnvT)
    (c : CptT)
    (h : ApproxTK natEnvU n Ξ ρ
        (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0))) c ∨
      ApproxTK natEnvU n Ξ ρ' (.const 2 []) c) :
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Γ
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) c covYNatArrowCode :=
  lrSCoreCovY_natArrow_of_covX_actions n Γ _ _ c
    (covY_natSucc_eta_or_code_typed n Ξ ρ ρ' c h)
    (covY_natSucc_eta_or_uniform_coverage n Ξ ρ ρ' c h)
    (covX_natSucc_eta_observed n Ξ Γ ρ ρ' c h)

/-- The rigid endpoint's self-relatedness uses the same finite type code. -/
theorem covY_natSucc_related (n : Nat) (Γ : LCtx) :
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Γ
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covYNatArrowCode :=
  lrSCoreCovY_natArrow_of_covX_actions n Γ _ _ _ covY_natSucc_code_typed
    covY_natSucc_uniform_coverage
    (covX_natArrow_spine_of_action n Γ _ _ (covX_natSucc_spine_action n Γ))

/-- An observed non-bottom native argument is related at the domain code. -/
theorem covY_natZero_related (n : Nat) (Γ : LCtx) :
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Γ
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) (.spine 0 []) := by
  apply lrSCoreCovY_of_old_leaf (C2 natEnvU)
    (fun d g he => CptT.noConfusion he) ?_ (covX_natZero_related n Γ)
  change CTyCov2 natEnvU (.spine 1 []) (.spine 0 [])
  rw [CTyCov2]
  exact Or.inr ⟨⟨1, [], rfl⟩, not_isPropCT_natEnvU_nat_spine []⟩

/-- Both previously troublesome compact shapes are positive with native
eta, actual model observations and a non-bottom related argument inhabited. -/
theorem covY_natSucc_eta_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    Nonempty (HasTyT natEnvU n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.pi (.const 0 []) (.const 0 []))) ∧
    Nonempty (HasTyT natEnvU n [] (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    Nonempty (ConvT natEnvU n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 2 []) (.spine 2 []) ∧
    ApproxTK natEnvU n [] EnvT.bot
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0))) covXNatEtaEmptyRow ∧
    ApproxTK natEnvU n [] EnvT.bot (.pi (.const 0 []) (.const 0 [])) covYNatArrowCode ∧
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) covYNatArrowCode ∧
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) covXNatEtaEmptyRow covYNatArrowCode ∧
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n []
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) (.spine 0 []) ∧
    (.spine 2 [] : CptT) ≠ .bot ∧ covXNatEtaEmptyRow ≠ .bot := by
  obtain ⟨hW, hΓ, hl, hr, hc, _, hobs, _⟩ := covX_natSucc_eta_control n
  have he := covX_natSucc_eta_empty_row_observed n [] EnvT.bot
  exact ⟨hW, hΓ, hl, hr, hc, hobs, he, approxTK_covYNatArrowCode n [] EnvT.bot,
    covY_natSucc_eta_observed n [] [] EnvT.bot EnvT.bot _ (Or.inr hobs),
    covY_natSucc_eta_observed n [] [] EnvT.bot EnvT.bot _ (Or.inl he),
    covY_natZero_related n [], fun h => CptT.noConfusion h,
    fun h => CptT.noConfusion h⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_ETA_CONTROL_ROOTS
#print axioms lrSCoreCovY_natArrow_of_covX_actions
#print axioms covY_natSucc_eta_observed
#print axioms covY_natSucc_related
#print axioms covY_natZero_related
#print axioms covY_natSucc_eta_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_ETA_CONTROL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYEtaAudit

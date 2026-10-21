import rcic.RcicNativeTypedModelCovYEtaControl
import rcic.RcicNativeTypedModelCovYRealization

/-!
# Exact-code hereditary realization of every successor eta observation

The constant Nat leaf observes its exact semantic type code in every native
context and valuation. Composition therefore realizes all domain demands,
the binder body, and both native codomain instances at the common actual
Nat-arrow code. This covers every endpoint-OR compact, not just the rigid
successor compact. No global escape or code-coherence law is assumed.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit
open TypedModelCovXAudit TypedModelCovXEtaAudit TypedModelCovYAudit

/-- The exact Nat code is a realized base leaf for every compact meeting
its C2 typing gate, in every actual context and valuation. -/
theorem covY_nat_hereditary_at (n : Nat) (Γ : LCtx) (ρ : EnvT) (c : CptT)
    (ht : (C2 natEnvU).ty c (.spine 0 [])) :
    HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ ρ (.const 0 []) c (.spine 0 []) :=
  hereditaryCovRealizationYAt_leaf (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
    (fun d g he => CptT.noConfusion he) ht (.refl _)
    (normalR_famAppCK2 natEnvUWfT
      (rfl : natEnvU.members 0 = some natFamMember) rfl Γ [] [])
    (ApproxTK.free (kFreeT_natEnvU _)
      (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat))

/-- Actual typed coverage and the common code gate suffice at this concrete
nondependent native arrow. The demanded argument realizations come from the
new relation's domain typing gates; no raw-domain observation is requested. -/
theorem covY_natArrow_hereditary_at (n : Nat) (Γ : LCtx) (ρ : EnvT) (c : CptT)
    (ht : (C2 natEnvU).ty c covYNatArrowCode)
    (hcov : CovYActionCoverage (C2 natEnvU) c (.spine 0 []) [([], .spine 0 [])]) :
    HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ ρ (.pi (.const 0 []) (.const 0 [])) c
      covYNatArrowCode := by
  rw [covYNatArrowCode, HereditaryCovRealizationYAt.eq_def]
  refine ⟨ht, Or.inr ⟨.const 0 [], .const 0 [], .refl _, hcov, ?_⟩⟩
  intro ds out ha hne row hr hs N N' hN hN' hc hd
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨?_, covY_nat_hereditary_at n (.assumption (.const 0 []) :: Γ)
    (EnvT.cons (demandT ds) ρ) out hs.2,
    covY_nat_hereditary_at n Γ ρ out hs.2,
    covY_nat_hereditary_at n Γ ρ out hs.2⟩
  intro u hu
  exact covY_nat_hereditary_at n Γ ρ u (lrSCoreCovY_typing (C2 natEnvU) (hd u hu))

/-- Every endpoint-OR observation is hereditarily realized in any target
context and valuation, at the exact code used by its new relation. -/
theorem covY_natSucc_eta_hereditary_observed (n : Nat) (Ξ Γ : LCtx)
    (ρ ρ' ν : EnvT) (c : CptT)
    (h : ApproxTK natEnvU n Ξ ρ
        (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0))) c ∨
      ApproxTK natEnvU n Ξ ρ' (.const 2 []) c) :
    HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ ν (.pi (.const 0 []) (.const 0 [])) c
      covYNatArrowCode :=
  covY_natArrow_hereditary_at n Γ ν c
    (covY_natSucc_eta_or_code_typed n Ξ ρ ρ' c h)
    (covY_natSucc_eta_or_uniform_coverage n Ξ ρ ρ' c h)

/-- The complete pointwise result keeps one shared finite type code for the
relation and both hereditary escape conclusions, for every OR observation. -/
theorem covY_natSucc_eta_observed_realized (n : Nat) (Ξ Γ : LCtx)
    (ρ ρ' : EnvT) (c : CptT)
    (h : ApproxTK natEnvU n Ξ ρ
        (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0))) c ∨
      ApproxTK natEnvU n Ξ ρ' (.const 2 []) c) :
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Γ
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) c covYNatArrowCode ∧
    HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ ρ (.pi (.const 0 []) (.const 0 [])) c
      covYNatArrowCode ∧
    HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ ρ' (.pi (.const 0 []) (.const 0 [])) c
      covYNatArrowCode :=
  ⟨covY_natSucc_eta_observed n Ξ Γ ρ ρ' c h,
    covY_natSucc_eta_hereditary_observed n Ξ Γ ρ ρ' ρ c h,
    covY_natSucc_eta_hereditary_observed n Ξ Γ ρ ρ' ρ' c h⟩

/-- The full escape result has real native endpoint typings and conversion,
and a left-only observed non-bottom lambda compact. -/
theorem covY_natSucc_eta_hereditary_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    Nonempty (HasTyT natEnvU n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.pi (.const 0 []) (.const 0 []))) ∧
    Nonempty (HasTyT natEnvU n [] (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    Nonempty (ConvT natEnvU n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    ApproxTK natEnvU n [] EnvT.bot
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0))) covXNatEtaEmptyRow ∧
    HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n [] EnvT.bot (.pi (.const 0 []) (.const 0 []))
      covXNatEtaEmptyRow covYNatArrowCode ∧ covXNatEtaEmptyRow ≠ .bot := by
  obtain ⟨hW, hΓ, hl, hr, hc, _, he, _⟩ := covY_natSucc_eta_control n
  exact ⟨hW, hΓ, hl, hr, hc, he,
    covY_natSucc_eta_hereditary_observed n [] [] EnvT.bot EnvT.bot EnvT.bot _ (Or.inl he),
    fun h => CptT.noConfusion h⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_ETA_REALIZATION_ROOTS
#print axioms covY_nat_hereditary_at
#print axioms covY_natArrow_hereditary_at
#print axioms covY_natSucc_eta_hereditary_observed
#print axioms covY_natSucc_eta_observed_realized
#print axioms covY_natSucc_eta_hereditary_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_ETA_REALIZATION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYEtaAudit

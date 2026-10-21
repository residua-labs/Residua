import rcic.RcicNativeTypedModelCovYEtaRealization
import rcic.RcicNativeTypedModelCovYCodeBoundary

/-!
# Exact code-order boundaries, without inventing a CptT order

The imported typed compact syntax has no landed order instance. The claims
below therefore quantify over a proposed relation and state the precise
comparison law used. No new approximation relation is defined.

Deleting a same-domain row can destroy the required rigid-action coverage,
even with both compact typing gates and both actual native type observations.
The source relation and hereditary realization are proved, not assumed.
The target realization is also false, since it retains the coverage conjunct.
This does not refute a transport already assuming target realization.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit
open TypedModelCovXAudit TypedModelCovXEtaAudit TypedModelCovYAudit
open TypedModelCovYEtaAudit

/-- The actual native Nat arrow observes both of the previously measured
rows. Its empty-demand row covers all the rigid successor actions. -/
def covZMatchedNatCode : CptT :=
  .pi (.spine 0 []) [([], .spine 0 []), ([.spine 0 []], .spine 0 [])]

theorem covZMatchedNatCode_not_prop : ¬ IsPropCT natEnvU covZMatchedNatCode := by
  intro h
  cases h with
  | pi _ hout =>
      exact not_isPropCT_natEnvU_nat_spine []
        (hout ([], .spine 0 []) (List.mem_cons_self _ _))

theorem approxTK_covZMatchedNatCode (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK natEnvU n Γ ρ (.pi (.const 0 []) (.const 0 [])) covZMatchedNatCode := by
  refine ApproxTK.pi
    (ApproxTK.free (kFreeT_natEnvU _)
      (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat)) ?_ ?_
  · intro s hs u hu
    rcases List.mem_cons.mp hs with rfl | hs
    · exact (List.not_mem_nil _ hu).elim
    · obtain rfl := List.mem_singleton.mp hs
      obtain rfl := List.mem_singleton.mp hu
      rw [CTyS]
      exact Or.inr ⟨⟨0, [], rfl⟩, not_isPropCT_natEnvU_nat_spine []⟩
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ApproxTK.free (kFreeT_natEnvU _)
        (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat)
    · obtain rfl := List.mem_singleton.mp hs
      exact ApproxTK.free (kFreeT_natEnvU _)
        (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat)

theorem covZ_natSucc_matched_code_typed :
    (C2 natEnvU).ty (.spine 2 []) covZMatchedNatCode :=
  ctyCov2_natSucc_spine
    (approxTK_forget (approxTK_covZMatchedNatCode 0 [] EnvT.bot))
    covZMatchedNatCode_not_prop

theorem covZ_natSucc_matched_coverage :
    CovYActionCoverage (C2 natEnvU) (.spine 2 []) (.spine 0 [])
      [([], .spine 0 []), ([.spine 0 []], .spine 0 [])] := by
  intro ds out ha hd
  rcases covY_natSucc_uniform_coverage ds out ha hd with hb | ⟨row, hr, hs⟩
  · exact Or.inl hb
  · obtain rfl := List.mem_singleton.mp hr
    exact Or.inr ⟨([], .spine 0 []), List.mem_cons_self _ _, hs⟩

/-- This transport reuses the old supplied action proof at the common
codomain. It adds no recursive proof or model assumption. -/
theorem covZ_natSucc_matched_related (n : Nat) (Γ : LCtx) :
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Γ
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covZMatchedNatCode := by
  rw [covZMatchedNatCode, lrSCoreCovY_pi_iff]
  refine ⟨covZ_natSucc_matched_code_typed,
    Or.inr ⟨.const 0 [], .const 0 [], .refl _, covZ_natSucc_matched_coverage, ?_⟩⟩
  intro ds out ha row hr hs N N' hN hN' hc hd
  have hcod : row.2 = .spine 0 [] := by
    rcases List.mem_cons.mp hr with rfl | hr
    · rfl
    · obtain rfl := List.mem_singleton.mp hr
      rfl
  have sel : CovYSelectedRow (C2 natEnvU) ds out ([], .spine 0 []) :=
    ⟨fun _ hu => (List.not_mem_nil _ hu).elim, hcod ▸ hs.2⟩
  simpa only [hcod] using
    (lrSCoreCovY_pi_action (C2 natEnvU) (readbackLaws_whStepCK2 natEnvU n)
      (covY_natSucc_related n Γ) ha (List.mem_singleton.mpr rfl)
      sel N N' hN hN' hc hd)

/-- Both rows descend to the already realized Nat leaf. The full source
hereditary target is supplied independently of the order comparison. -/
theorem covZ_natSucc_matched_realized (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ ρ (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covZMatchedNatCode := by
  rw [covZMatchedNatCode, HereditaryCovRealizationYAt.eq_def]
  refine ⟨covZ_natSucc_matched_code_typed,
    Or.inr ⟨.const 0 [], .const 0 [], .refl _, covZ_natSucc_matched_coverage, ?_⟩⟩
  intro ds out ha hne row hr hs N N' hN hN' hc hd
  have hcod : row.2 = .spine 0 [] := by
    rcases List.mem_cons.mp hr with rfl | hr
    · rfl
    · obtain rfl := List.mem_singleton.mp hr
      rfl
  rw [hcod]
  have hout : (C2 natEnvU).ty out (.spine 0 []) := hcod ▸ hs.2
  refine ⟨?_, covY_nat_hereditary_at n (.assumption (.const 0 []) :: Γ)
    (EnvT.cons (demandT ds) ρ) out hout,
    covY_nat_hereditary_at n Γ ρ out hout,
    covY_nat_hereditary_at n Γ ρ out hout⟩
  intro u hu
  exact covY_nat_hereditary_at n Γ ρ u
    (lrSCoreCovY_typing (C2 natEnvU) (hd u hu))

theorem not_covZ_natSucc_standard_realized (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ¬ HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ ρ (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) natNatCovCode := by
  intro h
  rw [natNatCovCode, HereditaryCovRealizationYAt.eq_def] at h
  rcases h.2 with hb | ⟨D, B, hr, hcov, _⟩
  · cases hb
  · exact not_covYActionCoverage_natNatCovCode hcov

/-- The source and target have the same native endpoints, native type and
non-bottom term compact. All native and both actual hereditary environment
guards are inhabited. Both type observations and both C2 gates hold. -/
theorem covZ_natSucc_row_deletion_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    Nonempty (HasTyT natEnvU n [] (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    Nonempty (HasTyT natEnvU n [] (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    EnvTypedCovYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n [] EnvT.bot ∧
    EnvTypedCovYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n [] EnvT.bot ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 2 []) (.spine 2 []) ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 2 []) (.spine 2 []) ∧
    ApproxTK natEnvU n [] EnvT.bot (.pi (.const 0 []) (.const 0 [])) natNatCovCode ∧
    ApproxTK natEnvU n [] EnvT.bot (.pi (.const 0 []) (.const 0 [])) covZMatchedNatCode ∧
    (C2 natEnvU).ty (.spine 2 []) natNatCovCode ∧
    (C2 natEnvU).ty (.spine 2 []) covZMatchedNatCode ∧
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n []
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covZMatchedNatCode ∧
    HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n [] EnvT.bot (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covZMatchedNatCode ∧
    (¬ LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n []
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) natNatCovCode) ∧
    (.spine 2 [] : CptT) ≠ .bot := by
  obtain ⟨hW, hΓ, hsucc, _, ho, _, hstd, ht, _⟩ :=
    covY_natSucc_standard_code_control n
  have he := envTypedCovYAt_nil (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
    (WhStepCK2 natEnvU n) n EnvT.bot
  exact ⟨hW, hΓ, hsucc, hsucc, he, he, ho, ho, hstd,
    approxTK_covZMatchedNatCode n [] EnvT.bot, ht, covZ_natSucc_matched_code_typed,
    covZ_natSucc_matched_related n [], covZ_natSucc_matched_realized n [] EnvT.bot,
    not_lrSCoreCovY_natSucc_standard_code n [] _ _ _, fun h => CptT.noConfusion h⟩

/-- A proposed order admitting same-domain row inclusion cannot make this
relation downward monotone. The only order hypothesis is displayed. -/
theorem not_covZ_core_downward_of_row_inclusion (n : Nat)
    (le : CptT → CptT → Prop)
    (hrow : ∀ (d : CptT) (g g' : List (List CptT × CptT)),
      (∀ row ∈ g, row ∈ g') → le (.pi d g) (.pi d g')) :
    ¬ (∀ {a b : CptT}, le a b →
      (C2 natEnvU).ty (.spine 2 []) a →
      ApproxTK natEnvU n [] EnvT.bot (.pi (.const 0 []) (.const 0 [])) a →
      ApproxTK natEnvU n [] EnvT.bot (.pi (.const 0 []) (.const 0 [])) b →
      HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
        (WhStepCK2 natEnvU n) n [] EnvT.bot (.pi (.const 0 []) (.const 0 []))
        (.spine 2 []) b →
      LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n []
        (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) b →
      LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n []
        (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) a) := by
  intro h
  have hle : le natNatCovCode covZMatchedNatCode := by
    apply hrow
    intro row hr
    obtain rfl := List.mem_singleton.mp hr
    exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
  exact not_lrSCoreCovY_natSucc_standard_code n [] _ _ _
    (h hle (ctyCov2_natSucc_spine (approxT_natNat_covCode EnvT.bot)
      not_isPropCT_natNatCovCode) (approxTK_natNat_covCode n [] EnvT.bot)
      (approxTK_covZMatchedNatCode n [] EnvT.bot)
      (covZ_natSucc_matched_realized n [] EnvT.bot) (covZ_natSucc_matched_related n []))

/-- The comparison operation itself is inhabited: ordinary landed list
inclusion relates the standard row list to the supplied two-row list. -/
theorem covZ_standard_rows_subset_matched :
    ([([.spine 0 []], .spine 0 [])] : List (List CptT × CptT)) ⊆
      [([], .spine 0 []), ([.spine 0 []], .spine 0 [])] := by
  intro row hr
  obtain rfl := List.mem_singleton.mp hr
  exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)

/-- An unconditional refutation using only the existing list-subset
operation. It is a genuine counterexample to deleting Pi rows; there is
no abstract compact-order premise whose satisfiability is left open. -/
theorem not_covZ_core_downward_row_subset (n : Nat) :
    ¬ (∀ (g g' : List (List CptT × CptT)), g ⊆ g' →
      (C2 natEnvU).ty (.spine 2 []) (.pi (.spine 0 []) g) →
      ApproxTK natEnvU n [] EnvT.bot (.pi (.const 0 []) (.const 0 []))
        (.pi (.spine 0 []) g) →
      ApproxTK natEnvU n [] EnvT.bot (.pi (.const 0 []) (.const 0 []))
        (.pi (.spine 0 []) g') →
      HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
        (WhStepCK2 natEnvU n) n [] EnvT.bot (.pi (.const 0 []) (.const 0 []))
        (.spine 2 []) (.pi (.spine 0 []) g') →
      LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n []
        (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
        (.spine 2 []) (.pi (.spine 0 []) g') →
      LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n []
        (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
        (.spine 2 []) (.pi (.spine 0 []) g)) := by
  intro h
  exact not_lrSCoreCovY_natSucc_standard_code n [] _ _ _
    (h [([.spine 0 []], .spine 0 [])]
      [([], .spine 0 []), ([.spine 0 []], .spine 0 [])]
      covZ_standard_rows_subset_matched
      (ctyCov2_natSucc_spine (approxT_natNat_covCode EnvT.bot)
        not_isPropCT_natNatCovCode)
      (approxTK_natNat_covCode n [] EnvT.bot)
      (approxTK_covZMatchedNatCode n [] EnvT.bot)
      (covZ_natSucc_matched_realized n [] EnvT.bot) (covZ_natSucc_matched_related n []))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Z_ORDER_ROOTS
#print axioms covZMatchedNatCode
#print axioms covZMatchedNatCode_not_prop
#print axioms approxTK_covZMatchedNatCode
#print axioms covZ_natSucc_matched_code_typed
#print axioms covZ_natSucc_matched_coverage
#print axioms covZ_natSucc_matched_related
#print axioms covZ_natSucc_matched_realized
#print axioms not_covZ_natSucc_standard_realized
#print axioms covZ_natSucc_row_deletion_control
#print axioms not_covZ_core_downward_of_row_inclusion
#print axioms covZ_standard_rows_subset_matched
#print axioms not_covZ_core_downward_row_subset
-- END RCIC_NATIVE_TYPED_MODEL_COV_Z_ORDER_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit

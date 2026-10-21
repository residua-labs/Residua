import rcic.RcicNativeTypedModelCovZOrderUp

/-!
# Common rows need not give a common realizing code

Both actual Nat-arrow codes below carry a universal row: one uses the empty
demand and the other uses the automatically available bottom demand. Their
exact common-row list contains only the restrictive Nat-demand row. Both
inputs have native type observations, compact typing, Core and hereditary
realization. Their common rows have the first two but fail Core and H.

The row-transport lemmas state what a working local reindexing needs:
coverage forward and selected-row behavior backward at identical codomain
codes. These are conditional adapters; only the concrete Nat applications
are supplies. No order, meet, or join on CptT is invented. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit
open TypedModelCovXAudit TypedModelCovXEtaAudit TypedModelCovYAudit
open TypedModelCovYEtaAudit

/-- A sufficient local transport uses two different row directions. It
recurses nowhere and keeps the domain and selected codomain codes literal. -/
theorem covZ_core_rows_transport {E : ResolvedEnv} (C : CovTyping E)
    {R : Readback} {n : Nat} {Γ : LCtx} {x y A : Expr Nat} {c d : CptT}
    {g g' : List (List CptT × CptT)}
    (ht : C.ty c (.pi d g'))
    (hcover : ∀ ds out, (∃ row ∈ g, CovYSelectedRow C ds out row) →
      ∃ row ∈ g', CovYSelectedRow C ds out row)
    (hback : ∀ ds out row, row ∈ g' → CovYSelectedRow C ds out row →
      ∃ old ∈ g, CovYSelectedRow C ds out old ∧ old.2 = row.2)
    (h : LRSCoreCovY C R n Γ x y A c (.pi d g)) :
    LRSCoreCovY C R n Γ x y A c (.pi d g') := by
  rw [lrSCoreCovY_pi_iff] at h ⊢
  refine ⟨ht, ?_⟩
  rcases h.2 with hb | ⟨D, B, hr, hcov, hact⟩
  · exact Or.inl hb
  · refine Or.inr ⟨D, B, hr, ?_, ?_⟩
    · intro ds out ha hd
      rcases hcov ds out ha hd with hb | hs
      · exact Or.inl hb
      · exact Or.inr (hcover ds out hs)
    · intro ds out ha row hrow hs N N' hN hN' hc hd
      obtain ⟨old, hold, hsold, he⟩ := hback ds out row hrow hs
      rw [← he]
      exact hact ds out ha old hold hsold N N' hN hN' hc hd

theorem covZ_realization_rows_transport {E : ResolvedEnv} (C : CovTyping E)
    {Q : LCtx → CtxModelT E} {R : Readback} {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {A : Expr Nat} {c d : CptT} {g g' : List (List CptT × CptT)}
    (ht : C.ty c (.pi d g'))
    (hcover : ∀ ds out, (∃ row ∈ g, CovYSelectedRow C ds out row) →
      ∃ row ∈ g', CovYSelectedRow C ds out row)
    (hback : ∀ ds out row, row ∈ g' → CovYSelectedRow C ds out row →
      ∃ old ∈ g, CovYSelectedRow C ds out old ∧ old.2 = row.2)
    (h : HereditaryCovRealizationYAt C Q R n Γ ρ A c (.pi d g)) :
    HereditaryCovRealizationYAt C Q R n Γ ρ A c (.pi d g') := by
  rw [HereditaryCovRealizationYAt.eq_def] at h ⊢
  refine ⟨ht, ?_⟩
  rcases h.2 with hb | ⟨D, B, hr, hcov, hact⟩
  · exact Or.inl hb
  · refine Or.inr ⟨D, B, hr, ?_, ?_⟩
    · intro ds out ha hd
      rcases hcov ds out ha hd with hb | hs
      · exact Or.inl hb
      · exact Or.inr (hcover ds out hs)
    · intro ds out ha hne row hrow hs N N' hN hN' hc hd
      obtain ⟨old, hold, hsold, he⟩ := hback ds out row hrow hs
      rw [← he]
      exact hact ds out ha hne old hold hsold N N' hN hN' hc hd

def covZBottomRowNatCode : CptT :=
  .pi (.spine 0 []) [([.bot], .spine 0 []), ([.spine 0 []], .spine 0 [])]

theorem covZBottomRowNatCode_not_prop : ¬ IsPropCT natEnvU covZBottomRowNatCode := by
  intro h
  cases h with
  | pi _ hout =>
      exact not_isPropCT_natEnvU_nat_spine []
        (hout ([.bot], .spine 0 []) (List.mem_cons_self _ _))

theorem approxTK_covZBottomRowNatCode (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK natEnvU n Γ ρ (.pi (.const 0 []) (.const 0 [])) covZBottomRowNatCode := by
  refine ApproxTK.pi
    (ApproxTK.free (kFreeT_natEnvU _)
      (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat)) ?_ ?_
  · intro row hr u hu
    rcases List.mem_cons.mp hr with rfl | hr
    · obtain rfl := List.mem_singleton.mp hu
      exact ctyS_bot _
    · obtain rfl := List.mem_singleton.mp hr
      obtain rfl := List.mem_singleton.mp hu
      rw [CTyS]
      exact Or.inr ⟨⟨0, [], rfl⟩, not_isPropCT_natEnvU_nat_spine []⟩
  · intro row hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ApproxTK.free (kFreeT_natEnvU _)
        (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat)
    · obtain rfl := List.mem_singleton.mp hr
      exact ApproxTK.free (kFreeT_natEnvU _)
        (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat)

theorem covZ_natSucc_bottomRow_code_typed :
    (C2 natEnvU).ty (.spine 2 []) covZBottomRowNatCode :=
  ctyCov2_natSucc_spine
    (approxTK_forget (approxTK_covZBottomRowNatCode 0 [] EnvT.bot))
    covZBottomRowNatCode_not_prop

theorem covZ_bottomRow_covers (ds : List CptT) (out : CptT)
    (h : ∃ row ∈ [([], .spine 0 [])], CovYSelectedRow (C2 natEnvU) ds out row) :
    ∃ row ∈ [([.bot], .spine 0 []), ([.spine 0 []], .spine 0 [])],
      CovYSelectedRow (C2 natEnvU) ds out row := by
  obtain ⟨row, hr, hs⟩ := h
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨([.bot], .spine 0 []), List.mem_cons_self _ _, ?_, hs.2⟩
  intro u hu
  exact Or.inl (List.mem_singleton.mp hu)

theorem covZ_bottomRow_reflects (ds : List CptT) (out : CptT)
    (row : List CptT × CptT)
    (hr : row ∈ [([.bot], .spine 0 []), ([.spine 0 []], .spine 0 [])])
    (hs : CovYSelectedRow (C2 natEnvU) ds out row) :
    ∃ old ∈ [([], .spine 0 [])],
      CovYSelectedRow (C2 natEnvU) ds out old ∧ old.2 = row.2 := by
  have he : row.2 = .spine 0 [] := by
    rcases List.mem_cons.mp hr with rfl | hr
    · rfl
    · obtain rfl := List.mem_singleton.mp hr
      rfl
  exact ⟨([], .spine 0 []), List.mem_singleton.mpr rfl,
    ⟨fun _ hu => (List.not_mem_nil _ hu).elim, he ▸ hs.2⟩, he.symm⟩

theorem covZ_natSucc_bottomRow_related (n : Nat) (Γ : LCtx) :
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Γ
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covZBottomRowNatCode :=
  covZ_core_rows_transport (C2 natEnvU) covZ_natSucc_bottomRow_code_typed
    covZ_bottomRow_covers covZ_bottomRow_reflects (covY_natSucc_related n Γ)

theorem covZ_natSucc_bottomRow_realized (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ ρ (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covZBottomRowNatCode :=
  covZ_realization_rows_transport (C2 natEnvU) covZ_natSucc_bottomRow_code_typed
    covZ_bottomRow_covers covZ_bottomRow_reflects
    (covY_natArrow_hereditary_at n Γ ρ _ covY_natSucc_code_typed covY_natSucc_uniform_coverage)

/-- The displayed list is exactly the common rows, independent of any
choice of an equality decision procedure or compact-order definition. -/
theorem covZ_exact_common_nat_rows (row : List CptT × CptT) :
    row ∈ [([.spine 0 []], .spine 0 [])] ↔
      row ∈ [([], .spine 0 []), ([.spine 0 []], .spine 0 [])] ∧
      row ∈ [([.bot], .spine 0 []), ([.spine 0 []], .spine 0 [])] := by
  constructor
  · intro h
    obtain rfl := List.mem_singleton.mp h
    exact ⟨List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl),
      List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)⟩
  · rintro ⟨hl, hr⟩
    rcases List.mem_cons.mp hl with rfl | hl
    · rcases List.mem_cons.mp hr with h | h
      · cases h
      · have h := List.mem_singleton.mp h
        cases h
    · exact hl

/-- Both input relations and realizations are supplied at nonempty actual
codes. Their exact common-row code fails the relation and realization. -/
theorem covZ_nat_common_rows_failure (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK natEnvU n Γ ρ (.pi (.const 0 []) (.const 0 [])) covZMatchedNatCode ∧
    ApproxTK natEnvU n Γ ρ (.pi (.const 0 []) (.const 0 [])) covZBottomRowNatCode ∧
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Γ
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covZMatchedNatCode ∧
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Γ
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covZBottomRowNatCode ∧
    HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ ρ (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covZMatchedNatCode ∧
    HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ ρ (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covZBottomRowNatCode ∧
    (¬ LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Γ
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) natNatCovCode) ∧
    (¬ HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ ρ (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) natNatCovCode) :=
  ⟨approxTK_covZMatchedNatCode n Γ ρ, approxTK_covZBottomRowNatCode n Γ ρ,
    covZ_natSucc_matched_related n Γ, covZ_natSucc_bottomRow_related n Γ,
    covZ_natSucc_matched_realized n Γ ρ, covZ_natSucc_bottomRow_realized n Γ ρ,
    not_lrSCoreCovY_natSucc_standard_code n Γ _ _ _,
    not_covZ_natSucc_standard_realized n Γ ρ⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Z_ORDER_MEET_ROOTS
#print axioms covZ_core_rows_transport
#print axioms covZ_realization_rows_transport
#print axioms covZBottomRowNatCode
#print axioms covZBottomRowNatCode_not_prop
#print axioms approxTK_covZBottomRowNatCode
#print axioms covZ_natSucc_bottomRow_code_typed
#print axioms covZ_bottomRow_covers
#print axioms covZ_bottomRow_reflects
#print axioms covZ_natSucc_bottomRow_related
#print axioms covZ_natSucc_bottomRow_realized
#print axioms covZ_exact_common_nat_rows
#print axioms covZ_nat_common_rows_failure
-- END RCIC_NATIVE_TYPED_MODEL_COV_Z_ORDER_MEET_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovZOrderAudit

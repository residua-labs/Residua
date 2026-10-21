import rcic.RcicNativeTypedModelCovYAliasSubst

/-!
# The alias-in-Pi fixture at a finite semantic type code

The domain is realized at its native sort readback, not at the alias's raw
model observation. The exact type code retains the identity's nonempty
demand row. Its gate composes the landed singleton-lambda typing theorem;
its extensional action composes the already checked CovX alias action.
The hereditary target visits every demanded argument, the binder body, and
both native codomain instances at this same fixed semantic code.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelKTypedBetaAudit
open TypedModelCovRelAudit TypedModelCovRelEscapeAudit TypedModelCovRelRealizationAudit
open TypedModelCovNormEscapeAudit TypedModelCovXAudit TypedModelCovXRealizationAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit

/-- A semantic type code whose only row keeps the actual nonempty demand. -/
def covYAliasPiCode : CptT := .pi .prop [([.pi .bot []], .prop)]

private theorem covY_alias_probe_ctyS (E : ResolvedEnv) :
    CTyS E (.pi .bot []) .prop := by
  rw [CTyS]
  exact Or.inr (.pi .bot (fun _ hs => (List.not_mem_nil _ hs).elim))

/-- The gate is obtained from the landed generic singleton constructor,
without copying the former existential Pi-gate proof. -/
theorem covY_aliasPi_code_typing (C : CovTyping eqEnvT) (hS : CovTypingIncludesS C) :
    C.ty covNormAliasIdentityCpt covYAliasPiCode := by
  apply hS
  exact ctyS_lam_singleton (not_isPropCT_prop eqEnvT)
    (fun u hu => by
      obtain rfl := List.mem_singleton.mp hu
      exact covY_alias_probe_ctyS eqEnvT) (covY_alias_probe_ctyS eqEnvT)

/-- Every non-bottom identity action is covered by the actual singleton
type row. Compatibility includes the model's automatic bottom observation. -/
theorem covY_aliasPi_coverage (C : CovTyping eqEnvT) (hS : CovTypingIncludesS C) :
    CovYActionCoverage C covNormAliasIdentityCpt .prop [([.pi .bot []], .prop)] := by
  intro ds out ha _
  cases ha with
  | bot => exact Or.inl rfl
  | app hs hx =>
      obtain rfl := List.mem_singleton.mp hs
      refine Or.inr ⟨([.pi .bot []], .prop), List.mem_singleton.mpr rfl, ?_,
        hS _ _ (covY_alias_probe_ctyS eqEnvT)⟩
      intro u hu
      exact approxT_bvar_inv (hx u hu)

/-- The new core uses the old verified alias application action, with leaf
composition at the domain and both distinct codomain positions. -/
theorem lrSCoreCovY_aliasPi (C : CovTyping eqEnvT) (hS : CovTypingIncludesS C)
    (n : Nat) (A B : Expr Nat)
    (hD : HasTyT eqEnvT n eqGapCtx (eqGapDirectAlias A B) (.sort (.succ .zero))) :
    LRSCoreCovY C (WhStepCK2 eqEnvT n) n eqGapCtx
      covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
      covNormAliasIdentityCpt covYAliasPiCode := by
  rw [LRSCoreCovY.eq_def]
  refine ⟨covY_aliasPi_code_typing C hS, Or.inr ⟨eqGapDirectAlias A B, .sort .zero,
    .refl _, covY_aliasPi_coverage C hS, ?_⟩⟩
  intro ds out ha row hr hsel N N' hN hN' hc hd
  obtain rfl := List.mem_singleton.mp hr
  have hdX : ∀ u ∈ ds, LRSCoreCovXAt (n := n) C
      (.sort .zero (eqGapAlias_type_read n A B)) N N' u := by
    intro u hu
    have h := hd u hu
    rw [LRSCoreCovY.eq_def] at h
    exact ⟨by simpa only [sortCode_zero] using h.1, h.2⟩
  obtain ⟨hl, hr⟩ := (covXAliasIdentity_related C hS n A B hD).2
    ds out ha N N' hN hN' hc hdX
  exact ⟨lrSCoreCovY_of_old_leaf C (fun _ _ h => CptT.noConfusion h) hsel.2 hl.2,
    lrSCoreCovY_of_old_leaf C (fun _ _ h => CptT.noConfusion h) hsel.2 hr.2⟩

/-- Full hereditary realization at the alias Pi, at its chosen fixed code.
All argument demands, the binder body, and BOTH instantiated codomains are
proved; none is a port assumed from the desired conclusion. -/
theorem hereditaryCovRealizationYAt_aliasPi (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (ρ : EnvT) (A B : Expr Nat) :
    HereditaryCovRealizationYAt C (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
      n eqGapCtx ρ (covNormAliasPi A B) covNormAliasIdentityCpt covYAliasPiCode := by
  rw [HereditaryCovRealizationYAt.eq_def]
  refine ⟨covY_aliasPi_code_typing C hS, Or.inr ⟨eqGapDirectAlias A B, .sort .zero,
    .refl _, covY_aliasPi_coverage C hS, ?_⟩⟩
  intro ds out ha hnb row hr hsel N N' hN hN' hc hd
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu
    simpa only [sortCode_zero] using hereditaryCovRealizationYAt_sort C n .zero
      (eqGapAlias_type_read n A B)
      (by simpa only [sortCode_zero] using lrSCoreCovY_typing C (hd u hu))
  · simpa only [sortCode_zero] using hereditaryCovRealizationYAt_sort C n .zero
      (Γ := .assumption (eqGapDirectAlias A B) :: eqGapCtx)
      (ρ := EnvT.cons (demandT ds) ρ) (.refl _)
      (by simpa only [sortCode_zero] using hsel.2)
  · simpa only [sortCode_zero] using hereditaryCovRealizationYAt_sort C n .zero
      (Γ := eqGapCtx) (ρ := ρ) (.refl _) (by simpa only [sortCode_zero] using hsel.2)
  · simpa only [sortCode_zero] using hereditaryCovRealizationYAt_sort C n .zero
      (Γ := eqGapCtx) (ρ := ρ) (.refl _) (by simpa only [sortCode_zero] using hsel.2)

/-- The original alias-Pi obstruction's native context and non-bottom
observation coexist with the new core and full hereditary target. The old
head-only normalized target remains false on the same actual compact. -/
theorem covY_aliasPi_control (C : CovTyping eqEnvT) (hS : CovTypingIncludesS C) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    EnvTypedCovYAt C (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
      n eqGapCtx EnvT.bot ∧
    ∃ A B : Expr Nat,
      Nonempty (HasTyT eqEnvT n eqGapCtx covNormAliasIdentity (covNormAliasPi A B)) ∧
      ApproxTK eqEnvT n eqGapCtx EnvT.bot covNormAliasIdentity covNormAliasIdentityCpt ∧
      LRSCoreCovY C (WhStepCK2 eqEnvT n) n eqGapCtx
        covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
        covNormAliasIdentityCpt covYAliasPiCode ∧
      HereditaryCovRealizationYAt C (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
        n eqGapCtx EnvT.bot (covNormAliasPi A B) covNormAliasIdentityCpt covYAliasPiCode ∧
      (¬ NormalizedCovRealization C (ctxModelT_approxTK eqEnvT n eqGapCtx)
        (WhStepCK2 eqEnvT n) eqGapCtx EnvT.bot (covNormAliasPi A B)
        covNormAliasIdentityCpt) ∧ covNormAliasIdentityCpt ≠ .bot := by
  obtain ⟨A, B, ⟨hD⟩, hx⟩ := covNormAliasIdentity_native n
  exact ⟨⟨pinEqGroupWfT⟩, eqGapCtx_wf n, envTypedCovYAt_eqGap_bot C n,
    A, B, hx, covNormAliasIdentity_approxTK eqEnvT n eqGapCtx EnvT.bot,
    lrSCoreCovY_aliasPi C hS n A B hD,
    hereditaryCovRealizationYAt_aliasPi C hS n EnvT.bot A B,
    not_normalizedCovRealization_covNormAliasPi C n EnvT.bot A B,
    fun h => CptT.noConfusion h⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_ALIAS_PI_ROOTS
#print axioms covYAliasPiCode
#print axioms covY_aliasPi_code_typing
#print axioms covY_aliasPi_coverage
#print axioms lrSCoreCovY_aliasPi
#print axioms hereditaryCovRealizationYAt_aliasPi
#print axioms covY_aliasPi_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_ALIAS_PI_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYAudit

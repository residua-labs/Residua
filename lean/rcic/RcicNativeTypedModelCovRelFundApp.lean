import rcic.RcicNativeTypedModelCovRelFund
import rcic.RcicNativeTypedModelCovRelApp

/-!
# The native lambda arm of the four-case application adapter

The retained native substitution evidence supplies both argument typings at
the left substituted domain and their native conversion.  The function and
argument motives then feed the actual recursive lambda action of the new
relation.  Only the spine and saturated branches remain explicit suppliers.

The application step consumes the motives of its two genuine constructor
children, with explicit strict native size comparisons.  It neither invokes
a motive for a generated derivation nor assumes a global typing escape.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.TypedModelKAudit

variable {E : ResolvedEnv} {C : CovTyping E} {M : CtxModelT E}
  {R : Readback} {n : Nat}

/-- The existing native substitution lemmas recover a common domain for both
instances.  No relation gate or model-typing conclusion is needed. -/
theorem RelSubstAtCov.nativeInstances
    (hW : EnvWfT E) (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E)
    (hι : IotaSubstT E) {Γ Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (hS : RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ)
    (hΓ : CtxWfT E n Γ) (hΔ : CtxWfT E n Δ)
    {a A : Expr Nat} (ha : HasTyT E n Γ a A) :
    Nonempty (HasTyT E n Δ (substT σ a) (substT σ A)) ∧
      Nonempty (HasTyT E n Δ (substT σ' a) (substT σ A)) ∧
      Nonempty (ConvT E n Δ (substT σ a) (substT σ' a) (substT σ A)) := by
  obtain ⟨u, hA⟩ := tySort hW hΓ ha
  obtain ⟨hx⟩ := hasTyT_substT hW hcl hst hι hΓ ha hΔ hS.typedL
  obtain ⟨hy⟩ := hasTyT_substT hW hcl hst hι hΓ ha hΔ hS.typedR
  obtain ⟨hdom⟩ := convT_substT_pointwise hW hcl hst hι hΓ hA hΔ
    hS.typedL hS.typedR hS.conv
  have hyLeft : HasTyT E n Δ (substT σ' a) (substT σ A) :=
    .conv _ _ _ _ u hy (.symm _ _ _ _ hdom)
  exact ⟨⟨hx⟩, ⟨hyLeft⟩,
    convT_substT_pointwise hW hcl hst hι hΓ ha hΔ hS.typedL hS.typedR hS.conv⟩

/-- The two unresolved non-lambda application arms.  Their exact observation
premises retain both environments and the explicit saturated computation. -/
structure CovAppResiduals (C : CovTyping E) (R : Readback) (n : Nat)
    (Ξ Γ : LCtx) (f a T : Expr Nat) : Prop where
  spine : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCov C (ctxModelT_approxTK E n Ξ) R n Δ ρ ρ' σ σ' Γ →
    ∀ r args u,
      ((ApproxTK E n Ξ ρ f (.spine r args) ∧ ApproxTK E n Ξ ρ a u) ∨
        (ApproxTK E n Ξ ρ' f (.spine r args) ∧ ApproxTK E n Ξ ρ' a u)) →
      LRSCoreCov C R n Δ (substT σ (.app f a)) (substT σ' (.app f a))
        (substT σ T) (.spine r (args ++ [u]))
  saturated : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCov C (ctxModelT_approxTK E n Ξ) R n Δ ρ ρ' σ σ' Γ →
    ∀ c, SaturatedComputationTK E n Ξ ρ (.app f a) c ∨
      SaturatedComputationTK E n Ξ ρ' (.app f a) c →
      LRSCoreCov C R n Δ (substT σ (.app f a)) (substT σ' (.app f a)) (substT σ T) c

/-- The lambda arm is proved from the two full new motives and the imported
native substitution lemmas, by calling the new recursive application action. -/
theorem covAppArms_of_native_motives (hL : ReadbackLaws E R)
    (hW : EnvWfT E) (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E)
    (hι : IotaSubstT E) {Ξ Γ : LCtx} {f a A B : Expr Nat}
    (hΓ : CtxWfT E n Γ) (ha : HasTyT E n Γ a A)
    (ihf : FundTyAtCov C (ctxModelT_approxTK E n Ξ) R n Γ f (.pi A B))
    (iha : FundTyAtCov C (ctxModelT_approxTK E n Ξ) R n Γ a A)
    (hRest : CovAppResiduals C R n Ξ Γ f a (instantiate0 a B)) :
    CovAppArms C R n Ξ Γ f a (instantiate0 a B) := by
  refine ⟨?_, hRest.spine, hRest.saturated⟩
  intro Δ ρ ρ' σ σ' hΔ hS g s hs ho
  obtain ⟨⟨hx⟩, ⟨hy⟩, hxy⟩ := hS.nativeInstances hW hcl hst hι hΓ hΔ ha
  have hfRel : LRSCoreCov C R n Δ (substT σ f) (substT σ' f)
      (.pi (substT σ A) (substT σ.up B)) (.lam g) :=
    ihf hΔ hS (.lam g) (ho.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  have demands : ∀ u ∈ s.1,
      LRSCoreCov C R n Δ (substT σ a) (substT σ' a) (substT σ A) u := by
    intro u hu
    exact iha hΔ hS u
      (ho.elim (fun h => Or.inl (h.2 u hu)) (fun h => Or.inr (h.2 u hu)))
  simpa only [substT, substT_instantiate0] using
    (lrSCoreCov_app C hL hfRel hs hx hy hxy demands)

/-- The exact four-case inversion now has a proved lambda arm.  The spine
and saturated supplies remain visible in `hRest`. -/
theorem fundCov_app_approxTK_of_residuals (hL : ReadbackLaws E R)
    (hW : EnvWfT E) (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E)
    (hι : IotaSubstT E) {Ξ Γ : LCtx} {f a A B : Expr Nat}
    (hΓ : CtxWfT E n Γ) (ha : HasTyT E n Γ a A)
    (ihf : FundTyAtCov C (ctxModelT_approxTK E n Ξ) R n Γ f (.pi A B))
    (iha : FundTyAtCov C (ctxModelT_approxTK E n Ξ) R n Γ a A)
    (hRest : CovAppResiduals C R n Ξ Γ f a (instantiate0 a B)) :
    FundTyAtCov C (ctxModelT_approxTK E n Ξ) R n Γ (.app f a) (instantiate0 a B) := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  exact fundCov_app_approxTK_of_arms
    (covAppArms_of_native_motives hL hW hcl hst hι hΓ ha ihf iha hRest) hΔ hS c hc

/-- The native application constructor uses precisely its function and
argument subderivations, with explicit strict size proofs. -/
theorem fundCov_app_step_approxTK (hL : ReadbackLaws E R)
    (hW : EnvWfT E) (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E)
    (hι : IotaSubstT E) {Ξ Γ : LCtx} {f a A B : Expr Nat}
    (hf : HasTyT E n Γ f (.pi A B)) (ha : HasTyT E n Γ a A)
    (hRest : CovAppResiduals C R n Ξ Γ f a (instantiate0 a B)) :
    FundTyCovStep C (ctxModelT_approxTK E n Ξ) R n (HasTyT.app Γ f a A B hf ha) := by
  intro hΓ ih
  have hltf : sizeOf hf < sizeOf (HasTyT.app Γ f a A B hf ha) := by simp; omega
  have hlta : sizeOf ha < sizeOf (HasTyT.app Γ f a A B hf ha) := by simp; omega
  have ihf : FundTyAtCov C (ctxModelT_approxTK E n Ξ) R n Γ f (.pi A B) := by
    intro Δ ρ ρ' σ σ' hΔ hS c hc
    exact ih.1 hf hltf hΓ hΔ hS c hc
  have iha : FundTyAtCov C (ctxModelT_approxTK E n Ξ) R n Γ a A := by
    intro Δ ρ ρ' σ σ' hΔ hS c hc
    exact ih.1 ha hlta hΓ hΔ hS c hc
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  exact fundCov_app_approxTK_of_residuals hL hW hcl hst hι hΓ ha ihf iha hRest
    hΔ hS c hc

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_REL_FUND_APP_ROOTS
#print axioms RelSubstAtCov.nativeInstances
#print axioms CovAppResiduals
#print axioms covAppArms_of_native_motives
#print axioms fundCov_app_approxTK_of_residuals
#print axioms fundCov_app_step_approxTK
-- END RCIC_NATIVE_TYPED_MODEL_COV_REL_FUND_APP_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRelAudit

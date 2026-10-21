import rcic.RcicNativeTypedModelCovNormEscape

/-!
# The exact observation boundary after outer weak-head normalization

The incompatibility is stated over any model and readback. It retains the
actual identity-row compact, a normal target type, and the measured shape
of that type's observations. The separate row control supplies a native,
observed and related argument for the identity's nonempty demand.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovNormBoundaryAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit TypedModelKAudit
open TypedModelKTypedBetaAudit TypedModelCovPropagationAudit
open TypedModelCovRelAudit TypedModelCovRelEscapeAudit
open TypedModelCovRelRealizationAudit TypedModelCovNormEscapeAudit

/-- With the compact typing inversion laws fixed, these observations and
normalized typing cannot hold together. No backward model transport or
native conversion soundness premise is used. -/
theorem not_normalizedTyping_of_pi_bot_observations
    {E : ResolvedEnv} (C : CovTyping E) (M : CtxModelT E) (R : Readback)
    (Γ : LCtx) (ρ : EnvT) (e A : Expr Nat)
    (hA : NormalR R Γ A)
    (he : M.Ap ρ e covNormAliasIdentityCpt)
    (hshape : ∀ a, M.Ap ρ A a → a = .bot ∨ ∃ f, a = .pi .bot f) :
    ¬ (∀ c, M.Ap ρ e c → NormalizedCovRealization C M R Γ ρ A c) := by
  intro h
  obtain ⟨a, ha, ht⟩ :=
    (normalizedCovRealization_iff_at_normal C M hA).mp
      (h covNormAliasIdentityCpt he)
  rcases hshape a ha with rfl | ⟨f, rfl⟩
  · exact CptT.noConfusion (C.bot_inv ht)
  · exact not_covNormAliasIdentityCpt_pi_bot C f ht

/-- All three measured inputs of the abstract restatement are realized by
the actual model, uniformly in valuation; the negative typing conclusion
is therefore not obtained from an uninhabited model law. -/
theorem approxTK_normalizedTyping_observation_boundary
    (C : CovTyping eqEnvT) (n : Nat) (ρ : EnvT) (A B : Expr Nat) :
    ¬ (∀ c, ApproxTK eqEnvT n eqGapCtx ρ covNormAliasIdentity c →
      NormalizedCovRealization C (ctxModelT_approxTK eqEnvT n eqGapCtx)
        (WhStepCK2 eqEnvT n) eqGapCtx ρ (covNormAliasPi A B) c) :=
  not_normalizedTyping_of_pi_bot_observations C
    (ctxModelT_approxTK eqEnvT n eqGapCtx) (WhStepCK2 eqEnvT n) eqGapCtx ρ
    covNormAliasIdentity (covNormAliasPi A B) (covNormAliasPi_normal n A B)
    (covNormAliasIdentity_approxTK eqEnvT n eqGapCtx ρ)
    (fun _ ha => covNormAliasPi_observation_shape n eqGapCtx ρ A B ha)

/-- The identity row has an inhabited demand: an actual proposition is
natively typed at the alias, observed at the demanded non-bottom compact,
and related at that alias. Its native conversion is reflexivity of the
displayed typing derivation. -/
theorem covNormAlias_identity_demand_control (C : CovTyping eqEnvT) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    EnvTypedCovAtP C (ctxModelT_approxTK eqEnvT n eqGapCtx) eqGapCtx EnvT.bot ∧
    ∃ A B : Expr Nat,
      Nonempty (HasTyT eqEnvT n eqGapCtx idPiProp (eqGapDirectAlias A B)) ∧
      Nonempty (ConvT eqEnvT n eqGapCtx idPiProp idPiProp (eqGapDirectAlias A B)) ∧
      ApproxTK eqEnvT n eqGapCtx EnvT.bot idPiProp (.pi .bot []) ∧
      LRSCoreCov C (WhStepCK2 eqEnvT n) n eqGapCtx idPiProp idPiProp
        (eqGapDirectAlias A B) (.pi .bot []) ∧
      (.pi .bot [] : CptT) ≠ .bot := by
  obtain ⟨hW, hΓ, hρ, A, B, ⟨ht⟩, hm, hr, _⟩ := alias_type_escape_counterexample C n
  exact ⟨hW, hΓ, hρ, A, B, ⟨ht⟩, ⟨.refl _ _ _ ht⟩, hm, hr,
    fun h => CptT.noConfusion h⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_NORM_BOUNDARY_ROOTS
#print axioms not_normalizedTyping_of_pi_bot_observations
#print axioms approxTK_normalizedTyping_observation_boundary
#print axioms covNormAlias_identity_demand_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_NORM_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovNormBoundaryAudit

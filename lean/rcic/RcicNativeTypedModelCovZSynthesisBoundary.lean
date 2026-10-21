import rcic.RcicNativeTypedModelCovZContract
import rcic.RcicNativeTypedModelCovZRigidPoly

/-!
# No code function satisfies the unchanged joint target

The input is a native admitted constant with a real non-bottom observation,
empty well-formed context, native reflexive conversion, and both hereditary
environment guards. It already has a complete relatedness-only fundamental
supplier. Nevertheless NO code realizes its dependent result. Thus choosing
the code rather than accepting a caller's code does not repair this target.

This result does not refute the weaker, relatedness-only `FundTyAtCovY`.
It refutes the additional same-code hereditary escape requested this round.
No strong-induction assembler is instantiated. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovZAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelKAudit
open ReadbackCK2Audit TypedModelCovRelAudit TypedModelCovNormCov2Audit
open TypedModelCovYAudit TypedModelCovZMeasureAudit

/-- This native constant supplies the entire weaker relation motive: every
target context, related substitution and either-side observation is covered.
The code is a leaf, and is deliberately not claimed to realize the type. -/
theorem fundTyCodeAtCovY_covZRigidPoly (n : Nat) (Γ : LCtx) :
    FundTyCodeAtCovY (C2 covZRigidPolyEnv) (ctxModelT_approxTK covZRigidPolyEnv n)
      (WhStepCK2 covZRigidPolyEnv n) n Γ covZRigidPolyHead covZRigidPolyTy .sort := by
  intro Δ ρ ρ' σ σ' _ _ c hc
  change LRSCoreCovY (C2 covZRigidPolyEnv) (WhStepCK2 covZRigidPolyEnv n) n Δ
    covZRigidPolyHead covZRigidPolyHead covZRigidPolyTy c .sort
  have hm := hc.elim
    (fun h => approxT_rigid_const_inv covZRigidPolyHead_rigid (approxTK_forget h))
    (fun h => approxT_rigid_const_inv covZRigidPolyHead_rigid (approxTK_forget h))
  rcases hm with rfl | rfl
  · exact lrSCoreCovY_bot (C2 covZRigidPolyEnv) _ _ _ _ _
  · exact covZRigidPolyHead_related_leaf n Δ

theorem fundTyAtCovY_covZRigidPoly (n : Nat) (Γ : LCtx) :
    FundTyAtCovY (C2 covZRigidPolyEnv) (ctxModelT_approxTK covZRigidPolyEnv n)
      (WhStepCK2 covZRigidPolyEnv n) n Γ covZRigidPolyHead covZRigidPolyTy :=
  fundTyAtCovY_of_code (fundTyCodeAtCovY_covZRigidPoly n Γ)

/-- Even the diagonal at the empty context has no common realizing code. -/
theorem not_covZ_rigidPoly_joint_code (n : Nat) :
    ¬ ∃ b, CovZJointCodeAt (C2 covZRigidPolyEnv)
      (ctxModelT_approxTK covZRigidPolyEnv n) (WhStepCK2 covZRigidPolyEnv n) n
      [] EnvT.bot EnvT.bot covZRigidPolyHead covZRigidPolyHead covZRigidPolyTy
      (.spine 0 []) b := by
  rintro ⟨b, _, hh, _⟩
  exact not_covZRigidPoly_hereditary_any_code n [] EnvT.bot b hh

theorem not_covZ_typedJointSynthesis (n : Nat) :
    ¬ CovZTypedJointSynthesis covZRigidPolyEnv n :=
  covZ_not_typedJoint_of_no_realization covZRigidPolyEnvWfT
    (covZRigidPolyHead_hasTy n []) (covZRigidPolyHead_observed n [] EnvT.bot)
    ⟨.sort, covZRigidPolyHead_related_leaf n []⟩
    (not_covZRigidPoly_hereditary_any_code n [] EnvT.bot)

/-- No total function has the requested specification, even without any
computability or structural-recursion restriction. The native type is already
in CK2 normal form, so missing readback data cannot explain the failure. -/
theorem not_covZ_closedCodeOf (n : Nat) :
    ¬ ∃ codeOf, CovZClosedCodeOfSpec covZRigidPolyEnv n codeOf :=
  covZ_no_codeOf_of_no_realization covZRigidPolyEnvWfT
    (covZRigidPolyHead_hasTy n []) (covZRigidPolyHead_observed n [] EnvT.bot)
    (RedR.refl _) (normalR_piCK2 [] (.sort (.succ .zero)) (.bvar 0))
    (not_covZRigidPoly_hereditary_any_code n [] EnvT.bot)

/-- Exact separation of the surviving motive and the refuted strengthening. -/
theorem covZ_rigidPoly_boundary (n : Nat) :
    Nonempty (EnvWfT covZRigidPolyEnv) ∧
    Nonempty (CtxWfT covZRigidPolyEnv n []) ∧
    Nonempty (HasTyT covZRigidPolyEnv n [] covZRigidPolyHead covZRigidPolyTy) ∧
    Nonempty (ConvT covZRigidPolyEnv n [] covZRigidPolyHead covZRigidPolyHead
      covZRigidPolyTy) ∧
    EnvTypedCovYAt (C2 covZRigidPolyEnv) (ctxModelT_approxTK covZRigidPolyEnv n)
      (WhStepCK2 covZRigidPolyEnv n) n [] EnvT.bot ∧
    EnvTypedCovYAt (C2 covZRigidPolyEnv) (ctxModelT_approxTK covZRigidPolyEnv n)
      (WhStepCK2 covZRigidPolyEnv n) n [] EnvT.bot ∧
    ApproxTK covZRigidPolyEnv n [] EnvT.bot covZRigidPolyHead (.spine 0 []) ∧
    ApproxTK covZRigidPolyEnv n [] EnvT.bot covZRigidPolyHead (.spine 0 []) ∧
    (CptT.spine 0 []) ≠ .bot ∧
    FundTyAtCovY (C2 covZRigidPolyEnv) (ctxModelT_approxTK covZRigidPolyEnv n)
      (WhStepCK2 covZRigidPolyEnv n) n [] covZRigidPolyHead covZRigidPolyTy ∧
    ¬ ∃ b, CovZJointCodeAt (C2 covZRigidPolyEnv)
      (ctxModelT_approxTK covZRigidPolyEnv n) (WhStepCK2 covZRigidPolyEnv n) n
      [] EnvT.bot EnvT.bot covZRigidPolyHead covZRigidPolyHead covZRigidPolyTy
      (.spine 0 []) b := by
  have he := envTypedCovYAt_nil (C2 covZRigidPolyEnv)
    (ctxModelT_approxTK covZRigidPolyEnv n) (WhStepCK2 covZRigidPolyEnv n) n EnvT.bot
  exact ⟨⟨covZRigidPolyEnvWfT⟩, ⟨.nil⟩, ⟨covZRigidPolyHead_hasTy n []⟩,
    ⟨.refl _ _ _ (covZRigidPolyHead_hasTy n [])⟩, he, he,
    covZRigidPolyHead_observed n [] EnvT.bot, covZRigidPolyHead_observed n [] EnvT.bot,
    CptT.noConfusion, fundTyAtCovY_covZRigidPoly n [], not_covZ_rigidPoly_joint_code n⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Z_SYNTHESIS_BOUNDARY_ROOTS
#print axioms fundTyCodeAtCovY_covZRigidPoly
#print axioms fundTyAtCovY_covZRigidPoly
#print axioms not_covZ_rigidPoly_joint_code
#print axioms not_covZ_typedJointSynthesis
#print axioms not_covZ_closedCodeOf
#print axioms covZ_rigidPoly_boundary
-- END RCIC_NATIVE_TYPED_MODEL_COV_Z_SYNTHESIS_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovZAudit

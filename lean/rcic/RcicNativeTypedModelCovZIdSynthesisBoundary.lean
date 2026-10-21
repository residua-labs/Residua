import rcic.RcicNativeTypedModelCovZSynthesisBoundary
import rcic.RcicNativeTypedModelCovZRigidId

/-!
# The joint synthesis refutation at an inhabited polymorphic identity type

This stronger instance has an imported native lambda inhabitant for the
declared type. The actual rigid Pi typing gate is inhabited, and an actual
typed application supplies its non-bottom empty-demand action. No Pi code
can satisfy both that gate and action coverage. Leaf codes cannot realize
the native Pi type. Code selection alone cannot meet the requested target.

The weaker relatedness-only fundamental motive still has a complete supplier.
These closed refutations add no model hypotheses. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovZAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelAudit.TypingFin TypedModelKAudit
open ReadbackCK2Audit TypedModelCovRelAudit TypedModelCovNormCov2Audit
open TypedModelCovYAudit TypedModelCovZMeasureAudit

theorem fundTyCodeAtCovY_covZRigidId (n : Nat) (Γ : LCtx) :
    FundTyCodeAtCovY (C2 covZRigidIdEnv) (ctxModelT_approxTK covZRigidIdEnv n)
      (WhStepCK2 covZRigidIdEnv n) n Γ (.const 0 []) cexPolyIdTy .sort := by
  intro Δ ρ ρ' σ σ' _ _ c hc
  change LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n Δ
    (.const 0 []) (.const 0 []) cexPolyIdTy c .sort
  have hm := hc.elim
    (fun h => approxT_rigid_const_inv covZRigidIdHead_rigid (approxTK_forget h))
    (fun h => approxT_rigid_const_inv covZRigidIdHead_rigid (approxTK_forget h))
  rcases hm with rfl | rfl
  · exact lrSCoreCovY_bot (C2 covZRigidIdEnv) _ _ _ _ _
  · exact covZRigidIdHead_related_leaf n Δ

theorem fundTyAtCovY_covZRigidId (n : Nat) (Γ : LCtx) :
    FundTyAtCovY (C2 covZRigidIdEnv) (ctxModelT_approxTK covZRigidIdEnv n)
      (WhStepCK2 covZRigidIdEnv n) n Γ (.const 0 []) cexPolyIdTy :=
  fundTyAtCovY_of_code (fundTyCodeAtCovY_covZRigidId n Γ)

theorem not_covZ_rigidId_joint_code (n : Nat) :
    ¬ ∃ b, CovZJointCodeAt (C2 covZRigidIdEnv)
      (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
      [] EnvT.bot EnvT.bot (.const 0 []) (.const 0 []) cexPolyIdTy
      (.spine 0 []) b := by
  rintro ⟨b, _, hh, _⟩
  exact not_covZRigidId_hereditary_any_code n [] EnvT.bot b hh

theorem not_covZ_typedJointSynthesis_rigidId (n : Nat) :
    ¬ CovZTypedJointSynthesis covZRigidIdEnv n :=
  covZ_not_typedJoint_of_no_realization covZRigidIdEnvWfT
    (covZRigidIdHead_hasTy n []) (covZRigidIdHead_observed n [] EnvT.bot)
    ⟨.sort, covZRigidIdHead_related_leaf n []⟩
    (not_covZRigidId_hereditary_any_code n [] EnvT.bot)

theorem not_covZ_closedCodeOf_rigidId (n : Nat) :
    ¬ ∃ codeOf, CovZClosedCodeOfSpec covZRigidIdEnv n codeOf :=
  covZ_no_codeOf_of_no_realization covZRigidIdEnvWfT
    (covZRigidIdHead_hasTy n []) (covZRigidIdHead_observed n [] EnvT.bot)
    (RedR.refl _)
    (normalR_piCK2 [] (.sort (.succ .zero)) (.pi (.bvar 0) (.bvar 1)))
    (not_covZRigidId_hereditary_any_code n [] EnvT.bot)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Z_ID_SYNTHESIS_BOUNDARY_ROOTS
#print axioms fundTyCodeAtCovY_covZRigidId
#print axioms fundTyAtCovY_covZRigidId
#print axioms not_covZ_rigidId_joint_code
#print axioms not_covZ_typedJointSynthesis_rigidId
#print axioms not_covZ_closedCodeOf_rigidId
-- END RCIC_NATIVE_TYPED_MODEL_COV_Z_ID_SYNTHESIS_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovZAudit

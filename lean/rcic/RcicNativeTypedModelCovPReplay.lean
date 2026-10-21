import rcic.RcicNativeTypedModelCovPIdentity
import rcic.RcicNativeTypedModelCovPTyping
import rcic.RcicNativeTypedModelCovPOuterIdentity
import rcic.RcicNativeTypedModelCovPStrictBoundary

/-!
# Concrete replay for positive collapse, with and without reflection

The Boolean switch names the two actual repaired compact typings: false is
(b), true is (b+r). Both pass the inhabited outer identity gate and action
coverage. Both retain bottom inversion, so neither can supply hereditary
realization at any code under the unchanged actions and exact leaves.

The old relatedness certificate remains explicit as the selected demand
relation payload. The obstruction holds for every alternative demand
relation as well, since its two decisive demand lists are empty.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit ReadbackCK2Audit TypedModelCovRelAudit
open TypedModelCovNormCov2Audit TypedModelCovYAudit TypedModelCovZMeasureAudit

theorem covP_identity_b_or_br_no_code (reflect : Bool) (Rel : CovPDemandRelation)
    (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ∀ a, ¬ HereditaryCovRealizationPAt (CTyCovP2 reflect covZRigidIdEnv) Rel
      (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
      Γ ρ cexPolyIdTy (.spine 0 []) a :=
  covP_not_hereditary_identity_spine (C2P reflect covZRigidIdEnv).bot_inv
    n Γ ρ 0 []

theorem covP_neutral_b_or_br_no_code (reflect : Bool) (E : ResolvedEnv)
    (Rel : CovPDemandRelation) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (r : Nat) (us : List CptT) :
    ∀ a, ¬ HereditaryCovRealizationPAt (CTyCovP2 reflect E) Rel
      (ctxModelT_approxTK E n) (WhStepCK2 E n) n Γ ρ
      (.pi (.sort (.succ .zero)) (.bvar 0)) (.spine r us) a :=
  covP_not_hereditary_poly_result_spine (C2P reflect E).bot_inv n Γ ρ r us

/-- Actual native and baseline-relation premises, plus the newly repaired
outer gate and coverage, coexist with the all-code hereditary failure. -/
theorem covP_identity_b_or_br_control (reflect : Bool) (n : Nat) :
    Nonempty (HasTyT emptyEnv n [] cexPolyId cexPolyIdTy) ∧
    Nonempty (EnvWfT covZRigidIdEnv) ∧
    Nonempty (CtxWfT covZRigidIdEnv n []) ∧
    Nonempty (HasTyT covZRigidIdEnv n [] (.const 0 []) cexPolyIdTy) ∧
    Nonempty (ConvT covZRigidIdEnv n [] (.const 0 []) (.const 0 []) cexPolyIdTy) ∧
    ApproxTK covZRigidIdEnv n [] EnvT.bot (.const 0 []) (.spine 0 []) ∧
    LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n []
      (.const 0 []) (.const 0 []) cexPolyIdTy (.spine 0 []) .sort ∧
    (CptT.spine 0 []) ≠ .bot ∧
    CTyCovP2 reflect covZRigidIdEnv (.spine 0 []) covPIdentityOuterCode ∧
    CovPActionCoverage covZRigidIdEnv (CTyCovP2 reflect covZRigidIdEnv)
      (.spine 0 []) .sort [([], .pi .bot [])] ∧
    ¬ ∃ a, HereditaryCovRealizationPAt (CTyCovP2 reflect covZRigidIdEnv)
      (LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n)
      (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
      [] EnvT.bot cexPolyIdTy (.spine 0 []) a := by
  obtain ⟨hLam, hW, hΓ, ht, hconv, ho, hrel, hnb, hno⟩ :=
    covP_rigidId_control (CTyCovP2 reflect covZRigidIdEnv)
      (LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n)
      (C2P reflect covZRigidIdEnv).bot_inv n
  exact ⟨hLam, hW, hΓ, ht, hconv, ho, hrel, hnb,
    covPIdentity_outer_gate reflect, covPIdentity_outer_coverage reflect, hno⟩

theorem covP_strict_identity_b_or_br_no_code (reflect : Bool)
    (Rel : CovPDemandRelation) (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ∀ a, ¬ HereditaryCovRealizationPAt (CTyCovP2 reflect covZRigidIdEnv) Rel
      (ctxModelT_approxTKStrictP covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
      Γ ρ cexPolyIdTy (.spine 0 []) a :=
  covP_not_hereditary_strict_identity_spine (C2P reflect covZRigidIdEnv).bot_inv
    n Γ ρ 0 []

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_REPLAY_ROOTS
#print axioms covP_identity_b_or_br_no_code
#print axioms covP_neutral_b_or_br_no_code
#print axioms covP_identity_b_or_br_control
#print axioms covP_strict_identity_b_or_br_no_code
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_REPLAY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPAudit

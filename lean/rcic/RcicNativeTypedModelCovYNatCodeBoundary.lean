import rcic.RcicNativeTypedModelCovYEtaRealization
import rcic.RcicNativeTypedModelCovYEnvironment

/-!
# Exact-code escape needs native type-code alignment even at Nat

This is a base-type boundary, independent of the retained universe payload.
Native zero has native type Nat and its actual non-bottom compact. C2 also
types that compact at `spine 0 [bot]`, a structural type code which native Nat
never observes. The leaf relation reuses its valid zero relation, whereas
hereditary realization at this exact unsupported code is false.

The correct code `spine 0 []` simultaneously supplies the relation and
realization. Thus this refutes bare relation-to-SAME-CODE escape, not the
existence of a suitable code or the relatedness-only Fundamental motive.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit
open TypedModelCovXAudit TypedModelCovXEtaAudit TypedModelCovYAudit

/-- The base relation is inhabited even at the extra-argument Nat code.
This is a consequence of the retained ordinary spine typing branch. -/
theorem covY_natZero_extraArgCode_related (n : Nat) (Γ : LCtx) :
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Γ
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) (.spine 0 [.bot]) := by
  apply lrSCoreCovY_of_old_leaf (C2 natEnvU)
    (fun d g he => CptT.noConfusion he) ?_ (covX_natZero_related n Γ)
  change CTyCov2 natEnvU (.spine 1 []) (.spine 0 [.bot])
  rw [CTyCov2]
  exact Or.inr ⟨⟨1, [], rfl⟩, not_isPropCT_natEnvU_nat_spine [.bot]⟩

/-- Exact-code realization is impossible: the actual normal Nat head only
observes bottom or its zero-argument family code. -/
theorem not_hereditaryCovRealizationYAt_nat_extraArgCode (n : Nat)
    (Γ : LCtx) (ρ : EnvT) :
    ¬ HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ ρ (.const 0 []) (.spine 1 []) (.spine 0 [.bot]) := by
  intro h
  rw [HereditaryCovRealizationYAt.eq_def] at h
  rcases h.2 with hb | ⟨A₀, hr, hn, ho⟩
  · exact CptT.noConfusion hb
  · have he := redR_of_normal
      (normalR_famAppCK2 natEnvUWfT
        (rfl : natEnvU.members 0 = some natFamMember) rfl Γ [] []) hr
    subst A₀
    rcases approxT_rigid_const_inv rigidConst_natEnvU_nat
      (approxTK_forget ho) with he | he <;> cases he

/-- All native, environment, structural-code and actual-observation guards
are inhabited. At the same term compact the correct actual code supplies
both relatedness and hereditary realization. -/
theorem covY_natZero_extraArgCode_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    EnvTypedCovYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n [] EnvT.bot ∧
    Nonempty (HasTyT natEnvU n [] (.const 1 []) (.const 0 [])) ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 1 []) (.spine 1 []) ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 0 []) (.spine 0 []) ∧
    TyCodeCT (.spine 0 [.bot]) ∧
    (C2 natEnvU).ty (.spine 1 []) (.spine 0 [.bot]) ∧
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n []
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) (.spine 0 [.bot]) ∧
    (¬ HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n [] EnvT.bot (.const 0 []) (.spine 1 []) (.spine 0 [.bot])) ∧
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n []
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) (.spine 0 []) ∧
    HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n [] EnvT.bot (.const 0 []) (.spine 1 []) (.spine 0 []) ∧
    (.spine 1 [] : CptT) ≠ .bot := by
  have hbad := covY_natZero_extraArgCode_related n []
  have hgood := covY_natZero_related n []
  exact ⟨⟨natEnvUWfT⟩, ⟨.nil⟩,
    envTypedCovYAt_nil (C2 natEnvU) (ctxModelT_approxTK natEnvU n) _ n EnvT.bot,
    ⟨hasTyT_natEnvU_zero n []⟩,
    ApproxTK.free (kFreeT_natEnvU _)
      (.const _ 1 [] rigidConst_natEnvU_zero not_propCtorT_natEnvU_zero),
    ApproxTK.free (kFreeT_natEnvU _)
      (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat),
    .spine _ _, lrSCoreCovY_typing (C2 natEnvU) hbad, hbad,
    not_hereditaryCovRealizationYAt_nat_extraArgCode n [] EnvT.bot,
    hgood, covY_nat_hereditary_at n [] EnvT.bot _
      (lrSCoreCovY_typing (C2 natEnvU) hgood), fun h => CptT.noConfusion h⟩

/-- Even the typed, actually observed diagonal does not imply escape at an
arbitrary structural code allowed by C2. Native code alignment is additional. -/
theorem not_covY_exactCode_escape_natEnv (n : Nat) :
    ¬ (∀ {Γ : LCtx} {ρ : EnvT} {x A : Expr Nat} {c a : CptT},
      CtxWfT natEnvU n Γ →
      EnvTypedCovYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
        (WhStepCK2 natEnvU n) n Γ ρ →
      HasTyT natEnvU n Γ x A → ApproxTK natEnvU n Γ ρ x c → TyCodeCT a →
      LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Γ x x A c a →
      HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
        (WhStepCK2 natEnvU n) n Γ ρ A c a) := by
  intro h
  exact not_hereditaryCovRealizationYAt_nat_extraArgCode n [] EnvT.bot
    (h .nil (envTypedCovYAt_nil (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      _ n EnvT.bot) (hasTyT_natEnvU_zero n [])
      (ApproxTK.free (kFreeT_natEnvU _)
        (.const _ 1 [] rigidConst_natEnvU_zero not_propCtorT_natEnvU_zero))
      (.spine _ _) (covY_natZero_extraArgCode_related n []))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_NAT_CODE_BOUNDARY_ROOTS
#print axioms covY_natZero_extraArgCode_related
#print axioms not_hereditaryCovRealizationYAt_nat_extraArgCode
#print axioms covY_natZero_extraArgCode_control
#print axioms not_covY_exactCode_escape_natEnv
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_NAT_CODE_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYEtaAudit

import rcic.RcicNativeTypedModelCovYEnvironment
import rcic.RcicNativeTypedModelCovYEtaRealization

/-!
# Native Pi typing does not select a semantic Pi code

The core branches on its displayed semantic type code. Without a native
code-shape anchor, the actually typed and observed successor can choose the
non-Pi Nat code: C2 admits its rigid compact there, and the non-Pi leaf composes
the old same-head relation. Thus a native Pi type alone does not expose the
new application clause. The exact false shape-extraction port is refuted with
all native/model/hereditary-environment premises inhabited.

The same input has a correctly shaped, actually observed Pi code with both
application relatedness and hereditary realization. This is not a refutation
of that positive construction or of an existential code-selection theorem.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCK2Audit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelCovRelAudit TypedModelCovRelWitnessAudit TypedModelCovNormCov2Audit
open TypedModelCovYEtaAudit

/-- The native arrow may use a non-Pi code under the literal current
definition. No Pi action or coverage is asserted for this leaf witness. -/
theorem covY_natSucc_nonPi_code_related (n : Nat) (Γ : LCtx) :
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Γ
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) (.spine 0 []) := by
  apply lrSCoreCovY_of_old_leaf (C2 natEnvU)
    (fun d g he => CptT.noConfusion he) ?_
    (lrSCoreCov_natSucc_spine (C2 natEnvU) n Γ)
  change CTyCov2 natEnvU (.spine 2 []) (.spine 0 [])
  rw [CTyCov2]
  exact Or.inr ⟨⟨2, [], rfl⟩, not_isPropCT_natEnvU_nat_spine []⟩

/-- The proposed inference keeps native Pi typing, real endpoint observations,
the structural type-code predicate, non-bottomness, and both new env guards. -/
def CovYNativePiCodeShape (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {ρ ρ' : EnvT} {x y D B : Expr Nat} {c a : CptT},
    EnvWfT natEnvU → CtxWfT natEnvU n Γ →
    HasTyT natEnvU n Γ x (.pi D B) → HasTyT natEnvU n Γ y (.pi D B) →
    EnvTypedCovYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ ρ →
    EnvTypedCovYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n Γ ρ' →
    ApproxTK natEnvU n Γ ρ x c → ApproxTK natEnvU n Γ ρ' y c →
    TyCodeCT a → c ≠ .bot →
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n Γ x y (.pi D B) c a →
    ∃ d g, a = CptT.pi d g

theorem not_covYNativePiCodeShape (n : Nat) : ¬ CovYNativePiCodeShape n := by
  intro shape
  have ht := hasTyT_natEnvU_succ n []
  have ho : ApproxTK natEnvU n [] EnvT.bot (.const 2 []) (.spine 2 []) :=
    ApproxTK.free (kFreeT_natEnvU _) (approxT_natSucc_spine EnvT.bot)
  have henv := envTypedCovYAt_nil (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
    (WhStepCK2 natEnvU n) n EnvT.bot
  obtain ⟨d, g, he⟩ := shape natEnvUWfT .nil ht ht henv henv ho ho (.spine _ _)
    (fun h => CptT.noConfusion h) (covY_natSucc_nonPi_code_related n [])
  cases he

/-- The same actual observation admits both the unanchored non-Pi leaf and
the proper, observed Pi code with its full hereditary realization. -/
theorem covY_natSucc_code_shape_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    Nonempty (HasTyT natEnvU n [] (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 2 []) (.spine 2 []) ∧
    EnvTypedCovYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n [] EnvT.bot ∧
    TyCodeCT (.spine 0 []) ∧
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n []
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) (.spine 0 []) ∧
    (¬ ∃ d g, (.spine 0 [] : CptT) = .pi d g) ∧
    ApproxTK natEnvU n [] EnvT.bot (.pi (.const 0 []) (.const 0 [])) covYNatArrowCode ∧
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n []
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covYNatArrowCode ∧
    HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n [] EnvT.bot (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covYNatArrowCode ∧
    (.spine 2 [] : CptT) ≠ .bot :=
  ⟨⟨natEnvUWfT⟩, ⟨.nil⟩, ⟨hasTyT_natEnvU_succ n []⟩,
    ApproxTK.free (kFreeT_natEnvU _) (approxT_natSucc_spine EnvT.bot),
    envTypedCovYAt_nil (C2 natEnvU) (ctxModelT_approxTK natEnvU n) _ n EnvT.bot,
    .spine _ _, covY_natSucc_nonPi_code_related n [],
    (fun ⟨_, _, he⟩ => CptT.noConfusion he),
    approxTK_covYNatArrowCode n [] EnvT.bot, covY_natSucc_related n [],
    covY_natArrow_hereditary_at n [] EnvT.bot _ covY_natSucc_code_typed
      covY_natSucc_uniform_coverage, fun h => CptT.noConfusion h⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_SHAPE_BOUNDARY_ROOTS
#print axioms covY_natSucc_nonPi_code_related
#print axioms CovYNativePiCodeShape
#print axioms not_covYNativePiCodeShape
#print axioms covY_natSucc_code_shape_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_SHAPE_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYAudit

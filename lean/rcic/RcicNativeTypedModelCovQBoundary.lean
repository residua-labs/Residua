import rcic.RcicNativeTypedModelCovQFinite
import rcic.RcicNativeTypedModelCovQReindex
import rcic.RcicNativeTypedModelCovPProofCollapse

/-!
# Pointwise finite realization and the missing uniform finite bound

Every closed tower instance below has native inhabitants, a non-bottom
observation, and a displayed full P-shaped hereditary code. No one finite
code realizes all tower depths, even under the weaker instance-first Q
interface. The actual proof-of-True model obstruction remains unchanged.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovQAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit ReadbackCK2Audit TypedModelCovRelAudit
open TypedModelCovNormCov2Audit TypedModelCovYAudit TypedModelCovZMeasureAudit
open TypedModelCovNormConvCasesAudit TypedModelCovPAudit

/-- A realized tower consumes at least its number of native Pi layers,
even after row selection has been moved behind the native arguments. -/
theorem covQ_realized_tower_lower_bound {E : ResolvedEnv}
    {T : CptT → CptT → Prop} {Rel : CovPDemandRelation}
    (hbot : ∀ {u}, T u .bot → u = .bot) (n k : Nat)
    (Γ : LCtx) (ρ : EnvT) (r : Nat) (us : List CptT) (a : CptT)
    (h : HereditaryCovRealizationQAt T Rel (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ (covQArrowTower k) (.spine r us) a) :
    k ≤ sizeOf a :=
  covQ_tower_code_lower_bound
    (covQ_hereditary_emptyStep (E := E) (T := T) (Rel := Rel) hbot n Γ ρ)
    k r us a h

theorem covQ_no_uniform_tower_code {E : ResolvedEnv}
    {T : CptT → CptT → Prop} {Rel : CovPDemandRelation}
    (hbot : ∀ {u}, T u .bot → u = .bot) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (r : Nat) (us : List CptT) :
    ¬ ∃ a, ∀ k, HereditaryCovRealizationQAt T Rel (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ (covQArrowTower k) (.spine r us) a := by
  rintro ⟨a, ha⟩
  have hsize := covQ_realized_tower_lower_bound hbot n (sizeOf a + 1)
    Γ ρ r us a (ha (sizeOf a + 1))
  omega

/-- All premise families are inhabited; there is no appeal to an arbitrary
fresh type variable having an inhabitant. Every positive witness is computed
by `covQArrowCode`, while a uniform finite witness is actually refuted. -/
theorem covQ_pointwise_not_uniform_control (n : Nat) :
    Nonempty (EnvWfT covZRigidIdEnv) ∧ Nonempty (CtxWfT covZRigidIdEnv n []) ∧
    (∀ k,
      Nonempty (HasTyT covZRigidIdEnv n [] (covQIdentityTowerApp k) (covQArrowTower k)) ∧
      Nonempty (ConvT covZRigidIdEnv n [] (covQIdentityTowerApp k)
        (covQIdentityTowerApp k) (covQArrowTower k)) ∧
      ApproxTK covZRigidIdEnv n [] EnvT.bot (covQIdentityTowerApp k)
        (.spine 0 [.bot, .bot]) ∧
      HereditaryCovRealizationPAt (CTyCovQ covZRigidIdEnv)
        (LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n)
        (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
        [] EnvT.bot (covQArrowTower k) (.spine 0 [.bot, .bot]) (covQArrowCode k)) ∧
    ¬ (∃ a, ∀ k,
      HereditaryCovRealizationQAt (CTyCovQ covZRigidIdEnv)
        (LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n)
        (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
        [] EnvT.bot (covQArrowTower k) (.spine 0 [.bot, .bot]) a) := by
  refine ⟨⟨covZRigidIdEnvWfT⟩, ⟨.nil⟩, ?_, ?_⟩
  · intro k
    obtain ⟨_, _, _, ht, hc, ho, _, hh⟩ := covQIdentityTower_control n k
    exact ⟨ht, hc, ho, hh⟩
  · exact covQ_no_uniform_tower_code ctyCovQ_bot_inv n [] EnvT.bot 0 [.bot, .bot]

/-- The new universe membership cannot turn the observation of a genuine
proof of True into a typed proof: its actual type observations are unchanged
and never the universe code `.prop`. This composes the old no-code result. -/
theorem covQProof_no_observed_type_code (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ¬ ∃ a, ApproxTK covPProofEnv n Γ ρ (.const 0 []) a ∧
      CTyCovQ covPProofEnv (.spine 3 []) a := by
  rintro ⟨a, ho, ht⟩
  have hnp : a ≠ .prop := by
    intro he
    subst a
    rcases approxT_rigid_const_inv covPProof_true_rigid (approxTK_forget ho) with
      he | he <;> exact CptT.noConfusion he
  exact covPProof_no_observed_type_code true n Γ ρ
    ⟨a, ho, (ctyCovQ_nonprop_iff hnp).mp ht⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Q_BOUNDARY_ROOTS
#print axioms covQ_realized_tower_lower_bound
#print axioms covQ_no_uniform_tower_code
#print axioms covQ_pointwise_not_uniform_control
#print axioms covQProof_no_observed_type_code
-- END RCIC_NATIVE_TYPED_MODEL_COV_Q_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovQAudit

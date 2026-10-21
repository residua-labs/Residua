import rcic.RcicNativeTypedModelCovQTower
import rcic.RcicNativeTypedModelCovQUniverse
import rcic.RcicNativeTypedModelCovPReflection

/-!
# Actual finite codes for each closed Prop-arrow instance

The code family is constructed by recursion on the finite native arrow tower.
The realization proof uses that same index, never the growing compact produced
by a rigid application. Universe reflection supplies its exact Prop leaves.

These are actual hereditary suppliers for every separately fixed tower depth.
They retain the landed CoreY relation as their demand payload. They do not claim
the old CoreY relation at the new realizing code, a common code for all depths,
or hereditary realization of the polymorphic identity head. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovQAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit ReadbackCK2Audit TypedModelCovRelAudit TypedModelCovNormCov2Audit
open TypedModelCovXAudit TypedModelCovYAudit TypedModelCovZMeasureAudit TypedModelCovPAudit

variable {E : ResolvedEnv}

def covQArrowCode : Nat → CptT
  | 0 => .prop
  | k + 1 => .pi .prop [([], covQArrowCode k)]

theorem covQArrowCode_type (k : Nat) : TyCodeCT (covQArrowCode k) := by
  induction k with
  | zero => exact .prop
  | succ k ih =>
      refine .pi .prop ?_
      intro row hrow
      obtain rfl := List.mem_singleton.mp hrow
      exact ih

theorem covQArrowCode_not_positive (E : ResolvedEnv) (k : Nat) :
    ¬ IsPropCTP E (covQArrowCode k) := by
  induction k with
  | zero => exact not_isPropCTP_prop E
  | succ k ih =>
      intro h
      cases h with
      | pi _ _ hout =>
          exact ih (hout _ (List.mem_singleton.mpr rfl))

theorem covQ_neutral_arrowCode_typing {r : Nat} (hh : NeutralHeadP E r)
    (k : Nat) (us : List CptT) :
    CTyCovQ E (.spine r us) (covQArrowCode k) := by
  cases k with
  | zero => exact ctyCovQ_univNeutral hh
  | succ k =>
      exact ctyCovQ_of_P (CTyCovP2.reflectedPi rfl hh
        (covQArrowCode_not_positive E (k + 1)))

theorem covQ_neutral_arrowCode_coverage {r : Nat} (hh : NeutralHeadP E r)
    (k : Nat) (us : List CptT) :
    CovPActionCoverage E (CTyCovQ E) (.spine r us) .prop
      [([], covQArrowCode k)] := by
  intro ds out hact _
  cases hact with
  | bot => exact Or.inl rfl
  | appSpine hx =>
      refine Or.inr ⟨([], covQArrowCode k), List.mem_singleton.mpr rfl, ?_, ?_⟩
      · intro u hu
        exact (List.not_mem_nil u hu).elim
      · exact covQ_neutral_arrowCode_typing hh k _

/-- Every finite native tower has its own actual code. The induction index
decreases while rigid output spines may grow. Both binder-body and instantiated
codomain obligations are supplied, with no change to the old-shaped H clauses. -/
theorem covQ_neutral_arrowTower_realization {r : Nat} (hh : NeutralHeadP E r)
    (n k : Nat) (Γ : LCtx) (ρ : EnvT) (us : List CptT) :
    HereditaryCovRealizationPAt (CTyCovQ E)
      (LRSCoreCovY (C2 E) (WhStepCK2 E n) n)
      (ctxModelT_approxTK E n) (WhStepCK2 E n) n
      Γ ρ (covQArrowTower k) (.spine r us) (covQArrowCode k) := by
  induction k generalizing Γ ρ us with
  | zero =>
      exact covQ_hereditary_sort_zero _ n Γ ρ (ctyCovQ_univNeutral hh)
  | succ k ih =>
      rw [covQArrowCode, HereditaryCovRealizationPAt.eq_def]
      refine ⟨covQ_neutral_arrowCode_typing hh (k + 1) us,
        Or.inr ⟨.sort .zero, covQArrowTower k, .refl _,
          covQ_neutral_arrowCode_coverage hh k us, ?_⟩⟩
      intro ds out hact hnb row hrow hsel N N' hN hN' hconv hrel
      obtain rfl := List.mem_singleton.mp hrow
      cases hact with
      | bot => exact (hnb rfl).elim
      | @appSpine r us x v hx =>
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro u hu
            exact covQ_hereditary_sort_zero _ n Γ ρ
              (ctyCovQ_of_C2 (lrSCoreCovY_typing (C2 E) (hrel u hu)))
          · exact ih (.assumption (.sort .zero) :: Γ)
              (EnvT.cons (demandT ds) ρ) (us ++ [v])
          · simpa only [covQArrowTower_instantiate0] using ih Γ ρ (us ++ [v])
          · simpa only [covQArrowTower_instantiate0] using ih Γ ρ (us ++ [v])

def covQIdentityTowerApp (k : Nat) : Expr Nat :=
  .app (.app (.const 0 []) (covQArrowTower k)) (covQArrowTowerWitness k)

theorem covQIdentityTowerApp_hasTy (n k : Nat) (Γ : LCtx) :
    Nonempty (HasTyT covZRigidIdEnv n Γ
      (covQIdentityTowerApp k) (covQArrowTower k)) :=
  (covQ_identity_tower_application_control n k Γ EnvT.bot).1

theorem covQIdentityTowerApp_observed (n k : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK covZRigidIdEnv n Γ ρ (covQIdentityTowerApp k)
      (.spine 0 [.bot, .bot]) :=
  (covQ_identity_tower_application_control n k Γ ρ).2

theorem covQIdentityTowerApp_realization (n k : Nat) (Γ : LCtx) (ρ : EnvT) :
    HereditaryCovRealizationPAt (CTyCovQ covZRigidIdEnv)
      (LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n)
      (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
      Γ ρ (covQArrowTower k) (.spine 0 [.bot, .bot]) (covQArrowCode k) :=
  covQ_neutral_arrowTower_realization covPIdentity_neutral_head n k Γ ρ _

/-- A supplier for every separately fixed depth, with actual native and model
premises. The selected code is displayed, not assumed as an input hypothesis. -/
theorem covQIdentityTower_control (n k : Nat) :
    Nonempty (HasTyT emptyEnv n [] cexPolyId cexPolyIdTy) ∧
    Nonempty (EnvWfT covZRigidIdEnv) ∧
    Nonempty (CtxWfT covZRigidIdEnv n []) ∧
    Nonempty (HasTyT covZRigidIdEnv n [] (covQIdentityTowerApp k) (covQArrowTower k)) ∧
    Nonempty (ConvT covZRigidIdEnv n [] (covQIdentityTowerApp k)
      (covQIdentityTowerApp k) (covQArrowTower k)) ∧
    ApproxTK covZRigidIdEnv n [] EnvT.bot (covQIdentityTowerApp k)
      (.spine 0 [.bot, .bot]) ∧
    (CptT.spine 0 [.bot, .bot]) ≠ .bot ∧
    HereditaryCovRealizationPAt (CTyCovQ covZRigidIdEnv)
      (LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n)
      (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
      [] EnvT.bot (covQArrowTower k) (.spine 0 [.bot, .bot]) (covQArrowCode k) := by
  obtain ⟨ht⟩ := covQIdentityTowerApp_hasTy n k []
  exact ⟨⟨hasTyT_cexPolyId emptyEnv n⟩, ⟨covZRigidIdEnvWfT⟩, ⟨.nil⟩,
    ⟨ht⟩, ⟨.refl _ _ _ ht⟩,
    covQIdentityTowerApp_observed n k [] EnvT.bot, CptT.noConfusion,
    covQIdentityTowerApp_realization n k [] EnvT.bot⟩

/-- The exact two native applications used by the earlier no-common-code
argument now each have their own supplied hereditary code. This states no old
CoreY certificate at either new realizing code. -/
theorem covQIdentity_two_instance_control (n : Nat) :
    Nonempty (EnvWfT covZRigidIdEnv) ∧ Nonempty (CtxWfT covZRigidIdEnv n []) ∧
    Nonempty (HasTyT covZRigidIdEnv n []
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp) (.sort .zero)) ∧
    Nonempty (HasTyT covZRigidIdEnv n []
      (.app (.app (.const 0 []) covPPropArrow) covPPropArrowId) covPPropArrow) ∧
    ApproxTK covZRigidIdEnv n [] EnvT.bot
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp) (.spine 0 [.bot, .bot]) ∧
    ApproxTK covZRigidIdEnv n [] EnvT.bot
      (.app (.app (.const 0 []) covPPropArrow) covPPropArrowId)
      (.spine 0 [.bot, .bot]) ∧
    HereditaryCovRealizationPAt (CTyCovQ covZRigidIdEnv)
      (LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n)
      (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
      [] EnvT.bot (.sort .zero) (.spine 0 [.bot, .bot]) .prop ∧
    HereditaryCovRealizationPAt (CTyCovQ covZRigidIdEnv)
      (LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n)
      (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
      [] EnvT.bot covPPropArrow (.spine 0 [.bot, .bot]) (.pi .prop [([], .prop)]) := by
  obtain ⟨ht₀, ht₁, ho₀, ho₁⟩ := covP_rigidId_two_application_control n [] EnvT.bot
  exact ⟨⟨covZRigidIdEnvWfT⟩, ⟨.nil⟩, ht₀, ht₁, ho₀, ho₁,
    covQIdentityTowerApp_realization n 0 [] EnvT.bot,
    covQIdentityTowerApp_realization n 1 [] EnvT.bot⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Q_FINITE_ROOTS
#print axioms covQArrowCode
#print axioms covQArrowCode_type
#print axioms covQArrowCode_not_positive
#print axioms covQ_neutral_arrowCode_typing
#print axioms covQ_neutral_arrowCode_coverage
#print axioms covQ_neutral_arrowTower_realization
#print axioms covQIdentityTowerApp
#print axioms covQIdentityTowerApp_hasTy
#print axioms covQIdentityTowerApp_observed
#print axioms covQIdentityTowerApp_realization
#print axioms covQIdentityTower_control
#print axioms covQIdentity_two_instance_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Q_FINITE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovQAudit

import rcic.RcicNativeTypedModelCovRSyntax
import rcic.RcicNativeTypedModelCovQFinite

/-!
# One candidate realization of the rigid polymorphic identity

The head relation is fixed once. Each native tower is fed into its sort
binder with the candidate supplied by structural interpretation of that
fixed tower. No code or finite code budget is attached to the head.
The final result relation is the new tower interpretation, never CoreY.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelAudit.TypingFin TypedModelKAudit ReadbackCK2Audit
open TypedModelCovXAudit TypedModelCovZMeasureAudit TypedModelCovPAudit TypedModelCovQAudit

def covRIdentitySyntax (E : ResolvedEnv) : CovRSyntax E :=
  .allSort .zero (.arrow (.var 0) (.var 0))

theorem covRIdentitySyntax_native (E : ResolvedEnv) (σ : Nat → Expr Nat) :
    covRNative (covRIdentitySyntax E) σ = cexPolyIdTy := rfl

theorem covRIdentitySyntax_wellFormed (E : ResolvedEnv) :
    CovRTemplateWellFormed (covRIdentitySyntax E) :=
  ⟨True.intro, True.intro, True.intro⟩

def covRIdentityRelation (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : CovRRel :=
  covRInterpret E n Γ (covRIdentitySyntax E) (fun _ => false) (covRBaseVal E)

theorem covRIdentity_isCandidate (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CandidateCov E (WhStepCK2 E n) Γ false (covRIdentityRelation E n Γ) :=
  covRInterpret_isCandidate E n Γ (covRIdentitySyntax E) (fun _ => false)
    (covRBaseVal E) (covRBaseVal_valid E n Γ)

/-- The landed polymorphic lambda's non-bottom compact is also admitted
by this same lexical interpretation, using actual beta readbacks. -/
theorem covR_lambdaIdentity_realization (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    covRIdentityRelation E n Γ cexPolyId cexPolyId polyIdCpt0 :=
  covROpaqueArrow_cexPolyId E n Γ

theorem covR_lambdaIdentity_joint (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CovRJoint E n Γ (covRIdentitySyntax E) (fun _ => false) (covRBaseVal E)
      cexPolyId cexPolyId polyIdCpt0 :=
  covRJoint_of_related E n Γ _ _ _ (covRBaseVal_valid E n Γ)
    (covR_lambdaIdentity_realization E n Γ)

theorem covR_lambdaIdentity_control (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] cexPolyId cexPolyIdTy) ∧
    Nonempty (ConvT emptyEnv n [] cexPolyId cexPolyId cexPolyIdTy) ∧
    ApproxTK emptyEnv n [] EnvT.bot cexPolyId polyIdCpt0 ∧ polyIdCpt0 ≠ .bot ∧
    CovRJoint emptyEnv n [] (covRIdentitySyntax emptyEnv) (fun _ => false)
      (covRBaseVal emptyEnv) cexPolyId cexPolyId polyIdCpt0 := by
  obtain ⟨hE, hΓ, ht, hc, ho, _, hnb, _⟩ := covROpaqueArrow_cexPolyId_control n EnvT.bot
  exact ⟨hE, hΓ, ht, hc, ho, hnb, covR_lambdaIdentity_joint emptyEnv n []⟩

/-- This single witness has no depth or code argument. -/
theorem covR_rigidIdentity_realization (n : Nat) (Γ : LCtx) :
    covRIdentityRelation covZRigidIdEnv n Γ
      (.const 0 []) (.const 0 []) (.spine 0 []) :=
  (covRIdentity_isCandidate covZRigidIdEnv n Γ).neutral rfl _ _ 0 []
    covPIdentity_neutral_head

/-- Eliminate the fixed head witness at any actual Sort-1 type and any
candidate at that type. The candidate remains opaque in the body. -/
theorem covR_rigidIdentity_instance (n : Nat) (Γ : LCtx)
    (T : Expr Nat) (hT : HasTyT covZRigidIdEnv n Γ T (.sort (.succ .zero)))
    (S : CovRRel) (hS : CandidateCov covZRigidIdEnv
      (WhStepCK2 covZRigidIdEnv n) Γ false S) :
    covROpaqueArrow covZRigidIdEnv n Γ false T S S
      (.app (.const 0 []) T) (.app (.const 0 []) T) (.spine 0 [.bot]) := by
  exact covRForall_apply (ds := []) (covR_rigidIdentity_realization n Γ)
    (AppCptT.appSpine (.bot _ _)) T hT S hS

/-- Each Prop-domain binder is interpreted as a sort binder. The body is
closed, so no valuation entry needs to be unfolded. -/
def covRTowerSyntax (E : ResolvedEnv) : Nat → CovRSyntax E
  | 0 => .prop
  | j + 1 => .allProp (covRTowerSyntax E j)

theorem covRTowerSyntax_tag (E : ResolvedEnv) (j : Nat) (sig : Nat → Bool) :
    covRTag (covRTowerSyntax E j) sig = false := by
  induction j generalizing sig with
  | zero => rfl
  | succ j ih => exact ih _

theorem covRTowerSyntax_native (E : ResolvedEnv) (j : Nat) (σ : Nat → Expr Nat) :
    covRNative (covRTowerSyntax E j) σ = covQArrowTower j := by
  induction j generalizing σ with
  | zero => rfl
  | succ j ih =>
      simp only [covRTowerSyntax, covRNative, covQArrowTower, ih]

theorem covRTowerSyntax_wellFormed (E : ResolvedEnv) (j : Nat) :
    CovRTemplateWellFormed (covRTowerSyntax E j) := by
  induction j with
  | zero => trivial
  | succ j ih => exact ih

def covRTowerRelation (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (j : Nat) : CovRRel :=
  covRInterpret E n Γ (covRTowerSyntax E j) (fun _ => false) (covRBaseVal E)

theorem covRTower_isCandidate (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (j : Nat) :
    CandidateCov E (WhStepCK2 E n) Γ false (covRTowerRelation E n Γ j) := by
  simpa only [covRTowerRelation, covRTowerSyntax_tag] using
    covRInterpret_isCandidate E n Γ (covRTowerSyntax E j) (fun _ => false)
      (covRBaseVal E) (covRBaseVal_valid E n Γ)

/-- The actual second application consumes the supplied tower candidate.
This proof goes through the one polymorphic head witness and both explicit
compact actions, rather than asserting unrelated pointwise reflection. -/
theorem covR_identity_tower_realization (n j : Nat) (Γ : LCtx) :
    covRTowerRelation covZRigidIdEnv n Γ j
      (covQIdentityTowerApp j) (covQIdentityTowerApp j) (.spine 0 [.bot, .bot]) := by
  have hfirst := covR_rigidIdentity_instance n Γ (covQArrowTower j)
    (covQArrowTower_hasTy covZRigidIdEnv n j Γ)
    (covRTowerRelation covZRigidIdEnv n Γ j)
    (covRTower_isCandidate covZRigidIdEnv n Γ j)
  have hw := covQArrowTowerWitness_hasTy covZRigidIdEnv n j Γ
  exact covROpaqueArrow_apply (ds := []) hfirst (AppCptT.appSpine (.bot _ _))
    (covQArrowTowerWitness j) (covQArrowTowerWitness j) hw hw
    ⟨.refl _ _ _ hw⟩ (fun u hu => (List.not_mem_nil u hu).elim)

theorem covR_identity_tower_joint (n j : Nat) (Γ : LCtx) :
    CovRJoint covZRigidIdEnv n Γ (covRTowerSyntax covZRigidIdEnv j)
      (fun _ => false) (covRBaseVal covZRigidIdEnv)
      (covQIdentityTowerApp j) (covQIdentityTowerApp j) (.spine 0 [.bot, .bot]) :=
  covRJoint_of_related _ n Γ _ _ _ (covRBaseVal_valid _ n Γ)
    (covR_identity_tower_realization n j Γ)

theorem covR_identity_native_view (n : Nat) (Γ : LCtx) :
    CovRNativeView covZRigidIdEnv n Γ cexPolyIdTy
      (covRIdentitySyntax covZRigidIdEnv) (covRBaseVal covZRigidIdEnv) :=
  ⟨covRIdentitySyntax_wellFormed _, .refl _,
    normalR_piCK2 Γ (.sort (.succ .zero)) (.pi (.bvar 0) (.bvar 1))⟩

theorem covR_tower_native_view (E : ResolvedEnv) (n j : Nat) (Γ : LCtx) :
    CovRNativeView E n Γ (covQArrowTower j) (covRTowerSyntax E j) (covRBaseVal E) := by
  refine ⟨covRTowerSyntax_wellFormed E j, ?_, ?_⟩
  · rw [covRTowerSyntax_native]
    exact .refl _
  · rw [covRTowerSyntax_native]
    cases j with
    | zero => exact normalR_sortCK2 Γ .zero
    | succ j => exact normalR_piCK2 Γ (.sort .zero) (covQArrowTower j)

/-- One head realization, with positive fresh joints for every finite
instance. All native, context and non-bottom observation premises are
supplied independently of the old hereditary and CoreY fields. -/
theorem covR_identity_uniform_control (n : Nat) :
    Nonempty (EnvWfT covZRigidIdEnv) ∧ Nonempty (CtxWfT covZRigidIdEnv n []) ∧
    Nonempty (HasTyT covZRigidIdEnv n [] (.const 0 []) cexPolyIdTy) ∧
    ApproxTK covZRigidIdEnv n [] EnvT.bot (.const 0 []) (.spine 0 []) ∧
    (CptT.spine 0 []) ≠ .bot ∧
    CovRNativeView covZRigidIdEnv n [] cexPolyIdTy
      (covRIdentitySyntax covZRigidIdEnv) (covRBaseVal covZRigidIdEnv) ∧
    covRIdentityRelation covZRigidIdEnv n [] (.const 0 []) (.const 0 []) (.spine 0 []) ∧
    ∀ j, Nonempty (HasTyT covZRigidIdEnv n [] (covQIdentityTowerApp j) (covQArrowTower j)) ∧
      Nonempty (ConvT covZRigidIdEnv n [] (covQIdentityTowerApp j)
        (covQIdentityTowerApp j) (covQArrowTower j)) ∧
      ApproxTK covZRigidIdEnv n [] EnvT.bot (covQIdentityTowerApp j) (.spine 0 [.bot, .bot]) ∧
      (CptT.spine 0 [.bot, .bot]) ≠ .bot ∧
      CovRNativeView covZRigidIdEnv n [] (covQArrowTower j)
        (covRTowerSyntax covZRigidIdEnv j) (covRBaseVal covZRigidIdEnv) ∧
      CandidateCov covZRigidIdEnv (WhStepCK2 covZRigidIdEnv n) [] false
        (covRTowerRelation covZRigidIdEnv n [] j) ∧
      CovRJoint covZRigidIdEnv n [] (covRTowerSyntax covZRigidIdEnv j)
        (fun _ => false) (covRBaseVal covZRigidIdEnv)
        (covQIdentityTowerApp j) (covQIdentityTowerApp j) (.spine 0 [.bot, .bot]) := by
  refine ⟨⟨covZRigidIdEnvWfT⟩, ⟨.nil⟩, ⟨covZRigidIdHead_hasTy n []⟩,
    covZRigidIdHead_observed n [] EnvT.bot, CptT.noConfusion,
    covR_identity_native_view n [], covR_rigidIdentity_realization n [], ?_⟩
  intro j
  obtain ⟨ht⟩ := covQIdentityTowerApp_hasTy n j []
  exact ⟨⟨ht⟩, ⟨.refl _ _ _ ht⟩, covQIdentityTowerApp_observed n j [] EnvT.bot,
    CptT.noConfusion, covR_tower_native_view _ n j [],
    covRTower_isCandidate _ n [] j, covR_identity_tower_joint n j []⟩

/-- The exact former universe-joint gap has a fresh result witness. -/
theorem covR_identity_universe_joint (n : Nat) :
    CovRJoint covZRigidIdEnv n [] .prop (fun _ => false) (covRBaseVal covZRigidIdEnv)
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp)
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp) (.spine 0 [.bot, .bot]) :=
  covR_identity_tower_joint n 0 []

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_R_IDENTITY_ROOTS
#print axioms covRIdentitySyntax
#print axioms covRIdentitySyntax_native
#print axioms covRIdentitySyntax_wellFormed
#print axioms covRIdentityRelation
#print axioms covRIdentity_isCandidate
#print axioms covR_lambdaIdentity_realization
#print axioms covR_lambdaIdentity_joint
#print axioms covR_lambdaIdentity_control
#print axioms covR_rigidIdentity_realization
#print axioms covR_rigidIdentity_instance
#print axioms covRTowerSyntax
#print axioms covRTowerSyntax_tag
#print axioms covRTowerSyntax_native
#print axioms covRTowerSyntax_wellFormed
#print axioms covRTowerRelation
#print axioms covRTower_isCandidate
#print axioms covR_identity_tower_realization
#print axioms covR_identity_tower_joint
#print axioms covR_identity_native_view
#print axioms covR_tower_native_view
#print axioms covR_identity_uniform_control
#print axioms covR_identity_universe_joint
-- END RCIC_NATIVE_TYPED_MODEL_COV_R_IDENTITY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRAudit

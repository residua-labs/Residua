import rcic.RcicNativeTypedModelCovQReindex
import rcic.RcicNativeTypedModelCovQUniverse
import rcic.RcicNativeTypedModelCovPFixtures
import rcic.RcicNativeTypedModelCovPWall4

/-!
# Eight retained fixtures for instance-first hereditary realization

The original native, observation, substitution and CoreY certificates are
retained literally. Both additional hereditary conjuncts use `CTyCovQ` and
the weaker instance-first `HereditaryCovRealizationQAt`. Their transport
uses the actual CoreY demand payload to recover old demand typing; no
unconditional reverse typing law is assumed for universe reflection.

These are measurements of a relaxation, not a replacement CoreY relation
or a claim of full hereditary P transport. Nat coverage is separately
transported at its unchanged rigid domain code. The actual rigid identity
still has no code even for the weaker target. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovQAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit TypedModelKControlAudit TypedModelKTypedBetaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit TypedModelCovNormEscapeAudit
open TypedModelCovXAudit TypedModelCovXEtaAudit TypedModelCovYAudit
open TypedModelCovYEtaAudit TypedModelCovYPolyPropAudit TypedModelCovZAudit
open TypedModelCovZMeasureAudit TypedModelCovPAudit

variable {E : ResolvedEnv}

/-- The frozen relation and the two relaxed hereditary interpretations are
explicitly separate conjuncts. No repaired CoreY package is asserted. -/
def CovQJointAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ ρ' : EnvT) (x y A : Expr Nat) (c b : CptT) : Prop :=
  LRSCoreCovY (C2 E) (WhStepCK2 E n) n Γ x y A c b ∧
  HereditaryCovRealizationQAt (CTyCovQ E)
    (LRSCoreCovY (C2 E) (WhStepCK2 E n) n)
    (ctxModelT_approxTK E n) (WhStepCK2 E n) n Γ ρ A c b ∧
  HereditaryCovRealizationQAt (CTyCovQ E)
    (LRSCoreCovY (C2 E) (WhStepCK2 E n) n)
    (ctxModelT_approxTK E n) (WhStepCK2 E n) n Γ ρ' A c b

/-- Actual related demands carry old C2 typing. This supplies the backward
premise needed by the generic relaxation theorem, including Prop domains. -/
theorem covQ_hereditary_from_P {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {A : Expr Nat} {c b : CptT}
    (h : HereditaryCovRealizationPAt (CTyCovP2 true E)
      (LRSCoreCovY (C2 E) (WhStepCK2 E n) n)
      (ctxModelT_approxTK E n) (WhStepCK2 E n) n Γ ρ A c b) :
    HereditaryCovRealizationQAt (CTyCovQ E)
      (LRSCoreCovY (C2 E) (WhStepCK2 E n) n)
      (ctxModelT_approxTK E n) (WhStepCK2 E n) n Γ ρ A c b :=
  hereditaryCovRealizationQAt_from_P (CTyCovP2 true E) (CTyCovQ E)
    (LRSCoreCovY (C2 E) (WhStepCK2 E n) n)
    (fun _ _ ht => ctyCovQ_of_P ht)
    (fun _ _ _ _ u d _ hr =>
      ctyCovP2_of_ctyCov2 true u d (lrSCoreCovY_typing (C2 E) hr))
    (ctxModelT_approxTK E n) (WhStepCK2 E n) n Γ ρ A c b h

theorem covQ_joint_of_P {n : Nat} {Γ : LCtx} {ρ ρ' : EnvT}
    {x y A : Expr Nat} {c b : CptT}
    (h : CovPJointAt true E n Γ ρ ρ' x y A c b) :
    CovQJointAt E n Γ ρ ρ' x y A c b :=
  ⟨h.1, covQ_hereditary_from_P h.2.1, covQ_hereditary_from_P h.2.2⟩

/-- Retain every inhabited premise of the original fixture, then exhibit
both additional hereditary witnesses for the weakened Q target. -/
def CovQFixtureAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvT) (x y A : Expr Nat) (c b : CptT) : Prop :=
  CovZInhabitedJointAt E n Γ ρ x y A c b ∧
  CovQJointAt E n Γ ρ ρ x y A c b

theorem covQ_fixture_of_P {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {x y A : Expr Nat} {c b : CptT}
    (h : CovPFixtureAt true E n Γ ρ x y A c b) :
    CovQFixtureAt E n Γ ρ x y A c b :=
  ⟨h.1, covQ_joint_of_P h.2⟩

theorem covQ_fixture_natSucc_eta (n : Nat) :
    CovQFixtureAt natEnvU n [] EnvT.bot
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      covXNatEtaEmptyRow covYNatArrowCode :=
  covQ_fixture_of_P (covP_fixture_natSucc_eta true n)

theorem covQ_fixture_alias_in_pi (n : Nat) :
    ∃ A B, CovQFixtureAt eqEnvT n eqGapCtx EnvT.bot
      covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
      covNormAliasIdentityCpt covYAliasPiCode := by
  obtain ⟨A, B, h⟩ := covP_fixture_alias_in_pi true n
  exact ⟨A, B, covQ_fixture_of_P h⟩

theorem covQ_fixture_polyPropLam (n : Nat) :
    CovQFixtureAt eqEnvT n [] EnvT.bot
      covXPolyPropLam covXPolyPropLam covXPolyPropLamTy
      (.lam [([], .prop)]) covYPolyPropCode :=
  covQ_fixture_of_P (covP_fixture_polyPropLam true n)

theorem covQ_fixture_alias_extension (n : Nat) :
    ∃ A B,
      RelSubstAtCovY (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
        n eqGapCtx (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (SubstT.cons idPiProp SubstT.id) (SubstT.cons idPiProp SubstT.id)
        (.assumption (eqGapDirectAlias A B) :: eqGapCtx) ∧
      CovQFixtureAt eqEnvT n eqGapCtx EnvT.bot idPiProp idPiProp
        (eqGapDirectAlias A B) (.pi .bot []) .prop := by
  obtain ⟨A, B, hs, h⟩ := covP_fixture_alias_extension true n
  exact ⟨A, B, hs, covQ_fixture_of_P h⟩

/-- The two Nat boundary cases retain a Pi-shaped code and actual coverage
under Q typing. The domain is a rigid code, so universe reflection adds
no new domain demands here. -/
theorem covQ_fixture_nat_coverage_shape (n : Nat) :
    (∃ d g, covYNatArrowCode = .pi d g) ∧
    CovPActionCoverage natEnvU (CTyCovQ natEnvU) (.spine 2 [])
      (.spine 0 []) [([], .spine 0 [])] ∧
    CovQFixtureAt natEnvU n [] EnvT.bot
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covYNatArrowCode := by
  obtain ⟨hs, hc, hj⟩ := covP_fixture_nat_coverage_shape true n
  refine ⟨hs, ?_, covQ_fixture_of_P hj⟩
  intro ds out ha hd
  have hdP : ∀ u ∈ ds, CTyCovP2 true natEnvU u (.spine 0 []) := by
    intro u hu
    exact (ctyCovQ_nonprop_iff (fun he => CptT.noConfusion he)).mp (hd u hu)
  rcases hc ds out ha hdP with hb | ⟨row, hr, hsel⟩
  · exact Or.inl hb
  · exact Or.inr ⟨row, hr, hsel.1, ctyCovQ_of_P hsel.2⟩

theorem covQ_fixture_eq_anchor (n : Nat) :
    CovQFixtureAt eqEnvT n eqGapCtx EnvT.bot idPiProp idPiProp
      (.sort .zero) (.pi .bot []) .prop :=
  covQ_fixture_of_P (covP_fixture_eq_anchor true n)

theorem covQ_fixture_nat_anchor (n : Nat) :
    CovQFixtureAt natEnvU n [] EnvT.bot
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) (.spine 0 []) :=
  covQ_fixture_of_P (covP_fixture_nat_anchor true n)

/-- The generic relevant-function alias pattern can be specialized by the
separate exact #7776 replay. Its old relation and both new Q witnesses are
supplied by composition, without an unconditional reverse typing premise. -/
theorem covQ_relevant_app_joint (hW : EnvWfT E) (n : Nat)
    {Γ : LCtx} (ρ ρ' : EnvT) {D Q : Expr Nat}
    (hr : RedR (WhStepCK2 E n) Γ D (.pi (.sort .zero) (.sort .zero)))
    (hQ : HasTyT E n Γ Q (.sort .zero)) :
    CovQJointAt E n Γ ρ ρ'
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.pi D (.sort .zero))
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])]) covZRelevantAppCode :=
  covQ_joint_of_P (covP_relevant_app_joint true hW n ρ ρ' hr hQ)

/-- All native and baseline relation premises are inherited actual
inhabitants. Universe reflection does not supply a finite code for the
polymorphic rigid head, even after instance-first row selection. -/
theorem covQ_rigidId_control (n : Nat) :
    Nonempty (HasTyT emptyEnv n [] cexPolyId cexPolyIdTy) ∧
    Nonempty (EnvWfT covZRigidIdEnv) ∧
    Nonempty (CtxWfT covZRigidIdEnv n []) ∧
    Nonempty (HasTyT covZRigidIdEnv n [] (.const 0 []) cexPolyIdTy) ∧
    Nonempty (ConvT covZRigidIdEnv n [] (.const 0 []) (.const 0 []) cexPolyIdTy) ∧
    ApproxTK covZRigidIdEnv n [] EnvT.bot (.const 0 []) (.spine 0 []) ∧
    LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n []
      (.const 0 []) (.const 0 []) cexPolyIdTy (.spine 0 []) .sort ∧
    (CptT.spine 0 []) ≠ .bot ∧
    (¬ ∃ b, HereditaryCovRealizationPAt (CTyCovQ covZRigidIdEnv)
      (LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n)
      (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
      [] EnvT.bot cexPolyIdTy (.spine 0 []) b) ∧
    ¬ ∃ b, HereditaryCovRealizationQAt (CTyCovQ covZRigidIdEnv)
      (LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n)
      (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
      [] EnvT.bot cexPolyIdTy (.spine 0 []) b := by
  obtain ⟨hi, hE, hΓ, ht, heq, ho, hc, hnb, hP⟩ :=
    covP_rigidId_control (CTyCovQ covZRigidIdEnv)
      (LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n)
      ctyCovQ_bot_inv n
  refine ⟨hi, hE, hΓ, ht, heq, ho, hc, hnb, hP, ?_⟩
  rintro ⟨b, hb⟩
  exact covQ_instance_first_identity_no_code ctyCovQ_bot_inv n [] EnvT.bot 0 [] b hb

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Q_FIXTURES_ROOTS
#print axioms CovQJointAt
#print axioms covQ_hereditary_from_P
#print axioms covQ_joint_of_P
#print axioms CovQFixtureAt
#print axioms covQ_fixture_of_P
#print axioms covQ_fixture_natSucc_eta
#print axioms covQ_fixture_alias_in_pi
#print axioms covQ_fixture_polyPropLam
#print axioms covQ_fixture_alias_extension
#print axioms covQ_fixture_nat_coverage_shape
#print axioms covQ_fixture_eq_anchor
#print axioms covQ_fixture_nat_anchor
#print axioms covQ_relevant_app_joint
#print axioms covQ_rigidId_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Q_FIXTURES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovQAudit

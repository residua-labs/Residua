import rcic.RcicNativeTypedModelCovWEtaInverseBoundary
import rcic.RcicNativeTypedModelCovWTypedBetaBoundary

/-!
# An inhabited native irrelevance boundary in the old eta grammar

Extend the admitted `P, p : P` environment by object-language axioms
`F : P -> Prop` at reference 5 and `q : P` at reference 8. The existing
proof `p : P` is reference 4. Native `ConvT.irr` followed
by application congruence relates the two head-normal proposition terms
`F p` and `F q`, without using beta conversion.

The unchanged `ApproxTKWEta` grammar observes the nonbottom compact
`spine 5 [spine 4 []]` at `F p`. Its complete finite-derivation cleanliness
invariant, including recursive eta, excludes that compact at `F q`.
Every admission, native typing, finite typed valuation, realizer, observed
result type, and strict top-level demand is inhabited explicitly.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelKGuardAudit
open TypedModelAudit.TypingFin
open TypedModelCovUAudit TypedModelCovVAudit TypedModelCovTAudit TypedModelCovWAudit
open TypedModelCovWTypedAudit TypedModelCovWEtaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- This is an object-language member, admitted by `EnvWfT.axiom`. -/
def covWIrrelQMember : CheckedMember := ⟨.axiomM, 0, covUProjP, none⟩

/-- The family is an admitted axiom; this fixture needs no indexed group. -/
def covWIrrelFamilyMember : CheckedMember :=
  ⟨.axiomM, 0, .pi covUProjP (.sort .zero), none⟩

def covWIrrelFamilyEnv : ResolvedEnv :=
  extendEnv covUProjEnv 5 covWIrrelFamilyMember

def covWIrrelEnv : ResolvedEnv := extendEnv covWIrrelFamilyEnv 8 covWIrrelQMember

def covWIrrelProp : Expr Nat := covUProjP
def covWIrrelP : Expr Nat := covUProjProof
def covWIrrelQ : Expr Nat := .const 8 []
def covWIrrelFamily : Expr Nat := .const 5 []
def covWIrrelFamilyType : Expr Nat := .pi covWIrrelProp (.sort .zero)
def covWIrrelLeft : Expr Nat := .app covWIrrelFamily covWIrrelP
def covWIrrelRight : Expr Nat := .app covWIrrelFamily covWIrrelQ
def covWIrrelFine : CptT := .spine 5 [.spine 4 []]
def covWIrrelOtherFine : CptT := .spine 5 [.spine 8 []]

def covWIrrelFamilyEnv_wf : EnvWfT covWIrrelFamilyEnv :=
  .axiom covUProjEnv 5 (.pi covUProjP (.sort .zero))
    (.imax .zero (.succ .zero)) covUProjEnvWfT rfl
    (.pi _ _ _ _ _ (covUProjP_ty 0 []) (.sort _ _)) (fun _ => rfl) rfl

def covWIrrelEnv_wf : EnvWfT covWIrrelEnv :=
  .axiom covWIrrelFamilyEnv 8 covUProjP .zero covWIrrelFamilyEnv_wf rfl
    (.const [] 3 [] covUProjPMember rfl rfl rfl) (fun _ => rfl) rfl

def covWIrrel_prop_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWIrrelEnv n Γ covWIrrelProp (.sort .zero) :=
  .const Γ 3 [] covUProjPMember rfl rfl rfl

def covWIrrel_p_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWIrrelEnv n Γ covWIrrelP covWIrrelProp :=
  .const Γ 4 [] covUProjProofMember rfl rfl rfl

def covWIrrel_q_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWIrrelEnv n Γ covWIrrelQ covWIrrelProp :=
  .const Γ 8 [] covWIrrelQMember rfl rfl rfl

def covWIrrel_family_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWIrrelEnv n Γ covWIrrelFamily covWIrrelFamilyType :=
  .const Γ 5 [] covWIrrelFamilyMember rfl rfl rfl

def covWIrrel_left_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWIrrelEnv n Γ covWIrrelLeft (.sort .zero) :=
  .app Γ covWIrrelFamily covWIrrelP covWIrrelProp (.sort .zero)
    (covWIrrel_family_ty n Γ) (covWIrrel_p_ty n Γ)

def covWIrrel_right_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWIrrelEnv n Γ covWIrrelRight (.sort .zero) :=
  .app Γ covWIrrelFamily covWIrrelQ covWIrrelProp (.sort .zero)
    (covWIrrel_family_ty n Γ) (covWIrrel_q_ty n Γ)

/-- The proof equality is an actual native irrelevance derivation. -/
def covWIrrel_pq_conv (n : Nat) (Γ : LCtx) :
    ConvT covWIrrelEnv n Γ covWIrrelP covWIrrelQ covWIrrelProp :=
  .irr Γ covWIrrelProp covWIrrelP covWIrrelQ
    (covWIrrel_prop_ty n Γ) (covWIrrel_p_ty n Γ) (covWIrrel_q_ty n Γ)

/-- Congruence transports native irrelevance through the admitted family. -/
def covWIrrel_family_conv (n : Nat) (Γ : LCtx) :
    ConvT covWIrrelEnv n Γ covWIrrelLeft covWIrrelRight (.sort .zero) :=
  .app Γ covWIrrelFamily covWIrrelFamily covWIrrelP covWIrrelQ
    covWIrrelProp (.sort .zero)
    (.refl Γ covWIrrelFamily covWIrrelFamilyType (covWIrrel_family_ty n Γ))
    (covWIrrel_pq_conv n Γ)

def covWIrrel_family_conv_rev (n : Nat) (Γ : LCtx) :
    ConvT covWIrrelEnv n Γ covWIrrelRight covWIrrelLeft (.sort .zero) :=
  .symm Γ covWIrrelLeft covWIrrelRight (.sort .zero) (covWIrrel_family_conv n Γ)

theorem covWIrrel_prop_rigid : RigidConst covWIrrelEnv 3 := by
  intro m hm
  have he : m = covUProjPMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

theorem covWIrrel_p_rigid : RigidConst covWIrrelEnv 4 := by
  intro m hm
  have he : m = covUProjProofMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

theorem covWIrrel_q_rigid : RigidConst covWIrrelEnv 8 := by
  intro m hm
  have he : m = covWIrrelQMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

theorem covWIrrel_family_rigid : RigidConst covWIrrelEnv 5 := by
  intro m hm
  have he : m = covWIrrelFamilyMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

theorem covWIrrel_prop_not_propCtor : ¬ PropCtorT covWIrrelEnv 3 := by
  rintro ⟨m, fam, fm, hm, hk, _⟩
  have he : m = covUProjPMember := Option.some.inj hm.symm
  subst m
  cases hk

theorem covWIrrel_p_not_propCtor : ¬ PropCtorT covWIrrelEnv 4 := by
  rintro ⟨m, fam, fm, hm, hk, _⟩
  have he : m = covUProjProofMember := Option.some.inj hm.symm
  subst m
  cases hk

theorem covWIrrel_q_not_propCtor : ¬ PropCtorT covWIrrelEnv 8 := by
  rintro ⟨m, fam, fm, hm, hk, _⟩
  have he : m = covWIrrelQMember := Option.some.inj hm.symm
  subst m
  cases hk

theorem covWIrrel_family_not_propCtor : ¬ PropCtorT covWIrrelEnv 5 := by
  rintro ⟨m, fam, fm, hm, hk, _⟩
  have he : m = covWIrrelFamilyMember := Option.some.inj hm.symm
  subst m
  cases hk

theorem covWIrrel_prop_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covWIrrelEnv n Γ ρ covWIrrelProp (.spine 3 []) :=
  .free (kFreeT_rigid_const covWIrrel_prop_rigid [])
    (.const ρ 3 [] covWIrrel_prop_rigid covWIrrel_prop_not_propCtor)

theorem covWIrrel_p_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covWIrrelEnv n Γ ρ covWIrrelP (.spine 4 []) :=
  .free (kFreeT_rigid_const covWIrrel_p_rigid [])
    (.const ρ 4 [] covWIrrel_p_rigid covWIrrel_p_not_propCtor)

theorem covWIrrel_q_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covWIrrelEnv n Γ ρ covWIrrelQ (.spine 8 []) :=
  .free (kFreeT_rigid_const covWIrrel_q_rigid [])
    (.const ρ 8 [] covWIrrel_q_rigid covWIrrel_q_not_propCtor)

theorem covWIrrel_family_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covWIrrelEnv n Γ ρ covWIrrelFamily (.spine 5 []) :=
  .free (kFreeT_rigid_const covWIrrel_family_rigid [])
    (.const ρ 5 [] covWIrrel_family_rigid covWIrrel_family_not_propCtor)

theorem covWIrrel_left_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covWIrrelEnv n Γ ρ covWIrrelLeft covWIrrelFine :=
  .appSpine (covWIrrel_family_observed n Γ ρ) (covWIrrel_p_observed n Γ ρ)

/-- The right term has its own nonbottom fine observation. -/
theorem covWIrrel_right_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covWIrrelEnv n Γ ρ covWIrrelRight covWIrrelOtherFine :=
  .appSpine (covWIrrel_family_observed n Γ ρ) (covWIrrel_q_observed n Γ ρ)

theorem covWIrrel_result_type_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta covWIrrelEnv n Γ ρ (.sort .zero) .prop :=
  .free (kFreeT_sort covWIrrelEnv .zero) (.sort ρ .zero)

theorem covWIrrel_fine_typed : CTyS covWIrrelEnv covWIrrelFine .prop := by
  rw [CTyS]
  exact Or.inr (.spine (m := covWIrrelFamilyMember) rfl rfl)

theorem covWIrrel_fine_nonbottom : covWIrrelFine ≠ .bot :=
  fun h => CptT.noConfusion h

theorem covWIrrel_other_fine_typed : CTyS covWIrrelEnv covWIrrelOtherFine .prop := by
  rw [CTyS]
  exact Or.inr (.spine (m := covWIrrelFamilyMember) rfl rfl)

theorem covWIrrel_other_fine_nonbottom : covWIrrelOtherFine ≠ .bot :=
  fun h => CptT.noConfusion h

/-- `F q` is in the rigid fragment excluding reference 4. -/
theorem covWIrrel_right_rigid : CovWEtaRigidTerm covWIrrelEnv covWIrrelRight :=
  .app (.const 5 [] covWIrrel_family_rigid (by decide))
    (.const 8 [] covWIrrel_q_rigid (by decide))

/-- This applies to every old derivation, including arbitrary eta alternatives. -/
theorem covWIrrel_right_clean {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTKWEta covWIrrelEnv n Γ ρ covWIrrelRight c)
    (hρ : CovWEtaCleanEnv ρ) : CovWEtaClean c :=
  covWEta_observation_clean h covWIrrel_right_rigid hρ

theorem covWIrrel_fine_not_clean : ¬ CovWEtaClean covWIrrelFine :=
  covWEtaInv_compact_not_clean

theorem covWIrrel_right_fine_absent (n : Nat) (Γ : LCtx) :
    ¬ ApproxTKWEta covWIrrelEnv n Γ EnvT.bot covWIrrelRight covWIrrelFine :=
  fun h => covWIrrel_fine_not_clean (covWIrrel_right_clean h covWEta_cleanEnv_bot)

/-- Both endpoints already have native normal heads; no beta step is involved. -/
theorem covWIrrel_endpoints_normal (n : Nat) (Γ : LCtx) :
    NormalR (WhStepCK2 covWIrrelEnv n) Γ covWIrrelLeft ∧
    NormalR (WhStepCK2 covWIrrelEnv n) Γ covWIrrelRight :=
  ⟨covV_body_free_spine_normal
      (rfl : covWIrrelEnv.members 5 = some covWIrrelFamilyMember) rfl (by decide)
      [] [covWIrrelP],
    covV_body_free_spine_normal
      (rfl : covWIrrelEnv.members 5 = some covWIrrelFamilyMember) rfl (by decide)
      [] [covWIrrelQ]⟩

theorem covWIrrel_kFree :
    KFreeT covWIrrelEnv covWIrrelLeft ∧ KFreeT covWIrrelEnv covWIrrelRight :=
  ⟨kFreeT_app (kFreeT_rigid_const covWIrrel_family_rigid [])
      (kFreeT_rigid_const covWIrrel_p_rigid []),
    kFreeT_app (kFreeT_rigid_const covWIrrel_family_rigid [])
      (kFreeT_rigid_const covWIrrel_q_rigid [])⟩

theorem covWIrrel_no_rec_occurrence :
    occursConst 2 covWIrrelLeft = false ∧ occursConst 7 covWIrrelLeft = false ∧
    occursConst 2 covWIrrelRight = false ∧ occursConst 7 covWIrrelRight = false := by
  decide

theorem covWIrrel_old_observations_differ (n : Nat) :
    ¬ (∀ c, ApproxTKWEta covWIrrelEnv n [] EnvT.bot covWIrrelLeft c ↔
      ApproxTKWEta covWIrrelEnv n [] EnvT.bot covWIrrelRight c) := by
  intro h
  exact covWIrrel_right_fine_absent n []
    ((h covWIrrelFine).mp (covWIrrel_left_observed n [] EnvT.bot))

/-- All native and semantic premises of the closed irrelevance failure. -/
structure CovWIrrelOldFailureAt (n : Nat) : Prop where
  envWf : Nonempty (EnvWfT covWIrrelEnv)
  ctxWf : Nonempty (CtxWfT covWIrrelEnv n [])
  realized : CovWEtaRealized covWIrrelEnv n 2 [] EnvT.bot SubstT.id
  valuation : EnvTypedFinAtT
    (⟨ApproxTKWEta covWIrrelEnv n []⟩ : CtxModelT covWIrrelEnv) [] EnvT.bot
  coherence : CtxEnvM
    (⟨ApproxTKWEta covWIrrelEnv n []⟩ : CtxModelT covWIrrelEnv) [] EnvT.bot
  propTy : Nonempty (HasTyT covWIrrelEnv n [] covWIrrelProp (.sort .zero))
  pTy : Nonempty (HasTyT covWIrrelEnv n [] covWIrrelP covWIrrelProp)
  qTy : Nonempty (HasTyT covWIrrelEnv n [] covWIrrelQ covWIrrelProp)
  familyTy : Nonempty (HasTyT covWIrrelEnv n [] covWIrrelFamily covWIrrelFamilyType)
  leftTy : Nonempty (HasTyT covWIrrelEnv n [] covWIrrelLeft (.sort .zero))
  rightTy : Nonempty (HasTyT covWIrrelEnv n [] covWIrrelRight (.sort .zero))
  typeTy : Nonempty (HasTyT covWIrrelEnv n [] (.sort .zero) (.sort (.succ .zero)))
  proofConversion : Nonempty (ConvT covWIrrelEnv n [] covWIrrelP covWIrrelQ covWIrrelProp)
  familyConversion : Nonempty
    (ConvT covWIrrelEnv n [] covWIrrelLeft covWIrrelRight (.sort .zero))
  reverseFamilyConversion : Nonempty
    (ConvT covWIrrelEnv n [] covWIrrelRight covWIrrelLeft (.sort .zero))
  leftNormal : NormalR (WhStepCK2 covWIrrelEnv n) [] covWIrrelLeft
  rightNormal : NormalR (WhStepCK2 covWIrrelEnv n) [] covWIrrelRight
  leftKFree : KFreeT covWIrrelEnv covWIrrelLeft
  rightKFree : KFreeT covWIrrelEnv covWIrrelRight
  leftObservation : ApproxTKWEta covWIrrelEnv n [] EnvT.bot covWIrrelLeft covWIrrelFine
  rightObservation : ApproxTKWEta covWIrrelEnv n [] EnvT.bot covWIrrelRight covWIrrelOtherFine
  typeObservation : ApproxTKWEta covWIrrelEnv n [] EnvT.bot (.sort .zero) .prop
  demand : CTyS covWIrrelEnv covWIrrelFine .prop
  nonbottom : covWIrrelFine ≠ .bot
  rightNoFine : ¬ ApproxTKWEta covWIrrelEnv n [] EnvT.bot covWIrrelRight covWIrrelFine

theorem covWIrrel_old_inhabited (n : Nat) : CovWIrrelOldFailureAt n where
  envWf := ⟨covWIrrelEnv_wf⟩
  ctxWf := ⟨.nil⟩
  realized := covWEta_realized_nil _ _ _
  valuation := envTypedFinAtT_nil _ _
  coherence := fun _ _ hv => Option.noConfusion hv
  propTy := ⟨covWIrrel_prop_ty n []⟩
  pTy := ⟨covWIrrel_p_ty n []⟩
  qTy := ⟨covWIrrel_q_ty n []⟩
  familyTy := ⟨covWIrrel_family_ty n []⟩
  leftTy := ⟨covWIrrel_left_ty n []⟩
  rightTy := ⟨covWIrrel_right_ty n []⟩
  typeTy := ⟨.sort [] .zero⟩
  proofConversion := ⟨covWIrrel_pq_conv n []⟩
  familyConversion := ⟨covWIrrel_family_conv n []⟩
  reverseFamilyConversion := ⟨covWIrrel_family_conv_rev n []⟩
  leftNormal := (covWIrrel_endpoints_normal n []).1
  rightNormal := (covWIrrel_endpoints_normal n []).2
  leftKFree := covWIrrel_kFree.1
  rightKFree := covWIrrel_kFree.2
  leftObservation := covWIrrel_left_observed n [] EnvT.bot
  rightObservation := covWIrrel_right_observed n [] EnvT.bot
  typeObservation := covWIrrel_result_type_observed n [] EnvT.bot
  demand := covWIrrel_fine_typed
  nonbottom := covWIrrel_fine_nonbottom
  rightNoFine := covWIrrel_right_fine_absent n []

/-- Native conversion cannot transport all strictly typed fine observations. -/
theorem covWIrrel_old_no_conversion_transport (n : Nat) :
    ¬ covWTyped_antiReductionAt covWIrrelEnv n []
      (⟨ApproxTKWEta covWIrrelEnv n []⟩ : CtxModelT covWIrrelEnv)
      (fun e e' => Nonempty (ConvT covWIrrelEnv n [] e e' (.sort .zero))) := by
  intro h
  have hi := covWIrrel_old_inhabited n
  exact hi.rightNoFine
    (h EnvT.bot covWIrrelRight covWIrrelLeft (.sort .zero) (.succ .zero)
      covWIrrelFine .prop hi.envWf hi.ctxWf hi.valuation hi.rightTy hi.leftTy
      hi.typeTy hi.reverseFamilyConversion hi.leftObservation hi.typeObservation
      hi.demand hi.nonbottom)

/-- The fine observations, their type, and the realizer coexist at stage 2. -/
theorem covWIrrel_old_same_stage (n : Nat) :
    CovWEtaRealized covWIrrelEnv n 2 [] EnvT.bot SubstT.id ∧
    ApproxTKWEtaStage covWIrrelEnv n 2 [] EnvT.bot covWIrrelLeft covWIrrelFine ∧
    ApproxTKWEtaStage covWIrrelEnv n 2 [] EnvT.bot covWIrrelRight covWIrrelOtherFine ∧
    ApproxTKWEtaStage covWIrrelEnv n 2 [] EnvT.bot (.sort .zero) .prop := by
  refine ⟨covWEta_realized_nil _ _ _,
    ⟨covWIrrel_left_observed n [] EnvT.bot, ?_⟩,
    ⟨covWIrrel_right_observed n [] EnvT.bot, ?_⟩,
    ⟨covWIrrel_result_type_observed n [] EnvT.bot, ?_⟩⟩
  all_goals simp [covTObservationBudget, covWIrrelFine, covWIrrelOtherFine]

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_BOUNDARY_ROOTS
#print axioms covWIrrelQMember
#print axioms covWIrrelFamilyMember
#print axioms covWIrrelFamilyEnv
#print axioms covWIrrelEnv
#print axioms covWIrrelProp
#print axioms covWIrrelP
#print axioms covWIrrelQ
#print axioms covWIrrelFamily
#print axioms covWIrrelFamilyType
#print axioms covWIrrelLeft
#print axioms covWIrrelRight
#print axioms covWIrrelFine
#print axioms covWIrrelOtherFine
#print axioms covWIrrelFamilyEnv_wf
#print axioms covWIrrelEnv_wf
#print axioms covWIrrel_prop_ty
#print axioms covWIrrel_p_ty
#print axioms covWIrrel_q_ty
#print axioms covWIrrel_family_ty
#print axioms covWIrrel_left_ty
#print axioms covWIrrel_right_ty
#print axioms covWIrrel_pq_conv
#print axioms covWIrrel_family_conv
#print axioms covWIrrel_family_conv_rev
#print axioms covWIrrel_prop_rigid
#print axioms covWIrrel_p_rigid
#print axioms covWIrrel_q_rigid
#print axioms covWIrrel_family_rigid
#print axioms covWIrrel_prop_not_propCtor
#print axioms covWIrrel_p_not_propCtor
#print axioms covWIrrel_q_not_propCtor
#print axioms covWIrrel_family_not_propCtor
#print axioms covWIrrel_prop_observed
#print axioms covWIrrel_p_observed
#print axioms covWIrrel_q_observed
#print axioms covWIrrel_family_observed
#print axioms covWIrrel_left_observed
#print axioms covWIrrel_right_observed
#print axioms covWIrrel_result_type_observed
#print axioms covWIrrel_fine_typed
#print axioms covWIrrel_fine_nonbottom
#print axioms covWIrrel_other_fine_typed
#print axioms covWIrrel_other_fine_nonbottom
#print axioms covWIrrel_right_rigid
#print axioms covWIrrel_right_clean
#print axioms covWIrrel_fine_not_clean
#print axioms covWIrrel_right_fine_absent
#print axioms covWIrrel_endpoints_normal
#print axioms covWIrrel_kFree
#print axioms covWIrrel_no_rec_occurrence
#print axioms covWIrrel_old_observations_differ
#print axioms CovWIrrelOldFailureAt
#print axioms covWIrrel_old_inhabited
#print axioms covWIrrel_old_no_conversion_transport
#print axioms covWIrrel_old_same_stage
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

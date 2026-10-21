import rcic.RcicNativeTypedModelCovZMeasure
import rcic.RcicNativeTypedModelCovZNeutralBody

/-!
# An admitted rigid dependent result with no hereditary code

The native environment contains a body-free declaration `k : (A : Sort 1) → A`.
This is an object-language axiom admitted by the landed `EnvWfT.axiom` rule;
no axiom is added to Lean. Its compact observation and the existing leaf
relation are non-bottom. No finite type code realizes the dependent result
under the empty-demand binder valuation required by the frozen CovY clause.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCK2Audit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit TypedModelCovYAudit
open TypedModelCovZAudit

def covZRigidPolyTy : Expr Nat := .pi (.sort (.succ .zero)) (.bvar 0)

def covZRigidPolyMember : CheckedMember := ⟨.axiomM, 0, covZRigidPolyTy, none⟩

def covZRigidPolyEnv : ResolvedEnv := extendEnv emptyEnv 0 covZRigidPolyMember

def covZRigidPolyHead : Expr Nat := .const 0 []

def covZRigidPolyTy_hasTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ covZRigidPolyTy
      (.sort (.imax (.succ (.succ .zero)) (.succ .zero))) :=
  .pi Γ (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0) (.succ .zero)
    (.sort Γ (.succ .zero))
    (.bvar (.assumption (.sort (.succ .zero)) :: Γ) 0 (.sort (.succ .zero)) rfl)

def covZRigidPolyEnvWfT : EnvWfT covZRigidPolyEnv :=
  .axiom emptyEnv 0 covZRigidPolyTy
    (.imax (.succ (.succ .zero)) (.succ .zero)) .empty rfl
    (covZRigidPolyTy_hasTy emptyEnv 0 [])
    (by intro k; simp [covZRigidPolyTy, lift]) rfl

def covZRigidPolyHead_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT covZRigidPolyEnv n Γ covZRigidPolyHead covZRigidPolyTy := by
  simpa [covZRigidPolyHead, covZRigidPolyMember, covZRigidPolyTy,
    instantiateLevels] using
    (HasTyT.const (E := covZRigidPolyEnv) (n := n) Γ 0 []
      covZRigidPolyMember rfl rfl rfl)

theorem covZRigidPolyHead_rigid : RigidConst covZRigidPolyEnv 0 := by
  intro m hm
  have he : m = covZRigidPolyMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

theorem covZRigidPolyHead_not_propCtor : ¬ PropCtorT covZRigidPolyEnv 0 := by
  rintro ⟨m, fam, fm, hm, hctor, _⟩
  have he : m = covZRigidPolyMember := Option.some.inj hm.symm
  subst m
  exact MemberClass.noConfusion hctor

theorem covZRigidPolyHead_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK covZRigidPolyEnv n Γ ρ covZRigidPolyHead (.spine 0 []) :=
  ApproxTK.free (kFreeT_rigid_const covZRigidPolyHead_rigid [])
    (ApproxT.const ρ 0 [] covZRigidPolyHead_rigid covZRigidPolyHead_not_propCtor)

theorem covZRigidPolyHead_normal (n : Nat) (Γ : LCtx) :
    NormalR (WhStepCK2 covZRigidPolyEnv n) Γ covZRigidPolyHead := by
  intro e h
  rcases whStepCK2_ctx_or_saturated h with h | h
  · exact whStepCtx_const_opaque_false
      (rfl : covZRigidPolyEnv.members 0 = some covZRigidPolyMember) rfl [] h
  · obtain ⟨f, x, he⟩ := saturatedRecSource_is_app h
    exact Expr.noConfusion he

theorem covZRigidPolyHead_old_related (n : Nat) (Γ : LCtx) :
    LRSCoreCov (C2 covZRigidPolyEnv) (WhStepCK2 covZRigidPolyEnv n) n Γ
      covZRigidPolyHead covZRigidPolyHead covZRigidPolyTy (.spine 0 []) := by
  rw [lrSCoreCov_spine_iff]
  refine ⟨covZRigidPolyMember, [], [], [], [], rfl, .refl _, .refl _,
    covZRigidPolyHead_normal n Γ, covZRigidPolyHead_normal n Γ,
    ?_, by decide, by decide, .nil _, ?_⟩
  · trivial
  · intro _ hind
    exact MemberClass.noConfusion hind

theorem covZRigidPolyHead_related_leaf (n : Nat) (Γ : LCtx) :
    LRSCoreCovY (C2 covZRigidPolyEnv) (WhStepCK2 covZRigidPolyEnv n) n Γ
      covZRigidPolyHead covZRigidPolyHead covZRigidPolyTy (.spine 0 []) .sort := by
  apply lrSCoreCovY_of_old_leaf (C2 covZRigidPolyEnv)
    (fun _ _ h => CptT.noConfusion h)
  · change CTyCov2 covZRigidPolyEnv (.spine 0 []) .sort
    rw [CTyCov2]
    exact Or.inr (.spine 0 [])
  · exact covZRigidPolyHead_old_related n Γ

theorem not_covZRigidPoly_hereditary_any_code (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ∀ b, ¬ HereditaryCovRealizationYAt (C2 covZRigidPolyEnv)
      (ctxModelT_approxTK covZRigidPolyEnv n) (WhStepCK2 covZRigidPolyEnv n) n
      Γ ρ covZRigidPolyTy (.spine 0 []) b :=
  covZ_not_hereditary_poly_result_spine (C2 covZRigidPolyEnv) n Γ ρ 0 []

/-- All native and model premises are actual inhabitants, and the frozen
relation already relates the observed head at a leaf code. Only the stronger
joint-code realization target fails. -/
theorem covZRigidPoly_control (n : Nat) :
    Nonempty (EnvWfT covZRigidPolyEnv) ∧
    Nonempty (CtxWfT covZRigidPolyEnv n []) ∧
    Nonempty (HasTyT covZRigidPolyEnv n [] covZRigidPolyHead covZRigidPolyTy) ∧
    Nonempty (ConvT covZRigidPolyEnv n [] covZRigidPolyHead covZRigidPolyHead
      covZRigidPolyTy) ∧
    ApproxTK covZRigidPolyEnv n [] EnvT.bot covZRigidPolyHead (.spine 0 []) ∧
    LRSCoreCovY (C2 covZRigidPolyEnv) (WhStepCK2 covZRigidPolyEnv n) n []
      covZRigidPolyHead covZRigidPolyHead covZRigidPolyTy (.spine 0 []) .sort ∧
    (CptT.spine 0 []) ≠ .bot ∧
    ¬ ∃ b, HereditaryCovRealizationYAt (C2 covZRigidPolyEnv)
      (ctxModelT_approxTK covZRigidPolyEnv n) (WhStepCK2 covZRigidPolyEnv n) n
      [] EnvT.bot covZRigidPolyTy (.spine 0 []) b :=
  ⟨⟨covZRigidPolyEnvWfT⟩, ⟨.nil⟩, ⟨covZRigidPolyHead_hasTy n []⟩,
    ⟨.refl _ _ _ (covZRigidPolyHead_hasTy n [])⟩,
    covZRigidPolyHead_observed n [] EnvT.bot, covZRigidPolyHead_related_leaf n [],
    CptT.noConfusion, fun ⟨b, hb⟩ => not_covZRigidPoly_hereditary_any_code n [] EnvT.bot b hb⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Z_RIGID_POLY_ROOTS
#print axioms covZRigidPolyTy
#print axioms covZRigidPolyMember
#print axioms covZRigidPolyEnv
#print axioms covZRigidPolyHead
#print axioms covZRigidPolyTy_hasTy
#print axioms covZRigidPolyEnvWfT
#print axioms covZRigidPolyHead_hasTy
#print axioms covZRigidPolyHead_rigid
#print axioms covZRigidPolyHead_not_propCtor
#print axioms covZRigidPolyHead_observed
#print axioms covZRigidPolyHead_normal
#print axioms covZRigidPolyHead_old_related
#print axioms covZRigidPolyHead_related_leaf
#print axioms not_covZRigidPoly_hereditary_any_code
#print axioms covZRigidPoly_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Z_RIGID_POLY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit

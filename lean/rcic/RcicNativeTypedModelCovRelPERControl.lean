import rcic.RcicNativeTypedModelCovRelPER
import rcic.RcicNativeTypedModelCovRelWitness

/-!
# A fully discharged PER instance with an actual lambda observation

The CK2 readback laws and uniqueness are supplied by their imported theorems.
The two spine-conversion laws use the imported empty-environment witnesses;
this module makes no claim that those laws have been discharged for a
nonempty member environment. The model itself is not bottom-only: the final
control realizes an actual native identity at a non-bottom lambda compact,
exhibits its self-related Pi type, and applies term symmetry and transitivity.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRelPERControlAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit ReadbackCK2Audit
open TypedModelKFragmentAudit TypedModelKAudit
open TypedModelCovRelAudit TypedModelCovRelWitnessAudit

/-- All hypotheses of the generic PER are discharged at the actual CK2
readback and the empty member environment. -/
theorem typedPERCov_whStepCK2_emptyEnv (C : CovTyping emptyEnv) (n k : Nat) :
    (∀ c, sizeOf c ≤ k →
      SymmTyAtCov C (WhStepCK2 emptyEnv n) n c ∧
      TransTyAtCov C (WhStepCK2 emptyEnv n) n c) ∧
    (∀ a u, sizeOf a + sizeOf u ≤ k →
      IrrelAtCov C (WhStepCK2 emptyEnv n) n a u ∧
      SymmTmAtCov C (WhStepCK2 emptyEnv n) n a u ∧
      TransTmAtCov C (WhStepCK2 emptyEnv n) n a u) :=
  typedPERCov C (readbackLaws_whStepCK2 emptyEnv n)
    (normalUniqueR_whStepCK2 (show EnvWfT emptyEnv from .empty)) .empty
    (convArgsSymmS_emptyEnv n) (convArgsTransS_emptyEnv n) k

/-- The concrete identity's Pi type is self-related at its nonempty-row
compact. The output is a constant sort and hence needs no model supplier. -/
theorem lrSCoreCov_idSort1Ty_polyIdDom1 {E : ResolvedEnv} (C : CovTyping E)
    (R : Readback) (n : Nat) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    LRSCoreCov C R n Γ idSort1Ty idSort1Ty
      (.sort (.succ (.succ .zero))) polyIdDom1 := by
  have hs : LRSCoreCov C R n Γ (.sort (.succ .zero)) (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) .sort := by
    rw [lrSCoreCov_sort_iff]
    exact ⟨⟨_, .refl _⟩, _, _, .refl _, .refl _⟩
  rw [polyIdDom1, LRSCoreCov.eq_def]
  refine ⟨⟨_, .refl _⟩, .sort (.succ .zero), .sort (.succ .zero),
    .sort (.succ .zero), .sort (.succ .zero), .refl _, .refl _,
    ⟨.assumption Γ (.sort (.succ .zero)) (.succ (.succ .zero)) hΓ (.sort _ _)⟩,
    ⟨.refl _ _⟩, ⟨.refl _ _⟩, ⟨_, hs⟩, ?_⟩
  intro s hmem hty x y hx hy hc hr
  obtain rfl := List.mem_singleton.mp hmem
  exact ⟨_, hs⟩

/-- Native typing, actual non-bottom lambda realization, a self-related Pi
type, and the applied term PER coexist in the same model instance. -/
theorem idSort1_cov_per_control_emptyEnv (C : CovTyping emptyEnv)
    (hS : CovTypingIncludesS C) (n : Nat) (ρ : EnvT) :
    Nonempty (HasTyT emptyEnv n [] idSort1 idSort1Ty) ∧
    ApproxTK emptyEnv n [] ρ idSort1 polyIdOut0 ∧
    polyIdOut0 ≠ .bot ∧ C.ty polyIdOut0 polyIdDom1 ∧
    LRSCoreCov C (WhStepCK2 emptyEnv n) n [] idSort1Ty idSort1Ty
      (.sort (.succ (.succ .zero))) polyIdDom1 ∧
    LRSCoreCov C (WhStepCK2 emptyEnv n) n [] idSort1 idSort1 idSort1Ty polyIdOut0 ∧
    (∀ x y, LRSCoreCov C (WhStepCK2 emptyEnv n) n [] x y idSort1Ty polyIdOut0 →
      LRSCoreCov C (WhStepCK2 emptyEnv n) n [] y x idSort1Ty polyIdOut0) ∧
    (∀ x y z, LRSCoreCov C (WhStepCK2 emptyEnv n) n [] x y idSort1Ty polyIdOut0 →
      LRSCoreCov C (WhStepCK2 emptyEnv n) n [] y z idSort1Ty polyIdOut0 →
      LRSCoreCov C (WhStepCK2 emptyEnv n) n [] x z idSort1Ty polyIdOut0) := by
  have hty : C.ty polyIdOut0 polyIdDom1 :=
    hS polyIdDom1 polyIdOut0 (ctyS_polyIdWitness1_polyIdDom1 emptyEnv)
  have hA := lrSCoreCov_idSort1Ty_polyIdDom1 C (WhStepCK2 emptyEnv n) n
    (Γ := []) .nil
  obtain ⟨_, sym, trans⟩ :=
    (typedPERCov_whStepCK2_emptyEnv C n _).2 polyIdDom1 polyIdOut0 (Nat.le_refl _)
  refine ⟨⟨.lam [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)
      (.sort (.succ .zero)) (.sort _ _) (.bvar _ 0 _ rfl)⟩,
    ApproxTK.free (kFreeT_lam (kFreeT_sort emptyEnv _) (kFreeT_bvar emptyEnv 0))
      (approxT_idSort1_polyIdOut0 emptyEnv ρ),
    (fun h => CptT.noConfusion h), hty, hA, ?_, ?_, ?_⟩
  · exact lrSCoreCov_identity_row C (readbackLaws_whStepCK2 emptyEnv n)
      (Γ := []) .nil (HasTyT.sort [] (.succ .zero)) .prop
  · intro x y hxy
    exact sym .nil hA hty hxy
  · intro x y z hxy hyz
    exact trans .nil hA hty hxy hyz

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_REL_PER_CONTROL_ROOTS
#print axioms typedPERCov_whStepCK2_emptyEnv
#print axioms lrSCoreCov_idSort1Ty_polyIdDom1
#print axioms idSort1_cov_per_control_emptyEnv
-- END RCIC_NATIVE_TYPED_MODEL_COV_REL_PER_CONTROL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRelPERControlAudit

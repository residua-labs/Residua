import rcic.RcicNativeTypedModelCovRForall

/-!
# An inhabited boundary for the strict-row polymorphic body

The landed native lambda identity has the actual compact `polyIdCpt0`.
Its outer action demands `.sort` and returns `polyIdOut0`. An unconditioned
sort-binder clause nevertheless tests that action at native Prop and the exact
Prop candidate. The strict ordinary arrow then requires its stored inner
`.prop` demand to belong to that candidate, which it does not.

This measures the strict-row callback displayed here. It does not refute
impredicative quantification in Prop, candidate consistency, or a separately
defined clause for an opaque candidate variable. It identifies a missing
connection among an outer action, its actual native type argument, and the
candidate assigned to that argument. All native and model premises of the
closed negative control are inhabited. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit TypedModelKFragmentAudit ReadbackCK2Audit TypedModelCovXAudit
open TypedModelCovPAudit TypedModelCovQAudit

/-- Diagnostic callback using the strict ordinary-arrow row obligations,
including when the supplied domain predicate comes from the sort binder. -/
def covRStrictIdentityBody (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CovRForallBody :=
  fun T S => covRArrow E n Γ false T S S

theorem covRStrictIdentityBody_candidates (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) :
    CovRForallBodyCandidates E n Γ false false (covRStrictIdentityBody E n Γ) :=
  fun _ _ hS => covRArrow_isCandidate hS hS

/-- Prop is a universe code, not an element of its own universe candidate. -/
theorem covRProp_support_not_prop (E : ResolvedEnv) :
    ¬ covRSupport (covRCodeRel E .prop) .prop := by
  rintro ⟨x, y, h⟩
  rcases ctyCovQ_prop_inv h with hb | hp | ⟨r, us, he, _⟩
  · exact CptT.noConfusion hb
  · cases hp
  · exact CptT.noConfusion he

theorem covRStrictIdentityBody_rejects_polyIdOut0
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (T x y : Expr Nat) :
    ¬ covRStrictIdentityBody E n Γ T (covRCodeRel E .prop) x y polyIdOut0 := by
  intro h
  have hr := covRArrow_rows h
  have hd := (hr ([.prop], .prop) (List.mem_singleton_self _)).1
  exact covRProp_support_not_prop E (hd .prop (List.mem_singleton_self _))

/-- This action is an actual constructor of the landed compact application
relation, with the exact stored demand list. -/
theorem covRPolyIdCpt0_action (E : ResolvedEnv) :
    CovXCompactAction E polyIdCpt0 [.sort] polyIdOut0 := by
  apply AppCptT.app (List.mem_singleton_self _)
  intro u hu
  exact .bvar hu

/-- The strict-body interpretation fails even though its callback satisfies
all candidate closure laws. The failing native argument is actual Prop. -/
theorem covRForall_strict_identity_rejects_polyIdCpt0
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (x y : Expr Nat) :
    ¬ covRForall E n Γ (.succ .zero) false false
      (covRStrictIdentityBody E n Γ) x y polyIdCpt0 := by
  intro h
  exact covRStrictIdentityBody_rejects_polyIdOut0 E n Γ (.sort .zero)
    (.app x (.sort .zero)) (.app y (.sort .zero))
    (covRForall_apply_prop h (covRPolyIdCpt0_action E))

/-- Reuse the landed observation and the actual K-free syntax proof. -/
theorem covRLambdaIdentity_observed (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) : ApproxTK E n Γ ρ cexPolyId polyIdCpt0 :=
  .free (kFreeT_lam (kFreeT_sort E _)
    (kFreeT_lam (kFreeT_bvar E 0) (kFreeT_bvar E 0)))
    (approxT_cexPolyId_cpt0 E ρ)

/-- Every source, type-argument, candidate, closure and action premise in
this exact failure is supplied, in the admitted empty environment/context. -/
theorem covRLambdaIdentity_strict_control (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] cexPolyId cexPolyIdTy) ∧
    Nonempty (ConvT emptyEnv n [] cexPolyId cexPolyId cexPolyIdTy) ∧
    ApproxTK emptyEnv n [] EnvT.bot cexPolyId polyIdCpt0 ∧
    polyIdCpt0 ≠ .bot ∧
    Nonempty (HasTyT emptyEnv n [] (.sort .zero) (.sort (.succ .zero))) ∧
    CandidateCov emptyEnv (WhStepCK2 emptyEnv n) [] false
      (covRCodeRel emptyEnv .prop) ∧
    CovRForallBodyCandidates emptyEnv n [] false false
      (covRStrictIdentityBody emptyEnv n []) ∧
    CovXCompactAction emptyEnv polyIdCpt0 [.sort] polyIdOut0 ∧
    ¬ covRForall emptyEnv n [] (.succ .zero) false false
      (covRStrictIdentityBody emptyEnv n []) cexPolyId cexPolyId polyIdCpt0 :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨hasTyT_cexPolyId emptyEnv n⟩,
    ⟨.refl _ _ _ (hasTyT_cexPolyId emptyEnv n)⟩,
    covRLambdaIdentity_observed emptyEnv n [] EnvT.bot, CptT.noConfusion,
    ⟨.sort [] .zero⟩, covRProp_isCandidate emptyEnv (WhStepCK2 emptyEnv n) [],
    covRStrictIdentityBody_candidates emptyEnv n [], covRPolyIdCpt0_action emptyEnv,
    covRForall_strict_identity_rejects_polyIdCpt0 emptyEnv n [] cexPolyId cexPolyId⟩

/-- The general observation supplier is already false at this one native
lambda, for the strict callback explicitly displayed in the statement. -/
theorem covRLambdaIdentity_no_strict_supplier (n : Nat) :
    ¬ (∀ c, ApproxTK emptyEnv n [] EnvT.bot cexPolyId c →
      covRForall emptyEnv n [] (.succ .zero) false false
        (covRStrictIdentityBody emptyEnv n []) cexPolyId cexPolyId c) := by
  intro h
  exact covRForall_strict_identity_rejects_polyIdCpt0 emptyEnv n [] cexPolyId cexPolyId
    (h polyIdCpt0 (covRLambdaIdentity_observed emptyEnv n [] EnvT.bot))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_R_LAMBDA_BOUNDARY_ROOTS
#print axioms covRStrictIdentityBody
#print axioms covRStrictIdentityBody_candidates
#print axioms covRProp_support_not_prop
#print axioms covRStrictIdentityBody_rejects_polyIdOut0
#print axioms covRPolyIdCpt0_action
#print axioms covRForall_strict_identity_rejects_polyIdCpt0
#print axioms covRLambdaIdentity_observed
#print axioms covRLambdaIdentity_strict_control
#print axioms covRLambdaIdentity_no_strict_supplier
-- END RCIC_NATIVE_TYPED_MODEL_COV_R_LAMBDA_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRAudit

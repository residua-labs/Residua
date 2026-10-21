import rcic.RcicNativeTypedModelCovZContract
import rcic.RcicNativeTypedModelCovYShapeBoundary

/-!
# Remeasurement of the four positive and four code-boundary fixtures

These are constructions of particular joint codes by composition with the
checked CovY proofs. They are not an implementation of a total `codeOf`.
In particular, the coverage and shape failures at caller-chosen Nat codes
are both repaired by the displayed empty-demand row. The two exact-code
escape failures use the actual native leaf codes. Native typing, actual
non-bottom observations, conversion, and hereditary environment guards are
kept in the control package.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovZAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelKTypedBetaAudit
open TypedModelCovRelAudit TypedModelCovRelEscapeAudit TypedModelCovNormCov2Audit
open TypedModelCovNormEscapeAudit TypedModelCovXAudit TypedModelCovXEtaAudit
open TypedModelCovYAudit TypedModelCovYEtaAudit TypedModelCovYPolyPropAudit

/-- A concrete positive control has native and model inhabitants, rather
than an uninstantiated realization or code-construction premise. -/
def CovZInhabitedJointAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (x y A : Expr Nat) (c b : CptT) : Prop :=
  Nonempty (EnvWfT E) ∧ Nonempty (CtxWfT E n Γ) ∧
  Nonempty (HasTyT E n Γ x A) ∧ Nonempty (HasTyT E n Γ y A) ∧
  Nonempty (ConvT E n Γ x y A) ∧
  EnvTypedCovYAt (C2 E) (ctxModelT_approxTK E n) (WhStepCK2 E n) n Γ ρ ∧
  (ApproxTK E n Γ ρ x c ∨ ApproxTK E n Γ ρ y c) ∧ c ≠ .bot ∧
  CovZJointCodeAt (C2 E) (ctxModelT_approxTK E n) (WhStepCK2 E n)
    n Γ ρ ρ x y A c b

/-- Fixture 1: the eta-only lambda observation retains the complete joint
target at the already constructed Nat-arrow code. -/
theorem covZ_fixture_natSucc_eta (n : Nat) :
    CovZInhabitedJointAt natEnvU n [] EnvT.bot
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      covXNatEtaEmptyRow covYNatArrowCode := by
  obtain ⟨hW, hΓ, hl, hr, hc, ho, hh, hnb⟩ :=
    covY_natSucc_eta_hereditary_control n
  exact ⟨hW, hΓ, hl, hr, hc, envTypedCovYAt_nil (C2 natEnvU) _ _ n EnvT.bot,
    Or.inl ho, hnb,
    covY_natSucc_eta_observed_realized n [] [] EnvT.bot EnvT.bot _ (Or.inl ho)⟩

/-- Fixture 2: the alias in a Pi domain remains positive at its nonempty
demand row, including both hereditary sides. -/
theorem covZ_fixture_alias_in_pi (n : Nat) :
    ∃ A B : Expr Nat, CovZInhabitedJointAt eqEnvT n eqGapCtx EnvT.bot
      covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
      covNormAliasIdentityCpt covYAliasPiCode := by
  obtain ⟨hW, hΓ, he, A, B, ⟨ht⟩, ho, hr, hh, hnb⟩ :=
    covY_fixture_alias_in_pi n
  exact ⟨A, B, hW, hΓ, ⟨ht⟩, ⟨ht⟩, ⟨.refl _ _ _ ht⟩,
    he, Or.inl ho, hnb, hr, hh, hh⟩

/-- Fixture 3: the impredicative domain is represented at finite bottom
depth while the actual function and its output remain non-bottom. -/
theorem covZ_fixture_polyPropLam (n : Nat) :
    CovZInhabitedJointAt eqEnvT n [] EnvT.bot
      covXPolyPropLam covXPolyPropLam covXPolyPropLamTy
      (.lam [([], .prop)]) covYPolyPropCode := by
  obtain ⟨hW, hΓ, hs, ⟨ht⟩, ho, _, hr, hh, _, _, hnb⟩ :=
    covY_fixture_polyPropLam n
  exact ⟨hW, hΓ, ⟨ht⟩, ⟨ht⟩, ⟨.refl _ _ _ ht⟩, hs.envL,
    Or.inl ho, hnb, hr, hh, hh⟩

/-- Fixture 4: keep the actual nonempty hereditary substitution and its
let-coherence fields, and construct the same-code target for the head. -/
theorem covZ_fixture_alias_extension (n : Nat) :
    ∃ A B : Expr Nat,
      RelSubstAtCovY (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n)
        (WhStepCK2 eqEnvT n) n eqGapCtx
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (SubstT.cons idPiProp SubstT.id) (SubstT.cons idPiProp SubstT.id)
        (.assumption (eqGapDirectAlias A B) :: eqGapCtx) ∧
      CovZInhabitedJointAt eqEnvT n eqGapCtx EnvT.bot idPiProp idPiProp
        (eqGapDirectAlias A B) (.pi .bot []) .prop := by
  obtain ⟨hW, hΓ, A, B, _, ⟨ht⟩, ho, hs, hh, _, hnb⟩ :=
    covY_fixture_alias_extension n
  exact ⟨A, B, hs, hW, hΓ, ⟨ht⟩, ⟨ht⟩, ⟨.refl _ _ _ ht⟩,
    envTypedCovYAt_eqGap_bot (C2 eqEnvT) n, Or.inl ho, hnb,
    lrSCoreCovY_idPiProp_alias (C2 eqEnvT) (C2_includesS eqEnvT) n A B, hh, hh⟩

/-- Boundaries A and B: the constructed code has native Pi shape and an
empty-demand covering row. Neither conclusion is extracted from the bad
caller-selected codes of the earlier counterexamples. -/
theorem covZ_fixture_nat_coverage_and_shape (n : Nat) :
    (∃ d g, covYNatArrowCode = .pi d g) ∧
    CovYActionCoverage (C2 natEnvU) (.spine 2 []) (.spine 0 []) [([], .spine 0 [])] ∧
    CovZInhabitedJointAt natEnvU n [] EnvT.bot
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covYNatArrowCode := by
  obtain ⟨hW, hΓ, ⟨ht⟩, ho, he, _, _, _, _, hr, hh, hnb⟩ :=
    covY_natSucc_code_shape_control n
  exact ⟨⟨_, _, rfl⟩, covY_natSucc_uniform_coverage,
    hW, hΓ, ⟨ht⟩, ⟨ht⟩, ⟨.refl _ _ _ ht⟩, he, Or.inl ho, hnb, hr, hh, hh⟩

/-- Boundary C at Eq: select `prop`, the actual code of native `Sort 0`,
and retain the same genuine proposition observation. -/
theorem covZ_fixture_eq_anchor (n : Nat) :
    CovZInhabitedJointAt eqEnvT n eqGapCtx EnvT.bot idPiProp idPiProp
      (.sort .zero) (.pi .bot []) .prop := by
  obtain ⟨hW, hΓ, ⟨ht⟩, ho, he, _, _, hr, hh, hnb⟩ :=
    covY_code_anchor_control (C2 eqEnvT) (C2_includesS eqEnvT) n
  exact ⟨hW, hΓ, ⟨ht⟩, ⟨ht⟩, ⟨.refl _ _ _ ht⟩, he, Or.inl ho, hnb, hr, hh, hh⟩

/-- Boundary C at Nat: select the zero-argument family code rather than
preserving the unsupported extra-argument code. -/
theorem covZ_fixture_nat_anchor (n : Nat) :
    CovZInhabitedJointAt natEnvU n [] EnvT.bot
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) (.spine 0 []) := by
  obtain ⟨hW, hΓ, he, ⟨ht⟩, ho, _, _, _, _, _, hr, hh, hnb⟩ :=
    covY_natZero_extraArgCode_control n
  exact ⟨hW, hΓ, ⟨ht⟩, ⟨ht⟩, ⟨.refl _ _ _ ht⟩, he, Or.inl ho, hnb, hr, hh, hh⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Z_FIXTURES_ROOTS
#print axioms CovZInhabitedJointAt
#print axioms covZ_fixture_natSucc_eta
#print axioms covZ_fixture_alias_in_pi
#print axioms covZ_fixture_polyPropLam
#print axioms covZ_fixture_alias_extension
#print axioms covZ_fixture_nat_coverage_and_shape
#print axioms covZ_fixture_eq_anchor
#print axioms covZ_fixture_nat_anchor
-- END RCIC_NATIVE_TYPED_MODEL_COV_Z_FIXTURES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovZAudit

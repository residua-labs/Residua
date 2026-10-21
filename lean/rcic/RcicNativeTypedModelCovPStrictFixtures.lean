import rcic.RcicNativeTypedModelCovPStrictRealization
import rcic.RcicNativeTypedModelCovZWall4Control

/-!
# Eight fixture observations and their joint codes survive strictness

The old native and substitution certificates remain explicit. In addition,
the actual displayed value observation belongs to the restricted model and
both hereditary witnesses use that model. The literal old substitution
package is not relabelled as a package for a new model. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelKTypedBetaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit TypedModelCovNormEscapeAudit
open TypedModelCovXAudit TypedModelCovXEtaAudit TypedModelCovYAudit
open TypedModelCovYEtaAudit TypedModelCovYPolyPropAudit TypedModelCovZAudit

theorem covP_strict_spine_nil (E : ResolvedEnv) (r : Nat) :
    CovPStrictCompact E (.spine r []) := by
  simp [CovPStrictCompact]

theorem covP_strict_natSucc_bot : CovPStrictCompact natEnvU (.spine 2 [.bot]) := by
  rw [CovPStrictCompact]
  constructor
  · intro u hu
    obtain rfl := List.mem_singleton.mp hu
    simp [CovPStrictCompact]
  · intro i hi hs
    exact (covP_constructor_not_type_slot
      (rfl : natEnvU.members 2 = some natSuccMember) rfl i hs).elim

theorem covP_strict_nat_eta : CovPStrictCompact natEnvU covXNatEtaEmptyRow := by
  change CovPStrictCompact natEnvU (.lam [([], .spine 2 [.bot])])
  rw [CovPStrictCompact]
  intro row hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨by simp, covP_strict_natSucc_bot⟩

theorem covP_strict_natArrow : CovPStrictCompact natEnvU covYNatArrowCode := by
  simp [covYNatArrowCode, CovPStrictCompact]

theorem covP_strict_alias_compact : CovPStrictCompact eqEnvT covNormAliasIdentityCpt := by
  simp [covNormAliasIdentityCpt, CovPStrictCompact]

theorem covP_strict_alias_code : CovPStrictCompact eqEnvT covYAliasPiCode := by
  simp [covYAliasPiCode, CovPStrictCompact]

theorem covP_strict_polyProp_compact : CovPStrictCompact eqEnvT (.lam [([], .prop)]) := by
  simp [CovPStrictCompact]

theorem covP_strict_polyProp_code : CovPStrictCompact eqEnvT covYPolyPropCode := by
  simp [covYPolyPropCode, CovPStrictCompact]

theorem covP_strict_eq_compact : CovPStrictCompact eqEnvT (.pi .bot []) := by
  simp [CovPStrictCompact]

theorem covP_strict_prop_code (E : ResolvedEnv) : CovPStrictCompact E .prop := by
  simp [CovPStrictCompact]

theorem covP_strict_wall4_compact (E : ResolvedEnv) :
    CovPStrictCompact E (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])]) := by
  simp [CovPStrictCompact]

theorem covP_strict_wall4_code (E : ResolvedEnv) :
    CovPStrictCompact E covZRelevantAppCode := by
  simp [covZRelevantAppCode, covZPropArrowCode, CovPStrictCompact]

def CovPStrictFixtureAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (x y A : Expr Nat) (c b : CptT) : Prop :=
  CovZInhabitedJointAt E n Γ ρ x y A c b ∧
  (ApproxTKStrictP E n Γ ρ x c ∨ ApproxTKStrictP E n Γ ρ y c) ∧
  CovZJointCodeAt (C2 E) (ctxModelT_approxTKStrictP E n) (WhStepCK2 E n)
    n Γ ρ ρ x y A c b

theorem covP_strict_fixture_of_certificates {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : EnvT} {x y A : Expr Nat} {c b : CptT}
    (h : CovZInhabitedJointAt E n Γ ρ x y A c b)
    (hc : CovPStrictCompact E c) (hb : CovPStrictCompact E b) :
    CovPStrictFixtureAt E n Γ ρ x y A c b := by
  refine ⟨h, ?_⟩
  obtain ⟨_, _, _, _, _, _, ho, _, hj⟩ := h
  exact ⟨ho.elim (fun h => Or.inl ⟨h, hc⟩) (fun h => Or.inr ⟨h, hc⟩),
    covP_strict_joint_of_code (C2 E) (WhStepCK2 E n) n Γ ρ ρ x y A c b hb hj⟩

theorem covP_strict_fixture_natSucc_eta (n : Nat) :
    CovPStrictFixtureAt natEnvU n [] EnvT.bot
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      covXNatEtaEmptyRow covYNatArrowCode :=
  covP_strict_fixture_of_certificates (covZ_fixture_natSucc_eta n)
    covP_strict_nat_eta covP_strict_natArrow

theorem covP_strict_fixture_alias_in_pi (n : Nat) :
    ∃ A B, CovPStrictFixtureAt eqEnvT n eqGapCtx EnvT.bot
      covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
      covNormAliasIdentityCpt covYAliasPiCode := by
  obtain ⟨A, B, h⟩ := covZ_fixture_alias_in_pi n
  exact ⟨A, B, covP_strict_fixture_of_certificates h
    covP_strict_alias_compact covP_strict_alias_code⟩

theorem covP_strict_fixture_polyPropLam (n : Nat) :
    CovPStrictFixtureAt eqEnvT n [] EnvT.bot
      covXPolyPropLam covXPolyPropLam covXPolyPropLamTy
      (.lam [([], .prop)]) covYPolyPropCode :=
  covP_strict_fixture_of_certificates (covZ_fixture_polyPropLam n)
    covP_strict_polyProp_compact covP_strict_polyProp_code

theorem covP_strict_fixture_alias_extension (n : Nat) :
    ∃ A B,
      RelSubstAtCovY (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
        n eqGapCtx (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (SubstT.cons idPiProp SubstT.id) (SubstT.cons idPiProp SubstT.id)
        (.assumption (eqGapDirectAlias A B) :: eqGapCtx) ∧
      CovPStrictFixtureAt eqEnvT n eqGapCtx EnvT.bot idPiProp idPiProp
        (eqGapDirectAlias A B) (.pi .bot []) .prop := by
  obtain ⟨A, B, hs, h⟩ := covZ_fixture_alias_extension n
  exact ⟨A, B, hs, covP_strict_fixture_of_certificates h
    covP_strict_eq_compact (covP_strict_prop_code _)⟩

theorem covP_strict_fixture_nat_coverage_shape (n : Nat) :
    (∃ d g, covYNatArrowCode = .pi d g) ∧
    CovYActionCoverage (C2 natEnvU) (.spine 2 []) (.spine 0 []) [([], .spine 0 [])] ∧
    CovPStrictFixtureAt natEnvU n [] EnvT.bot
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covYNatArrowCode := by
  obtain ⟨hs, hc, h⟩ := covZ_fixture_nat_coverage_and_shape n
  exact ⟨hs, hc, covP_strict_fixture_of_certificates h
    (covP_strict_spine_nil _ _) covP_strict_natArrow⟩

theorem covP_strict_fixture_eq_anchor (n : Nat) :
    CovPStrictFixtureAt eqEnvT n eqGapCtx EnvT.bot idPiProp idPiProp
      (.sort .zero) (.pi .bot []) .prop :=
  covP_strict_fixture_of_certificates (covZ_fixture_eq_anchor n)
    covP_strict_eq_compact (covP_strict_prop_code _)

theorem covP_strict_fixture_nat_anchor (n : Nat) :
    CovPStrictFixtureAt natEnvU n [] EnvT.bot
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) (.spine 0 []) :=
  covP_strict_fixture_of_certificates (covZ_fixture_nat_anchor n)
    (covP_strict_spine_nil _ _) (covP_strict_spine_nil _ _)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_STRICT_FIXTURES_ROOTS
#print axioms covP_strict_spine_nil
#print axioms covP_strict_natSucc_bot
#print axioms covP_strict_nat_eta
#print axioms covP_strict_natArrow
#print axioms covP_strict_alias_compact
#print axioms covP_strict_alias_code
#print axioms covP_strict_polyProp_compact
#print axioms covP_strict_polyProp_code
#print axioms covP_strict_eq_compact
#print axioms covP_strict_prop_code
#print axioms covP_strict_wall4_compact
#print axioms covP_strict_wall4_code
#print axioms CovPStrictFixtureAt
#print axioms covP_strict_fixture_of_certificates
#print axioms covP_strict_fixture_natSucc_eta
#print axioms covP_strict_fixture_alias_in_pi
#print axioms covP_strict_fixture_polyPropLam
#print axioms covP_strict_fixture_alias_extension
#print axioms covP_strict_fixture_nat_coverage_shape
#print axioms covP_strict_fixture_eq_anchor
#print axioms covP_strict_fixture_nat_anchor
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_STRICT_FIXTURES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPAudit

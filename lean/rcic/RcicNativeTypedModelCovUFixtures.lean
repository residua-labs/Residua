import rcic.RcicNativeTypedModelCovURecInstance

/-!
# Explicit native realizers for the eight retained view fixtures

Each row retains its actual native/model premises and its existing provenance
view, and supplies the displayed closed native substitution for its valuation.
The empty contexts use `SubstT.id`; the Eq context uses `covUEqSubst`.
This packages actual realizers, not a choice of one from a general existence
port.  It does not assert a general observation-soundness theorem or interpret
the old Type-valued views.  `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovTAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelAudit.TypingFin TypedModelKAudit TypedModelKTypedBetaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelCovNormEscapeAudit TypedModelCovXAudit TypedModelCovXEtaAudit
open TypedModelCovRelBoundaryAudit
open TypedModelCovYEtaAudit TypedModelCovZAudit TypedModelCovPAudit
open TypedModelCovRAudit TypedModelCovSAudit

/-- The retained local fixture plus an actual closed realization of its
valuation, with the same information-stage bound. No interpretation field is
silently added to the earlier fixture. -/
def CovURealizedFixtureAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (σ : SubstT) (x y A : Expr Nat) (c a : CptT) : Prop :=
  CovTTypeFixtureAt E n Γ ρ x y A c a ∧
  CovTRealized E n covTFixtureStage Γ ρ σ

theorem covU_fixture_natSucc_eta (n : Nat) :
    CovURealizedFixtureAt natEnvU n [] EnvT.bot SubstT.id
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      covXNatEtaEmptyRow covYNatArrowCode :=
  ⟨covT_fixture_natSucc_eta n, covU_realized_nil _ _ _⟩

theorem covU_fixture_alias_in_pi (n : Nat) :
    ∃ A B, CovURealizedFixtureAt eqEnvT n eqGapCtx EnvT.bot covUEqSubst
      covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
      covNormAliasIdentityCpt (.pi .bot []) := by
  obtain ⟨A, B, h⟩ := covT_fixture_alias_in_pi n
  exact ⟨A, B, h, covUEqEnv_realized n covTFixtureStage⟩

theorem covU_fixture_polyPropLam (n : Nat) :
    CovURealizedFixtureAt eqEnvT n [] EnvT.bot SubstT.id
      covXPolyPropLam covXPolyPropLam covXPolyPropLamTy
      (.lam [([], .prop)]) covSPolyPropCode :=
  ⟨covT_fixture_polyPropLam n, covU_realized_nil _ _ _⟩

/-- As in the signed-off fixture, the tested value and valuation live in the
base Eq context. The extra native assumption is separately well formed; this
row does not claim a new model valuation for that larger context. -/
theorem covU_fixture_alias_extension (n : Nat) :
    ∃ A B,
      Nonempty (CtxWfT eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx)) ∧
      CovURealizedFixtureAt eqEnvT n eqGapCtx EnvT.bot covUEqSubst
        idPiProp idPiProp (eqGapDirectAlias A B) (.pi .bot []) .bot := by
  obtain ⟨A, B, hΓ, h⟩ := covT_fixture_alias_extension n
  exact ⟨A, B, hΓ, h, covUEqEnv_realized n covTFixtureStage⟩

theorem covU_fixture_nat_coverage (n : Nat) :
    CovURealizedFixtureAt natEnvU n [] EnvT.bot SubstT.id
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covYNatArrowCode :=
  ⟨covT_fixture_nat_coverage n, covU_realized_nil _ _ _⟩

theorem covU_fixture_nat_shape (n : Nat) :
    CovURealizedFixtureAt natEnvU n [] EnvT.bot SubstT.id
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covYNatArrowCode :=
  ⟨covT_fixture_nat_shape n, covU_realized_nil _ _ _⟩

theorem covU_fixture_eq_anchor (n : Nat) :
    CovURealizedFixtureAt eqEnvT n eqGapCtx EnvT.bot covUEqSubst
      idPiProp idPiProp (.sort .zero) (.pi .bot []) .prop :=
  ⟨covT_fixture_eq_anchor n, covUEqEnv_realized n covTFixtureStage⟩

theorem covU_fixture_nat_anchor (n : Nat) :
    CovURealizedFixtureAt natEnvU n [] EnvT.bot SubstT.id
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) (.spine 0 []) :=
  ⟨covT_fixture_nat_anchor n, covU_realized_nil _ _ _⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_U_FIXTURES_ROOTS
#print axioms CovURealizedFixtureAt
#print axioms covU_fixture_natSucc_eta
#print axioms covU_fixture_alias_in_pi
#print axioms covU_fixture_polyPropLam
#print axioms covU_fixture_alias_extension
#print axioms covU_fixture_nat_coverage
#print axioms covU_fixture_nat_shape
#print axioms covU_fixture_eq_anchor
#print axioms covU_fixture_nat_anchor
-- END RCIC_NATIVE_TYPED_MODEL_COV_U_FIXTURES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovTAudit

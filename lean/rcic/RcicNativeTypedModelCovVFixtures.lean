import rcic.RcicNativeTypedModelCovVNativeHeads
import rcic.RcicNativeTypedModelCovVRealized
import rcic.RcicNativeTypedModelCovUFixtures

/-!
# The eight actual fixtures in the native-eligible observation model

The earlier native evidence, explicit realized valuation and provenance view
are retained as data. Each concrete row additionally supplies the actual value
observation, type observation and all native-realizer image observations in
ApproxTKN. These are local supplies, not a new interpretation of every view
or a general fundamental theorem.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovVAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelKAudit TypedModelKTypedBetaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelCovNormEscapeAudit TypedModelCovXAudit TypedModelCovXEtaAudit
open TypedModelCovRelBoundaryAudit TypedModelCovYEtaAudit TypedModelCovZAudit
open TypedModelCovPAudit TypedModelCovRAudit TypedModelCovSAudit TypedModelCovTAudit

/-- The fresh model observations accompany the retained, explicitly realized
native fixture. Both observations and the native realizer use the aligned
stage predicate with the exact old information bound. -/
def CovVFixtureAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (σ : SubstT) (x y A : Expr Nat) (c a : CptT) : Prop :=
  CovURealizedFixtureAt E n Γ ρ σ x y A c a ∧
  ApproxTKNStage E n covTFixtureStage Γ ρ x c ∧
  ApproxTKNStage E n covTFixtureStage Γ ρ A a ∧
  CovVRealized E n covTFixtureStage Γ ρ σ

/-- Packaging after an environment has separately supplied exact native
eligibility. The eight following theorems instantiate every premise. -/
theorem covV_fixture_of_native_heads {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : EnvT} {σ : SubstT} {x y A : Expr Nat} {c a : CptT}
    (hE : CovVPropHeadsNative E)
    (h : CovURealizedFixtureAt E n Γ ρ σ x y A c a) :
    CovVFixtureAt E n Γ ρ σ x y A c a := by
  obtain ⟨_, _, _, _, _, _, _, ho, _, ⟨hv⟩⟩ := h.1
  exact ⟨h, covV_stage_of_native_heads hE ho,
    covV_stage_of_native_heads hE hv.observed,
    covV_realized_of_native_heads hE h.2⟩

theorem covV_fixture_natSucc_eta (n : Nat) :
    CovVFixtureAt natEnvU n [] EnvT.bot SubstT.id
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      covXNatEtaEmptyRow covYNatArrowCode :=
  covV_fixture_of_native_heads covV_nat_native_heads (covU_fixture_natSucc_eta n)

theorem covV_fixture_alias_in_pi (n : Nat) :
    ∃ A B, CovVFixtureAt eqEnvT n eqGapCtx EnvT.bot covUEqSubst
      covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
      covNormAliasIdentityCpt (.pi .bot []) := by
  obtain ⟨A, B, h⟩ := covU_fixture_alias_in_pi n
  exact ⟨A, B, covV_fixture_of_native_heads covV_eq_native_heads h⟩

theorem covV_fixture_polyPropLam (n : Nat) :
    CovVFixtureAt eqEnvT n [] EnvT.bot SubstT.id
      covXPolyPropLam covXPolyPropLam covXPolyPropLamTy
      (.lam [([], .prop)]) covSPolyPropCode :=
  covV_fixture_of_native_heads covV_eq_native_heads (covU_fixture_polyPropLam n)

theorem covV_fixture_alias_extension (n : Nat) :
    ∃ A B,
      Nonempty (CtxWfT eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx)) ∧
      CovVFixtureAt eqEnvT n eqGapCtx EnvT.bot covUEqSubst
        idPiProp idPiProp (eqGapDirectAlias A B) (.pi .bot []) .bot := by
  obtain ⟨A, B, hΓ, h⟩ := covU_fixture_alias_extension n
  exact ⟨A, B, hΓ, covV_fixture_of_native_heads covV_eq_native_heads h⟩

theorem covV_fixture_nat_coverage (n : Nat) :
    CovVFixtureAt natEnvU n [] EnvT.bot SubstT.id
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covYNatArrowCode :=
  covV_fixture_of_native_heads covV_nat_native_heads (covU_fixture_nat_coverage n)

theorem covV_fixture_nat_shape (n : Nat) :
    CovVFixtureAt natEnvU n [] EnvT.bot SubstT.id
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covYNatArrowCode :=
  covV_fixture_of_native_heads covV_nat_native_heads (covU_fixture_nat_shape n)

theorem covV_fixture_eq_anchor (n : Nat) :
    CovVFixtureAt eqEnvT n eqGapCtx EnvT.bot covUEqSubst
      idPiProp idPiProp (.sort .zero) (.pi .bot []) .prop :=
  covV_fixture_of_native_heads covV_eq_native_heads (covU_fixture_eq_anchor n)

theorem covV_fixture_nat_anchor (n : Nat) :
    CovVFixtureAt natEnvU n [] EnvT.bot SubstT.id
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) (.spine 0 []) :=
  covV_fixture_of_native_heads covV_nat_native_heads (covU_fixture_nat_anchor n)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_V_FIXTURES_ROOTS
#print axioms CovVFixtureAt
#print axioms covV_fixture_of_native_heads
#print axioms covV_fixture_natSucc_eta
#print axioms covV_fixture_alias_in_pi
#print axioms covV_fixture_polyPropLam
#print axioms covV_fixture_alias_extension
#print axioms covV_fixture_nat_coverage
#print axioms covV_fixture_nat_shape
#print axioms covV_fixture_eq_anchor
#print axioms covV_fixture_nat_anchor
-- END RCIC_NATIVE_TYPED_MODEL_COV_V_FIXTURES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovVAudit

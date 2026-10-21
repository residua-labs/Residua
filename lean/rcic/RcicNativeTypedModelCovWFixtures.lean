import rcic.RcicNativeTypedModelCovWRealized
import rcic.RcicNativeTypedModelCovVFixtures

/-! # Actual fixtures after per-call K alignment
All old native evidence is retained; every new value/type observation and
realizer image uses ApproxTKW. These are local supplies. closure_claim = 0. -/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelKAudit TypedModelKTypedBetaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelCovNormEscapeAudit TypedModelCovXAudit TypedModelCovXEtaAudit
open TypedModelCovRelBoundaryAudit TypedModelCovYEtaAudit TypedModelCovZAudit
open TypedModelCovPAudit TypedModelCovRAudit TypedModelCovSAudit TypedModelCovTAudit
open TypedModelCovVAudit

def CovWFixtureAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (σ : SubstT) (x y A : Expr Nat) (c a : CptT) : Prop :=
  CovVFixtureAt E n Γ ρ σ x y A c a ∧
  ApproxTKWStage E n covTFixtureStage Γ ρ x c ∧
  ApproxTKWStage E n covTFixtureStage Γ ρ A a ∧
  CovWRealized E n covTFixtureStage Γ ρ σ

theorem covW_fixture_of_indexed_prop {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : EnvT} {σ : SubstT} {x y A : Expr Nat} {c a : CptT}
    (hE : CovWPropRecIndexed E)
    (h : CovVFixtureAt E n Γ ρ σ x y A c a) :
    CovWFixtureAt E n Γ ρ σ x y A c a :=
  ⟨h, covW_stage_of_indexed_prop hE h.2.1,
    covW_stage_of_indexed_prop hE h.2.2.1,
    covW_realized_of_indexed_prop hE h.2.2.2⟩

theorem covW_fixture_natSucc_eta (n : Nat) :
    CovWFixtureAt natEnvU n [] EnvT.bot SubstT.id
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      covXNatEtaEmptyRow covYNatArrowCode :=
  covW_fixture_of_indexed_prop covW_nat_prop_indexed (covV_fixture_natSucc_eta n)

theorem covW_fixture_alias_in_pi (n : Nat) :
    ∃ A B, CovWFixtureAt eqEnvT n eqGapCtx EnvT.bot covUEqSubst
      covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
      covNormAliasIdentityCpt (.pi .bot []) := by
  obtain ⟨A, B, h⟩ := covV_fixture_alias_in_pi n
  exact ⟨A, B, covW_fixture_of_indexed_prop covW_eq_prop_indexed h⟩

theorem covW_fixture_polyPropLam (n : Nat) :
    CovWFixtureAt eqEnvT n [] EnvT.bot SubstT.id
      covXPolyPropLam covXPolyPropLam covXPolyPropLamTy
      (.lam [([], .prop)]) covSPolyPropCode :=
  covW_fixture_of_indexed_prop covW_eq_prop_indexed (covV_fixture_polyPropLam n)

theorem covW_fixture_alias_extension (n : Nat) :
    ∃ A B,
      Nonempty (CtxWfT eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx)) ∧
      CovWFixtureAt eqEnvT n eqGapCtx EnvT.bot covUEqSubst
        idPiProp idPiProp (eqGapDirectAlias A B) (.pi .bot []) .bot := by
  obtain ⟨A, B, hΓ, h⟩ := covV_fixture_alias_extension n
  exact ⟨A, B, hΓ, covW_fixture_of_indexed_prop covW_eq_prop_indexed h⟩

theorem covW_fixture_nat_coverage (n : Nat) :
    CovWFixtureAt natEnvU n [] EnvT.bot SubstT.id
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covYNatArrowCode :=
  covW_fixture_of_indexed_prop covW_nat_prop_indexed (covV_fixture_nat_coverage n)

theorem covW_fixture_nat_shape (n : Nat) :
    CovWFixtureAt natEnvU n [] EnvT.bot SubstT.id
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covYNatArrowCode :=
  covW_fixture_of_indexed_prop covW_nat_prop_indexed (covV_fixture_nat_shape n)

theorem covW_fixture_eq_anchor (n : Nat) :
    CovWFixtureAt eqEnvT n eqGapCtx EnvT.bot covUEqSubst
      idPiProp idPiProp (.sort .zero) (.pi .bot []) .prop :=
  covW_fixture_of_indexed_prop covW_eq_prop_indexed (covV_fixture_eq_anchor n)

theorem covW_fixture_nat_anchor (n : Nat) :
    CovWFixtureAt natEnvU n [] EnvT.bot SubstT.id
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) (.spine 0 []) :=
  covW_fixture_of_indexed_prop covW_nat_prop_indexed (covV_fixture_nat_anchor n)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_FIXTURES_ROOTS
#print axioms CovWFixtureAt
#print axioms covW_fixture_of_indexed_prop
#print axioms covW_fixture_natSucc_eta
#print axioms covW_fixture_alias_in_pi
#print axioms covW_fixture_polyPropLam
#print axioms covW_fixture_alias_extension
#print axioms covW_fixture_nat_coverage
#print axioms covW_fixture_nat_shape
#print axioms covW_fixture_eq_anchor
#print axioms covW_fixture_nat_anchor
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_FIXTURES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWAudit

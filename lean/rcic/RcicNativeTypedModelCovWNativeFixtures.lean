import rcic.RcicNativeTypedModelCovWNativeAliasControl
import rcic.RcicNativeTypedModelCovWIrrelFixtures
import rcic.RcicNativeTypedModelCovWEtaControls
import rcic.RcicNativeTypedModelCovWEtaNat

/-!
# Fresh native-aligned observations for the eight retained fixtures

The old native/view payload is retained explicitly. Every new observation
and realizer image below is constructed in the native-aligned grammar. Packaging a
fixture requires its new observations; no old-to-new embedding is used.
These are local supplies. closure_claim = 0.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelCovWIrrelAudit
open FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelKAudit TypedModelKFragmentAudit TypedModelKTypedBetaAudit
open TypedModelCovNormEscapeAudit TypedModelCovXAudit TypedModelCovXEtaAudit
open TypedModelCovRelBoundaryAudit TypedModelCovYEtaAudit TypedModelCovZAudit
open TypedModelCovPAudit TypedModelCovQAudit TypedModelCovRAudit TypedModelCovSAudit
open TypedModelCovTAudit TypedModelCovVAudit TypedModelCovWAudit TypedModelCovWEtaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit

theorem covWNative_rigid_observed {E : ResolvedEnv} {r : Nat}
    (hr : RigidConst E r) (hn : ¬ PropCtorT E r)
    (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative E n Γ ρ (.const r []) (.spine r [] []) :=
  .const Γ ρ r [] hr hn

theorem covWNative_neutral_observed {E : ResolvedEnv} {r : Nat}
    (hh : NeutralHeadP E r) (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative E n Γ ρ (.const r []) (.spine r [] []) := by
  apply covWNative_rigid_observed (neutralHeadP_rigid hh) ?_ n Γ ρ
  rintro ⟨m, fam, fm, hm, hctor, _⟩
  exact neutralHeadP_not_constructor hh hm hctor

theorem covWNative_pi_nil (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (A B : Expr Nat) :
    ApproxTKWNative E n Γ ρ (.pi A B) (.pi .bot []) :=
  .pi (.bot _ _ _) (fun _ h => (List.not_mem_nil _ h).elim)
    (fun _ h => (List.not_mem_nil _ h).elim)

theorem covWNative_nat_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative natEnvU n Γ ρ (.const 0 []) (.spine 0 [] []) :=
  covWNative_rigid_observed rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat n Γ ρ

theorem covWNative_succ_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative natEnvU n Γ ρ (.const 2 []) (.spine 2 [] []) :=
  covWNative_rigid_observed rigidConst_natEnvU_succ not_propCtorT_natEnvU_succ n Γ ρ

def covWNativeNatArrowCode : CptWIrrel :=
  .pi (.spine 0 [] []) [([], .spine 0 [] [])]

theorem covWNative_natArrow_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative natEnvU n Γ ρ (.pi (.const 0 []) (.const 0 [])) covWNativeNatArrowCode := by
  refine .pi (covWNative_nat_observed n Γ ρ) ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil _ hu).elim
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact covWNative_nat_observed n _ _

theorem covWNative_natEta_empty (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative natEnvU n Γ ρ
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.lam [([], .spine 2 [] [.bot])]) := by
  apply covWNative_empty_lam (by intro h; cases h)
  exact covWNative_guarded_appSpine_bot
    (covWEtaNatFn_ty n (.assumption (.const 0 []) :: Γ))
    (.bvar _ 0 _ rfl) (covWNative_succ_observed n _ _)

theorem covWNative_aliasIdentity_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative eqEnvT n Γ ρ covNormAliasIdentity
      (.lam [([.pi .bot []], .pi .bot [])]) := by
  refine .lam (covWNative_sort_observed eqEnvT n Γ ρ .zero) ?_ ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    change CTyS eqEnvT (.pi .bot []) .prop
    rw [CTyS]
    exact Or.inr (.pi .bot (fun _ h => (List.not_mem_nil _ h).elim))
  · exact ⟨_, List.mem_singleton.mpr rfl, fun h => CptWIrrel.noConfusion h⟩
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact .bvar (List.mem_singleton.mpr rfl)

def covWNativePolyPropCode : CptWIrrel := .pi (.pi .prop []) [([], .sort)]

theorem covWNative_poly_type_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative eqEnvT n Γ ρ covXPolyPropLamTy covWNativePolyPropCode := by
  refine .pi (.pi (covWNative_sort_observed eqEnvT n Γ ρ .zero)
    (fun _ h => (List.not_mem_nil _ h).elim)
    (fun _ h => (List.not_mem_nil _ h).elim)) ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil _ hu).elim
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact covWNative_sort_observed eqEnvT n _ _ (.succ .zero)

theorem covWNative_poly_value_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative eqEnvT n Γ ρ covXPolyPropLam (.lam [([], .prop)]) :=
  covWNative_empty_lam (fun h => CptWIrrel.noConfusion h)
    (covWNative_sort_observed eqEnvT n _ _ .zero)

theorem covWNative_eq_realized (n stage : Nat) :
    CovWNativeRealized eqEnvT n stage eqGapCtx EnvWIrrel.bot covUEqSubst := by
  refine ⟨covUEqSubst_typed n, ?_⟩
  intro i c hc
  cases hc
  exact ⟨.bot _ _ _, by simp [covWIrrelErase, covTObservationBudget]⟩

def CovWNativeFixtureAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (σ : SubstT) (x y A : Expr Nat) (c a : CptWIrrel) : Prop :=
  CovWEtaFixtureAt E n Γ EnvT.bot σ x y A (covWIrrelErase c) (covWIrrelErase a) ∧
  ApproxTKWNativeStage E n covTFixtureStage Γ EnvWIrrel.bot x c ∧
  ApproxTKWNativeStage E n covTFixtureStage Γ EnvWIrrel.bot A a ∧
  CovWNativeRealized E n covTFixtureStage Γ EnvWIrrel.bot σ

/-- Packaging only: both new observations and the new realizer are inputs. -/
theorem covWNative_fixture_pack {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {σ : SubstT} {x y A : Expr Nat} {c a : CptWIrrel}
    (h : CovWEtaFixtureAt E n Γ EnvT.bot σ x y A (covWIrrelErase c) (covWIrrelErase a))
    (hx : ApproxTKWNative E n Γ EnvWIrrel.bot x c)
    (hA : ApproxTKWNative E n Γ EnvWIrrel.bot A a)
    (hσ : CovWNativeRealized E n covTFixtureStage Γ EnvWIrrel.bot σ) :
    CovWNativeFixtureAt E n Γ σ x y A c a :=
  ⟨h, ⟨hx, h.2.1.2⟩, ⟨hA, h.2.2.1.2⟩, hσ⟩

theorem covWNative_fixture_natSucc_eta (n : Nat) :
    CovWNativeFixtureAt natEnvU n [] SubstT.id
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.lam [([], .spine 2 [] [.bot])]) covWNativeNatArrowCode :=
  covWNative_fixture_pack (covWEta_fixture_natSucc_eta n)
    (covWNative_natEta_empty n [] EnvWIrrel.bot) (covWNative_natArrow_observed n [] EnvWIrrel.bot)
    (covWNative_realized_nil natEnvU n covTFixtureStage)

theorem covWNative_fixture_alias_in_pi (n : Nat) :
    ∃ A B, CovWNativeFixtureAt eqEnvT n eqGapCtx covUEqSubst
      covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
      (.lam [([.pi .bot []], .pi .bot [])]) (.pi .bot []) := by
  obtain ⟨A, B, h⟩ := covWEta_fixture_alias_in_pi n
  exact ⟨A, B, covWNative_fixture_pack h (covWNative_aliasIdentity_observed n _ _)
    (covWNative_pi_nil eqEnvT n _ _ _ _) (covWNative_eq_realized n covTFixtureStage)⟩

theorem covWNative_fixture_polyPropLam (n : Nat) :
    CovWNativeFixtureAt eqEnvT n [] SubstT.id
      covXPolyPropLam covXPolyPropLam covXPolyPropLamTy
      (.lam [([], .prop)]) covWNativePolyPropCode :=
  covWNative_fixture_pack (covWEta_fixture_polyPropLam n)
    (covWNative_poly_value_observed n _ _) (covWNative_poly_type_observed n _ _)
    (covWNative_realized_nil eqEnvT n covTFixtureStage)

theorem covWNative_fixture_alias_extension (n : Nat) :
    ∃ A B,
      Nonempty (CtxWfT eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx)) ∧
      CovWNativeFixtureAt eqEnvT n eqGapCtx covUEqSubst
        idPiProp idPiProp (eqGapDirectAlias A B) (.pi .bot []) .bot := by
  obtain ⟨A, B, hΓ, h⟩ := covWEta_fixture_alias_extension n
  exact ⟨A, B, hΓ, covWNative_fixture_pack h (covWNative_pi_nil eqEnvT n _ _ _ _)
    (.bot _ _ _) (covWNative_eq_realized n covTFixtureStage)⟩

theorem covWNative_fixture_nat_coverage (n : Nat) :
    CovWNativeFixtureAt natEnvU n [] SubstT.id
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 [] []) covWNativeNatArrowCode :=
  covWNative_fixture_pack (covWEta_fixture_nat_coverage n)
    (covWNative_succ_observed n _ _) (covWNative_natArrow_observed n _ _)
    (covWNative_realized_nil natEnvU n covTFixtureStage)

theorem covWNative_fixture_nat_shape (n : Nat) :
    CovWNativeFixtureAt natEnvU n [] SubstT.id
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 [] []) covWNativeNatArrowCode :=
  covWNative_fixture_pack (covWEta_fixture_nat_shape n)
    (covWNative_succ_observed n _ _) (covWNative_natArrow_observed n _ _)
    (covWNative_realized_nil natEnvU n covTFixtureStage)

theorem covWNative_fixture_eq_anchor (n : Nat) :
    CovWNativeFixtureAt eqEnvT n eqGapCtx covUEqSubst
      idPiProp idPiProp (.sort .zero) (.pi .bot []) .prop :=
  covWNative_fixture_pack (covWEta_fixture_eq_anchor n)
    (covWNative_pi_nil eqEnvT n _ _ _ _) (covWNative_sort_observed eqEnvT n _ _ .zero)
    (covWNative_eq_realized n covTFixtureStage)

theorem covWNative_fixture_nat_anchor (n : Nat) :
    CovWNativeFixtureAt natEnvU n [] SubstT.id
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 [] []) (.spine 0 [] []) :=
  covWNative_fixture_pack (covWEta_fixture_nat_anchor n)
    (covWNative_rigid_observed rigidConst_natEnvU_zero not_propCtorT_natEnvU_zero n _ _)
    (covWNative_nat_observed n _ _) (covWNative_realized_nil natEnvU n covTFixtureStage)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_FIXTURES_ROOTS
#print axioms covWNative_rigid_observed
#print axioms covWNative_neutral_observed
#print axioms covWNative_pi_nil
#print axioms covWNative_nat_observed
#print axioms covWNative_succ_observed
#print axioms covWNativeNatArrowCode
#print axioms covWNative_natArrow_observed
#print axioms covWNative_natEta_empty
#print axioms covWNative_aliasIdentity_observed
#print axioms covWNativePolyPropCode
#print axioms covWNative_poly_type_observed
#print axioms covWNative_poly_value_observed
#print axioms covWNative_eq_realized
#print axioms CovWNativeFixtureAt
#print axioms covWNative_fixture_pack
#print axioms covWNative_fixture_natSucc_eta
#print axioms covWNative_fixture_alias_in_pi
#print axioms covWNative_fixture_polyPropLam
#print axioms covWNative_fixture_alias_extension
#print axioms covWNative_fixture_nat_coverage
#print axioms covWNative_fixture_nat_shape
#print axioms covWNative_fixture_eq_anchor
#print axioms covWNative_fixture_nat_anchor
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_FIXTURES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

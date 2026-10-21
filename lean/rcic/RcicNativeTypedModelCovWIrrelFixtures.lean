import rcic.RcicNativeTypedModelCovWIrrelAliasControl
import rcic.RcicNativeTypedModelCovWEtaControls

/-!
# Fresh proof-erasing observations for the eight retained fixtures

The old native/view payload is retained explicitly. Every new observation
and realizer image below is constructed in the new grammar. Packaging a
fixture requires its new observations; no old-to-new embedding is used.
These are local supplies. closure_claim = 0.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelKAudit TypedModelKFragmentAudit TypedModelKTypedBetaAudit
open TypedModelCovNormEscapeAudit TypedModelCovXAudit TypedModelCovXEtaAudit
open TypedModelCovRelBoundaryAudit TypedModelCovYEtaAudit TypedModelCovZAudit
open TypedModelCovPAudit TypedModelCovQAudit TypedModelCovRAudit TypedModelCovSAudit
open TypedModelCovTAudit TypedModelCovVAudit TypedModelCovWAudit TypedModelCovWEtaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit

theorem covWIrrel_rigid_observed {E : ResolvedEnv} {r : Nat}
    (hr : RigidConst E r) (hn : ¬ PropCtorT E r)
    (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel E n Γ ρ (.const r []) (.spine r [] []) :=
  .free (kFreeT_rigid_const hr []) (.const ρ r [] hr hn)

theorem covWIrrel_neutral_observed {E : ResolvedEnv} {r : Nat}
    (hh : NeutralHeadP E r) (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel E n Γ ρ (.const r []) (.spine r [] []) := by
  apply covWIrrel_rigid_observed (neutralHeadP_rigid hh) ?_ n Γ ρ
  rintro ⟨m, fam, fm, hm, hctor, _⟩
  exact neutralHeadP_not_constructor hh hm hctor

theorem covWIrrel_pi_nil (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (A B : Expr Nat) :
    ApproxTKWIrrel E n Γ ρ (.pi A B) (.pi .bot []) :=
  .pi (.bot _ _ _) (fun _ h => (List.not_mem_nil _ h).elim)
    (fun _ h => (List.not_mem_nil _ h).elim)

theorem covWIrrel_nat_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel natEnvU n Γ ρ (.const 0 []) (.spine 0 [] []) :=
  covWIrrel_rigid_observed rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat n Γ ρ

theorem covWIrrel_succ_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel natEnvU n Γ ρ (.const 2 []) (.spine 2 [] []) :=
  covWIrrel_rigid_observed rigidConst_natEnvU_succ not_propCtorT_natEnvU_succ n Γ ρ

def covWIrrelNatArrowCode : CptWIrrel :=
  .pi (.spine 0 [] []) [([], .spine 0 [] [])]

theorem covWIrrel_natArrow_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel natEnvU n Γ ρ (.pi (.const 0 []) (.const 0 [])) covWIrrelNatArrowCode := by
  refine .pi (covWIrrel_nat_observed n Γ ρ) ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil _ hu).elim
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact covWIrrel_nat_observed n _ _

theorem covWIrrel_natEta_empty (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel natEnvU n Γ ρ
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.lam [([], .spine 2 [] [.bot])]) := by
  apply covWIrrel_empty_lam (by intro h; cases h)
  exact covWIrrel_guarded_appSpine_bot (covWIrrel_succ_observed n _ _)

theorem covWIrrel_aliasIdentity_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel eqEnvT n Γ ρ covNormAliasIdentity
      (.lam [([.pi .bot []], .pi .bot [])]) := by
  refine .lam (covWIrrel_sort_observed eqEnvT n Γ ρ .zero) ?_ ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    change CTyS eqEnvT (.pi .bot []) .prop
    rw [CTyS]
    exact Or.inr (.pi .bot (fun _ h => (List.not_mem_nil _ h).elim))
  · exact ⟨_, List.mem_singleton.mpr rfl, fun h => CptWIrrel.noConfusion h⟩
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact .free (kFreeT_bvar eqEnvT 0) (.bvar (List.mem_singleton.mpr rfl))

def covWIrrelPolyPropCode : CptWIrrel := .pi (.pi .prop []) [([], .sort)]

theorem covWIrrel_poly_type_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel eqEnvT n Γ ρ covXPolyPropLamTy covWIrrelPolyPropCode := by
  refine .pi (.pi (covWIrrel_sort_observed eqEnvT n Γ ρ .zero)
    (fun _ h => (List.not_mem_nil _ h).elim)
    (fun _ h => (List.not_mem_nil _ h).elim)) ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil _ hu).elim
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact covWIrrel_sort_observed eqEnvT n _ _ (.succ .zero)

theorem covWIrrel_poly_value_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel eqEnvT n Γ ρ covXPolyPropLam (.lam [([], .prop)]) :=
  covWIrrel_empty_lam (fun h => CptWIrrel.noConfusion h)
    (covWIrrel_sort_observed eqEnvT n _ _ .zero)

theorem covWIrrel_eq_realized (n stage : Nat) :
    CovWIrrelRealized eqEnvT n stage eqGapCtx EnvWIrrel.bot covUEqSubst := by
  refine ⟨covUEqSubst_typed n, ?_⟩
  intro i c hc
  cases hc
  exact ⟨.bot _ _ _, by simp [covWIrrelErase, covTObservationBudget]⟩

def CovWIrrelFixtureAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (σ : SubstT) (x y A : Expr Nat) (c a : CptWIrrel) : Prop :=
  CovWEtaFixtureAt E n Γ EnvT.bot σ x y A (covWIrrelErase c) (covWIrrelErase a) ∧
  ApproxTKWIrrelStage E n covTFixtureStage Γ EnvWIrrel.bot x c ∧
  ApproxTKWIrrelStage E n covTFixtureStage Γ EnvWIrrel.bot A a ∧
  CovWIrrelRealized E n covTFixtureStage Γ EnvWIrrel.bot σ

/-- Packaging only: both new observations and the new realizer are inputs. -/
theorem covWIrrel_fixture_pack {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {σ : SubstT} {x y A : Expr Nat} {c a : CptWIrrel}
    (h : CovWEtaFixtureAt E n Γ EnvT.bot σ x y A (covWIrrelErase c) (covWIrrelErase a))
    (hx : ApproxTKWIrrel E n Γ EnvWIrrel.bot x c)
    (hA : ApproxTKWIrrel E n Γ EnvWIrrel.bot A a)
    (hσ : CovWIrrelRealized E n covTFixtureStage Γ EnvWIrrel.bot σ) :
    CovWIrrelFixtureAt E n Γ σ x y A c a :=
  ⟨h, ⟨hx, h.2.1.2⟩, ⟨hA, h.2.2.1.2⟩, hσ⟩

theorem covWIrrel_fixture_natSucc_eta (n : Nat) :
    CovWIrrelFixtureAt natEnvU n [] SubstT.id
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.lam [([], .spine 2 [] [.bot])]) covWIrrelNatArrowCode :=
  covWIrrel_fixture_pack (covWEta_fixture_natSucc_eta n)
    (covWIrrel_natEta_empty n [] EnvWIrrel.bot) (covWIrrel_natArrow_observed n [] EnvWIrrel.bot)
    (covWIrrel_realized_nil natEnvU n covTFixtureStage)

theorem covWIrrel_fixture_alias_in_pi (n : Nat) :
    ∃ A B, CovWIrrelFixtureAt eqEnvT n eqGapCtx covUEqSubst
      covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
      (.lam [([.pi .bot []], .pi .bot [])]) (.pi .bot []) := by
  obtain ⟨A, B, h⟩ := covWEta_fixture_alias_in_pi n
  exact ⟨A, B, covWIrrel_fixture_pack h (covWIrrel_aliasIdentity_observed n _ _)
    (covWIrrel_pi_nil eqEnvT n _ _ _ _) (covWIrrel_eq_realized n covTFixtureStage)⟩

theorem covWIrrel_fixture_polyPropLam (n : Nat) :
    CovWIrrelFixtureAt eqEnvT n [] SubstT.id
      covXPolyPropLam covXPolyPropLam covXPolyPropLamTy
      (.lam [([], .prop)]) covWIrrelPolyPropCode :=
  covWIrrel_fixture_pack (covWEta_fixture_polyPropLam n)
    (covWIrrel_poly_value_observed n _ _) (covWIrrel_poly_type_observed n _ _)
    (covWIrrel_realized_nil eqEnvT n covTFixtureStage)

theorem covWIrrel_fixture_alias_extension (n : Nat) :
    ∃ A B,
      Nonempty (CtxWfT eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx)) ∧
      CovWIrrelFixtureAt eqEnvT n eqGapCtx covUEqSubst
        idPiProp idPiProp (eqGapDirectAlias A B) (.pi .bot []) .bot := by
  obtain ⟨A, B, hΓ, h⟩ := covWEta_fixture_alias_extension n
  exact ⟨A, B, hΓ, covWIrrel_fixture_pack h (covWIrrel_pi_nil eqEnvT n _ _ _ _)
    (.bot _ _ _) (covWIrrel_eq_realized n covTFixtureStage)⟩

theorem covWIrrel_fixture_nat_coverage (n : Nat) :
    CovWIrrelFixtureAt natEnvU n [] SubstT.id
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 [] []) covWIrrelNatArrowCode :=
  covWIrrel_fixture_pack (covWEta_fixture_nat_coverage n)
    (covWIrrel_succ_observed n _ _) (covWIrrel_natArrow_observed n _ _)
    (covWIrrel_realized_nil natEnvU n covTFixtureStage)

theorem covWIrrel_fixture_nat_shape (n : Nat) :
    CovWIrrelFixtureAt natEnvU n [] SubstT.id
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 [] []) covWIrrelNatArrowCode :=
  covWIrrel_fixture_pack (covWEta_fixture_nat_shape n)
    (covWIrrel_succ_observed n _ _) (covWIrrel_natArrow_observed n _ _)
    (covWIrrel_realized_nil natEnvU n covTFixtureStage)

theorem covWIrrel_fixture_eq_anchor (n : Nat) :
    CovWIrrelFixtureAt eqEnvT n eqGapCtx covUEqSubst
      idPiProp idPiProp (.sort .zero) (.pi .bot []) .prop :=
  covWIrrel_fixture_pack (covWEta_fixture_eq_anchor n)
    (covWIrrel_pi_nil eqEnvT n _ _ _ _) (covWIrrel_sort_observed eqEnvT n _ _ .zero)
    (covWIrrel_eq_realized n covTFixtureStage)

theorem covWIrrel_fixture_nat_anchor (n : Nat) :
    CovWIrrelFixtureAt natEnvU n [] SubstT.id
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 [] []) (.spine 0 [] []) :=
  covWIrrel_fixture_pack (covWEta_fixture_nat_anchor n)
    (covWIrrel_rigid_observed rigidConst_natEnvU_zero not_propCtorT_natEnvU_zero n _ _)
    (covWIrrel_nat_observed n _ _) (covWIrrel_realized_nil natEnvU n covTFixtureStage)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_FIXTURES_ROOTS
#print axioms covWIrrel_rigid_observed
#print axioms covWIrrel_neutral_observed
#print axioms covWIrrel_pi_nil
#print axioms covWIrrel_nat_observed
#print axioms covWIrrel_succ_observed
#print axioms covWIrrelNatArrowCode
#print axioms covWIrrel_natArrow_observed
#print axioms covWIrrel_natEta_empty
#print axioms covWIrrel_aliasIdentity_observed
#print axioms covWIrrelPolyPropCode
#print axioms covWIrrel_poly_type_observed
#print axioms covWIrrel_poly_value_observed
#print axioms covWIrrel_eq_realized
#print axioms CovWIrrelFixtureAt
#print axioms covWIrrel_fixture_pack
#print axioms covWIrrel_fixture_natSucc_eta
#print axioms covWIrrel_fixture_alias_in_pi
#print axioms covWIrrel_fixture_polyPropLam
#print axioms covWIrrel_fixture_alias_extension
#print axioms covWIrrel_fixture_nat_coverage
#print axioms covWIrrel_fixture_nat_shape
#print axioms covWIrrel_fixture_eq_anchor
#print axioms covWIrrel_fixture_nat_anchor
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_FIXTURES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

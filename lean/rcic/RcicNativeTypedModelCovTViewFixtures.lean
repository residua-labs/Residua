import rcic.RcicNativeTypedModelCovTView
import rcic.RcicNativeTypedModelCovTData
import rcic.RcicNativeTypedModelCovSFixtures
import rcic.RcicNativeTypedModelCovSOrigin
import rcic.RcicNativeTypedModelCovSWall4

/-!
# Concrete provenance views at one finite information stage

These supplies construct actual view data. The two raw alias observations
remain shallow, but their views retain the certified native sort readback;
the Pi domain is not replaced by an unknown view. The rich Nat, V and
normalized relevant-function observations retain their recursive children.
Every nonempty row callback below has a closed codomain, so it is supplied
as a function without extracting a function from pointwise Nonempty data.

The eight prior measurement rows are repackaged using only their native
and observation fields. Nat coverage and shape share one actual type view,
as they shared the type observation before. No new semantic joint, general
view supplier, interpretation or native substitution theorem is asserted.
Additional origin controls distinguish variables and literal sort levels,
and the admitted Eq family keeps its actual lambda argument observation in
TyObsArgs. The explicit common information stage is 8; native arity remains
an independent arbitrary parameter. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovTAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelAudit.TypingFin TypedModelKAudit
open TypedModelKFragmentAudit TypedModelKControlAudit TypedModelKTypedBetaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit ReadbackCK2IndexAudit
open TypedModelCovRelBoundaryAudit TypedModelCovRelEscapeAudit
open TypedModelCovNormEscapeAudit TypedModelCovXAudit TypedModelCovXEtaAudit
open TypedModelCovYEtaAudit TypedModelCovZAudit TypedModelCovPAudit
open TypedModelCovRAudit TypedModelCovSAudit

def covTFixtureStage : Nat := 8

def covT_sort_view (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (l : Level) :
    TyObsView E n covTFixtureStage Γ ρ (.sort l) (sortCode l) := by
  refine .sort (.succ l) (.sort Γ l) l (.refl _) ?_
  refine ⟨approxTK_sort_code E n Γ ρ l, ?_⟩
  rcases sortCode_prop_or_sort l with hs | hs <;>
    simp [hs, covTObservationBudget, covTFixtureStage]

/-- A bottom observation does not prevent retaining an independently
supplied native sort head. This is an actual sort constructor. -/
def covT_sort_bot_view (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (l : Level) : TyObsView E n covTFixtureStage Γ ρ (.sort l) .bot :=
  .sort (.succ l) (.sort Γ l) l (.refl _)
    (approxTKStage_bot E n covTFixtureStage Γ ρ (.sort l))

/-- Finite empty-row construction from supplied domain data. -/
def covT_pi_nil_view {E : ResolvedEnv} {n stage : Nat} {Γ : LCtx} {ρ : EnvT}
    {D B : Expr Nat} {d : CptT} (u : Level)
    (hT : HasTyT E n Γ (.pi D B) (.sort u))
    (hD : TyObsView E n stage Γ ρ D d)
    (ho : ApproxTKStage E n stage Γ ρ (.pi D B) (.pi d [])) :
    TyObsView E n stage Γ ρ (.pi D B) (.pi d []) :=
  .pi u hT (.refl _) ho hD
    (fun row _ _ => False.elim (List.not_mem_nil _ row.property))

def covT_nat_view (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    TyObsView natEnvU n covTFixtureStage Γ ρ (.const 0 []) (.spine 0 []) := by
  refine .rigid (.succ .zero) (hasTyT_natEnvU_nat n Γ) 0 [] [] []
    (.refl _) ?_ ?_ (.nil Γ ρ) ?_
  · exact normalR_famAppCK2 natEnvUWfT
      (rfl : natEnvU.members 0 = some natFamMember) rfl Γ [] []
  · exact ⟨.free (kFreeT_natEnvU _)
      (.const ρ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat),
      by simp [covTObservationBudget, covTFixtureStage]⟩
  · exact covT_spine_provenance_of_observed
      (.free (kFreeT_natEnvU _)
        (.const ρ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat))

def covT_nat_bot_view (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    TyObsView natEnvU n covTFixtureStage Γ ρ (.const 0 []) .bot :=
  .rigid (.succ .zero) (hasTyT_natEnvU_nat n Γ) 0 [] [] [] (.refl _)
    (normalR_famAppCK2 natEnvUWfT
      (rfl : natEnvU.members 0 = some natFamMember) rfl Γ [] [])
    (approxTKStage_bot _ _ _ _ _ _) (.nil Γ ρ)
    (covT_spine_provenance_of_observed (.bot Γ ρ (.const 0 [])))

/-- The empty-demand row has the actual closed Nat output for every
admissible native argument, with no row choice or argument extraction. -/
def covT_natArrow_view (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    TyObsView natEnvU n covTFixtureStage Γ ρ
      (.pi (.const 0 []) (.const 0 [])) covYNatArrowCode := by
  refine .pi (.succ .zero) (covSOriginNatArrow_hasTy n Γ) (.refl _)
    ⟨approxTK_covYNatArrowCode n Γ ρ, ?_⟩ (covT_nat_view n Γ ρ) ?_
  · simp [covYNatArrowCode, covTObservationBudget, covTFixtureStage]
  · intro row a _
    rcases row with ⟨row, hrow⟩
    obtain rfl := List.mem_singleton.mp hrow
    exact covT_nat_view n Γ ρ

def covT_idPiProp_view (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    TyObsView E n covTFixtureStage Γ ρ idPiProp (.pi .prop []) := by
  apply covT_pi_nil_view .zero (hasTyT_idPiProp_ctx E n Γ)
    (covT_sort_view E n Γ ρ .zero)
  refine ⟨.pi (approxTK_sort_code E n Γ ρ .zero)
    (fun _ h => (List.not_mem_nil _ h).elim)
    (fun _ h => (List.not_mem_nil _ h).elim), ?_⟩
  simp [sortCode_zero, covTObservationBudget, covTFixtureStage]

def covT_polyProp_view (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    TyObsView eqEnvT n covTFixtureStage Γ ρ covXPolyPropLamTy covSPolyPropCode := by
  refine .pi (.imax .zero (.succ (.succ .zero)))
    (.pi Γ idPiProp .zero (.sort (.succ .zero)) (.succ (.succ .zero))
      (hasTyT_idPiProp_ctx eqEnvT n Γ) (.sort _ (.succ .zero)))
    (.refl _) ⟨covSPolyPropCode_observed n Γ ρ, ?_⟩
    (covT_idPiProp_view eqEnvT n Γ ρ) ?_
  · simp [covSPolyPropCode, covTObservationBudget, covTFixtureStage]
  · intro row a _
    rcases row with ⟨row, hrow⟩
    obtain rfl := List.mem_singleton.mp hrow
    exact covT_sort_view eqEnvT n Γ ρ (.succ .zero)

def covT_propArrow_view (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    TyObsView E n covTFixtureStage Γ ρ covPPropArrow covZPropArrowCode := by
  refine .pi (.succ .zero) (covPPropArrow_hasTy E n Γ) (.refl _)
    ⟨covSPropArrowCode_observed E n Γ ρ, ?_⟩
    (covT_sort_view E n Γ ρ .zero) ?_
  · simp [covZPropArrowCode, covTObservationBudget, covTFixtureStage]
  · intro row a _
    rcases row with ⟨row, hrow⟩
    obtain rfl := List.mem_singleton.mp hrow
    exact covT_sort_view E n Γ ρ .zero

/-- The normalized relevant-function type used by the #7776 replay has
a rich actual view. Its raw alias is not identified with this observation. -/
def covT_relevant_view (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    TyObsView E n covTFixtureStage Γ ρ
      (.pi covPPropArrow (.sort .zero)) covSRelevantCode := by
  refine .pi (.imax (.succ .zero) (.succ .zero))
    (.pi Γ covPPropArrow (.succ .zero) (.sort .zero) (.succ .zero)
      (covPPropArrow_hasTy E n Γ) (.sort _ .zero))
    (.refl _) ⟨covSRelevantCode_observed E n Γ ρ, ?_⟩
    (covT_propArrow_view E n Γ ρ) ?_
  · simp [covSRelevantCode, covZPropArrowCode, covTObservationBudget, covTFixtureStage]
  · intro row a _
    rcases row with ⟨row, hrow⟩
    obtain rfl := List.mem_singleton.mp hrow
    exact covT_sort_view E n Γ ρ .zero

def covT_alias_sort_view (n : Nat) (ρ : EnvT) (A B : Expr Nat) (u : Level)
    (hA : HasTyT eqEnvT n eqGapCtx (eqGapDirectAlias A B) (.sort u)) :
    TyObsView eqEnvT n covTFixtureStage eqGapCtx ρ (eqGapDirectAlias A B) .bot :=
  .sort u hA .zero (eqGapAlias_type_read n A B)
    (approxTKStage_bot _ _ _ _ _ _)

def covT_aliasPi_view (n : Nat) (ρ : EnvT) (A B : Expr Nat) (u : Level)
    (hA : HasTyT eqEnvT n eqGapCtx (eqGapDirectAlias A B) (.sort u)) :
    TyObsView eqEnvT n covTFixtureStage eqGapCtx ρ (covNormAliasPi A B)
      (.pi .bot []) := by
  apply covT_pi_nil_view (.imax u (.succ .zero))
    (.pi eqGapCtx (eqGapDirectAlias A B) u (.sort .zero) (.succ .zero)
      hA (.sort _ .zero))
    (covT_alias_sort_view n ρ A B u hA)
  exact ⟨approxTK_pi_bot_nil _ _ _ _ _ _,
    by simp [covTObservationBudget, covTFixtureStage]⟩

/-- Native/model evidence plus an actual type view. There is no candidate
relation field in this first-gate fixture package. -/
def CovTTypeFixtureAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (x y A : Expr Nat) (c a : CptT) : Prop :=
  Nonempty (EnvWfT E) ∧ Nonempty (CtxWfT E n Γ) ∧
  EnvTypedFinAtT (ctxModelT_approxTK E n Γ) Γ ρ ∧
  CtxEnvM (ctxModelT_approxTK E n Γ) Γ ρ ∧
  Nonempty (HasTyT E n Γ x A) ∧ Nonempty (HasTyT E n Γ y A) ∧
  Nonempty (ConvT E n Γ x y A) ∧
  ApproxTKStage E n covTFixtureStage Γ ρ x c ∧ c ≠ .bot ∧
  Nonempty (TyObsView E n covTFixtureStage Γ ρ A a)

theorem covT_typeFixture_of_S {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {x y A : Expr Nat} {c a : CptT}
    (h : CovSFixtureAt E n Γ ρ x y A c a)
    (hρ : EnvTypedFinAtT (ctxModelT_approxTK E n Γ) Γ ρ)
    (hctx : CtxEnvM (ctxModelT_approxTK E n Γ) Γ ρ)
    (hbudget : covTObservationBudget c ≤ covTFixtureStage)
    (hv : Nonempty (TyObsView E n covTFixtureStage Γ ρ A a)) :
    CovTTypeFixtureAt E n Γ ρ x y A c a := by
  obtain ⟨hW, hΓ, hx, hy, hc, ho, hnb, _⟩ := h
  exact ⟨hW, hΓ, hρ, hctx, hx, hy, hc, ⟨ho, hbudget⟩, hnb, hv⟩

theorem covT_fixture_bot_env_typed (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    EnvTypedFinAtT (ctxModelT_approxTK E n Γ) Γ EnvT.bot :=
  envTypedFinAtT_bot _ (fun ρ e => ApproxTK.bot Γ ρ e) Γ

theorem covT_fixture_nil_coherent (E : ResolvedEnv) (n : Nat) :
    CtxEnvM (ctxModelT_approxTK E n []) [] EnvT.bot := by
  intro i v hv
  exact Option.noConfusion hv

theorem covT_fixture_natSucc_eta (n : Nat) :
    CovTTypeFixtureAt natEnvU n [] EnvT.bot
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      covXNatEtaEmptyRow covYNatArrowCode :=
  covT_typeFixture_of_S (covS_fixture_natSucc_eta n).2
    (covT_fixture_bot_env_typed _ _ _) (covT_fixture_nil_coherent _ _)
    (by simp [covXNatEtaEmptyRow, covTObservationBudget, covTFixtureStage])
    ⟨covT_natArrow_view n [] EnvT.bot⟩

theorem covT_fixture_alias_in_pi (n : Nat) :
    ∃ A B, CovTTypeFixtureAt eqEnvT n eqGapCtx EnvT.bot
      covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
      covNormAliasIdentityCpt (.pi .bot []) := by
  obtain ⟨A, B, _, _, _, h⟩ := covS_fixture_alias_in_pi_fallback n
  obtain ⟨hW⟩ := h.1
  obtain ⟨hΓ⟩ := h.2.1
  obtain ⟨hx⟩ := h.2.2.1
  obtain ⟨_, hPi⟩ := tySort hW hΓ hx
  obtain ⟨u, _, hA, _, _⟩ := hasTyTInv_pi hPi rfl
  exact ⟨A, B, covT_typeFixture_of_S h
    (covT_fixture_bot_env_typed _ _ _) (envTypedCovAtM_eqGap_bot n).2
    (by simp [covNormAliasIdentityCpt, covTObservationBudget, covTFixtureStage])
    ⟨covT_aliasPi_view n EnvT.bot A B u hA⟩⟩

theorem covT_fixture_polyPropLam (n : Nat) :
    CovTTypeFixtureAt eqEnvT n [] EnvT.bot covXPolyPropLam covXPolyPropLam
      covXPolyPropLamTy (.lam [([], .prop)]) covSPolyPropCode :=
  covT_typeFixture_of_S (covS_fixture_polyPropLam n).2
    (covT_fixture_bot_env_typed _ _ _) (covT_fixture_nil_coherent _ _)
    (by simp [covTObservationBudget, covTFixtureStage])
    ⟨covT_polyProp_view n [] EnvT.bot⟩

theorem covT_fixture_alias_extension (n : Nat) :
    ∃ A B,
      Nonempty (CtxWfT eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx)) ∧
      CovTTypeFixtureAt eqEnvT n eqGapCtx EnvT.bot
        idPiProp idPiProp (eqGapDirectAlias A B) (.pi .bot []) .bot := by
  obtain ⟨A, B, _, hΓext, _, _, _, h⟩ := covS_fixture_alias_extension_fallback n
  obtain ⟨hW⟩ := h.1
  obtain ⟨hΓ⟩ := h.2.1
  obtain ⟨hx⟩ := h.2.2.1
  obtain ⟨u, hA⟩ := tySort hW hΓ hx
  exact ⟨A, B, hΓext, covT_typeFixture_of_S h
    (covT_fixture_bot_env_typed _ _ _) (envTypedCovAtM_eqGap_bot n).2
    (by simp [covTObservationBudget, covTFixtureStage])
    ⟨covT_alias_sort_view n EnvT.bot A B u hA⟩⟩

theorem covT_fixture_nat_coverage (n : Nat) :
    CovTTypeFixtureAt natEnvU n [] EnvT.bot (.const 2 []) (.const 2 [])
      (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) covYNatArrowCode :=
  covT_typeFixture_of_S (covS_fixture_nat_coverage_shape n).2.2.2
    (covT_fixture_bot_env_typed _ _ _) (covT_fixture_nil_coherent _ _)
    (by simp [covTObservationBudget, covTFixtureStage])
    ⟨covT_natArrow_view n [] EnvT.bot⟩

/-- The prior shape row uses the same actual Nat type observation as the
coverage row. This is not counted as a second general supplier. -/
theorem covT_fixture_nat_shape (n : Nat) :
    CovTTypeFixtureAt natEnvU n [] EnvT.bot (.const 2 []) (.const 2 [])
      (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) covYNatArrowCode :=
  covT_fixture_nat_coverage n

theorem covT_fixture_eq_anchor (n : Nat) :
    CovTTypeFixtureAt eqEnvT n eqGapCtx EnvT.bot
      idPiProp idPiProp (.sort .zero) (.pi .bot []) .prop :=
  covT_typeFixture_of_S (covS_fixture_eq_anchor n).2
    (covT_fixture_bot_env_typed _ _ _) (envTypedCovAtM_eqGap_bot n).2
    (by simp [covTObservationBudget, covTFixtureStage])
    ⟨covT_sort_view eqEnvT n eqGapCtx EnvT.bot .zero⟩

theorem covT_fixture_nat_anchor (n : Nat) :
    CovTTypeFixtureAt natEnvU n [] EnvT.bot
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) (.spine 0 []) :=
  covT_typeFixture_of_S (covS_fixture_nat_anchor n).2
    (covT_fixture_bot_env_typed _ _ _) (covT_fixture_nil_coherent _ _)
    (by simp [covTObservationBudget, covTFixtureStage])
    ⟨covT_nat_view n [] EnvT.bot⟩

def covT_origin_var0_view (E : ResolvedEnv) (n : Nat) :
    TyObsView E n covTFixtureStage covSOriginCtx covSOriginEnv (.bvar 0) .prop :=
  .var (.succ .zero) (covSOrigin_var0_hasTy E n) 0 [] [] (.refl _)
    (normalR_bvarCK2 rfl)
    ⟨covSOrigin_var0_observed E n, by simp [covTObservationBudget, covTFixtureStage]⟩
    (.nil _ _)
    (covT_spine_provenance_of_observed (covSOrigin_var0_observed E n))

def covT_origin_var1_view (E : ResolvedEnv) (n : Nat) :
    TyObsView E n covTFixtureStage covSOriginCtx covSOriginEnv (.bvar 1) .prop :=
  .var (.succ .zero) (covSOrigin_var1_hasTy E n) 1 [] [] (.refl _)
    (normalR_bvarCK2 rfl)
    ⟨covSOrigin_var1_observed E n, by simp [covTObservationBudget, covTFixtureStage]⟩
    (.nil _ _)
    (covT_spine_provenance_of_observed (covSOrigin_var1_observed E n))

def covT_origin_literal_domain_view (E : ResolvedEnv) (n : Nat) :
    TyObsView E n covTFixtureStage covSOriginCtx covSOriginEnv
      covPPropArrow (.pi .prop []) :=
  covT_pi_nil_view (.succ .zero) (covPPropArrow_hasTy E n covSOriginCtx)
    (covT_sort_view E n covSOriginCtx covSOriginEnv .zero)
    ⟨(covSOrigin_prop_domain_observations E n).2.2.1,
      by simp [covTObservationBudget, covTFixtureStage]⟩

def covT_origin_variable_domain_view (E : ResolvedEnv) (n : Nat) :
    TyObsView E n covTFixtureStage covSOriginCtx covSOriginEnv
      covSOriginVarArrow (.pi .prop []) :=
  covT_pi_nil_view (.succ .zero) (covSOriginVarArrow_hasTy E n)
    (covT_origin_var0_view E n)
    ⟨(covSOrigin_prop_domain_observations E n).2.2.2,
      by simp [covTObservationBudget, covTFixtureStage]⟩

def covT_origin_sort_bot_domain_view (n : Nat) :
    TyObsView natEnvU n covTFixtureStage [] EnvT.bot covPPropArrow (.pi .bot []) :=
  covT_pi_nil_view (.succ .zero) (covPPropArrow_hasTy natEnvU n [])
    (covT_sort_bot_view natEnvU n [] EnvT.bot .zero)
    ⟨(covSOrigin_pi_observations n).1,
      by simp [covTObservationBudget, covTFixtureStage]⟩

def covT_origin_nat_bot_domain_view (n : Nat) :
    TyObsView natEnvU n covTFixtureStage [] EnvT.bot covSOriginNatArrow (.pi .bot []) :=
  covT_pi_nil_view (.succ .zero) (covSOriginNatArrow_hasTy n [])
    (covT_nat_bot_view n [] EnvT.bot)
    ⟨(covSOrigin_pi_observations n).2,
      by simp [covTObservationBudget, covTFixtureStage]⟩

/-- The colliding compact observations now coexist with their distinct
native variable origins, in the same actual typed and coherent valuation. -/
theorem covT_origin_variable_control (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n covSOriginCtx) ∧
    EnvTypedFinAtT (ctxModelT_approxTK emptyEnv n covSOriginCtx)
      covSOriginCtx covSOriginEnv ∧
    CtxEnvM (ctxModelT_approxTK emptyEnv n covSOriginCtx) covSOriginCtx covSOriginEnv ∧
    Nonempty (TyObsView emptyEnv n covTFixtureStage covSOriginCtx covSOriginEnv
      (.bvar 0) .prop) ∧
    Nonempty (TyObsView emptyEnv n covTFixtureStage covSOriginCtx covSOriginEnv
      (.bvar 1) .prop) :=
  ⟨⟨.empty⟩, ⟨covSOriginCtx_wf emptyEnv n⟩,
    covSOrigin_env_typed emptyEnv n, covSOrigin_ctx_coherent emptyEnv n,
    ⟨covT_origin_var0_view emptyEnv n⟩, ⟨covT_origin_var1_view emptyEnv n⟩⟩

theorem covT_origin_sort_level_control (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (TyObsView emptyEnv n covTFixtureStage [] EnvT.bot
      (.sort (.succ .zero)) .sort) ∧
    Nonempty (TyObsView emptyEnv n covTFixtureStage [] EnvT.bot
      (.sort (.succ (.succ .zero))) .sort) :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨covT_sort_view emptyEnv n [] EnvT.bot (.succ .zero)⟩,
    ⟨covT_sort_view emptyEnv n [] EnvT.bot (.succ (.succ .zero))⟩⟩

/-- The exact native arguments and the exact observed lambda table are
retained. No type-head grammar is imposed on a term argument. -/
def covT_rigid_lambda_args (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    TyObsArgs eqEnvT n covTFixtureStage Γ ρ
      [indexFn, indexId, indexId] [.bot, covTLambdaArg, .bot] :=
  .cons (approxTKStage_bot _ _ _ _ _ _)
    (.cons ⟨covT_indexId_observed eqEnvT n Γ ρ,
      by simp [covTLambdaArg, covTProbe, covTObservationBudget, covTFixtureStage]⟩
      (.cons (approxTKStage_bot _ _ _ _ _ _) (.nil Γ ρ)))

def covT_rigid_lambda_view (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    TyObsView eqEnvT n covTFixtureStage Γ ρ covTRigidType covTRigidTypeCode :=
  .rigid .zero (covTRigidType_hasTy n Γ) 63 []
    [indexFn, indexId, indexId] [.bot, covTLambdaArg, .bot]
    (.refl _) (covTRigidType_normal n Γ)
    ⟨covTRigidType_observed n Γ ρ,
      by simp [covTRigidTypeCode, covTObservationBudget, covTFixtureStage]⟩
    (covT_rigid_lambda_args n Γ ρ)
    (covT_spine_provenance_of_observed (covTRigidType_observed n Γ ρ))

def covT_wrapped_lambda_view (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    TyObsView eqEnvT n covTFixtureStage Γ ρ covTWrappedType covTWrappedTypeCode :=
  covT_pi_nil_view (.succ .zero) (covTWrappedType_hasTy n Γ)
    (covT_rigid_lambda_view n Γ ρ)
    ⟨covTWrappedType_observed n Γ ρ,
      by simp [covTWrappedTypeCode, covTRigidTypeCode,
        covTObservationBudget, covTFixtureStage]⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_T_VIEW_FIXTURES_ROOTS
#print axioms covTFixtureStage
#print axioms covT_sort_view
#print axioms covT_sort_bot_view
#print axioms covT_pi_nil_view
#print axioms covT_nat_view
#print axioms covT_nat_bot_view
#print axioms covT_natArrow_view
#print axioms covT_idPiProp_view
#print axioms covT_polyProp_view
#print axioms covT_propArrow_view
#print axioms covT_relevant_view
#print axioms covT_alias_sort_view
#print axioms covT_aliasPi_view
#print axioms CovTTypeFixtureAt
#print axioms covT_typeFixture_of_S
#print axioms covT_fixture_bot_env_typed
#print axioms covT_fixture_nil_coherent
#print axioms covT_fixture_natSucc_eta
#print axioms covT_fixture_alias_in_pi
#print axioms covT_fixture_polyPropLam
#print axioms covT_fixture_alias_extension
#print axioms covT_fixture_nat_coverage
#print axioms covT_fixture_nat_shape
#print axioms covT_fixture_eq_anchor
#print axioms covT_fixture_nat_anchor
#print axioms covT_origin_var0_view
#print axioms covT_origin_var1_view
#print axioms covT_origin_literal_domain_view
#print axioms covT_origin_variable_domain_view
#print axioms covT_origin_sort_bot_domain_view
#print axioms covT_origin_nat_bot_domain_view
#print axioms covT_origin_variable_control
#print axioms covT_origin_sort_level_control
#print axioms covT_rigid_lambda_args
#print axioms covT_rigid_lambda_view
#print axioms covT_wrapped_lambda_view
-- END RCIC_NATIVE_TYPED_MODEL_COV_T_VIEW_FIXTURES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovTAudit

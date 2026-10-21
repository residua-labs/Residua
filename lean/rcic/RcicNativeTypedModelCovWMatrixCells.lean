import rcic.RcicNativeTypedModelCovWMatrixCore
import rcic.RcicNativeTypedModelCovWMatrixLiteral
import rcic.RcicNativeTypedModelCovWMatrixRawDelta
import rcic.RcicNativeTypedModelCovWMatrixIotaHead
import rcic.RcicNativeTypedModelCovWMatrixMajorIrrel
import rcic.RcicNativeTypedModelCovWMatrixFunctionCells
import rcic.RcicNativeTypedModelCovWMatrixRawEtaHead
import rcic.RcicNativeTypedModelCovWIrrelFullProofEquality

/-!
# Matrix interfaces for the measured cells

These declarations put the concrete results at the same shared-type-code
interface. Finite-demand transport is a composition theorem, not an inverse
substitution supply. In particular, the raw delta/literal context results
are not promoted to guarded context results. The proof-field theorem is
the supplied axiom-family fixture, not a universal native irr theorem.

The structured ordinary-iota result is a CK2 step; no legacy ConvT.iota
certificate is claimed. Native K and proof-major irr have their actual
native conversion evidence in the imported inhabited bundles.
closure_claim = 0.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelCovTAudit TypedModelCovWIrrelAudit
open ReadbackCKAudit ReadbackCK2IndexAudit

theorem covWMatrix_K_head_not_invariant (n : Nat) :
    ¬ CovWMatrixTypedInvariant eqEnvT n etaEqCtx EnvWIrrel.bot
      (.sort (.succ .zero)) etaIndexRedex (.sort .zero) := by
  intro h
  exact covWMatrix_K_source_excluded n EnvWIrrel.bot
    ((h .sort .prop (covWMatrix_K_type_observed n)
      covWMatrix_K_compact_typed).mpr (covWMatrix_K_rhs_observed n))

theorem covWMatrix_structured_iota_head_not_invariant (n : Nat) :
    ¬ CovWMatrixTypedInvariant covUHoEnv n [] EnvWIrrel.bot
      (.sort (.succ .zero)) covWMatrixIotaSource covWMatrixIotaTarget := by
  intro h
  exact covWMatrix_iota_source_excluded n [] EnvWIrrel.bot
    ((h .sort .prop
      (covWIrrel_observation_of
        (covWIrrel_sort_observed covUHoEnv n [] EnvWIrrel.bot (.succ .zero)))
      covWMatrix_iota_compact_typed).mpr
        (covWIrrel_observation_of (covWMatrix_iota_rhs_observed n [] EnvWIrrel.bot)))

theorem covWMatrix_irr_major_not_invariant (n : Nat) :
    ¬ CovWMatrixTypedInvariant eqEnvT n etaEqCtx EnvWIrrel.bot
      (.sort (.succ .zero)) etaIndexRedex covWMatrixMajorCtorCall := by
  intro h
  exact covWMatrix_K_source_excluded n EnvWIrrel.bot
    ((h .sort .prop (covWMatrix_K_type_observed n)
      covWMatrix_K_compact_typed).mpr
        (covWIrrel_observation_of (covWMatrix_major_ctor_observed n EnvWIrrel.bot)))

/-- Literal HEAD equality is general, even without a native typing restriction. -/
theorem covWMatrix_literal_head_invariant (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvWIrrel) (A : Expr Nat) (t : Nat) :
    CovWMatrixTypedInvariant E n Γ ρ A (.lit t) (natExpand t) :=
  covWMatrix_invariant_of_observation_equality
    (covWMatrix_literal_observation_iff E n Γ ρ t)

/-- This is the exact previously supplied proof-field fixture. -/
theorem covWMatrix_irr_proof_field_fixture_invariant (n : Nat)
    (Γ : LCtx) (hΓ : CtxWfT covWIrrelEnv n Γ) (ρ : EnvWIrrel) :
    CovWMatrixTypedInvariant covWIrrelEnv n Γ ρ (.sort .zero)
      covWIrrelLeft covWIrrelRight :=
  covWMatrix_invariant_of_observation_equality
    (covWIrrel_family_all_public_observations_equal n Γ hΓ ρ)

/-- Binder demands are a finite test, not another syntactic context. -/
def CovWMatrixFiniteDemands (Obs : Expr Nat → CptT → Prop)
    (U : List CptT) (e : Expr Nat) : Prop :=
  ∀ c ∈ U, Obs e c

theorem covWMatrix_finite_demands_congr
    {Obs : Expr Nat → CptT → Prop} {left right : Expr Nat}
    (heq : ∀ c, Obs left c ↔ Obs right c) (U : List CptT) :
    CovWMatrixFiniteDemands Obs U left ↔ CovWMatrixFiniteDemands Obs U right := by
  constructor
  · intro h c hc
    exact (heq c).mp (h c hc)
  · intro h c hc
    exact (heq c).mpr (h c hc)

theorem covWMatrix_typed_finite_demands_congr {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : EnvWIrrel} {A left right : Expr Nat}
    (hi : CovWMatrixTypedInvariant E n Γ ρ A left right)
    {a : CptT} (ha : CovWIrrelObservation E n Γ ρ A a)
    (U : List CptT) (hU : ∀ c ∈ U, CTyS E c a) :
    CovWMatrixFiniteDemands (CovWIrrelObservation E n Γ ρ) U left ↔
      CovWMatrixFiniteDemands (CovWIrrelObservation E n Γ ρ) U right := by
  constructor
  · intro h c hc
    exact (hi a c ha (hU c hc)).mp (h c hc)
  · intro h c hc
    exact (hi a c ha (hU c hc)).mpr (h c hc)

theorem covWMatrix_literal_binder_demands (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvWIrrel) (t : Nat) (U : List CptT) :
    CovWMatrixFiniteDemands (CovWIrrelObservation E n Γ ρ) U (.lit t) ↔
      CovWMatrixFiniteDemands (CovWIrrelObservation E n Γ ρ) U (natExpand t) :=
  covWMatrix_finite_demands_congr (covWMatrix_literal_observation_iff E n Γ ρ t) U

theorem covWMatrix_raw_literal_binder_demands (E : ResolvedEnv) (n : Nat)
    (ρ : EnvWIrrel) (t : Nat) (U : List CptT) :
    CovWMatrixFiniteDemands (CovWIrrelRawObservation E n ρ) U (.lit t) ↔
      CovWMatrixFiniteDemands (CovWIrrelRawObservation E n ρ) U (natExpand t) :=
  covWMatrix_finite_demands_congr
    (covWMatrix_raw_eq_erased (covWMatrix_raw_literal_eq E n t) ρ) U

theorem covWMatrix_raw_eq_binder_demands {E : ResolvedEnv} {n : Nat}
    {left right : Expr Nat} (heq : CovWMatrixRawEq E n left right)
    (ρ : EnvWIrrel) (U : List CptT) :
    CovWMatrixFiniteDemands (CovWIrrelRawObservation E n ρ) U left ↔
      CovWMatrixFiniteDemands (CovWIrrelRawObservation E n ρ) U right :=
  covWMatrix_finite_demands_congr (covWMatrix_raw_eq_erased heq ρ) U

/-- A singleton finite test detects exactly its one observation. -/
theorem covWMatrix_finite_demands_singleton
    (Obs : Expr Nat → CptT → Prop) (e : Expr Nat) (c : CptT) :
    CovWMatrixFiniteDemands Obs [c] e ↔ Obs e c := by
  constructor
  · intro h
    exact h c (by simp)
  · intro h d hd
    rcases List.mem_singleton.mp hd with rfl
    exact h

/-- The negative singleton test is supplied, not merely hypothesized. -/
theorem covWMatrix_closed_failure_binder_test {E : ResolvedEnv}
    {n stage : Nat} {left right A : Expr Nat} {u : Level} {c a : CptT}
    (h : CovWMatrixClosedFailure E n stage left right A u c a) :
    (∀ d ∈ [c], CTyS E d a) ∧
    CovWMatrixFiniteDemands (CovWIrrelObservation E n [] EnvWIrrel.bot) [c] right ∧
    ¬ CovWMatrixFiniteDemands (CovWIrrelObservation E n [] EnvWIrrel.bot) [c] left := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rcases List.mem_singleton.mp hd with rfl
    exact h.demand
  · exact (covWMatrix_finite_demands_singleton _ _ _).mpr h.rightObserved
  · intro hl
    exact h.leftAbsent ((covWMatrix_finite_demands_singleton _ _ _).mp hl)

theorem covWMatrix_beta_binder_test (n : Nat) :
    (∀ d ∈ [covWFunctionFine], CTyS covWFunctionEnv d .prop) ∧
    CovWMatrixFiniteDemands
      (CovWIrrelObservation covWFunctionEnv n [] EnvWIrrel.bot)
      [covWFunctionFine] covWFunctionTarget ∧
    ¬ CovWMatrixFiniteDemands
      (CovWIrrelObservation covWFunctionEnv n [] EnvWIrrel.bot)
      [covWFunctionFine] covWFunctionBetaSource :=
  covWMatrix_closed_failure_binder_test (covWMatrix_beta_head_failure n)

theorem covWMatrix_zeta_binder_test (n : Nat) :
    (∀ d ∈ [covWFunctionFine], CTyS covWFunctionEnv d .prop) ∧
    CovWMatrixFiniteDemands
      (CovWIrrelObservation covWFunctionEnv n [] EnvWIrrel.bot)
      [covWFunctionFine] covWFunctionTarget ∧
    ¬ CovWMatrixFiniteDemands
      (CovWIrrelObservation covWFunctionEnv n [] EnvWIrrel.bot)
      [covWFunctionFine] covWFunctionLetSource :=
  covWMatrix_closed_failure_binder_test (covWMatrix_zeta_head_failure n)

/-- This is the native eta generator placed in `G [-]`, then tested once.
It does not assert a failure for the bare eta pair at its own Pi type. -/
theorem covWMatrix_contextual_eta_binder_test (n : Nat) :
    (∀ d ∈ [covWFunctionFine], CTyS covWFunctionEnv d .prop) ∧
    CovWMatrixFiniteDemands
      (CovWIrrelObservation covWFunctionEnv n [] EnvWIrrel.bot)
      [covWFunctionFine] covWFunctionTarget ∧
    ¬ CovWMatrixFiniteDemands
      (CovWIrrelObservation covWFunctionEnv n [] EnvWIrrel.bot)
      [covWFunctionFine] covWFunctionEtaSource :=
  covWMatrix_closed_failure_binder_test (covWMatrix_eta_argument_failure n)

theorem covWMatrix_K_binder_test (n : Nat) :
    CTyS eqEnvT .prop .sort ∧
    CovWMatrixFiniteDemands (CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot)
      [.prop] (.sort .zero) ∧
    ¬ CovWMatrixFiniteDemands (CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot)
      [.prop] etaIndexRedex := by
  refine ⟨covWMatrix_K_compact_typed,
    (covWMatrix_finite_demands_singleton _ _ _).mpr (covWMatrix_K_rhs_observed n), ?_⟩
  intro h
  exact covWMatrix_K_source_excluded n EnvWIrrel.bot
    ((covWMatrix_finite_demands_singleton _ _ _).mp h)

/-- Positive proposition-code demands collapse at the demand interface.
This does not assert that every native proposition has supplied such a code. -/
theorem covWMatrix_positive_code_demands (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvWIrrel) (left right : Expr Nat)
    {a c : CptT} (hP : IsPropCT E a) (hc : CTyS E c a) :
    CovWIrrelObservation E n Γ ρ left c ↔
      CovWIrrelObservation E n Γ ρ right c := by
  have hb := ctyT_prop_bot hP (ctyT_of_ctyS a c hc)
  subst c
  exact ⟨fun _ => ⟨.bot, rfl, .bot _ _ _⟩,
    fun _ => ⟨.bot, rfl, .bot _ _ _⟩⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_CELLS_ROOTS
#print axioms covWMatrix_K_head_not_invariant
#print axioms covWMatrix_structured_iota_head_not_invariant
#print axioms covWMatrix_irr_major_not_invariant
#print axioms covWMatrix_literal_head_invariant
#print axioms covWMatrix_irr_proof_field_fixture_invariant
#print axioms CovWMatrixFiniteDemands
#print axioms covWMatrix_finite_demands_congr
#print axioms covWMatrix_typed_finite_demands_congr
#print axioms covWMatrix_literal_binder_demands
#print axioms covWMatrix_raw_literal_binder_demands
#print axioms covWMatrix_raw_eq_binder_demands
#print axioms covWMatrix_finite_demands_singleton
#print axioms covWMatrix_closed_failure_binder_test
#print axioms covWMatrix_beta_binder_test
#print axioms covWMatrix_zeta_binder_test
#print axioms covWMatrix_contextual_eta_binder_test
#print axioms covWMatrix_K_binder_test
#print axioms covWMatrix_positive_code_demands
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_CELLS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit

import rcic.RcicNativeTypedModelCovTView
import rcic.RcicNativeTypedModelCovTRecursor

/-!
# A supplied stage-three provenance view of the neutral Nat recursor

This fixture supplies an actual Type-valued view of the native Sort-1 type
from CovTRecursor. Its constant-head readback retains the four native
arguments and their actual observations `[bot, bot, minorCode, majorCode]`.
The nonbottom minor table has budget three; the type observation, the major
observation, and the observed term `y : A` all fit the same budget.

The view also carries the actual source spine-observation trace, obtained
from the supplied raw observation. Its argument records preserve the actual
minor and major observations used above. This does not identify every stored
compact node with a native subexpression or prove general readback transport.
It supplies no general view theorem or interpreter. The existing rigid-data predicate rejects the
actual term observation, while both the existing total predicate and the
existing exact Prop-universe leaf accept it. That comparison is specific to
those predicates and does not refute arbitrary provenance interpretations.
The parameter `n` remains universe-parameter arity. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovTAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit TypedModelKFragmentAudit ReadbackCK2Audit
open TypedModelCovRAudit TypedModelCovSAudit

theorem covTRec_minor_stage3 (n : Nat) :
    ApproxTKStage natEnvU n 3 covTRecExtCtx covTRecExtEnv
      covTRecMinor covTRecMinorCode := by
  refine ⟨.free (kFreeT_natEnvU _) (covTRecMinor_observed covTRecExtEnv), ?_⟩
  simp [covTRecMinorCode, covTObservationBudget]

theorem covTRec_major_stage3 (n : Nat) :
    ApproxTKStage natEnvU n 3 covTRecExtCtx covTRecExtEnv
      (.bvar 1) covTRecMajorCode := by
  refine ⟨.free (kFreeT_bvar natEnvU 1) (.bvar rfl), ?_⟩
  simp [covTRecMajorCode, covTObservationBudget]

theorem covTRec_type_stage3 (n : Nat) :
    ApproxTKStage natEnvU n 3 covTRecExtCtx covTRecExtEnv
      (covTRecTypeAt 1) .prop := by
  exact ⟨covTRecTypeAt_observed n _ _ 1 rfl, by simp [covTObservationBudget]⟩

theorem covTRec_y_stage3 (n : Nat) :
    ApproxTKStage natEnvU n 3 covTRecExtCtx covTRecExtEnv (.bvar 0) covTProbe := by
  exact ⟨covTRec_ext_y_observed n, by simp [covTProbe, covTObservationBudget]⟩

/-- These four records use the actual native arguments of the head and
the minor/major observations used in its supplied model derivation. -/
def covTRec_args_stage3 (n : Nat) :
    TyObsArgs natEnvU n 3 covTRecExtCtx covTRecExtEnv
      [covTRecMotive, .sort .zero, covTRecMinor, .bvar 1]
      [.bot, .bot, covTRecMinorCode, covTRecMajorCode] :=
  .cons (approxTKStage_bot _ _ _ _ _ covTRecMotive)
    (.cons (approxTKStage_bot _ _ _ _ _ (.sort .zero))
      (.cons (covTRec_minor_stage3 n)
        (.cons (covTRec_major_stage3 n) (.nil _ _))))

/-- A concrete constructed view, with no choice of witnesses from Prop. -/
def covTRec_view_stage3 (n : Nat) :
    TyObsView natEnvU n 3 covTRecExtCtx covTRecExtEnv (covTRecTypeAt 1) .prop :=
  .rigid (.succ .zero)
    (covTRecTypeAt_hasTy n _ 1 (.bvar _ 1 _ rfl))
    3 [.succ (.succ .zero)]
    [covTRecMotive, .sort .zero, covTRecMinor, .bvar 1]
    [.bot, .bot, covTRecMinorCode, covTRecMajorCode]
    (covTRecTypeAt_head n _ 1)
    (covTRecTypeAt_normal n _ 1 rfl)
    (covTRec_type_stage3 n) (covTRec_args_stage3 n)
    (covT_spine_provenance_of_observed
      (covTRecTypeAt_observed n covTRecExtCtx covTRecExtEnv 1 rfl))

def covTRec_unknown_view_stage3 (n : Nat) :
    TyObsView natEnvU n 3 covTRecExtCtx covTRecExtEnv (covTRecTypeAt 1) .bot :=
  .unknown (.succ .zero) (covTRecTypeAt_hasTy n _ 1 (.bvar _ 1 _ rfl))

theorem covTRec_view_universe (n : Nat) :
    (covTRec_view_stage3 n).universe = .succ .zero := rfl

/-- This is the tag of the supplied Sort-1 typing. It is not a theorem
that the native type has no other typing derivation at Prop. -/
theorem covTRec_view_not_positive (n : Nat) :
    (covTRec_view_stage3 n).positive = false := by
  change decEqN (.succ .zero) .zero = false
  decide

theorem covTRec_motive_admissible (n : Nat) :
    CovTAdmissible natEnvU n 3 covTRecExtCtx covTRecExtEnv
      (.pi (.const 0 []) (.sort (.succ (.succ .zero)))) covTRecMotive [] :=
  ⟨⟨covTRecMotive_hasTy n _⟩, fun _ h => (List.not_mem_nil _ h).elim⟩

theorem covTRec_zero_admissible (n : Nat) :
    CovTAdmissible natEnvU n 3 covTRecExtCtx covTRecExtEnv
      (.app covTRecMotive (.const 1 [])) (.sort .zero) [] :=
  ⟨⟨covTRecProp_hasTy n _ (.const 1 []) (hasTyT_natEnvU_zero n _)⟩,
    fun _ h => (List.not_mem_nil _ h).elim⟩

theorem covTRec_minor_admissible (n : Nat) :
    CovTAdmissible natEnvU n 3 covTRecExtCtx covTRecExtEnv
      covTRecMinorTy covTRecMinor [covTRecMinorCode] := by
  refine ⟨⟨covTRecMinor_hasTy n _⟩, ?_⟩
  intro c hc
  obtain rfl := List.mem_singleton.mp hc
  exact covTRec_minor_stage3 n

theorem covTRec_major_admissible (n : Nat) :
    CovTAdmissible natEnvU n 3 covTRecExtCtx covTRecExtEnv
      (.const 0 []) (.bvar 1) [covTRecMajorCode] := by
  refine ⟨⟨.bvar _ 1 _ rfl⟩, ?_⟩
  intro c hc
  obtain rfl := List.mem_singleton.mp hc
  exact covTRec_major_stage3 n

/-- All type, term, view, argument, environment, and stage premises of
the leaf comparison are supplied together. The predicates compared are
the existing leaves; there is no new interpretation of TyObsView here. -/
structure CovTRecStage3Control (n : Nat) : Prop where
  environment : Nonempty (EnvWfT natEnvU)
  context : Nonempty (CtxWfT natEnvU n covTRecExtCtx)
  valuation : EnvTypedFinAtT (ctxModelT_approxTK natEnvU n covTRecExtCtx)
    covTRecExtCtx covTRecExtEnv
  coherent : CtxEnvM (ctxModelT_approxTK natEnvU n covTRecExtCtx)
    covTRecExtCtx covTRecExtEnv
  nativeType : Nonempty (HasTyT natEnvU n covTRecExtCtx
    (covTRecTypeAt 1) (.sort (.succ .zero)))
  nativeTerm : Nonempty (HasTyT natEnvU n covTRecExtCtx (.bvar 0) (covTRecTypeAt 1))
  nativeConversion : Nonempty (ConvT natEnvU n covTRecExtCtx
    (.bvar 0) (.bvar 0) (covTRecTypeAt 1))
  actualView : Nonempty (TyObsView natEnvU n 3 covTRecExtCtx covTRecExtEnv
    (covTRecTypeAt 1) .prop)
  unknownView : Nonempty (TyObsView natEnvU n 3 covTRecExtCtx covTRecExtEnv
    (covTRecTypeAt 1) .bot)
  stagedType : ApproxTKStage natEnvU n 3 covTRecExtCtx covTRecExtEnv
    (covTRecTypeAt 1) .prop
  stagedTerm : ApproxTKStage natEnvU n 3 covTRecExtCtx covTRecExtEnv (.bvar 0) covTProbe
  arguments : Nonempty (TyObsArgs natEnvU n 3 covTRecExtCtx covTRecExtEnv
    [covTRecMotive, .sort .zero, covTRecMinor, .bvar 1]
    [.bot, .bot, covTRecMinorCode, covTRecMajorCode])
  motive : CovTAdmissible natEnvU n 3 covTRecExtCtx covTRecExtEnv
    (.pi (.const 0 []) (.sort (.succ (.succ .zero)))) covTRecMotive []
  zero : CovTAdmissible natEnvU n 3 covTRecExtCtx covTRecExtEnv
    (.app covTRecMotive (.const 1 [])) (.sort .zero) []
  minor : CovTAdmissible natEnvU n 3 covTRecExtCtx covTRecExtEnv
    covTRecMinorTy covTRecMinor [covTRecMinorCode]
  major : CovTAdmissible natEnvU n 3 covTRecExtCtx covTRecExtEnv
    (.const 0 []) (.bvar 1) [covTRecMajorCode]
  nativeNormal : NormalR (WhStepCK2 natEnvU n) covTRecExtCtx (covTRecTypeAt 1)
  compactTyping : CTyS natEnvU covTProbe .prop
  valueNonbottom : covTProbe ≠ .bot
  rigidRejection : ¬ covSRigidRel (.bvar 0) (.bvar 0) covTProbe
  totalAcceptance : covSTotalRel (.bvar 0) (.bvar 0) covTProbe
  universeAcceptance : covRCodeRel natEnvU .prop (.bvar 0) (.bvar 0) covTProbe

theorem covTRec_stage3_control (n : Nat) : CovTRecStage3Control n where
  environment := ⟨natEnvUWfT⟩
  context := ⟨covTRecExtCtx_wf n⟩
  valuation := covTRec_ext_env_typed n
  coherent := covTRec_ext_ctx_coherent n
  nativeType := ⟨covTRecTypeAt_hasTy n _ 1 (.bvar _ 1 _ rfl)⟩
  nativeTerm := ⟨covTRecExt_y_hasTy n⟩
  nativeConversion := ⟨.refl _ _ _ (covTRecExt_y_hasTy n)⟩
  actualView := ⟨covTRec_view_stage3 n⟩
  unknownView := ⟨covTRec_unknown_view_stage3 n⟩
  stagedType := covTRec_type_stage3 n
  stagedTerm := covTRec_y_stage3 n
  arguments := ⟨covTRec_args_stage3 n⟩
  motive := covTRec_motive_admissible n
  zero := covTRec_zero_admissible n
  minor := covTRec_minor_admissible n
  major := covTRec_major_admissible n
  nativeNormal := covTRecTypeAt_normal n _ 1 rfl
  compactTyping := covTProbe_typed natEnvU
  valueNonbottom := covTProbe_nonbot
  rigidRejection := covTRec_rigid_rejects
  totalAcceptance := covTRec_unknown_accepts
  universeAcceptance := covTRec_prop_leaf_accepts

/-- An additional compact/native-head alignment assertion: an actual
`.prop` observation must read back to some literal native sort. This is
strictly a sort-head claim, not the broader native head/view supply port. -/
def CovTPropObservationSortReadback (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (u : Level),
    Nonempty (EnvWfT E) → Nonempty (CtxWfT E n Γ) →
    Nonempty (HasTyT E n Γ A (.sort u)) →
    EnvTypedFinAtT (ctxModelT_approxTK E n Γ) Γ ρ →
    CtxEnvM (ctxModelT_approxTK E n Γ) Γ ρ →
    ApproxTK E n Γ ρ A .prop →
    ∃ l, RedR (WhStepCK2 E n) Γ A (.sort l)

theorem covT_no_prop_observation_sort_readback (n : Nat) :
    ¬ CovTPropObservationSortReadback natEnvU n := by
  intro supply
  obtain ⟨hE, hΓ, hρ, hcoherent, hA, _, _, hobs, _, hno⟩ :=
    covTRec_type_control n
  obtain ⟨l, hl⟩ := supply covTRecCtx covTRecEnv (covTRecTypeAt 0) (.succ .zero)
    hE hΓ hA hρ hcoherent hobs
  exact hno l hl

/-- The same extra alignment assertion restricted to actual supplied
views at a fixed stage. Having a view does not imply this sort-head match. -/
def CovTViewedPropSortReadback (E : ResolvedEnv) (n stage : Nat) : Prop :=
  ∀ (Γ : LCtx) (ρ : EnvT) (A : Expr Nat),
    Nonempty (EnvWfT E) → Nonempty (CtxWfT E n Γ) →
    EnvTypedFinAtT (ctxModelT_approxTK E n Γ) Γ ρ →
    CtxEnvM (ctxModelT_approxTK E n Γ) Γ ρ →
    TyObsView E n stage Γ ρ A .prop →
    ∃ l, RedR (WhStepCK2 E n) Γ A (.sort l)

theorem covT_no_viewed_prop_sort_readback (n : Nat) :
    ¬ CovTViewedPropSortReadback natEnvU n 3 := by
  intro supply
  obtain ⟨l, hl⟩ := supply covTRecExtCtx covTRecExtEnv (covTRecTypeAt 1)
    ⟨natEnvUWfT⟩ ⟨covTRecExtCtx_wf n⟩ (covTRec_ext_env_typed n)
    (covTRec_ext_ctx_coherent n) (covTRec_view_stage3 n)
  exact covTRecTypeAt_no_sort_read n covTRecExtCtx 1 rfl l hl

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_T_RECURSOR_VIEW_ROOTS
#print axioms covTRec_minor_stage3
#print axioms covTRec_major_stage3
#print axioms covTRec_type_stage3
#print axioms covTRec_y_stage3
#print axioms covTRec_args_stage3
#print axioms covTRec_view_stage3
#print axioms covTRec_unknown_view_stage3
#print axioms covTRec_view_universe
#print axioms covTRec_view_not_positive
#print axioms covTRec_motive_admissible
#print axioms covTRec_zero_admissible
#print axioms covTRec_minor_admissible
#print axioms covTRec_major_admissible
#print axioms CovTRecStage3Control
#print axioms covTRec_stage3_control
#print axioms CovTPropObservationSortReadback
#print axioms covT_no_prop_observation_sort_readback
#print axioms CovTViewedPropSortReadback
#print axioms covT_no_viewed_prop_sort_readback
-- END RCIC_NATIVE_TYPED_MODEL_COV_T_RECURSOR_VIEW_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovTAudit

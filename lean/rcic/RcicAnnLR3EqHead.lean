import rcic.RcicAnnLR3Chain
import rcic.RcicAnnKEqPositive
import rcic.RcicAnnLR3HeadBoundary

/-!
# Inhabited Eq rules in the new contextual head relation

These fixtures supply the actual old-stage frames, positive neutral
prefixes, and typed new steps.  The beta-major example demonstrates the
chosen K priority: its competing old major step is excluded by the proved
new-head determinism theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3EqHead

open Rcic.Declarative EqLargeFixture LR3

theorem prefixNeutral (Γ : LCtxA) :
    NeutralA3 env (iotaIfaceA env) 0 Γ EqLargeFixture.recPrefix :=
  target_prefix_neutral (iotaFnA_recHead env) Γ
    (KEqPositive.target parameter (motiveAt parameter (.bvar 0)) (.bvar 0))

theorem letPrefixNeutral : NeutralA3 env (iotaIfaceA env) 0
    RouteCKContext.letContext KEqPositive.letShape.prefix :=
  target_prefix_neutral (iotaFnA_recHead env) RouteCKContext.letContext
    (KEqPositive.target (.bvar 1) (motiveAt (.bvar 2) (.bvar 0)) (.bvar 0))

theorem resultNormal (Γ : LCtxA) : NormalA3 env (iotaIfaceA env) 0 Γ result :=
  .pi (.sort .zero) one (.sort .zero) one

theorem eqHead : HeadA3 env (iotaIfaceA env) 0 context
    (call (.bvar 0)) result KEqPositive.eqShape.resultType :=
  .k KEqPositive.eqShape KEqPositive.eqFrame

theorem eqHeadSort : HeadA3 env (iotaIfaceA env) 0 context
    (call (.bvar 0)) result (.sort one) :=
  .convert _ _ _ _ eqHead (motiveTypeConv contextWf parameterTyped majorTyped)

theorem letHead : HeadA3 env (iotaIfaceA env) 0 RouteCKContext.letContext
    RouteCKContext.contextCall result KEqPositive.letShape.resultType :=
  .k KEqPositive.letShape KEqPositive.letFrame

theorem letHeadSort : HeadA3 env (iotaIfaceA env) 0 RouteCKContext.letContext
    RouteCKContext.contextCall result (.sort one) :=
  .convert _ _ _ _ letHead
    (motiveTypeConv RouteCKContext.letContextWf (RouteCKContext.indexTyped rfl)
      (RouteCKContext.proofTyped RouteCKContext.letContextWf rfl rfl))

theorem betaHead : HeadA3 env (iotaIfaceA env) 0 context
    (call (LR3HeadBoundary.betaMajor (.bvar 0))) result LR3HeadBoundary.betaShape.resultType :=
  .k LR3HeadBoundary.betaShape LR3HeadBoundary.betaFrame

theorem betaHeadSort : HeadA3 env (iotaIfaceA env) 0 context
    (call (LR3HeadBoundary.betaMajor (.bvar 0))) result (.sort one) :=
  .convert _ _ _ _ betaHead
    (motiveTypeConv contextWf parameterTyped
      (LR3HeadBoundary.betaMajorTyped contextWf majorTyped))

/-- The old beta-major route exists, but the new priority relation cannot
also choose its different intermediate reduct, at any result type. -/
theorem betaOldRouteExcluded (T : ExprA) :
    ¬ HeadA3 env (iotaIfaceA env) 0 context
      (call (LR3HeadBoundary.betaMajor (.bvar 0))) (call (.bvar 0)) T := by
  intro h
  exact LR3HeadBoundary.reductsDiffer (headA3_deterministic betaHead h).symm

theorem eqNotNormal : ¬ NormalA3 env (iotaIfaceA env) 0 context (call (.bvar 0)) :=
  fun h => normalA3_no_head h eqHead

theorem betaNotNormal : ¬ NormalA3 env (iotaIfaceA env) 0 context
    (call (LR3HeadBoundary.betaMajor (.bvar 0))) :=
  fun h => normalA3_no_head h betaHead

theorem eqSourceTyped : Nonempty (HasTyA env (iotaIfaceA env) 0 context
    (call (.bvar 0)) (.sort one)) :=
  eqHeadSort.leftTyped closed liftIface (iotaFnA_recHead env) substIface contextWf

theorem eqWhTy : WhTyA3 env (iotaIfaceA env) 0
    (contextualHeadLayerA3 env (iotaIfaceA env) 0) context (call (.bvar 0)) result := by
  obtain ⟨ha⟩ := eqSourceTyped
  exact whTyA3_cons ha eqHeadSort (whTyA3_of_hasTy resultTyped (resultNormal context))

theorem letWhTy : WhTyA3 env (iotaIfaceA env) 0
    (contextualHeadLayerA3 env (iotaIfaceA env) 0) RouteCKContext.letContext
    RouteCKContext.contextCall result := by
  obtain ⟨ha⟩ := letHeadSort.leftTyped closed liftIface (iotaFnA_recHead env) substIface
    RouteCKContext.letContextWf
  exact whTyA3_cons ha letHeadSort
    (whTyA3_of_hasTy resultTyped (resultNormal RouteCKContext.letContext))

theorem betaWhTy : WhTyA3 env (iotaIfaceA env) 0
    (contextualHeadLayerA3 env (iotaIfaceA env) 0) context
    (call (LR3HeadBoundary.betaMajor (.bvar 0))) result := by
  obtain ⟨ha⟩ := betaHeadSort.leftTyped closed liftIface (iotaFnA_recHead env) substIface contextWf
  exact whTyA3_cons ha betaHeadSort (whTyA3_of_hasTy resultTyped (resultNormal context))

/-- The normalized let-index call uses an old-stage conversion between
literally different declared and actual index lists. -/
theorem nonliteralIndexWhTy :
    KEqPositive.letShape.declaredIndices ≠ KEqPositive.letShape.actualIndices ∧
    WhTyA3 env (iotaIfaceA env) 0 (contextualHeadLayerA3 env (iotaIfaceA env) 0)
      RouteCKContext.letContext RouteCKContext.contextCall result :=
  ⟨KEqPositive.letIndices_differ, letWhTy⟩

theorem inhabited_head_supply :
    eraseEnv env = eqEnvT ∧ Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 context) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] (reflAt parameter) domain) ∧
    NeutralA3 env (iotaIfaceA env) 0 context EqLargeFixture.recPrefix ∧
    NormalA3 env (iotaIfaceA env) 0 context result ∧
    HeadA3 env (iotaIfaceA env) 0 context (call (.bvar 0)) result (.sort one) ∧
    HeadA3 env (iotaIfaceA env) 0 context
      (call (LR3HeadBoundary.betaMajor (.bvar 0))) result (.sort one) ∧
    Nonempty (TyHRedA env (iotaIfaceA env) 0 context
      (call (LR3HeadBoundary.betaMajor (.bvar 0))) (call (.bvar 0))
      LR3HeadBoundary.betaShape.resultType) :=
  ⟨erase_env, wf, ⟨contextWf⟩, ⟨reflTyped .nil parameterTyped⟩,
    prefixNeutral context, resultNormal context, eqHeadSort, betaHeadSort,
    LR3HeadBoundary.betaOldTypedStep⟩

#print axioms prefixNeutral
#print axioms letPrefixNeutral
#print axioms resultNormal
#print axioms eqHead
#print axioms eqHeadSort
#print axioms letHead
#print axioms letHeadSort
#print axioms betaHead
#print axioms betaHeadSort
#print axioms betaOldRouteExcluded
#print axioms eqNotNormal
#print axioms betaNotNormal
#print axioms eqSourceTyped
#print axioms eqWhTy
#print axioms letWhTy
#print axioms betaWhTy
#print axioms nonliteralIndexWhTy
#print axioms inhabited_head_supply

end Rcic.Declarative.Ann.LR3EqHead

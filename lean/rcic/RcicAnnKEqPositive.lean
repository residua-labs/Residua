import rcic.RcicAnnKTransport
import rcic.RcicRouteCKContextBoundary

/-!
# Inhabited Eq K frames, including a convertible nonliteral index

Every premise of the new typed K rule is supplied in the already admitted
Eq environment. The second frame uses actual local zeta at its index. The
old functional head remains stuck; the new relational head consumes these
frames without changing the conversion used by their guards.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.KEqPositive

open Rcic.Declarative KStage EqLargeFixture

def group : IotaGroupA :=
  ⟨recMember, reflMember, fam, 64, 63, 2, 1, 1, 0⟩

def shape (idx body major : ExprA) : KStage.Shape where
  recRef := 65
  ctorRef := 64
  group := group
  recLevels := [two]
  familyLevels := []
  ctorLevels := []
  params := [.sort .zero, parameter]
  declaredIndices := [parameter]
  actualIndices := [idx]
  motive := motive
  minor := result
  major := major
  body := body
  codSort := two

theorem target (idx body major : ExprA) : KStage.Target env (shape idx body major) := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  change iotaGroupA env 65 64 = some group
  rfl

abbrev familyTelescope : ExprA := .pi (.sort .zero) one (.sort .zero) one

private def applyE {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {f a D C : ExprA} {u v : Level}
    (hf : HasTyA env (iotaIfaceA env) 0 Γ f (.pi D u C v))
    (ha : HasTyA env (iotaIfaceA env) 0 Γ a D) :
    HasTyA env (iotaIfaceA env) 0 Γ (.app f a) (instantiate0A a C) :=
  convA_hasTy_left closed liftIface (iotaFnA_recHead env) substIface hΓ
    (KStage.appCongr closed liftIface (iotaFnA_recHead env) substIface hΓ
      (.refl Γ f _ hf) (.refl Γ a D ha))

def familyHeadTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    HasTyA env (iotaIfaceA env) 0 Γ
      (foldAppsA (.const 63 []) [.sort .zero, parameter]) familyTelescope :=
  applyE hΓ (applyE hΓ (famConstTyped (E := env) (I := iotaIfaceA env)
    (n := 0) (Γ := Γ) rfl) (.sort Γ .zero)) parameterTyped

abbrev eqShape : KStage.Shape :=
  shape parameter (motiveAt parameter (.bvar 0)) (.bvar 0)

theorem eqFrame : Nonempty (KStage.Frame env (iotaIfaceA env) 0 context eqShape) := by
  obtain ⟨hf⟩ := prefixTyped
  refine ⟨{
    target := target _ _ _
    familyTelescope := familyTelescope
    telescope := rfl
    familyHeadType := familyHeadTyped contextWf
    indexGuard := .cons (.sort .zero) one (.sort .zero) one parameter parameter [] []
      ⟨.refl context parameter (.sort .zero) parameterTyped⟩ (.nil (.sort .zero))
    familyResult := rfl
    prefixType := hf
    majorType := majorTyped
    canonicalType := reflTyped contextWf parameterTyped
    canonicalIota := ⟨by decide, by decide⟩
    minorType := ?_
  }⟩
  exact hasTyA_of_tyConvA resultTyped
    (motiveTypeConv contextWf parameterTyped majorTyped).symm

theorem eqFrame_sound : Nonempty (ConvA env (iotaIfaceA env) 0 context
    (call (.bvar 0)) result (.sort one)) := by
  obtain ⟨w⟩ := eqFrame
  obtain ⟨hc⟩ := w.sound closed liftIface (iotaFnA_recHead env) substIface contextWf
  exact ⟨convA_of_tyConvA hc (motiveTypeConv contextWf parameterTyped majorTyped)⟩

abbrev letShape : KStage.Shape :=
  shape (.bvar 1) (motiveAt (.bvar 2) (.bvar 0)) (.bvar 0)

/-- The guard is genuinely conversion-based: its two index expressions differ. -/
theorem letIndices_differ : letShape.declaredIndices ≠ letShape.actualIndices := by decide

theorem letFrame :
    Nonempty (KStage.Frame env (iotaIfaceA env) 0 RouteCKContext.letContext letShape) := by
  obtain ⟨hf⟩ := RouteCKContext.contextPrefixTyped RouteCKContext.letContextWf rfl
  refine ⟨{
    target := target _ _ _
    familyTelescope := familyTelescope
    telescope := rfl
    familyHeadType := familyHeadTyped RouteCKContext.letContextWf
    indexGuard := .cons (.sort .zero) one (.sort .zero) one parameter (.bvar 1) [] []
      ⟨.symm _ _ _ _ RouteCKContext.letIndexConversion⟩ (.nil (.sort .zero))
    familyResult := rfl
    prefixType := hf
    majorType := RouteCKContext.proofTyped RouteCKContext.letContextWf rfl rfl
    canonicalType := reflTyped RouteCKContext.letContextWf parameterTyped
    canonicalIota := ⟨by decide, by decide⟩
    minorType := ?_
  }⟩
  exact hasTyA_of_tyConvA resultTyped
    (motiveTypeConv RouteCKContext.letContextWf (RouteCKContext.indexTyped rfl)
      (RouteCKContext.proofTyped RouteCKContext.letContextWf rfl rfl)).symm

theorem letFrame_sound : Nonempty (ConvA env (iotaIfaceA env) 0 RouteCKContext.letContext
    RouteCKContext.contextCall result (.sort one)) := by
  obtain ⟨w⟩ := letFrame
  obtain ⟨hc⟩ := w.sound closed liftIface (iotaFnA_recHead env) substIface
    RouteCKContext.letContextWf
  exact ⟨convA_of_tyConvA hc
    (motiveTypeConv RouteCKContext.letContextWf (RouteCKContext.indexTyped rfl)
      (RouteCKContext.proofTyped RouteCKContext.letContextWf rfl rfl))⟩

/-- The fixture's formerly stuck call has an actual new K head step. -/
theorem eqHead : KStage.Head env (iotaIfaceA env) 0 context
    (call (.bvar 0)) result eqShape.resultType :=
  .k eqShape eqFrame

theorem eqHead_not_stuck :
    ¬ (∀ rhs T, ¬ KStage.Head env (iotaIfaceA env) 0 context (call (.bvar 0)) rhs T) :=
  fun h => h result eqShape.resultType eqHead

/-- The nonliteral index is accepted by old-stage conversion, using local zeta. -/
theorem letHead : KStage.Head env (iotaIfaceA env) 0 RouteCKContext.letContext
    RouteCKContext.contextCall result letShape.resultType :=
  .k letShape letFrame

/-- The witnessed step survives an actual typed closing substitution. -/
theorem letHead_closed : KStage.Head env (iotaIfaceA env) 0 []
    (substA RouteCKContext.closeSubstitution RouteCKContext.contextCall)
    (substA RouteCKContext.closeSubstitution result)
    (substA RouteCKContext.closeSubstitution letShape.resultType) :=
  KStage.Head.subst closed liftIface (iotaFnA_recHead env) substIface
    RouteCKContext.letContextWf RouteCKContext.letClosingSubstitution letHead

/-- Positive supply at the admitted Eq environment, including its closed
proof inhabitant and both Type-level typings. The old functional strategy is
still named separately; no semantic environment claim is hidden here. -/
theorem inhabited_step_positive :
    eraseEnv env = eqEnvT ∧ Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 context) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] (reflAt parameter) domain) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context (call (.bvar 0)) (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context result (.sort one)) ∧
    StuckA env (iotaIfaceA env) context (call (.bvar 0)) ∧
    KStage.Head env (iotaIfaceA env) 0 context (call (.bvar 0)) result eqShape.resultType ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 context (call (.bvar 0)) result (.sort one)) := by
  obtain ⟨hc⟩ := eqFrame_sound
  exact ⟨erase_env, wf, ⟨contextWf⟩, ⟨reflTyped .nil parameterTyped⟩,
    ⟨convA_hasTy_left closed liftIface (iotaFnA_recHead env) substIface contextWf hc⟩,
    ⟨resultTyped⟩, callStuck, eqHead, ⟨hc⟩⟩

theorem inhabited_nonliteral_positive :
    letShape.declaredIndices ≠ letShape.actualIndices ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 RouteCKContext.letContext) ∧
    Nonempty (SubstTyA env (iotaIfaceA env) 0 []
      RouteCKContext.closeSubstitution RouteCKContext.letContext) ∧
    KStage.Head env (iotaIfaceA env) 0 RouteCKContext.letContext
      RouteCKContext.contextCall result letShape.resultType ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 RouteCKContext.letContext
      RouteCKContext.contextCall result (.sort one)) :=
  ⟨letIndices_differ, ⟨RouteCKContext.letContextWf⟩,
    ⟨RouteCKContext.letClosingSubstitution⟩, letHead, letFrame_sound⟩

#print axioms group
#print axioms shape
#print axioms target
#print axioms familyTelescope
#print axioms familyHeadTyped
#print axioms eqShape
#print axioms eqFrame
#print axioms eqFrame_sound
#print axioms letShape
#print axioms letIndices_differ
#print axioms letFrame
#print axioms letFrame_sound
#print axioms eqHead
#print axioms eqHead_not_stuck
#print axioms letHead
#print axioms letHead_closed
#print axioms inhabited_step_positive
#print axioms inhabited_nonliteral_positive

end Rcic.Declarative.Ann.KEqPositive

import rcic.RcicAnnLR3FrameSource
import rcic.RcicAnnLR3Sort

/-!
# The exact remaining type agreement at the fixed canonical proof

Typing generation at `reflAt parameter` exposes two potentially converted
Pi carriers.  It supplies conversions from the stored constructor type
to the first Pi, from its instantiated codomain to the second Pi, and
from that Pi's instantiated codomain to the final type.  It does not by
itself identify either intermediate codomain with the stored one.

Relational inference of the fixed proof at `domain` is supplied below,
using actual typed normal Pi witnesses.  Inference determinism identifies
other inference results.  Agreement with an arbitrary declarative typing
is named separately, both for this fixed subject and for the single actual
type needed by the open Eq frame reduction.

The final theorem consumes the named agreement slice to finish the
frame-to-family-conversion reduction.  No agreement, separation or semantic
environment theorem is claimed as a supply.  `closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3.ReflInference

open Rcic.Declarative EqLargeFixture RouteCKContext FrameSource

/-- The intermediate carriers returned by ordinary generation remain explicit. -/
theorem reflTypingGenerationA3 {T : ExprA}
    (ht : HasTyA env (iotaIfaceA env) 0 assumptionContext (reflAt parameter) T) :
    ∃ (D₀ C₀ D₁ C₁ : ExprA) (u₀ v₀ u₁ v₁ : Level),
      Nonempty (HasTyA env (iotaIfaceA env) 0 assumptionContext (.sort .zero) D₀) ∧
      Nonempty (HasTyA env (iotaIfaceA env) 0 assumptionContext parameter D₁) ∧
      Nonempty (TyConvA env (iotaIfaceA env) 0 assumptionContext
        reflTy (.pi D₀ u₀ C₀ v₀)) ∧
      Nonempty (TyConvA env (iotaIfaceA env) 0 assumptionContext
        (instantiate0A (.sort .zero) C₀) (.pi D₁ u₁ C₁ v₁)) ∧
      Nonempty (TyConvA env (iotaIfaceA env) 0 assumptionContext
        (instantiate0A parameter C₁) T) := by
  obtain ⟨D₁, u₁, C₁, v₁, _, ⟨hf₁⟩, ha₁, _, _, hc₁⟩ := hasTyA_app_gen ht
  obtain ⟨D₀, u₀, C₀, v₀, _, ⟨hf₀⟩, ha₀, _, _, hc₀⟩ := hasTyA_app_gen hf₁
  obtain ⟨m, hm, hcm⟩ := hasTyA_const_gen hf₀
  have hmem : env.members 64 = some reflMember := rfl
  rw [hmem] at hm
  cases hm
  exact ⟨D₀, C₀, D₁, C₁, u₀, v₀, u₁, v₁, ha₀, ha₁, hcm, hc₀, hc₁⟩

private abbrev partialReflTy : ExprA :=
  .pi (.sort .zero) one (eqAt (.bvar 0) (.bvar 0)) .zero

private def partialReflTyped : HasTyA env (iotaIfaceA env) 0 assumptionContext
    (.app (.const 64 []) (.sort .zero)) partialReflTy :=
  convA_hasTy_left closed liftIface (iotaFnA_recHead env) substIface assumptionContextWf
    (KStage.appCongr closed liftIface (iotaFnA_recHead env) substIface assumptionContextWf
      (.refl assumptionContext (.const 64 []) reflTy (reflConstTyped assumptionContext))
      (.refl assumptionContext (.sort .zero) (.sort one) (.sort assumptionContext .zero)))

/-- Actual relational inference at the stored result type, for every supplied head layer. -/
theorem reflInferA3 (H : HeadLayerA3 env (iotaIfaceA env) 0) :
    InferA3 env (iotaIfaceA env) 0 H assumptionContext (reflAt parameter) domain := by
  have ht₀ := (hasTyA_regular closed liftIface (iotaFnA_recHead env) substIface
    assumptionContextWf (reflConstTyped assumptionContext)).2
  have ht₁ := (hasTyA_regular closed liftIface (iotaFnA_recHead env) substIface
    assumptionContextWf partialReflTyped).2
  have hi₀ : InferA3 env (iotaIfaceA env) 0 H assumptionContext (.const 64 []) reflTy :=
    .const (m := reflMember) rfl rfl
  have hi₁ : InferA3 env (iotaIfaceA env) 0 H assumptionContext
      (.app (.const 64 []) (.sort .zero)) partialReflTy :=
    .app hi₀ (whTyA3_of_hasTy ht₀ (H.normal_pi _ _ _ _ _))
  exact .app hi₁ (whTyA3_of_hasTy ht₁ (H.normal_pi _ _ _ _ _))

/-- Every synthesis result for this proof is literally the supplied stored result. -/
theorem reflInferA3_unique (H : HeadLayerA3 env (iotaIfaceA env) 0) {T : ExprA}
    (ht : InferA3 env (iotaIfaceA env) 0 H assumptionContext (reflAt parameter) T) :
    T = domain :=
  inferA3_det H ht (reflInferA3 H)

/-- A fixed-subject declarative type-agreement obligation, not a supplied theorem. -/
def ReflTypeAgreementA3 : Prop :=
  ∀ T : ExprA,
    HasTyA env (iotaIfaceA env) 0 assumptionContext (reflAt parameter) T →
    Nonempty (TyConvA env (iotaIfaceA env) 0 assumptionContext domain T)

/-- The same fixed-subject obligation phrased against actual relational inference. -/
def ReflInferenceAgreementA3 (H : HeadLayerA3 env (iotaIfaceA env) 0) : Prop :=
  ∀ T U : ExprA,
    HasTyA env (iotaIfaceA env) 0 assumptionContext (reflAt parameter) T →
    InferA3 env (iotaIfaceA env) 0 H assumptionContext (reflAt parameter) U →
    Nonempty (TyConvA env (iotaIfaceA env) 0 assumptionContext U T)

/-- The actual inference supply makes these two agreement obligations equivalent.
This equivalence does not prove either obligation. -/
theorem reflAgreementA3_iff_inference (H : HeadLayerA3 env (iotaIfaceA env) 0) :
    ReflTypeAgreementA3 ↔ ReflInferenceAgreementA3 H := by
  constructor
  · intro h T U ht hi
    have hU := reflInferA3_unique H hi
    rw [hU]
    exact h T ht
  · intro h T ht
    exact h T domain ht (reflInferA3 H)

/-- Only this single target-type slice is needed after arbitrary-frame extraction. -/
def ReflActualTypeAgreementA3 : Prop :=
  HasTyA env (iotaIfaceA env) 0 assumptionContext
      (reflAt parameter) (eqAt parameter (.bvar 1)) →
    Nonempty (TyConvA env (iotaIfaceA env) 0 assumptionContext
      domain (eqAt parameter (.bvar 1)))

theorem reflActualTypeAgreementA3_of_general (h : ReflTypeAgreementA3) :
    ReflActualTypeAgreementA3 :=
  h (eqAt parameter (.bvar 1))

/-- Exact conditional reduction from any matching frame, with no constraint
on its declared indices and with the remaining agreement premise named. -/
theorem assumptionFrameFamilyConversionA3 (h : ReflActualTypeAgreementA3)
    {s : KStage.Shape}
    (w : KStage.Frame env (iotaIfaceA env) 0 assumptionContext s)
    (he : s.source = contextCall) :
    Nonempty (TyConvA env (iotaIfaceA env) 0 assumptionContext
      domain (eqAt parameter (.bvar 1))) := by
  obtain ⟨ht⟩ := assumptionFrameCanonicalActualA3 w he
  exact h ht

#print axioms reflTypingGenerationA3
#print axioms reflInferA3
#print axioms reflInferA3_unique
#print axioms ReflTypeAgreementA3
#print axioms ReflInferenceAgreementA3
#print axioms reflAgreementA3_iff_inference
#print axioms ReflActualTypeAgreementA3
#print axioms reflActualTypeAgreementA3_of_general
#print axioms assumptionFrameFamilyConversionA3

end Rcic.Declarative.Ann.LR3.ReflInference

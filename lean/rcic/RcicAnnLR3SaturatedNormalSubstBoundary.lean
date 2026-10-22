import rcic.RcicAnnLR3NormalSubstBoundary

/-!
# A saturated Eq obstruction to raw stable-normal certificates

This module isolates a proposed recipe for a richer LR3 head layer:
retain the supplied stage-1 K frames, certify the actual open assumption
call as normal, and preserve raw normality under every typed substitution.
These three requirements are incompatible. The already supplied closing
substitution sends the open call to a closed K call. Its K frame is obtained
by transporting the actual let-context frame through that same substitution.

The open context, closed context, full call typing, closing substitution,
and apart canonical erased indices are all inhabited. The result does not
claim annotated nonconversion of the open indices. It excludes only this
raw stable-normal recipe; semantic substitution and `EnvSem3` are not refuted.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3.SaturatedNormalSubstBoundary

open Rcic.Declarative Rcic.Syn EqLargeFixture RouteCKContext
open LR3NormalSubstBoundary (RawNormalSubstA3)

/-- Coverage of the actual earlier-stage frames, independently of any
particular positive normality language. -/
def StageOneKCoverageA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (Γ : LCtxA) (s : KStage.Shape), Nonempty (KStage.Frame E I n Γ s) →
    H.step Γ s.source s.minor s.resultType

theorem contextual_stageOneKCoverageA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    StageOneKCoverageA3 E I n (contextualHeadLayerA3 E I n) :=
  fun _ s hw => HeadA3.k s hw

abbrev closedCallShape : KStage.Shape :=
  KEqPositive.letShape.map (substMapA closeSubstitution)

/-- The closed frame is a composition of the supplied let frame and the
supplied typed closing substitution; no guard decision is made. -/
theorem closedCallFrame :
    Nonempty (KStage.Frame env (iotaIfaceA env) 0 [] closedCallShape) := by
  obtain ⟨w⟩ := KEqPositive.letFrame
  exact w.subst closed liftIface (iotaFnA_recHead env) substIface
    letContextWf letClosingSubstitution

theorem closedCallSource :
    closedCallShape.source = substA closeSubstitution contextCall :=
  KStage.Shape.map_source KEqPositive.letShape (substMapA closeSubstitution)

/-- Every layer retaining stage-1 K takes a step at the closed image of
the open assumption call, irrespective of its positive normality language. -/
theorem coveredClosedCallStep (H : HeadLayerA3 env (iotaIfaceA env) 0)
    (hK : StageOneKCoverageA3 env (iotaIfaceA env) 0 H) :
    H.step [] (substA closeSubstitution contextCall)
      closedCallShape.minor closedCallShape.resultType := by
  have hs := hK [] closedCallShape closedCallFrame
  rw [closedCallSource] at hs
  exact hs

/-- In a K-preserving layer with raw substitution-stable normality, the
actual open saturated call cannot receive a normal certificate. -/
theorem rawStableNormal_excludes_openCall
    (H : HeadLayerA3 env (iotaIfaceA env) 0)
    (hK : StageOneKCoverageA3 env (iotaIfaceA env) 0 H)
    (hS : RawNormalSubstA3 H) :
    ¬ H.normal assumptionContext contextCall := by
  intro hn
  obtain ⟨ht⟩ := contextCallTyped assumptionContextWf rfl rfl
  have hn' := hS assumptionContext [] closeSubstitution contextCall (.sort one)
    assumptionContextWf .nil assumptionClosingSubstitution ht hn
  exact H.normal_excludes hn' (coveredClosedCallStep H hK)

/-- This refutes the three-property recipe itself, not a semantic
substitution theorem or a richer layer without the raw stability demand. -/
theorem no_rawStableNormal_recipe :
    ¬ ∃ H : HeadLayerA3 env (iotaIfaceA env) 0,
      StageOneKCoverageA3 env (iotaIfaceA env) 0 H ∧ RawNormalSubstA3 H ∧
      H.normal assumptionContext contextCall := by
  rintro ⟨H, hK, hS, hn⟩
  exact rawStableNormal_excludes_openCall H hK hS hn

theorem inhabited_saturated_normal_subst_boundary :
    eraseEnv env = eqEnvT ∧
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 assumptionContext) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 []) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 assumptionContext contextCall (.sort one)) ∧
    Nonempty (SubstTyA env (iotaIfaceA env) 0 [] closeSubstitution assumptionContext) ∧
    TableWF [] ∧ ¬ assumptionErasedGuard [] ∧
    Nonempty (KStage.Frame env (iotaIfaceA env) 0 [] closedCallShape) ∧
    (¬ ∃ H : HeadLayerA3 env (iotaIfaceA env) 0,
      StageOneKCoverageA3 env (iotaIfaceA env) 0 H ∧ RawNormalSubstA3 H ∧
      H.normal assumptionContext contextCall) :=
  ⟨erase_env, wf, ⟨assumptionContextWf⟩, ⟨.nil⟩,
    contextCallTyped assumptionContextWf rfl rfl,
    ⟨assumptionClosingSubstitution⟩, emptyTable_wf,
    assumptionErasedGuard_fails emptyTable_wf, closedCallFrame,
    no_rawStableNormal_recipe⟩

#print axioms StageOneKCoverageA3
#print axioms contextual_stageOneKCoverageA3
#print axioms closedCallShape
#print axioms closedCallFrame
#print axioms closedCallSource
#print axioms coveredClosedCallStep
#print axioms rawStableNormal_excludes_openCall
#print axioms no_rawStableNormal_recipe
#print axioms inhabited_saturated_normal_subst_boundary

end Rcic.Declarative.Ann.LR3.SaturatedNormalSubstBoundary

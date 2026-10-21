import rcic.RcicNativeTypedModelCovWConvControls
import rcic.RcicNativeTypedModelCovWConvReduction

/-!
The local-zeta observation gap persists with the new explicit realization
guard.  A concrete typed closing substitution realizes the bottom observation
environment for the local-definition context at every stage.

This is a failure of the current open-term observation invariant even with
that guard.  After the displayed closing substitution, the two terms are
definitionally the same expression.  Thus this fixture is not a counterexample
to a model that first closes the terms and then compares their observations.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelCovTAudit TypedModelCovWAudit
open TypedModelCovWIrrelAudit TypedModelCovWNativeAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit

/-- Every slot is sent to the same closed value, `Sort 1`. -/
def covWConvLocalSubst : SubstT := fun _ => covWConvLocalValue

theorem covWConvLocal_subst_typed (n : Nat) :
    TypedSubstT emptyEnv n [] covWConvLocalSubst covWConvLocalCtx := by
  constructor
  · intro i A hA
    cases i with
    | zero =>
        change some covWConvLocalType = some A at hA
        cases hA
        exact ⟨.sort [] levelOne⟩
    | succ i =>
        change (none : Option (Expr Nat)) = some A at hA
        cases hA
  · intro i v hv
    cases i with
    | zero =>
        change some covWConvLocalValue = some v at hv
        cases hv
        exact ⟨covWConvLocalType, rfl,
          ⟨.refl [] covWConvLocalValue covWConvLocalType (.sort [] levelOne)⟩⟩
    | succ i =>
        change (none : Option (Expr Nat)) = some v at hv
        cases hv

theorem covWConvLocal_realized (n stage : Nat) :
    CovWConvRealized emptyEnv n stage covWConvLocalCtx
      EnvWConvR.bot covWConvLocalSubst :=
  covWConv_realized_bot (covWConvLocal_subst_typed n)

/-- Closing the endpoints removes this particular open-term distinction. -/
theorem covWConvLocal_closed_endpoints_identical :
    substT covWConvLocalSubst (.bvar 0) =
      substT covWConvLocalSubst covWConvLocalValue :=
  rfl

/--
The full declared realization guard accompanies every premise and conclusion
of the local-zeta counterexample.  The negative conclusion remains about the
open terms in the original local-definition context.
-/
theorem covWConvLocal_realized_cell_inhabited (n stage : Nat) :
    CovWConvRealized emptyEnv n stage covWConvLocalCtx
      EnvWConvR.bot covWConvLocalSubst ∧
    Nonempty (EnvWfT emptyEnv) ∧
    Nonempty (CtxWfT emptyEnv n covWConvLocalCtx) ∧
    Nonempty (HasTyT emptyEnv n covWConvLocalCtx covWConvLocalType
      (.sort levelThree)) ∧
    Nonempty (HasTyT emptyEnv n covWConvLocalCtx (.bvar 0) covWConvLocalType) ∧
    Nonempty (HasTyT emptyEnv n covWConvLocalCtx covWConvLocalValue
      covWConvLocalType) ∧
    Nonempty (ConvT emptyEnv n covWConvLocalCtx (.bvar 0)
      covWConvLocalValue covWConvLocalType) ∧
    WhStepCK2 emptyEnv n covWConvLocalCtx (.bvar 0) covWConvLocalValue ∧
    CovWConvObservation emptyEnv n covWConvLocalCtx EnvWConvR.bot
      covWConvLocalType covWConvLocalTypeCode ∧
    CTySConv emptyEnv covWConvLocalDemand covWConvLocalTypeCode ∧
    covWConvLocalDemand ≠ .bot ∧
    CovWConvObservation emptyEnv n covWConvLocalCtx EnvWConvR.bot
      covWConvLocalValue covWConvLocalDemand ∧
    (¬ CovWConvObservation emptyEnv n covWConvLocalCtx EnvWConvR.bot
      (.bvar 0) covWConvLocalDemand) ∧
    ¬ CovWConvTypedInvariant emptyEnv n covWConvLocalCtx EnvWConvR.bot
      covWConvLocalType (.bvar 0) covWConvLocalValue :=
  ⟨covWConvLocal_realized n stage, covWConvLocal_cell_inhabited n⟩

/-- This is also a step of the actual typed ConvT-sound fragment. -/
theorem covWConvLocal_aligned_step (n : Nat) :
    CovWConvReduction emptyEnv n covWConvLocalCtx
      (.bvar 0) covWConvLocalValue covWConvLocalType :=
  .zetaLocal 0 covWConvLocalType covWConvLocalValue
    rfl rfl (covWConvLocal_value_typed n)

#print axioms covWConvLocal_aligned_step
#print axioms covWConvLocal_subst_typed
#print axioms covWConvLocal_realized
#print axioms covWConvLocal_closed_endpoints_identical
#print axioms covWConvLocal_realized_cell_inhabited

end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

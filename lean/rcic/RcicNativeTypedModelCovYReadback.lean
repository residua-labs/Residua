import rcic.RcicNativeTypedModelCovXEnvBoundary
import rcic.RcicNativeReadbackCK2Gap

/-!
# CK2 readback at the actual lifted assumption-entry type

The environment lookup at a newly added assumption is its lifted type.
These proofs compose the native K theorem with the shifted variables'
native typing derivations, then compose the alias's ordinary outer beta.
They do not assume a model lifting law or a global readback substitution law.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit ReadbackCKAudit
open ReadbackCK2Audit ReadbackCK2ConvAudit ReadbackCK2GapAudit
open TypedModelKFailureAudit TypedModelKTypedBetaAudit

/-- The genuine shifted Eq-gap redex still fires K. Each major/index
typing premise is obtained from the actual extended native context. -/
theorem redR_lift_eqGapRedex_cons (n : Nat) (D : Expr Nat) :
    RedR (WhStepCK2 eqEnvT n) (.assumption D :: eqGapCtx)
      (lift 0 1 eqGapRedex) (.sort .zero) := by
  have hA : HasTyT eqEnvT n (.assumption D :: eqGapCtx)
      (.bvar 3) (.sort (.succ .zero)) := .bvar _ 3 _ rfl
  have ha : HasTyT eqEnvT n (.assumption D :: eqGapCtx)
      (.bvar 2) (.bvar 3) := .bvar _ 2 _ rfl
  have hx : HasTyT eqEnvT n (.assumption D :: eqGapCtx) (.bvar 1)
      (foldApps (.const 63 []) [.bvar 3, .bvar 2,
        gapBetaIndex (.bvar 3) (.bvar 2)]) := .bvar _ 1 _ rfl
  exact .step (.native (kNativeHead_eq_of_indexConv (fun _ _ h => h)
    (lift 0 1 eqGapMot) (.sort .zero) hA ha (gapBetaIndexTy hA ha) hx
    (gapBetaIndexConv hA ha) not_isCtorSpine_bvar)) (.refl _)

/-- This is exactly the type returned by lookup zero at the alias
assumption. The proof preserves its native context throughout both steps. -/
theorem redR_lift_eqGapDirectAlias_cons (n : Nat) (D A B : Expr Nat) :
    RedR (WhStepCK2 eqEnvT n) (.assumption D :: eqGapCtx)
      (lift 0 1 (eqGapDirectAlias A B)) (.sort .zero) :=
  .step ((readbackLaws_whStepCK2 eqEnvT n).beta (.assumption D :: eqGapCtx)
    (lift 0 1 (.pi A B)) (.app (.bvar 0) (.bvar 2)) (lift 0 1 eqGapPrefix))
    (redR_lift_eqGapRedex_cons n D)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_READBACK_ROOTS
#print axioms redR_lift_eqGapRedex_cons
#print axioms redR_lift_eqGapDirectAlias_cons
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_READBACK_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYAudit

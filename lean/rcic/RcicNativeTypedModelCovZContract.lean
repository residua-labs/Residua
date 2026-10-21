import rcic.RcicNativeTypedModelCovYFixtures
import rcic.RcicNativeTypedModelCovYCodeBoundary
import rcic.RcicNativeTypedModelCovYNatCodeBoundary

/-!
# The joint code-construction target, with its native and semantic guards

The code is a conclusion. Neither realization nor action coverage is an
input. The pointwise target retains both hereditary realizations at the SAME
code. The global specification below even assumes an existing relation code,
two actual observations, native conversion, and the new environment guards.

The function specification is restricted to closed typed inputs and is given
an actual normal readback of the native type. It imposes no recursion strategy;
refuting it would therefore rule out more than one proposed algorithm.
No assembler is instantiated here. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovZAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelKAudit
open ReadbackCK2Audit TypedModelCovRelAudit TypedModelCovNormCov2Audit
open TypedModelCovYAudit

/-- The exact same-code conclusion requested for the two endpoints. -/
def CovZJointCodeAt (C : CovTyping E) (Q : LCtx → CtxModelT E)
    (R : Readback) (n : Nat) (Γ : LCtx) (ρ ρ' : EnvT)
    (x y A : Expr Nat) (c b : CptT) : Prop :=
  LRSCoreCovY C R n Γ x y A c b ∧
  HereditaryCovRealizationYAt C Q R n Γ ρ A c b ∧
  HereditaryCovRealizationYAt C Q R n Γ ρ' A c b

/-- A strong-input version of global code synthesis. An arbitrary prior
relation code may be replaced; no caller-selected output code is preserved. -/
def CovZTypedJointSynthesis (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ (Γ : LCtx) (ρ ρ' : EnvT) (x y A : Expr Nat) (c : CptT),
    EnvWfT E → CtxWfT E n Γ →
    HasTyT E n Γ x A → HasTyT E n Γ y A →
    Nonempty (ConvT E n Γ x y A) →
    EnvTypedCovYAt (covTypingCTyCov2 E) (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ →
    EnvTypedCovYAt (covTypingCTyCov2 E) (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ' →
    ApproxTK E n Γ ρ x c → ApproxTK E n Γ ρ' y c →
    (∃ a, LRSCoreCovY (covTypingCTyCov2 E) (WhStepCK2 E n) n Γ x y A c a) →
    ∃ b, CovZJointCodeAt (covTypingCTyCov2 E) (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ ρ' x y A c b

/-- Even closed diagonal inputs are enough to test a proposed `codeOf`.
The function receives the actual native type normal form and observed value
compact. The specification does not require a fixed code to be retained. -/
def CovZClosedCodeOfSpec (E : ResolvedEnv) (n : Nat)
    (codeOf : Expr Nat → CptT → CptT) : Prop :=
  ∀ (x A A₀ : Expr Nat) (c : CptT),
    EnvWfT E → HasTyT E n [] x A →
    ApproxTK E n [] EnvT.bot x c →
    RedR (WhStepCK2 E n) [] A A₀ → NormalR (WhStepCK2 E n) [] A₀ →
    CovZJointCodeAt (covTypingCTyCov2 E) (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n [] EnvT.bot EnvT.bot x x A c (codeOf A₀ c)

/-- A local all-code obstruction refutes every closed code function,
independently of its termination measure or implementation. -/
theorem covZ_no_codeOf_of_no_realization {E : ResolvedEnv} {n : Nat}
    {x A A₀ : Expr Nat} {c : CptT} (hW : EnvWfT E)
    (ht : HasTyT E n [] x A) (ho : ApproxTK E n [] EnvT.bot x c)
    (hr : RedR (WhStepCK2 E n) [] A A₀) (hn : NormalR (WhStepCK2 E n) [] A₀)
    (hno : ∀ b, ¬ HereditaryCovRealizationYAt (covTypingCTyCov2 E)
      (ctxModelT_approxTK E n) (WhStepCK2 E n) n [] EnvT.bot A c b) :
    ¬ ∃ codeOf, CovZClosedCodeOfSpec E n codeOf := by
  rintro ⟨codeOf, hs⟩
  exact hno _ (hs x A A₀ c hW ht ho hr hn).2.1

/-- The same local obstruction also refutes synthesis from an already
related closed diagonal. All environment and native-conversion guards are
constructed here; only the displayed native/model inputs are consumed. -/
theorem covZ_not_typedJoint_of_no_realization {E : ResolvedEnv} {n : Nat}
    {x A : Expr Nat} {c : CptT} (hW : EnvWfT E)
    (ht : HasTyT E n [] x A) (ho : ApproxTK E n [] EnvT.bot x c)
    (hc : ∃ a, LRSCoreCovY (covTypingCTyCov2 E) (WhStepCK2 E n) n [] x x A c a)
    (hno : ∀ b, ¬ HereditaryCovRealizationYAt (covTypingCTyCov2 E)
      (ctxModelT_approxTK E n) (WhStepCK2 E n) n [] EnvT.bot A c b) :
    ¬ CovZTypedJointSynthesis E n := by
  intro hs
  have he := envTypedCovYAt_nil (covTypingCTyCov2 E)
    (ctxModelT_approxTK E n) (WhStepCK2 E n) n EnvT.bot
  obtain ⟨b, _, hh, _⟩ := hs [] EnvT.bot EnvT.bot x x A c hW .nil ht ht
    ⟨.refl _ _ _ ht⟩ he he ho ho hc
  exact hno b hh

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Z_CONTRACT_ROOTS
#print axioms CovZJointCodeAt
#print axioms CovZTypedJointSynthesis
#print axioms CovZClosedCodeOfSpec
#print axioms covZ_no_codeOf_of_no_realization
#print axioms covZ_not_typedJoint_of_no_realization
-- END RCIC_NATIVE_TYPED_MODEL_COV_Z_CONTRACT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovZAudit

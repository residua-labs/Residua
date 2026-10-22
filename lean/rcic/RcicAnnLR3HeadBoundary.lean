import rcic.RcicAnnKEqPositive

/-!
# A typed overlap between old head evaluation and the stage-1 K clause

The admitted Eq environment supplies a proof major that is a beta redex.
The existing typed major rule evaluates that proof, whereas the contextual
K frame returns the minor immediately.  The two reducts have different
syntactic shapes.  Consequently a deterministic contextual relation cannot
include every old typed head step and every supplied K frame as one step.

This is an obstruction to simultaneous step inclusion.  It does not rule
out a priority strategy or a simulation using zero or more steps.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3HeadBoundary

open Rcic.Declarative EqLargeFixture

/-- A proof that computes to its argument in one old beta step. -/
def betaMajor (p : ExprA) : ExprA :=
  .app (.lam domain .zero (.bvar 0)) p

def betaMajorTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {p : ExprA} (hp : HasTyA env (iotaIfaceA env) 0 Γ p domain) :
    HasTyA env (iotaIfaceA env) 0 Γ (betaMajor p) domain := by
  let hD := eqTyped hΓ parameterTyped parameterTyped
  let hΓD := CtxWfA.assumption hΓ hD
  let hD' := eqTyped hΓD parameterTyped parameterTyped
  let hv : HasTyA env (iotaIfaceA env) 0 (.assumption domain :: Γ)
      (.bvar 0) domain := .bvar _ 0 domain .zero rfl hD'
  exact .app Γ _ p domain domain .zero .zero .zero hD' hD
    (.lam Γ domain .zero (.bvar 0) domain .zero hD hD' hv) hp

def betaMajorStep {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {p : ExprA} (hp : HasTyA env (iotaIfaceA env) 0 Γ p domain) :
    TyHRedA env (iotaIfaceA env) 0 Γ (betaMajor p) p domain := by
  let hD := eqTyped hΓ parameterTyped parameterTyped
  let hΓD := CtxWfA.assumption hΓ hD
  let hv : HasTyA env (iotaIfaceA env) 0 (.assumption domain :: Γ)
      (.bvar 0) domain :=
    .bvar _ 0 domain .zero rfl (eqTyped hΓD parameterTyped parameterTyped)
  exact .beta Γ domain .zero (.bvar 0) p domain hD hv hp hp

abbrev betaShape : KStage.Shape :=
  KEqPositive.shape parameter (motiveAt parameter (.bvar 0)) (betaMajor (.bvar 0))

/-- The K frame's actual proof major may itself compute. -/
theorem betaFrame :
    Nonempty (KStage.Frame env (iotaIfaceA env) 0 context betaShape) := by
  obtain ⟨w⟩ := KEqPositive.eqFrame
  refine ⟨{
    target := KEqPositive.target _ _ _
    familyTelescope := w.familyTelescope
    telescope := w.telescope
    familyHeadType := w.familyHeadType
    indexGuard := w.indexGuard
    familyResult := w.familyResult
    prefixType := w.prefixType
    majorType := betaMajorTyped contextWf majorTyped
    canonicalType := w.canonicalType
    canonicalIota := w.canonicalIota
    minorType := ?_
  }⟩
  exact hasTyA_of_tyConvA resultTyped
    (motiveTypeConv contextWf parameterTyped (betaMajorTyped contextWf majorTyped)).symm

theorem betaKHead : KStage.Head env (iotaIfaceA env) 0 context
    (call (betaMajor (.bvar 0))) result betaShape.resultType :=
  .k betaShape betaFrame

theorem betaCallTyped : Nonempty (HasTyA env (iotaIfaceA env) 0 context
    (call (betaMajor (.bvar 0))) betaShape.resultType) := by
  obtain ⟨w⟩ := betaFrame
  obtain ⟨hc⟩ := w.sound closed liftIface (iotaFnA_recHead env) substIface contextWf
  exact ⟨convA_hasTy_left closed liftIface (iotaFnA_recHead env) substIface contextWf hc⟩

/-- The competing old step is an actual `TyHRedA.major`, including its
dependent reduct typing; it is not just an untyped computation. -/
theorem betaOldTypedStep : Nonempty (TyHRedA env (iotaIfaceA env) 0 context
    (call (betaMajor (.bvar 0))) (call (.bvar 0)) betaShape.resultType) := by
  obtain ⟨hf⟩ := prefixTyped
  obtain ⟨hc⟩ := KEqPositive.eqFrame_sound
  let hD := eqTyped contextWf parameterTyped parameterTyped
  let hΓD := CtxWfA.assumption contextWf hD
  let hv : HasTyA env (iotaIfaceA env) 0 (.assumption domain :: context)
      (.bvar 0) domain :=
    .bvar _ 0 domain .zero rfl (eqTyped hΓD parameterTyped parameterTyped)
  have hrt : HasTyA env (iotaIfaceA env) 0 context
      (call (.bvar 0)) betaShape.resultType :=
    hasTyA_of_tyConvA
      (convA_hasTy_left closed liftIface (iotaFnA_recHead env) substIface contextWf hc)
      (motiveTypeConv contextWf parameterTyped (betaMajorTyped contextWf majorTyped)).symm
  exact ⟨.major context EqLargeFixture.recPrefix (betaMajor (.bvar 0)) (.bvar 0) domain
    (motiveAt parameter (.bvar 0)) domain .zero two
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (betaMajorStep contextWf majorTyped) (.refl context domain) hf
    (motiveAtTyped hΓD parameterTyped hv) hrt⟩

theorem betaOldStep : hStepFnA env (iotaIfaceA env).fn context
    (call (betaMajor (.bvar 0))) = some (call (.bvar 0)) := by
  obtain ⟨h⟩ := betaOldTypedStep
  exact tyHRedA_hStep h

theorem reductsDiffer : call (.bvar 0) ≠ result := by decide

/-- Determinism concerns the contextual term relation, independently of
which type witnesses establish its steps. -/
def Deterministic (R : LCtxA → ExprA → ExprA → Prop) : Prop :=
  ∀ Γ a b c, R Γ a b → R Γ a c → b = c

/-- Including all existing typed head steps and all K frames is
incompatible with determinism, even restricted to well-formed contexts
of this one admitted environment. -/
theorem no_deterministic_extension (R : LCtxA → ExprA → ExprA → Prop)
    (hOld : ∀ (Γ : LCtxA) (a b T : ExprA),
      CtxWfA env (iotaIfaceA env) 0 Γ →
      TyHRedA env (iotaIfaceA env) 0 Γ a b T → R Γ a b)
    (hK : ∀ (Γ : LCtxA) (s : KStage.Shape),
      CtxWfA env (iotaIfaceA env) 0 Γ →
      Nonempty (KStage.Frame env (iotaIfaceA env) 0 Γ s) → R Γ s.source s.minor) :
    ¬ Deterministic R := by
  intro hd
  obtain ⟨h⟩ := betaOldTypedStep
  exact reductsDiffer (hd context (call (betaMajor (.bvar 0))) (call (.bvar 0)) result
    (hOld context _ _ betaShape.resultType contextWf h)
    (hK context betaShape contextWf betaFrame))

/-- The raw proposed union already fails determinism on the supplied
typed witness. -/
def RawUnion (Γ : LCtxA) (a b : ExprA) : Prop :=
  hStepFnA env (iotaIfaceA env).fn Γ a = some b ∨
    ∃ T, KStage.Head env (iotaIfaceA env) 0 Γ a b T

theorem rawUnion_not_deterministic : ¬ Deterministic RawUnion := by
  intro h
  exact reductsDiffer (h context (call (betaMajor (.bvar 0))) (call (.bvar 0)) result
    (.inl betaOldStep) (.inr ⟨betaShape.resultType, betaKHead⟩))

/-- Admission, well-formedness, a closed proof inhabitant, source typing,
and both competing typed steps are all supplied. -/
theorem inhabited_overlap :
    eraseEnv env = eqEnvT ∧ Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 context) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] (reflAt parameter) domain) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context
      (call (betaMajor (.bvar 0))) betaShape.resultType) ∧
    Nonempty (TyHRedA env (iotaIfaceA env) 0 context
      (call (betaMajor (.bvar 0))) (call (.bvar 0)) betaShape.resultType) ∧
    KStage.Head env (iotaIfaceA env) 0 context
      (call (betaMajor (.bvar 0))) result betaShape.resultType ∧
    call (.bvar 0) ≠ result :=
  ⟨erase_env, wf, ⟨contextWf⟩, ⟨reflTyped .nil parameterTyped⟩,
    betaCallTyped, betaOldTypedStep, betaKHead, reductsDiffer⟩

#print axioms betaMajor
#print axioms betaMajorTyped
#print axioms betaMajorStep
#print axioms betaShape
#print axioms betaFrame
#print axioms betaKHead
#print axioms betaCallTyped
#print axioms betaOldTypedStep
#print axioms betaOldStep
#print axioms reductsDiffer
#print axioms Deterministic
#print axioms no_deterministic_extension
#print axioms RawUnion
#print axioms rawUnion_not_deterministic
#print axioms inhabited_overlap

end Rcic.Declarative.Ann.LR3HeadBoundary

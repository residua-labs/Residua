import rcic.RcicAnnLR3HeadBoundary
import rcic.RcicAnnKDeterminism

/-!
# The exact substitution limit of old-first head priority

Old-first priority removes the overlapping beta-major K step.  At a
neutral proof major it still takes K.  Substituting a closed beta-redex
proof makes old evaluation available and suppresses that same K reduct
for one step.  All substitution premises are supplied below.

This only refutes exact one-step preservation under general typed
substitution.  The concrete substituted source reaches the K reduct in
two old steps, which is also witnessed here.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3HeadSubstBoundary

open Rcic.Declarative EqLargeFixture LR3HeadBoundary

/-- Old computation has priority; contextual K is available only when
the old computation returns `none`. -/
def OldFirst (Γ : LCtxA) (a b : ExprA) : Prop :=
  hStepFnA env (iotaIfaceA env).fn Γ a = some b ∨
    (hStepFnA env (iotaIfaceA env).fn Γ a = none ∧
      ∃ T, KStage.Head env (iotaIfaceA env) 0 Γ a b T)

/-- With the old evaluator stopped, every new head witness must be a K
frame.  Its minor is determined by the source, independently of typing
derivations and result-type annotations. -/
theorem head_reduct_unique_of_old_none {Γ : LCtxA} {a b c T U : ExprA}
    (hn : hStepFnA env (iotaIfaceA env).fn Γ a = none)
    (hb : KStage.Head env (iotaIfaceA env) 0 Γ a b T)
    (hc : KStage.Head env (iotaIfaceA env) 0 Γ a c U) : b = c := by
  have extract : ∀ {d V : ExprA}, KStage.Head env (iotaIfaceA env) 0 Γ a d V →
      ∃ s, Nonempty (KStage.Frame env (iotaIfaceA env) 0 Γ s) ∧
        s.source = a ∧ s.minor = d := by
    intro d V hd
    cases hd with
    | old h _ _ => exact Option.noConfusion (hn.symm.trans h.exec)
    | k s hs => exact ⟨s, hs, rfl, rfl⟩
  obtain ⟨s, ⟨hs⟩, hsa, hsb⟩ := extract hb
  obtain ⟨t, ⟨ht⟩, hta, htc⟩ := extract hc
  exact hsb.symm.trans
    ((hs.minor_eq_of_source_eq ht (hsa.trans hta.symm)).trans htc)

/-- Old-first priority really repairs the overlap: this is determinism
of the full contextual relation, not an assumed property. -/
theorem oldFirst_deterministic : Deterministic OldFirst := by
  intro Γ a b c hb hc
  rcases hb with hb | ⟨hn, T, hb⟩
  · rcases hc with hc | ⟨hn, _⟩
    · exact Option.some.inj (hb.symm.trans hc)
    · exact Option.noConfusion (hb.symm.trans hn)
  · rcases hc with hc | ⟨_, U, hc⟩
    · exact Option.noConfusion (hn.symm.trans hc)
    · exact head_reduct_unique_of_old_none hn hb hc

theorem neutralOldNone :
    hStepFnA env (iotaIfaceA env).fn context (call (.bvar 0)) = none := by decide

theorem neutralOldFirst : OldFirst context (call (.bvar 0)) result :=
  .inr ⟨neutralOldNone, KEqPositive.eqShape.resultType, KEqPositive.eqHead⟩

def closedMajor : ExprA := betaMajor (reflAt parameter)

def closeSubstitution : SubstA := SubstA.cons closedMajor SubstA.id

def closingTyped : SubstTyA env (iotaIfaceA env) 0 [] closeSubstitution context :=
  substTyA_cons_id closed liftIface .nil
    (betaMajorTyped .nil (reflTyped .nil parameterTyped))

theorem sourceSubst : substA closeSubstitution (call (.bvar 0)) = call closedMajor := rfl

theorem resultSubst : substA closeSubstitution result = result := rfl

theorem closedOldStep :
    hStepFnA env (iotaIfaceA env).fn [] (call closedMajor) =
      some (call (reflAt parameter)) := by decide

theorem closedOldSecondStep :
    hStepFnA env (iotaIfaceA env).fn [] (call (reflAt parameter)) =
      some result := by decide

theorem closedReductDiffers : call (reflAt parameter) ≠ result := by decide

/-- The original K frame survives this typed substitution.  It is the
priority guard, not K-frame transport, that excludes its immediate use. -/
theorem closedKHead : KStage.Head env (iotaIfaceA env) 0 []
    (call closedMajor) result
    (substA closeSubstitution KEqPositive.eqShape.resultType) := by
  have h := KStage.Head.subst closed liftIface (iotaFnA_recHead env) substIface
    contextWf closingTyped KEqPositive.eqHead
  simpa only [sourceSubst, resultSubst] using h

theorem closedNotOneStep : ¬ OldFirst [] (call closedMajor) result := by
  intro h
  rcases h with h | ⟨hn, _⟩
  · exact closedReductDiffers (Option.some.inj (closedOldStep.symm.trans h))
  · exact Option.noConfusion (closedOldStep.symm.trans hn)

/-- This is deliberately exact one-step substitution preservation,
including well-formed source and target contexts. -/
def ExactTypedSubstitution (R : LCtxA → ExprA → ExprA → Prop) : Prop :=
  ∀ (Γ Δ : LCtxA) (σ : SubstA),
    CtxWfA env (iotaIfaceA env) 0 Γ → CtxWfA env (iotaIfaceA env) 0 Δ →
    SubstTyA env (iotaIfaceA env) 0 Δ σ Γ →
    ∀ (a b : ExprA), R Γ a b → R Δ (substA σ a) (substA σ b)

theorem oldFirst_not_exactTypedSubstitution : ¬ ExactTypedSubstitution OldFirst := by
  intro h
  have hs := h context [] closeSubstitution contextWf .nil closingTyped
    (call (.bvar 0)) result neutralOldFirst
  exact closedNotOneStep (by simpa only [sourceSubst, resultSubst] using hs)

/-- The same concrete substitution is simulated by two old-first steps;
the one-step counterexample does not refute multistep simulation. -/
theorem closedTwoSteps :
    OldFirst [] (call closedMajor) (call (reflAt parameter)) ∧
    OldFirst [] (call (reflAt parameter)) result :=
  ⟨.inl closedOldStep, .inl closedOldSecondStep⟩

theorem inhabited_substitution_boundary :
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 context) ∧
    Nonempty (SubstTyA env (iotaIfaceA env) 0 [] closeSubstitution context) ∧
    OldFirst context (call (.bvar 0)) result ∧
    KStage.Head env (iotaIfaceA env) 0 [] (call closedMajor) result
      (substA closeSubstitution KEqPositive.eqShape.resultType) ∧
    ¬ OldFirst [] (call closedMajor) result ∧
    OldFirst [] (call closedMajor) (call (reflAt parameter)) ∧
    OldFirst [] (call (reflAt parameter)) result :=
  ⟨wf, ⟨contextWf⟩, ⟨closingTyped⟩, neutralOldFirst,
    closedKHead, closedNotOneStep, closedTwoSteps⟩

#print axioms OldFirst
#print axioms head_reduct_unique_of_old_none
#print axioms oldFirst_deterministic
#print axioms neutralOldNone
#print axioms neutralOldFirst
#print axioms closedMajor
#print axioms closeSubstitution
#print axioms closingTyped
#print axioms sourceSubst
#print axioms resultSubst
#print axioms closedOldStep
#print axioms closedOldSecondStep
#print axioms closedReductDiffers
#print axioms closedKHead
#print axioms closedNotOneStep
#print axioms ExactTypedSubstitution
#print axioms oldFirst_not_exactTypedSubstitution
#print axioms closedTwoSteps
#print axioms inhabited_substitution_boundary

end Rcic.Declarative.Ann.LR3HeadSubstBoundary

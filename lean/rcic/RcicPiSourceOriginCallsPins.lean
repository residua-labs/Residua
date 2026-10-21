import rcic.RcicPiSourceOriginCalls
import rcic.RcicPiSourceOriginPins

/-!
# Actual call-site tests, stored answers, and a generated-size control

The origins use the original proof data. Known generated answers are
bound to the exact previously implemented producer output. The inflation
control compares against a stated Nat input-size sum only: it is NOT a
refutation of all provenance measures or all possible global induction.
-/

namespace Rcic.Declarative.F8PiSourceOrigin.CallPins
open PEqTProofFront PEqLeafTPropPins

private def emptyCl : EnvClosed emptyEnv := envClosed_of_envWfT EnvWfT.empty
private def emptySub : EnvMembersSubstStable emptyEnv := envWfT_subst_inst EnvWfT.empty

/-- A genuine bounded caller can use the independent intro-spine solver.
The bound is supplied by the consumer, not asserted by this solver. -/
def localU : SourceUniqueBelow emptyEnv 0 [] p
    (stepSize Pins.wrappedStep + stepSize Pins.wrappedOther) :=
  fun ht hp _ => introTypeSpine_unique emptyCl emptySub (e := p) rfl ht hp

def bounded_left_join :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] q p aliasP ×'
      (ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] p p aliasP ×'
        ConvT emptyEnv 0 [] q p aliasP) :=
  finish_peak_below_left Pins.wrappedStep Pins.wrappedOther Pins.wrappedOrigin localU

/-- Right-branch origin, with the same canonical output orientation. -/
def bounded_right_join :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] p q aliasP ×'
      (ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] q q aliasP ×'
        ConvT emptyEnv 0 [] p q aliasP) :=
  finish_peak_below_right Pins.wrappedOther Pins.wrappedStep Pins.wrappedOrigin
    (fun ht hp _ => introTypeSpine_unique emptyCl emptySub (e := p) rfl ht hp)

/-- The same input is completed with neither a U callback nor a chain
argument: the independent solver works on the traced original fields. -/
def intro_origin_join :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] q p aliasP ×'
      (ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] p p aliasP ×'
        ConvT emptyEnv 0 [] q p aliasP) :=
  finish_origin_intro emptyCl emptySub Pins.wrappedStep Pins.wrappedOther Pins.wrappedOrigin rfl

/-- The actual old producer output from a beta/structural-leaf peak. -/
def emitted : ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] p rGood P :=
  (parRedT_propIndex_diamond_data (P_ty []) (.refl [] P) beta_branch peq_branch).1

def emitted_answer : AnsweredOrigin emitted :=
  generated_peak_origin_answer (P_ty []) (.refl [] P) beta_branch peq_branch

/-- No solver has rediscovered this answer: it is the original chain. -/
theorem emitted_answer_is_original : emitted_answer.2 = TyConvT.refl [] P := rfl

def emitted_wrapped : ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] p rGood aliasP :=
  .conv [] _ _ _ _ (.conv [] _ _ _ _ emitted alias_chain.symmT) (.refl [] aliasP)

def emitted_wrapped_answer : AnsweredOrigin emitted_wrapped :=
  answered_origin_conv (.refl [] aliasP) (answered_origin_conv alias_chain.symmT emitted_answer)

theorem wrapping_keeps_answer : emitted_wrapped_answer.2 = emitted_answer.2 := rfl

/-- Consume a produced leaf again, but use its stored answer rather
than recursively requesting uniqueness on its fabricated typings. -/
def emitted_second_peak :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] rGood p aliasP ×'
      (ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] p p aliasP ×'
        ConvT emptyEnv 0 [] rGood p aliasP) :=
  finish_peak_answered emitted_wrapped Pins.wrappedOther emitted_wrapped_answer

/-- The structural Pi branch asks no question of the bounded callback.
The callback is quantified, not supplied by any semantic row oracle. -/
theorem structural_dispatch_ignores_callback
    (hU : SourceUniqueBelow emptyEnv 0 [] Pins.piSource
      (stepSize Pins.piStructuralStep + stepSize
        (ParRedT.refl (PEq := PEqLeafT emptyEnv 0) [] Pins.piSource Pins.piIndex Pins.piSource_ty))) :
    pi_peak_dispatch_below Pins.piStructuralStep
      (.refl [] Pins.piSource Pins.piIndex Pins.piSource_ty) hU =
    Sum.inl (PiHead.mk (Pins.domain q) (.sort .zero) rfl,
      PiHead.mk (Pins.domain p) (.sort .zero) rfl) := rfl

/-- Inflate proof evidence without changing the term or its type. -/
def paddedProof : Nat → HasTyT emptyEnv 0 [] p P
  | 0 => p_ty []
  | k + 1 => .conv [] p P P .zero (paddedProof k)
      (.refl [] P (.sort .zero) (P_ty []))

/-- A genuine beta step with a larger carried reduct typing. -/
def paddedBeta (k : Nat) : ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] q p P :=
  .beta [] P (.bvar 0) (.bvar 0) p p P .zero .zero .zero
    (P_ty []) (P_ty [.assumption P]) (P_ty [])
    (.refl [.assumption P] (.bvar 0) P (.bvar [.assumption P] 0 P rfl))
    (.refl [] p P (p_ty [])) (paddedProof k)

/-- This origin is indexed by the actual new output of the old producer. -/
def paddedGenerated (k : Nat) :=
  generated_peak_origin_answer (P_ty []) (TyConvT.refl [] P)
    (paddedBeta k) (peq_branch (n := 0))

/-- All judgment-valued inputs of that producer are included in this
explicit size sum: proposition typing, type chain and both reductions. -/
def producerInputSize (k : Nat) : Nat :=
  hasTyTSize (P_ty (E := emptyEnv) (n := 0) []) +
    tyConvTSize (TyConvT.refl (E := emptyEnv) (n := 0) [] P) +
    stepSize (paddedBeta k) + stepSize (peq_branch (n := 0))

/-- The tempting original-input Nat descent fails after production,
even though local descent relative to the GENERATED step remains true. -/
theorem generated_origin_exceeds_producer_inputs :
    producerInputSize 32 < (paddedGenerated 32).1.origin.cost := by decide

/-- It remains safe to finish: hTP is an actual answer, not an oracle. -/
theorem padded_generated_answer_is_refl (k : Nat) :
    (paddedGenerated k).2 = TyConvT.refl [] P := rfl

def padded_second_peak :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] rGood p P ×'
      (ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] p p P ×'
        ConvT emptyEnv 0 [] rGood p P) :=
  finish_peak_answered
    (parRedT_propIndex_diamond_data (P_ty []) (.refl [] P)
      (paddedBeta 32) (peq_branch (n := 0))).1
    (.refl [] p P (p_ty [])) (paddedGenerated 32)

end Rcic.Declarative.F8PiSourceOrigin.CallPins

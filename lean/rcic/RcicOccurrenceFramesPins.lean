import rcic.RcicOccurrenceFrames
import rcic.RcicProofOccurrencesPins

/-!
Concrete preservation pins for the exact request maps, at nested beta/lam/app
and raw app/lam roots. Neither the host term nor its reduction is rebuilt.
The nonliteral bodyIndex is retained; no easy proposition-index replacement.
-/
namespace Rcic.Declarative.F8Occurrences.FramePins
open F8OriginSubst.Pins PEqTProofFront

private def innerRequests : Requests innerStep
  | _, .left => ⟨bodyIndex, xAtIndex⟩
  | _, .right => ⟨bodyIndex, yAtIndex⟩

private def innerAnswers : AnsweredOrigins innerStep innerRequests
  | _, .left => originalAnswer
  | _, .right => originalAnswer

def betaRequests : Requests Pins.betaWithProofBody
  | Sum.inl o, side => innerRequests o side
  | Sum.inr o, _ => nomatch o

def betaStore : AnsweredOrigins Pins.betaWithProofBody betaRequests :=
  answers_of_frame _ _ ⟨innerAnswers, fun o _ => nomatch o⟩

def lambdaRequests : Requests Pins.lambdaWithProofBody := innerRequests

def lambdaStore : AnsweredOrigins Pins.lambdaWithProofBody lambdaRequests :=
  answers_of_frame _ _ innerAnswers

def appRequests : Requests Pins.appWithProofArgument
  | Sum.inl o, _ => nomatch o
  | Sum.inr _, .left => ⟨P, p_ty []⟩
  | Sum.inr _, .right => ⟨P, q_ty []⟩

def appStore : AnsweredOrigins Pins.appWithProofArgument appRequests :=
  answers_of_frame _ _ ⟨(fun o _ => nomatch o), (fun _ side => match side with | .left => .refl [] P | .right => .refl [] P)⟩

/-- Assemble the raw app's two child stores independently. -/
def nestedStore : AnsweredOrigins (structuralInput 32) Pins.nestedRequests := by
  refine answers_of_frame _ _ (rawAnswers_of_frame _ _ ?_)
  constructor
  · intro o side
    match o with
    | Sum.inl (Sum.inl h) => nomatch h
    | Sum.inl (Sum.inr (Sum.inl h)) => nomatch h
    | Sum.inl (Sum.inr (Sum.inr h)) => nomatch h
    | Sum.inr _ => cases side <;> exact originalAnswer
  · intro o side
    cases side <;> exact .refl [] P

theorem beta_left_index : (betaRequests Pins.betaBodyOccurrence .left).index = bodyIndex := rfl
theorem beta_right_index : (betaRequests Pins.betaBodyOccurrence .right).index = bodyIndex := rfl
theorem beta_answer_exact : betaStore Pins.betaBodyOccurrence .left = originalAnswer := rfl
theorem lambda_answer_exact : lambdaStore Pins.lambdaBodyOccurrence .right = originalAnswer := rfl
theorem nested_answer_exact : nestedStore Pins.nestedLambda .left = originalAnswer := rfl

/-- Both occurrences and sides survive a full decomposition/assembly roundtrip. -/
theorem nested_roundtrip (o : Occ (structuralInput 32)) (side : Side) :
    answers_of_frame _ _ (frame_of_answers _ _ nestedStore) o side = nestedStore o side :=
  answers_frame_roundtrip _ _ nestedStore o side

end Rcic.Declarative.F8Occurrences.FramePins

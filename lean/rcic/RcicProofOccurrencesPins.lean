import rcic.RcicProofOccurrences
import rcic.RcicOriginSubstPins
import rcic.RcicPiSourceOriginPins

namespace Rcic.Declarative.F8Occurrences.Pins
open F8PiSourceOrigin PEqTProofFront F8OriginSubst F8OriginSubst.Pins

/-- A proof root under raw app -> lam-body, invisible to OriginTrace. -/
def nestedLambda : Occ (structuralInput 32) := .inl (.inr PUnit.unit)
def outerArgument : Occ (structuralInput 32) := .inr PUnit.unit

theorem nested_lambda_covered : nestedLambda ∈ occurrences (structuralInput 32) :=
  occurrences_complete _ nestedLambda

theorem nested_context_exact : (site (structuralInput 32) nestedLambda).context = binder := rfl
theorem nested_typing_exact : (site (structuralInput 32) nestedLambda).leftTy = xTy := rfl
theorem structural_count : (occurrences (structuralInput 32)).length = 2 := rfl

def betaWithProofBody :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] source (instantiate0 p y) commonIndex :=
  .beta [] P x y p p bodyIndex .zero .zero .zero
    (P_ty []) bodyIndexTy
    (substTy0 (envClosed_of_envWfT EnvWfT.empty) (envWfT_subst_inst EnvWfT.empty)
      (p_ty []) bodyIndexTy)
    innerStep (.refl [] p P (p_ty []))
    (substTy0 (envClosed_of_envWfT EnvWfT.empty) (envWfT_subst_inst EnvWfT.empty)
      (p_ty []) yAtIndex)

def betaBodyOccurrence : Occ betaWithProofBody := .inl PUnit.unit

def lambdaWithProofBody :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] (.lam P x) (.lam P y) (.pi P bodyIndex) :=
  .lam [] P P x y bodyIndex .zero .zero (.refl [] P (.sort .zero) (P_ty []))
    (P_ty []) bodyIndexTy innerStep (.lam [] P .zero y bodyIndex (P_ty []) yAtIndex)

def lambdaBodyOccurrence : Occ lambdaWithProofBody := PUnit.unit

def appWithProofArgument :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] (.app idP p) (.app idP q) P :=
  .app [] idP idP p q P P (.pi P P) .zero .zero
    (.refl [] idP (.pi P P) (idP_ty [])) (.refl [] (.pi P P))
    (P_ty [.assumption P]) (P_ty [])
    (.peq [] p q P PEqLeafTPropPins.first_leaf) (PEqLeafTPropPins.rGood_ty [])

def appArgumentOccurrence : Occ appWithProofArgument := .inr PUnit.unit

def piDomainOccurrence : Occ F8PiSourceOrigin.Pins.piStructuralStep :=
  .inl (.inr PUnit.unit)

theorem beta_count : (occurrences betaWithProofBody).length = 1 := rfl
theorem lambda_count : (occurrences lambdaWithProofBody).length = 1 := rfl
theorem app_count : (occurrences appWithProofArgument).length = 1 := rfl
theorem pi_count : (occurrences F8PiSourceOrigin.Pins.piStructuralStep).length = 1 := rfl

theorem beta_old_trace_absent (h : OriginTrace betaWithProofBody) : False := by cases h
theorem lambda_old_trace_absent (h : OriginTrace lambdaWithProofBody) : False := by cases h
theorem app_old_trace_absent (h : OriginTrace appWithProofArgument) : False := by cases h

private def noPReflOcc {Γ : LCtx} : RawOcc (PEqT.refl (E := emptyEnv) (n := 0) (Γ := Γ) P) → False
  | .inl h => nomatch h
  | .inr (.inl h) => nomatch h
  | .inr (.inr h) => nomatch h

/-- The typed position assignment is explicit, covers every address, and keeps
bodyIndex at the inner root rather than picking P just to make the answer easy. -/
def nestedRequests : Requests (structuralInput 32)
  | .inl (.inl impossible), _ => False.elim (noPReflOcc impossible)
  | .inl (.inr _), .left => ⟨bodyIndex, xAtIndex⟩
  | .inl (.inr _), .right => ⟨bodyIndex, yAtIndex⟩
  | .inr _, .left => ⟨P, p_ty []⟩
  | .inr _, .right => ⟨P, q_ty []⟩

/-- A real nested example of the invariant; not a supplier for arbitrary inputs. -/
def nestedAnswers : AnsweredOrigins (structuralInput 32) nestedRequests
  | .inl (.inl impossible), _ => False.elim (noPReflOcc impossible)
  | .inl (.inr _), .left => originalAnswer
  | .inl (.inr _), .right => originalAnswer
  | .inr _, .left => .refl [] P
  | .inr _, .right => .refl [] P

theorem nested_index_retained : (nestedRequests nestedLambda .left).index = bodyIndex := rfl

def emitted := (parRedT_propIndex_diamond_data (P_ty (E := emptyEnv) (n := 0) [])
  (.refl [] P) PEqLeafTPropPins.beta_branch PEqLeafTPropPins.peq_branch).1

def emittedRequests : Requests emitted :=
  peakRequests (P_ty []) (.refl [] P) PEqLeafTPropPins.beta_branch PEqLeafTPropPins.peq_branch

def emittedAnswers : AnsweredOrigins emitted emittedRequests :=
  peakAnswers (P_ty []) (.refl [] P) PEqLeafTPropPins.beta_branch PEqLeafTPropPins.peq_branch

theorem emitted_count : (occurrences emitted).length = 1 := rfl

end Rcic.Declarative.F8Occurrences.Pins

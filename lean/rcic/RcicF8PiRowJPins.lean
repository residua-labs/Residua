import rcic.RcicF8JTransPins
import rcic.RcicF8PiRowJ

/-! Task 1 pins through the packaging adapter. closure_claim = 0. -/
set_option autoImplicit false
set_option maxHeartbeats 0
namespace Rcic.Declarative.F8Measure.PiRowPackaging.JPins
open PEqTProofFront PEqLeafTPropPins
open J5a.Pins

def out (su : F8A2Support.SortUnique emptyEnv 0) : J3.Result EnvWfT.empty roots input :=
  J5a.buildFragment EnvWfT.empty su roots CtxWfT.nil input admissible_input cert

theorem certified_return (su : F8A2Support.SortUnique emptyEnv 0) :
    j5aCertified EnvWfT.empty su roots CtxWfT.nil input cert = some (out su) := rfl

theorem projected_return (su : F8A2Support.SortUnique emptyEnv 0) :
    j5aWfP EnvWfT.empty su roots CtxWfT.nil input cert = some (out su).valley := rfl

theorem projected_trans (su : F8A2Support.SortUnique emptyEnv 0) :
    j5aWfP EnvWfT.empty su roots CtxWfT.nil input cert = some groundValley := rfl

theorem same_output (su : F8A2Support.SortUnique emptyEnv 0) :
    ∃ actual : J3.Result EnvWfT.empty roots input,
      j5aCertified EnvWfT.empty su roots CtxWfT.nil input cert = some actual ∧
      actual.valley = groundValley :=
  (j5aWfP_some_iff EnvWfT.empty su roots CtxWfT.nil input cert groundValley).mp
    (projected_trans su)

/-- A typed view of the certificates returned by the actual worker. -/
def leftCertificates (su : F8A2Support.SortUnique emptyEnv 0) :
    J3.StepCertificate roots [.cv input] (closingStep.val cl ss) × PUnit :=
  Eq.mp (congrArg
    (fun v : Valley roots [] q third aliasP =>
      J3.Certified roots [.cv input] (v.left.val cl ss))
    (J5a.Pins.actual_worker su)) (out su).leftTiles

def emittedTile (su : F8A2Support.SortUnique emptyEnv 0) : DTile roots :=
  (leftCertificates su).1.tile

/-- Same output, exact emitted raw step (including its index), exact removed caller. -/
def Accepts (su : F8A2Support.SortUnique emptyEnv 0) (candidate : DTile roots) : Prop :=
  j5aCertified EnvWfT.empty su roots CtxWfT.nil input cert = some (out su) ∧
  j5aWfP EnvWfT.empty su roots CtxWfT.nil input cert = some (out su).valley ∧
  HEq candidate.step (emittedTile su).step ∧ candidate.X = [.cv input]

def HeadersOnly (su : F8A2Support.SortUnique emptyEnv 0) (candidate : DTile roots) : Prop :=
  j5aCertified EnvWfT.empty su roots CtxWfT.nil input cert = some (out su) ∧
  j5aWfP EnvWfT.empty su roots CtxWfT.nil input cert = some (out su).valley ∧
  SameHeader candidate (emittedTile su)

def StepOnly (su : F8A2Support.SortUnique emptyEnv 0) (candidate : DTile roots) : Prop :=
  j5aCertified EnvWfT.empty su roots CtxWfT.nil input cert = some (out su) ∧
  j5aWfP EnvWfT.empty su roots CtxWfT.nil input cert = some (out su).valley ∧
  HEq candidate.step (emittedTile su).step

theorem actual_accepted (su : F8A2Support.SortUnique emptyEnv 0) :
    Accepts su (emittedTile su) := ⟨rfl, rfl, HEq.rfl, rfl⟩

/-- Same endpoints and index, but an extra raw conv constructor. -/
def wrappedActual (su : F8A2Support.SortUnique emptyEnv 0) : DTile roots :=
  ((leftCertificates su).1.reindex (TyConvT.refl [] aliasP)).tile

theorem step_mutant_accepts (su : F8A2Support.SortUnique emptyEnv 0) :
    HeadersOnly su (wrappedActual su) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem exact_step_refuses (su : F8A2Support.SortUnique emptyEnv 0) :
    ¬ Accepts su (wrappedActual su) := by
  intro h
  have he := eq_of_heq h.2.2.1
  cases he

theorem caller_mutant_accepts (su : F8A2Support.SortUnique emptyEnv 0) :
    StepOnly su badCaller := ⟨rfl, rfl, HEq.rfl⟩

theorem exact_caller_refuses (su : F8A2Support.SortUnique emptyEnv 0) :
    ¬ Accepts su badCaller := by
  intro h
  exact J5a.Pins.exact_caller_refuses h.2.2.2

end Rcic.Declarative.F8Measure.PiRowPackaging.JPins

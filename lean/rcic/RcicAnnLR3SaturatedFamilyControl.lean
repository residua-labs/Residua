import rcic.RcicAnnLR3SaturatedFamilyCode
import rcic.RcicAnnLR3RetainedAccEnvironment

/-!
# The admitted retained-Acc signature in the saturated family interface

The source index/guard data and constructor raw image are unchanged.
The new family carrier admits every application-neutral as a legal leaf.
The structural family quotient is retained: this control does not claim
that proof irrelevance or a source recursor arm follows from that quotient.
closure_claim = 0.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.SaturatedFamilyControl

open Rcic.Declarative
open UnitModel TypedPER TypedInductive NeutralDataFamily
open RetainedAccFamily

abbrev Element (i : Index) :=
  SaturatedFamilyCode.Element signature constructorValue i

def reflect (i : Index) (x : Value) (hx : CandidatePi.Neutral x) : Element i :=
  SaturatedFamilyCode.reflect signature constructorValue i x hx

def major (A : IndexCode) : Element (classify A) :=
  SaturatedFamilyCode.node signature constructorValue (classify A)
    (IndexedFamilyDecoder.ruleClass semanticData (classify A))
    (fun p => reflect (IndexedFamilyDecoder.child semanticData (classify A) p)
      (NeutralPER.neutralAtom 7) (.atom 7))

theorem major_member (A : IndexCode) : PairPER (major A) (major A) :=
  (major A).admitted

theorem major_value (A : IndexCode) :
    (major A).value = (RetainedAccFamily.pairedMajor A).value := rfl

/-- The source class is inhabited. Saturation also includes the neutral
application to every retained, bottom-completed proposition index. -/
theorem admitted_saturated_control (A B : IndexCode) (name : Nat) :
    Nonempty (EnvWfA noIotaA pinAccGroupEnvA) ∧
    falseIndex ≠ trueIndex ∧
    PairPER (major A) (major A) ∧
    (major A).value = (RetainedAccFamily.pairedMajor A).value ∧
    PairPER
      (reflect (classify B)
        (NeutralPi.applyValue (NeutralPER.neutralAtom name)
          (RetainedAccEnvironment.codeValue A))
        (.app (.atom name) _ (CandidatePi.nonempty_of_bot
          (RetainedAccEnvironment.closed A).bot)))
      (reflect (classify B)
        (NeutralPi.applyValue (NeutralPER.neutralAtom name)
          (RetainedAccEnvironment.codeValue A))
        (.app (.atom name) _ (CandidatePi.nonempty_of_bot
          (RetainedAccEnvironment.closed A).bot))) :=
  ⟨⟨pinAccGroupWfA noIotaA⟩, indices_distinct, major_member A, major_value A,
    (reflect (classify B) _ (.app (.atom name) _
      (CandidatePi.nonempty_of_bot (RetainedAccEnvironment.closed A).bot))).admitted⟩

end Rcic.Declarative.Ann.LR3.SaturatedFamilyControl

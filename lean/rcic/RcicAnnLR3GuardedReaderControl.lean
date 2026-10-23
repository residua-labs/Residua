import rcic.RcicAnnLR3GuardedCodeRead
import rcic.RcicAnnLR3TaggedKCoherenceBoundary
import rcic.RcicAnnLR3SemanticMemberAdmissionDelta

/-!
# Guarded reading of the actual positive Pi/K fixture

The decision is the proved semantic guard for the admitted source fixture.
The output is the actual existing Pi minor code, with its evaluator image.
No fresh K edge or alternate family attachment enters CodeRelated.
The semantic major in this control is the proof unit. This does not assert
an evaluator-image law for all semantic neutral majors or a whole-language
reader. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.GuardedReaderControl

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TaggedSaturatedTower TaggedKClosure
open TaggedKCoherenceBoundary

def guard (ν : Valuation) : Prop := Guard (frame ν)

def decision (ν : Valuation) : Decidable (guard ν) :=
  isTrue (frame_guard ν)

def readCall (ν : Valuation) (name : Nat) : Code.{0} 1 :=
  GuardedCodeRead.ofDecision (decision ν) (minorCode ν) (Code.neutral 1 name)

theorem readCall_reads (ν : Valuation) (name : Nat) :
    GuardedCodeRead.Read (guard ν) (minorCode ν) (Code.neutral 1 name)
      (readCall ν name) :=
  GuardedCodeRead.ofDecision_reads (decision ν) _ _

theorem readCall_same_minor (ν : Valuation) (name : Nat) :
    readCall ν name = minorCode ν := rfl

theorem readCall_tag (ν : Valuation) (name : Nat) :
    (readCall ν name).tag = .pi := rfl

theorem readCall_actual_image (ν : Valuation) (name : Nat) :
    ValueEq (readCall ν name).view.value
      (TaggedKEvaluation.image ν fixtureEnv (EqLargeFixture.call (.bvar 0))) :=
  (minorCode_image ν).trans (TaggedKEvaluation.open_call_image ν).symm

def readCall_kernelIso (ν : Valuation) (name : Nat) :
    KernelIso (readCall ν name).kernel (minorCode ν).kernel :=
  KernelIso.refl (minorCode ν).kernel

theorem readCall_related (ν : Valuation) (name : Nat) :
    CodeRelated (readCall ν name) (minorCode ν) := codeRelated_refl _

theorem readCall_transport (ν : Valuation) (name : Nat) :
    PairTransport (readCall ν name) (minorCode ν) :=
  pairTransport_of_kernelIso (readCall_kernelIso ν name)

theorem readCall_transport_reverse (ν : Valuation) (name : Nat) :
    PairTransport (minorCode ν) (readCall ν name) :=
  pairTransport_of_kernelIso (readCall_kernelIso ν name).symm

theorem readCall_decoded_same (ν : Valuation) (name : Nat) :
    NeutralK.Same (Decoded (readCall ν name)) (Decoded (minorCode ν)) :=
  codeRelated_decoded_same (readCall_related ν name)

def readFrame (ν : Valuation) (name : Nat) : Frame.{0} 1 :=
  { frame ν with call := readCall ν name }

theorem readFrame_atTarget (ν : Valuation) (name : Nat) :
    AtTarget ν (readFrame ν name) := compatible_atTarget ν

theorem readFrame_guard (ν : Valuation) (name : Nat) :
    Guard (readFrame ν name) := frame_guard ν

theorem readCall_inhabited (ν : Valuation) (name : Nat) :
    ∃ a : (readCall ν name).Element,
      (readCall ν name).view.relation a a := minor_inhabited ν

theorem readCall_stable {ν μ : Valuation}
    (h : PairedStatements.ValuationRel ν μ) (name : Nat) :
    readCall ν name = readCall μ name := by
  have he : ν = μ := funext h
  cases he
  rfl

theorem readCall_independent_name (ν : Valuation) (name other : Nat) :
    readCall ν name = readCall ν other := rfl

/-- The old sort/delta reader is also stable under the actual level relation.
This is not a claim that its range already contains general tagged codes. -/
theorem admitted_read_stable {I : IotaIfaceA} {E : ResolvedEnvA}
    (hE : EnvWfA I E) {ν μ : Valuation}
    (h : PairedStatements.ValuationRel ν μ) (A : ExprA) :
    AdmissionUniverseReadback.readAdmitted hE ν A =
      AdmissionUniverseReadback.readAdmitted hE μ A := by
  have he : ν = μ := funext h
  cases he
  rfl

theorem admitted_positive_control (ν : Valuation) (name : Nat) :
    AtTarget ν (readFrame ν name) ∧
    Nonempty (ConvA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      EqLargeFixture.context (EqLargeFixture.call (.bvar 0))
      EqLargeFixture.result (.sort EqLargeFixture.one)) ∧
    GuardedCodeRead.Read (guard ν) (minorCode ν) (Code.neutral 1 name)
      (readCall ν name) ∧
    readCall ν name = minorCode ν ∧
    ValueEq (readCall ν name).view.value
      (TaggedKEvaluation.image ν fixtureEnv (EqLargeFixture.call (.bvar 0))) ∧
    CodeRelated (readCall ν name) (minorCode ν) ∧
    PairTransport (readCall ν name) (minorCode ν) ∧
    PairTransport (minorCode ν) (readCall ν name) ∧
    NeutralK.Same (Decoded (readCall ν name)) (Decoded (minorCode ν)) :=
  ⟨readFrame_atTarget ν name, EqLargeFixture.conversion, readCall_reads ν name,
    readCall_same_minor ν name, readCall_actual_image ν name,
    readCall_related ν name, readCall_transport ν name,
    readCall_transport_reverse ν name, readCall_decoded_same ν name⟩

end Rcic.Declarative.Ann.LR3.GuardedReaderControl

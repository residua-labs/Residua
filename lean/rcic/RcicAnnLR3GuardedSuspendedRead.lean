import rcic.RcicAnnLR3GuardedTaggedCode
import rcic.RcicAnnLR3GuardedTypeImage
import rcic.RcicAnnLR3GuardedMinorTransport
import rcic.RcicAnnLR3GuardedImageBoundary

/-!
# A total suspended reading of the actual open Eq call

The source call, retained index assignment, actual Pi minor and local
neutral-call name are fixed by the existing open-call construction. Reading
now constructs a certified suspended code without deciding its guard.
Actual input images are supplied for every proposition-index assignment.

The normalized type image is the conditional raw value. Under the true
guard it is the actual minor image; under the false guard it is the named
native fallback. This is not an image theorem for the old unguarded call
evaluator, a general source reader, a source substitution theorem, or a
proof of all-Pi closure. Exact raw-neutral CR3 is not claimed for the actual
Pi action supplier. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.GuardedSuspendedRead

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel GuardedReaderSource
open TaggedSaturatedTower (KernelIso)

def reading (ν : Valuation) (a : IndexAssignment) (name : Nat) :
    GuardedTaggedCode.Code.{0} 1 :=
  GuardedTaggedCode.Code.guarded (guard a)
    (GuardedTaggedCode.Code.legacy (GuardedOpenEqCall.minorCode ν a))
    (GuardedTaggedCode.Code.legacy (TaggedSaturatedTower.Code.neutral.{0} 1 name))
    (GuardedTypeImage.source ν a name)

def Read (ν : Valuation) (a : IndexAssignment) (name : Nat)
    (C : GuardedTaggedCode.Code.{0} 1) : Prop := C = reading ν a name

theorem reading_reads (ν : Valuation) (a : IndexAssignment) (name : Nat) :
    Read ν a name (reading ν a name) := rfl

theorem read_functional {ν : Valuation} {a : IndexAssignment} {name : Nat}
    {C D : GuardedTaggedCode.Code.{0} 1}
    (hC : Read ν a name C) (hD : Read ν a name D) : C = D := hC.trans hD.symm

theorem total_unique (ν : Valuation) (a : IndexAssignment) (name : Nat) :
    ∃ C, Read ν a name C ∧ ∀ D, Read ν a name D → D = C :=
  ⟨reading ν a name, rfl, fun _ h => h⟩

theorem reading_tag (ν : Valuation) (a : IndexAssignment) (name : Nat) :
    (reading ν a name).tag = .guarded := rfl

theorem reading_type_image (ν : Valuation) (a : IndexAssignment) (name : Nat) :
    (reading ν a name).view.value =
      GuardedKernel.conditionalValue (guard a)
        (GuardedOpenEqCall.minorCode ν a).view.value
        (NativeMemberValues.value (some 1) name) :=
  GuardedTypeImage.source_value ν a name

def isoTrue {ν : Valuation} {a : IndexAssignment} {name : Nat} (hG : guard a) :
    KernelIso (reading ν a name).kernel (GuardedOpenEqCall.minorCode ν a).kernel :=
  GuardedKernel.isoTrue (GuardedTypeImage.source ν a name) hG

def isoFalse {ν : Valuation} {a : IndexAssignment} {name : Nat} (hG : ¬ guard a) :
    KernelIso (reading ν a name).kernel
      (TaggedSaturatedTower.Code.neutral.{0} 1 name).kernel :=
  GuardedKernel.isoFalse (GuardedTypeImage.source ν a name) hG

theorem converts_true {ν : Valuation} {a : IndexAssignment} {name : Nat}
    (hG : guard a) :
    GuardedTaggedCode.Converts (reading ν a name)
      (GuardedTaggedCode.Code.legacy (GuardedOpenEqCall.minorCode ν a)) :=
  ⟨isoTrue hG⟩

theorem converts_false {ν : Valuation} {a : IndexAssignment} {name : Nat}
    (hG : ¬ guard a) :
    GuardedTaggedCode.Converts (reading ν a name)
      (GuardedTaggedCode.Code.legacy (TaggedSaturatedTower.Code.neutral.{0} 1 name)) :=
  ⟨isoFalse hG⟩

/-- Under the guard, the normalized reading has the actual source minor's
evaluation image; no result-image property of the old call is used. -/
theorem image_true {ν : Valuation} {a : IndexAssignment} {name : Nat}
    (hG : guard a) :
    ValueEq (reading ν a name).view.value
      (TaggedKEvaluation.image ν (rawEnvironment a) EqLargeFixture.result) :=
  GuardedTypeImage.source_true hG

theorem image_false {ν : Valuation} {a : IndexAssignment} {name : Nat}
    (hG : ¬ guard a) :
    ValueEq (reading ν a name).view.value (NativeMemberValues.value (some 1) name) :=
  GuardedTypeImage.source_false hG

theorem decoded_true {ν : Valuation} {a : IndexAssignment} {name : Nat}
    (hG : guard a) :
    NeutralK.Same (GuardedTaggedCode.Decoded (reading ν a name).kernel)
      (GuardedTaggedCode.Decoded (GuardedOpenEqCall.minorCode ν a).kernel) :=
  GuardedTaggedCode.decoded_same (isoTrue hG)

theorem decoded_false {ν : Valuation} {a : IndexAssignment} {name : Nat}
    (hG : ¬ guard a) :
    NeutralK.Same (GuardedTaggedCode.Decoded (reading ν a name).kernel)
      (GuardedTaggedCode.Decoded (TaggedSaturatedTower.Code.neutral.{0} 1 name).kernel) :=
  GuardedTaggedCode.decoded_same (isoFalse hG)

/-- Designated members are constructed unconditionally. These points are
the suspended branch points; this is not arbitrary raw-neutral CR3. -/
theorem designated_member (ν : Valuation) (a : IndexAssignment) (name j : Nat) :
    (reading ν a name).view.relation
      ((reading ν a name).view.point j) ((reading ν a name).view.point j) :=
  (reading ν a name).view.point_member j

theorem universe_member (ν : Valuation) (a : IndexAssignment) (name : Nat) :
    (GuardedTaggedCode.universeCode.{0} 1).view.relation
      (reading ν a name) (reading ν a name) :=
  GuardedTaggedCode.universe_member 1 (reading ν a name)

/-- The actual minor is independent of the input valuation/environment;
guard coherence and native-name identity complete the genuine transport. -/
def relatedIso (ν μ : Valuation) (a b : IndexAssignment) (name : Nat)
    (h : IndexRel a b) : KernelIso (reading ν a name).kernel (reading μ b name).kernel :=
  GuardedKernelTransport.isoConditional
    (GuardedTypeImage.source ν a name) (GuardedTypeImage.source μ b name)
    (GuardedTypeImage.source_value ν a name) (GuardedTypeImage.source_value μ b name)
    (guard_congr h) (GuardedMinorTransport.openMinorIso ν μ a b)
    (KernelIso.refl (TaggedSaturatedTower.Code.neutral.{0} 1 name).kernel)

theorem related (ν μ : Valuation) (a b : IndexAssignment) (name : Nat)
    (h : IndexRel a b) :
    GuardedTaggedCode.CodeRelated (reading ν a name) (reading μ b name) :=
  ⟨rfl, ⟨relatedIso ν μ a b name h⟩⟩

/-- The advertised level-valuation relation is pointwise literal equality.
This fixed minor permits the stronger arbitrary-valuation theorem above. -/
theorem stable {ν μ : Valuation} {a b : IndexAssignment} (name : Nat)
    (_hν : PairedStatements.ValuationRel ν μ) (h : IndexRel a b) :
    GuardedTaggedCode.CodeRelated (reading ν a name) (reading μ b name) :=
  related ν μ a b name h

theorem read_stable {ν μ : Valuation} {a b : IndexAssignment} {name : Nat}
    {C D : GuardedTaggedCode.Code.{0} 1}
    (h : IndexRel a b) (hC : Read ν a name C) (hD : Read μ b name D) :
    GuardedTaggedCode.CodeRelated C D := by
  change C = reading ν a name at hC
  change D = reading μ b name at hD
  rw [hC, hD]
  exact related ν μ a b name h

/-- Under false guards, conversion still sees the actual native name,
including across different valuations and retained index assignments. -/
theorem false_converts_iff (ν μ : Valuation) (a b : IndexAssignment) (r s : Nat)
    (ha : ¬ guard a) (hb : ¬ guard b) :
    GuardedTaggedCode.Converts (reading ν a r) (reading μ b s) ↔ r = s := by
  constructor
  · intro h
    apply (GuardedTaggedCode.neutral_converts_iff.{0} 1 r s).mp
    exact GuardedTaggedCode.converts_trans
      (GuardedTaggedCode.converts_symm (converts_false (ν := ν) (name := r) ha))
      (GuardedTaggedCode.converts_trans h (converts_false (ν := μ) (name := s) hb))
  · intro h
    cases h
    exact GuardedTaggedCode.converts_trans (converts_false (ν := ν) (name := r) ha)
      (GuardedTaggedCode.converts_symm (converts_false (ν := μ) (name := r) hb))

theorem false_related_iff (ν μ : Valuation) (a b : IndexAssignment) (r s : Nat)
    (ha : ¬ guard a) (hb : ¬ guard b) :
    GuardedTaggedCode.CodeRelated (reading ν a r) (reading μ b s) ↔ r = s :=
  ⟨fun h => (false_converts_iff ν μ a b r s ha hb).mp h.2,
    fun h => ⟨rfl, (false_converts_iff ν μ a b r s ha hb).mpr h⟩⟩

def readPolicy (ν : Valuation) (i : GuardedOpenEqCall.PolicyInput) :
    GuardedTaggedCode.Code.{0} 1 :=
  reading ν i.assignment GuardedOpenEqCall.callName

/-- Totality on the exact admitted call and its constructed interpreted
inputs. The output is suspended; no existence premise for G/¬G is used. -/
def InterpretedTotal (ν : Valuation) : Prop :=
  ∀ P : Prop, ∃ (i : GuardedOpenEqCall.PolicyInput) (C : GuardedTaggedCode.Code.{0} 1),
    i.assignment = propositionAssignment P 0 ∧ GuardedOpenEqCall.InputImages ν i ∧
      Read ν i.assignment GuardedOpenEqCall.callName C

theorem interpreted_total (ν : Valuation) : InterpretedTotal ν := by
  intro P
  obtain ⟨i, hi, himages⟩ := GuardedOpenEqCall.proposition_policy_images ν P
  exact ⟨i, readPolicy ν i, hi, himages, rfl⟩

/-- This contrasts two precisely stated policies on the same interpreted
source-input class; it is not a decision procedure for semantic equality. -/
theorem suspended_total_and_eager_boundary (ν : Valuation) :
    InterpretedTotal ν ∧
      (GuardedOpenEqCall.InterpretedTotal ν ↔ (∀ P : Prop, P ∨ ¬ P)) :=
  ⟨interpreted_total ν, GuardedOpenEqCall.interpreted_total_iff_em ν⟩

theorem true_control (ν : Valuation) (name : Nat) :
    GuardedTaggedCode.Converts (reading ν (propositionAssignment True 0) name)
      (GuardedTaggedCode.Code.legacy
        (GuardedOpenEqCall.minorCode ν (propositionAssignment True 0))) :=
  converts_true ((proposition_guard_iff True 0).mpr True.intro)

theorem false_control (ν : Valuation) (name : Nat) :
    GuardedTaggedCode.Converts (reading ν (propositionAssignment False 0) name)
      (GuardedTaggedCode.Code.legacy (TaggedSaturatedTower.Code.neutral.{0} 1 name)) :=
  converts_false (fun h => (proposition_guard_iff False 0).mp h)

/-- An output interface seeing only the erased environment cannot recover
this normalized type image on the actual retained-index input class. -/
def RawOutputImage (ν : Valuation) (name : Nat) (eval : EnvI → Value) : Prop :=
  ∀ P : Prop, ValueEq (eval (rawEnvironment (propositionAssignment P 0)))
    (reading ν (propositionAssignment P 0) name).view.value

theorem no_raw_output_image (ν : Valuation) (name : Nat) (eval : EnvI → Value) :
    ¬ RawOutputImage ν name eval := by
  intro h
  have ht := (h True).trans
    (image_true (ν := ν) (name := name)
      ((proposition_guard_iff True 0).mpr True.intro))
  have hf := (h False).trans
    (image_false (ν := ν) (name := name)
      (fun hg => (proposition_guard_iff False 0).mp hg))
  rw [proposition_raw_environments_same True False 0] at ht
  exact GuardedImageBoundary.result_image_not_native ν
    (rawEnvironment (propositionAssignment True 0)) (some 1) name
    (ht.symm.trans hf)

theorem old_call_output_image_impossible (ν : Valuation) (name : Nat) :
    ¬ RawOutputImage ν name
      (fun ρ => TaggedKEvaluation.image ν ρ
        (GuardedOpenEqCall.call GuardedReaderSource.proofTerm)) :=
  no_raw_output_image ν name _

/-- Both separating inputs come with the actual source admission, call
typing and all input images. The missing information is retained semantic
index data; this does not forbid an evaluator that keeps that data. -/
theorem inhabited_raw_output_boundary (ν : Valuation) (name : Nat) :
    ∃ i j : GuardedOpenEqCall.PolicyInput,
      i.assignment = propositionAssignment True 0 ∧
      j.assignment = propositionAssignment False 0 ∧
      GuardedOpenEqCall.InputImages ν i ∧ GuardedOpenEqCall.InputImages ν j ∧
      rawEnvironment i.assignment = rawEnvironment j.assignment ∧
      ∀ eval : EnvI → Value, ¬ RawOutputImage ν name eval := by
  obtain ⟨i, hi, him⟩ := GuardedOpenEqCall.proposition_policy_images ν True
  obtain ⟨j, hj, hjm⟩ := GuardedOpenEqCall.proposition_policy_images ν False
  refine ⟨i, j, hi, hj, him, hjm, ?_, no_raw_output_image ν name⟩
  rw [hi, hj]
  exact proposition_raw_environments_same True False 0

end Rcic.Declarative.Ann.LR3.GuardedSuspendedRead

import rcic.RcicAnnLR3GuardedSuspendedRead
import rcic.RcicAnnLR3GuardedConversionUniverse
import rcic.RcicAnnLR3RetainedArmTransfer

/-!
# Retained evaluation of the admitted open Eq call

The semantic result retains two distinct observations: the actual inherited
raw source evaluation and the certified suspended code. The environment
retains the actual admitted source input and its semantic index codes.
Reading the result projects the retained code; it never decodes a code
from its raw image, chooses a branch, or consults an external reader.

`evalRaw` is defined on every source expression and keeps the inherited raw
semantics exactly. `evalOpenEq` is the enriched evaluator of one fixed,
source-typed open Eq call. Its reading is total on every supplied PolicyInput,
and actual inputs with all input-image obligations are constructed for every
proposition. This is a concrete semantic fragment, not a whole-language
`evalSem`, a general source type reader, a new Eq supplier, or an NbE theorem.

The inherited input guard is retained on this fixed input class. The new
conversion universe interprets the output-code relations. The strong-tag
universe and its relation remain unchanged. A same-tag proposition-family
bridge below also obtains output stability from conversion of retained
indices. Generalizing this bridge to arbitrary tag-changing indices requires
a new Eq interpretation, which is not asserted here.

The conditional code image need not equal the inherited raw call image.
The final theorem proves that universal equality would contradict the
existing inhabited open-input boundary. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.RetainedOpenEqEvaluation

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER
open GuardedTaggedCode

universe u

/-- Raw execution and the interpreted type code are retained separately.
Only the concrete evaluator below supplies their source provenance. -/
structure SemValue (k : Nat) where
  raw : Value
  code : Code.{u} k

def erase {k : Nat} (s : SemValue.{u} k) : Value := s.raw

def read {k : Nat} (s : SemValue.{u} k) : Code.{u} k := s.code

def reifyCode {k : Nat} (s : SemValue.{u} k) : Value := (read s).view.value

/-- The input includes actual environment admission, source context and
call typing, together with the retained semantic index assignment. -/
structure SemEnv where
  input : GuardedOpenEqCall.PolicyInput

def SemEnv.assignment (ρ : SemEnv) : GuardedReaderSource.IndexAssignment :=
  ρ.input.assignment

def eraseEnv (ρ : SemEnv) : EnvI :=
  GuardedReaderSource.rawEnvironment ρ.assignment

def evalRawIn (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : SemEnv) (e : ExprA) : Value :=
  EnvironmentEval.denote E F ν (eraseEnv ρ) e

def evalRaw (ν : Valuation) (ρ : SemEnv) (e : ExprA) : Value :=
  evalRawIn EqLargeFixture.env TaggedKEvaluation.eqSyntax ν ρ e

theorem evalRaw_erasure (ν : Valuation) (ρ : SemEnv) (e : ExprA) :
    evalRaw ν ρ e = TaggedKEvaluation.image ν (eraseEnv ρ) e := rfl

/-- Every predicate of the raw result transfers, uniformly over all source
expressions. The statement deliberately does not inspect retained codes. -/
theorem raw_predicate_bridge (ν : Valuation) (ρ : SemEnv) (e : ExprA)
    (P : Value → Prop) :
    P (evalRaw ν ρ e) ↔ P (TaggedKEvaluation.image ν (eraseEnv ρ) e) := Iff.rfl

theorem raw_relation_bridge (ν μ : Valuation) (ρ σ : SemEnv) (e f : ExprA)
    (R : Relation) :
    R (evalRaw ν ρ e) (evalRaw μ σ f) ↔
      R (TaggedKEvaluation.image ν (eraseEnv ρ) e)
        (TaggedKEvaluation.image μ (eraseEnv σ) f) := Iff.rfl

/-- The actual inherited application theorem is reused without reproof. -/
theorem raw_application (ν : Valuation) (ρ : SemEnv) (f a : ExprA) :
    ValueEq (evalRaw ν ρ (.app f a))
      (NeutralPi.applyValue (evalRaw ν ρ f) (evalRaw ν ρ a)) :=
  EnvironmentEval.denote_application EqLargeFixture.env TaggedKEvaluation.eqSyntax
    ν (eraseEnv ρ) f a

/-- The same erasure projection reuses transparent-definition unfolding
for arbitrary source environments and inherited family hooks. -/
theorem raw_delta {E : ResolvedEnvA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} {b : ExprA} (hm : E.members r = some m)
    (hb : m.bodyA = some b) (ht : transparent m.mclass = true)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : SemEnv) :
    ValueEq (evalRawIn E F ν ρ (.const r ls))
      (evalRawIn E F ν ρ (instantiateLevelsA ls b)) :=
  EnvironmentEval.denote_delta hm hb ht F ν (eraseEnv ρ)

/-- The two source type variables retain their supplied codes under the
same semantic-value interface as the open call. -/
def evalLeftIndex (ν : Valuation) (ρ : SemEnv) : SemValue.{0} 0 where
  raw := evalRaw ν ρ GuardedReaderSource.liftedLeftIndex
  code := Code.legacy ρ.assignment.left

def evalRightIndex (ν : Valuation) (ρ : SemEnv) : SemValue.{0} 0 where
  raw := evalRaw ν ρ GuardedReaderSource.liftedRightIndex
  code := Code.legacy ρ.assignment.right

theorem left_index_image (ν : Valuation) (ρ : SemEnv)
    (h : GuardedOpenEqCall.InputImages ν ρ.input) :
    ValueEq (erase (evalLeftIndex ν ρ)) (reifyCode (evalLeftIndex ν ρ)) :=
  h.left_image

theorem right_index_image (ν : Valuation) (ρ : SemEnv)
    (h : GuardedOpenEqCall.InputImages ν ρ.input) :
    ValueEq (erase (evalRightIndex ν ρ)) (reifyCode (evalRightIndex ν ρ)) :=
  h.right_image

/-- Same-tag input indices express the inherited local guard in the new
conversion universe using the actual retained variable evaluations. -/
theorem guard_as_conversion_universe (ν : Valuation) (ρ : SemEnv)
    (ht : ρ.assignment.left.tag = ρ.assignment.right.tag) :
    GuardedReaderSource.guard ρ.assignment ↔
      (GuardedConversionUniverse.conversionUniverse.{0} 0).view.relation
        (read (evalLeftIndex ν ρ)) (read (evalRightIndex ν ρ)) :=
  ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩

theorem proposition_guard_as_conversion_universe (ν : Valuation)
    {ρ : SemEnv} {P : Prop}
    (hρ : ρ.assignment = GuardedReaderSource.propositionAssignment P 0) :
    GuardedReaderSource.guard ρ.assignment ↔
      (GuardedConversionUniverse.conversionUniverse.{0} 0).view.relation
        (read (evalLeftIndex ν ρ)) (read (evalRightIndex ν ρ)) := by
  apply guard_as_conversion_universe ν ρ
  rw [hρ]
  rfl

/-- Enriched evaluation for the one fixed admitted open call. Its code is
computed from the retained indices and the existing actual Pi minor. -/
def evalOpenEq (ν : Valuation) (ρ : SemEnv) : SemValue.{0} 1 where
  raw := evalRaw ν ρ (GuardedOpenEqCall.call GuardedReaderSource.proofTerm)
  code := GuardedSuspendedRead.reading ν ρ.assignment GuardedOpenEqCall.callName

theorem erase_evalOpenEq (ν : Valuation) (ρ : SemEnv) :
    erase (evalOpenEq ν ρ) =
      TaggedKEvaluation.image ν (eraseEnv ρ)
        (GuardedOpenEqCall.call GuardedReaderSource.proofTerm) := rfl

theorem read_evalOpenEq (ν : Valuation) (ρ : SemEnv) :
    read (evalOpenEq ν ρ) =
      GuardedSuspendedRead.reading ν ρ.assignment GuardedOpenEqCall.callName := rfl

theorem evalOpenEq_reads (ν : Valuation) (ρ : SemEnv) :
    GuardedSuspendedRead.Read ν ρ.assignment GuardedOpenEqCall.callName
      (read (evalOpenEq ν ρ)) := rfl

theorem read_evalOpenEq_total_unique (ν : Valuation) (ρ : SemEnv) :
    ∃ C : Code.{0} 1,
      GuardedSuspendedRead.Read ν ρ.assignment GuardedOpenEqCall.callName C ∧
        ∀ D, GuardedSuspendedRead.Read ν ρ.assignment GuardedOpenEqCall.callName D → D = C :=
  GuardedSuspendedRead.total_unique ν ρ.assignment GuardedOpenEqCall.callName

theorem reifyCode_evalOpenEq (ν : Valuation) (ρ : SemEnv) :
    reifyCode (evalOpenEq ν ρ) =
      GuardedKernel.conditionalValue (GuardedReaderSource.guard ρ.assignment)
        (GuardedOpenEqCall.minorCode ν ρ.assignment).view.value
        (NativeMemberValues.value (some 1) GuardedOpenEqCall.callName) :=
  GuardedSuspendedRead.reading_type_image ν ρ.assignment GuardedOpenEqCall.callName

theorem read_conversion_universe_member (ν : Valuation) (ρ : SemEnv) :
    (GuardedConversionUniverse.conversionUniverse.{0} 1).view.relation
      (read (evalOpenEq ν ρ)) (read (evalOpenEq ν ρ)) :=
  GuardedConversionUniverse.member 1 (read (evalOpenEq ν ρ))

def SemEnv.Rel (ρ σ : SemEnv) : Prop :=
  GuardedReaderSource.IndexRel ρ.assignment σ.assignment

/-- The existing concrete transport of the minor and guard supplies actual
kernel conversion of readings; no raw type-image coherence is assumed. -/
theorem stableCodes (ν μ : Valuation) {ρ σ : SemEnv} (h : SemEnv.Rel ρ σ) :
    Converts (read (evalOpenEq ν ρ)) (read (evalOpenEq μ σ)) :=
  (GuardedSuspendedRead.related ν μ ρ.assignment σ.assignment
    GuardedOpenEqCall.callName h).2

theorem stable_conversion_universe (ν μ : Valuation) {ρ σ : SemEnv}
    (h : SemEnv.Rel ρ σ) :
    (GuardedConversionUniverse.conversionUniverse.{0} 1).view.relation
      (read (evalOpenEq ν ρ)) (read (evalOpenEq μ σ)) :=
  stableCodes ν μ h

theorem stable_decoded (ν μ : Valuation) {ρ σ : SemEnv} (h : SemEnv.Rel ρ σ) :
    NeutralK.Same (Decoded (read (evalOpenEq ν ρ)).kernel)
      (Decoded (read (evalOpenEq μ σ)).kernel) :=
  converts_decoded_same (stableCodes ν μ h)

/-- This relation uses conversion of the actual retained index codes.
Recovering the old input guard additionally uses tag agreement below. -/
def ConversionIndexRel (ρ σ : SemEnv) : Prop :=
  Converts (Code.legacy ρ.assignment.left) (Code.legacy σ.assignment.left) ∧
    Converts (Code.legacy ρ.assignment.right) (Code.legacy σ.assignment.right)

theorem indexRel_of_conversion {ρ σ : SemEnv} (h : ConversionIndexRel ρ σ)
    (hl : ρ.assignment.left.tag = σ.assignment.left.tag)
    (hr : ρ.assignment.right.tag = σ.assignment.right.tag) : SemEnv.Rel ρ σ :=
  ⟨⟨hl, h.1⟩, ⟨hr, h.2⟩⟩

/-- On the actual arbitrary-proposition input family, both index tags are
fixed. Hence conversion of retained indices suffices for output stability. -/
theorem proposition_stableCodes (ν μ : Valuation) {ρ σ : SemEnv} {P Q : Prop}
    (hρ : ρ.assignment = GuardedReaderSource.propositionAssignment P 0)
    (hσ : σ.assignment = GuardedReaderSource.propositionAssignment Q 0)
    (h : ConversionIndexRel ρ σ) :
    Converts (read (evalOpenEq ν ρ)) (read (evalOpenEq μ σ)) := by
  apply stableCodes ν μ
  apply indexRel_of_conversion h
  · rw [hρ, hσ]
    rfl
  · rw [hρ, hσ]
    rfl

theorem proposition_index_relation_iff {ρ σ : SemEnv} {P Q : Prop}
    (hρ : ρ.assignment = GuardedReaderSource.propositionAssignment P 0)
    (hσ : σ.assignment = GuardedReaderSource.propositionAssignment Q 0) :
    ConversionIndexRel ρ σ ↔ (P ↔ Q) := by
  unfold ConversionIndexRel
  rw [hρ, hσ]
  constructor
  · intro h
    exact (RetainedArmTransfer.proposition_converts_iff P Q).mp h.1
  · intro h
    exact ⟨(RetainedArmTransfer.proposition_converts_iff P Q).mpr h,
      converts_refl _⟩

theorem converts_true (ν : Valuation) (ρ : SemEnv)
    (hG : GuardedReaderSource.guard ρ.assignment) :
    Converts (read (evalOpenEq ν ρ))
      (Code.legacy (GuardedOpenEqCall.minorCode ν ρ.assignment)) :=
  GuardedSuspendedRead.converts_true hG

theorem converts_false (ν : Valuation) (ρ : SemEnv)
    (hG : ¬ GuardedReaderSource.guard ρ.assignment) :
    Converts (read (evalOpenEq ν ρ))
      (Code.legacy (TaggedSaturatedTower.Code.neutral.{0} 1 GuardedOpenEqCall.callName)) :=
  GuardedSuspendedRead.converts_false hG

theorem conversion_universe_true (ν : Valuation) (ρ : SemEnv)
    (hG : GuardedReaderSource.guard ρ.assignment) :
    (GuardedConversionUniverse.conversionUniverse.{0} 1).view.relation
      (read (evalOpenEq ν ρ))
      (Code.legacy (GuardedOpenEqCall.minorCode ν ρ.assignment)) :=
  converts_true ν ρ hG

theorem conversion_universe_false (ν : Valuation) (ρ : SemEnv)
    (hG : ¬ GuardedReaderSource.guard ρ.assignment) :
    (GuardedConversionUniverse.conversionUniverse.{0} 1).view.relation
      (read (evalOpenEq ν ρ))
      (Code.legacy (TaggedSaturatedTower.Code.neutral.{0} 1 GuardedOpenEqCall.callName)) :=
  converts_false ν ρ hG

theorem reifyCode_true (ν : Valuation) (ρ : SemEnv)
    (hG : GuardedReaderSource.guard ρ.assignment) :
    ValueEq (reifyCode (evalOpenEq ν ρ))
      (evalRaw ν ρ EqLargeFixture.result) :=
  GuardedSuspendedRead.image_true hG

theorem reifyCode_false (ν : Valuation) (ρ : SemEnv)
    (hG : ¬ GuardedReaderSource.guard ρ.assignment) :
    ValueEq (reifyCode (evalOpenEq ν ρ))
      (NativeMemberValues.value (some 1) GuardedOpenEqCall.callName) :=
  GuardedSuspendedRead.image_false hG

/-- Source admission, all input images, reading, and output universe
membership are obtained together for every proposition, without deciding it. -/
theorem all_proposition_inputs (ν : Valuation) (P : Prop) :
    ∃ ρ : SemEnv,
      ρ.assignment = GuardedReaderSource.propositionAssignment P 0 ∧
      GuardedOpenEqCall.InputImages ν ρ.input ∧
      GuardedSuspendedRead.Read ν ρ.assignment GuardedOpenEqCall.callName
        (read (evalOpenEq ν ρ)) ∧
      (GuardedConversionUniverse.conversionUniverse.{0} 1).view.relation
        (read (evalOpenEq ν ρ)) (read (evalOpenEq ν ρ)) := by
  obtain ⟨i, hi, him⟩ := GuardedOpenEqCall.proposition_policy_images ν P
  exact ⟨⟨i⟩, hi, him, evalOpenEq_reads ν ⟨i⟩,
    read_conversion_universe_member ν ⟨i⟩⟩

theorem true_false_not_convert (ν μ : Valuation) (ρ σ : SemEnv)
    (ht : GuardedReaderSource.guard ρ.assignment)
    (hf : ¬ GuardedReaderSource.guard σ.assignment) :
    ¬ Converts (read (evalOpenEq ν ρ)) (read (evalOpenEq μ σ)) := by
  intro h
  have hbranches := converts_trans (converts_symm (converts_true ν ρ ht))
    (converts_trans h (converts_false μ σ hf))
  exact GuardedImageBoundary.open_minor_not_neutral ν ρ.assignment
    GuardedOpenEqCall.callName (converts_type_image hbranches)

/-- Two actual source inputs have identical raw evaluations of every
expression, while their retained open-call readings are not convertible.
The retained environment supplies exactly the data erased execution loses. -/
theorem inhabited_retained_separation (ν : Valuation) :
    ∃ ρ σ : SemEnv,
      GuardedOpenEqCall.InputImages ν ρ.input ∧
      GuardedOpenEqCall.InputImages ν σ.input ∧
      eraseEnv ρ = eraseEnv σ ∧
      (∀ e, evalRaw ν ρ e = evalRaw ν σ e) ∧
      ¬ Converts (read (evalOpenEq ν ρ)) (read (evalOpenEq ν σ)) := by
  obtain ⟨i, hi, him⟩ := GuardedOpenEqCall.proposition_policy_images ν True
  obtain ⟨j, hj, hjm⟩ := GuardedOpenEqCall.proposition_policy_images ν False
  have he : eraseEnv ⟨i⟩ = eraseEnv ⟨j⟩ := by
    change GuardedReaderSource.rawEnvironment i.assignment =
      GuardedReaderSource.rawEnvironment j.assignment
    rw [hi, hj]
    exact GuardedReaderSource.proposition_raw_environments_same True False 0
  have ht : GuardedReaderSource.guard (SemEnv.assignment ⟨i⟩) := by
    change GuardedReaderSource.guard i.assignment
    rw [hi]
    exact (GuardedReaderSource.proposition_guard_iff True 0).mpr True.intro
  have hf : ¬ GuardedReaderSource.guard (SemEnv.assignment ⟨j⟩) := by
    change ¬ GuardedReaderSource.guard j.assignment
    rw [hj]
    exact fun h => (GuardedReaderSource.proposition_guard_iff False 0).mp h
  refine ⟨⟨i⟩, ⟨j⟩, him, hjm, he, ?_, true_false_not_convert ν ν ⟨i⟩ ⟨j⟩ ht hf⟩
  intro e
  exact congrArg (fun ρ => TaggedKEvaluation.image ν ρ e) he

/-- The old raw evaluator cannot universally equal the conditional code
image of this retained evaluation, even on the fully inhabited source class. -/
theorem no_universal_raw_code_image (ν : Valuation) :
    ¬ (∀ ρ : SemEnv, ValueEq (erase (evalOpenEq ν ρ))
      (reifyCode (evalOpenEq ν ρ))) := by
  intro h
  apply GuardedSuspendedRead.old_call_output_image_impossible ν GuardedOpenEqCall.callName
  intro P
  obtain ⟨i, hi, _⟩ := GuardedOpenEqCall.proposition_policy_images ν P
  have hv := h ⟨i⟩
  change ValueEq
    (TaggedKEvaluation.image ν (GuardedReaderSource.rawEnvironment i.assignment)
      (GuardedOpenEqCall.call GuardedReaderSource.proofTerm))
    (GuardedSuspendedRead.reading ν i.assignment GuardedOpenEqCall.callName).view.value at hv
  rw [hi] at hv
  exact hv

end Rcic.Declarative.Ann.LR3.RetainedOpenEqEvaluation

import rcic.RcicAnnLR3RCodeInterface
import rcic.RcicAnnLR3RetainedOpenEqEvaluation

/-!
# Discrete sound universe readback decides the retained proposition indices

The strengthened RCode has decidable normal-form equality, PER-respecting
quotation, and a sound retained evaluator for its quoted normal forms.
Consequently quotation equality is equivalent to its member relation.

The two actual retained proposition indices in each admitted open-Eq
input are propCode P and propCode True. In the conversion universe their
relation is equivalent to P. Their source variables, fixed source world,
retained evaluation and raw-image agreement are all supplied below.

An explicit two-object embedding into an RCode in that same world therefore
gives Decidable P. A family of such packages for all P gives excluded
middle. The embedding is constructed when the RCode uses the actual
conversion-universe carrier. Whether a future restricted generator tower
contains both indices with this relation remains an explicit closure
condition. This is a conditional logical-strength theorem, not a proof of
not RCode, a contradiction, or a source-language counterexample.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.RCodeUniverseReadback

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER GuardedTaggedCode RCodeInterface

universe u v w

/-- Sound discrete reification decides the PER on its self-members. -/
def relationDecision {W : World} {k : Nat} {NF : Type v}
    (C : RCode.{u,v,w} W k NF) (x y : C.Element) :
    Decidable (RCodeInterface.Related x y) := by
  letI := C.normalEq
  exact if h : C.reify x = C.reify y then
    isTrue ((C.quote_eq_iff x y).mp h)
  else
    isFalse (fun hr => h ((C.quote_eq_iff x y).mpr hr))

abbrev propositionUniverse : Code.{1} 1 :=
  GuardedConversionUniverse.conversionUniverse.{0} 0

def propositionMember (P : Prop) : RCodeInterface.Member propositionUniverse :=
  ⟨Code.legacy (GuardDecision.propCode P),
    GuardedConversionUniverse.member 0 _⟩

theorem proposition_members_related_iff (P Q : Prop) :
    RCodeInterface.Related (propositionMember P) (propositionMember Q) ↔ (P ↔ Q) :=
  RetainedArmTransfer.proposition_converts_iff P Q

theorem proposition_true_related_iff (P : Prop) :
    RCodeInterface.Related (propositionMember P) (propositionMember True) ↔ P := by
  constructor
  · intro h
    exact ((proposition_members_related_iff P True).mp h).mpr True.intro
  · intro h
    exact (proposition_members_related_iff P True).mpr
      ⟨fun _ => True.intro, fun _ => h⟩

/-- A code identity transports membership as data; no code is inferred
from equality of erased type images. -/
def castMember {k : Nat} {C D : Code.{u} k} (h : C = D)
    (x : RCodeInterface.Member D) : RCodeInterface.Member C := h.symm ▸ x

theorem castMember_related {k : Nat} {C D : Code.{u} k} (h : C = D)
    (x y : RCodeInterface.Member D) :
    RCodeInterface.Related (castMember h x) (castMember h y) ↔
      RCodeInterface.Related x y := by
  cases h
  rfl

theorem castMember_erasure {k : Nat} {C D : Code.{u} k} (h : C = D)
    (x : RCodeInterface.Member D) :
    C.erase (castMember h x).val = D.erase x.val := by
  cases h
  rfl

/-- The actual fixed world of the retained left/right index evaluators. -/
def indexWorld (ν : Valuation) (ρ : RetainedOpenEqEvaluation.SemEnv) : World where
  env := EqLargeFixture.env
  iota := iotaIfaceA EqLargeFixture.env
  levelCount := 0
  context := GuardedReaderSource.proofContext
  family := TaggedKEvaluation.eqSyntax
  valuation := ν
  rawEnvironment := RetainedOpenEqEvaluation.eraseEnv ρ
  envWf := ρ.input.sourceInput.source.admitted
  contextWf := ρ.input.sourceInput.source.contextWf

def leftSource (ν : Valuation) (ρ : RetainedOpenEqEvaluation.SemEnv) :
    Source (indexWorld ν ρ) (.sort .zero) :=
  ⟨GuardedReaderSource.liftedLeftIndex, ρ.input.sourceInput.source.leftTyped⟩

def rightSource (ν : Valuation) (ρ : RetainedOpenEqEvaluation.SemEnv) :
    Source (indexWorld ν ρ) (.sort .zero) :=
  ⟨GuardedReaderSource.liftedRightIndex, ρ.input.sourceInput.source.rightTyped⟩

def leftMember (ν : Valuation) (ρ : RetainedOpenEqEvaluation.SemEnv) :
    RCodeInterface.Member propositionUniverse :=
  ⟨RetainedOpenEqEvaluation.read (RetainedOpenEqEvaluation.evalLeftIndex ν ρ),
    GuardedConversionUniverse.member 0 _⟩

def rightMember (ν : Valuation) (ρ : RetainedOpenEqEvaluation.SemEnv) :
    RCodeInterface.Member propositionUniverse :=
  ⟨RetainedOpenEqEvaluation.read (RetainedOpenEqEvaluation.evalRightIndex ν ρ),
    GuardedConversionUniverse.member 0 _⟩

theorem leftMember_image (ν : Valuation) (ρ : RetainedOpenEqEvaluation.SemEnv)
    (h : GuardedOpenEqCall.InputImages ν ρ.input) :
    ValueEq (propositionUniverse.erase (leftMember ν ρ).val)
      ((indexWorld ν ρ).evaluate (leftSource ν ρ).term) :=
  (RetainedOpenEqEvaluation.left_index_image ν ρ h).symm

theorem rightMember_image (ν : Valuation) (ρ : RetainedOpenEqEvaluation.SemEnv)
    (h : GuardedOpenEqCall.InputImages ν ρ.input) :
    ValueEq (propositionUniverse.erase (rightMember ν ρ).val)
      ((indexWorld ν ρ).evaluate (rightSource ν ρ).term) :=
  (RetainedOpenEqEvaluation.right_index_image ν ρ h).symm

theorem actual_indices_related_iff (ν : Valuation)
    {ρ : RetainedOpenEqEvaluation.SemEnv} {P : Prop}
    (hρ : ρ.assignment = GuardedReaderSource.propositionAssignment P 0) :
    RCodeInterface.Related (leftMember ν ρ) (rightMember ν ρ) ↔ P := by
  change Converts (Code.legacy ρ.assignment.left) (Code.legacy ρ.assignment.right) ↔ P
  rw [hρ]
  exact proposition_true_related_iff P

/-- All source and image premises of the two tested universe members
exist for every proposition before any readback is requested. -/
theorem inhabited_index_source (ν : Valuation) (P : Prop) :
    ∃ ρ : RetainedOpenEqEvaluation.SemEnv,
      ρ.assignment = GuardedReaderSource.propositionAssignment P 0 ∧
      GuardedOpenEqCall.InputImages ν ρ.input ∧
      Nonempty (Source (indexWorld ν ρ) (.sort .zero)) ∧
      ValueEq (propositionUniverse.erase (leftMember ν ρ).val)
        ((indexWorld ν ρ).evaluate (leftSource ν ρ).term) ∧
      ValueEq (propositionUniverse.erase (rightMember ν ρ).val)
        ((indexWorld ν ρ).evaluate (rightSource ν ρ).term) ∧
      (RCodeInterface.Related (leftMember ν ρ) (rightMember ν ρ) ↔ P) := by
  obtain ⟨ρ, hρ, hi, _hr, _hm⟩ := RetainedOpenEqEvaluation.all_proposition_inputs ν P
  exact ⟨ρ, hρ, hi, ⟨leftSource ν ρ⟩, leftMember_image ν ρ hi,
    rightMember_image ν ρ hi, actual_indices_related_iff ν hρ⟩

/-- The only local closure requirement: both actual retained indices
occur in this same RCode with their actual relation and evaluator images.
It does not assert that a future restricted universe has this embedding. -/
structure IndexEmbedding (ν : Valuation) (ρ : RetainedOpenEqEvaluation.SemEnv)
    {NF : Type v} (C : RCode.{u,v,w} (indexWorld ν ρ) 1 NF) where
  sourceType : C.sourceType = .sort .zero
  left : C.Element
  right : C.Element
  relation : RCodeInterface.Related left right ↔
    RCodeInterface.Related (leftMember ν ρ) (rightMember ν ρ)
  left_image : ValueEq (C.erase left)
    ((indexWorld ν ρ).evaluate (leftSource ν ρ).term)
  right_image : ValueEq (C.erase right)
    ((indexWorld ν ρ).evaluate (rightSource ν ρ).term)

/-- The actual conversion-universe carrier supplies this embedding by
identity. Source-image premises are discharged by the existing evaluators. -/
def indexEmbeddingOfCode (ν : Valuation) (ρ : RetainedOpenEqEvaluation.SemEnv)
    {NF : Type v} (C : RCode.{1,v,w} (indexWorld ν ρ) 1 NF)
    (hc : C.code = propositionUniverse) (hA : C.sourceType = .sort .zero)
    (hi : GuardedOpenEqCall.InputImages ν ρ.input) : IndexEmbedding ν ρ C where
  sourceType := hA
  left := castMember hc (leftMember ν ρ)
  right := castMember hc (rightMember ν ρ)
  relation := castMember_related hc _ _
  left_image := by
    change ValueEq (C.code.erase (castMember hc (leftMember ν ρ)).val) _
    rw [castMember_erasure]
    exact leftMember_image ν ρ hi
  right_image := by
    change ValueEq (C.code.erase (castMember hc (rightMember ν ρ)).val) _
    rw [castMember_erasure]
    exact rightMember_image ν ρ hi

/-- With sound discrete readback, these two objects decide P itself,
not only its negation. Every semantic/source premise is local to ρ. -/
def propositionDecision (ν : Valuation) {ρ : RetainedOpenEqEvaluation.SemEnv}
    {P : Prop} {NF : Type v} (C : RCode.{u,v,w} (indexWorld ν ρ) 1 NF)
    (hρ : ρ.assignment = GuardedReaderSource.propositionAssignment P 0)
    (e : IndexEmbedding ν ρ C) : Decidable P :=
  match relationDecision C e.left e.right with
  | isTrue h => isTrue ((actual_indices_related_iff ν hρ).mp (e.relation.mp h))
  | isFalse h => isFalse (fun hp =>
      h (e.relation.mpr ((actual_indices_related_iff ν hρ).mpr hp)))

theorem local_readback_implies_em (ν : Valuation)
    {ρ : RetainedOpenEqEvaluation.SemEnv} {P : Prop} {NF : Type v}
    (C : RCode.{u,v,w} (indexWorld ν ρ) 1 NF)
    (hρ : ρ.assignment = GuardedReaderSource.propositionAssignment P 0)
    (e : IndexEmbedding ν ρ C) : P ∨ ¬ P := by
  cases propositionDecision ν C hρ e with
  | isTrue h => exact Or.inl h
  | isFalse h => exact Or.inr h

/-- The retained input, code and two-object embedding are explicit data.
Only the existence of the source input is unconditional. -/
structure LocalReadback (ν : Valuation) (P : Prop) (NF : Type v) where
  environment : RetainedOpenEqEvaluation.SemEnv
  assignment : environment.assignment = GuardedReaderSource.propositionAssignment P 0
  images : GuardedOpenEqCall.InputImages ν environment.input
  code : RCode.{u,v,w} (indexWorld ν environment) 1 NF
  indices : IndexEmbedding ν environment code

/-- Worlds, normal-form formats and reifiers may all depend on P.
No comparison of quotations from different worlds is used. -/
theorem worldwise_readback_implies_em (ν : Valuation) (NF : Prop → Type v)
    (readbacks : ∀ P : Prop, Nonempty (LocalReadback.{u,v,w} ν P (NF P))) :
    ∀ P : Prop, P ∨ ¬ P := by
  intro P
  rcases readbacks P with ⟨r⟩
  exact local_readback_implies_em ν r.code r.assignment r.indices

/-- A future generator may be applied only to inputs with all existing
source-image premises. Their unconditional construction suffices for the
same implication; no arbitrary raw or ill-typed assignment is needed. -/
theorem admitted_universe_closure_implies_em (ν : Valuation) (NF : Prop → Type v)
    (closed : ∀ (P : Prop) (ρ : RetainedOpenEqEvaluation.SemEnv),
      ρ.assignment = GuardedReaderSource.propositionAssignment P 0 →
      GuardedOpenEqCall.InputImages ν ρ.input →
      ∃ C : RCode.{u,v,w} (indexWorld ν ρ) 1 (NF P),
        Nonempty (IndexEmbedding ν ρ C)) :
    ∀ P : Prop, P ∨ ¬ P := by
  apply worldwise_readback_implies_em ν NF
  intro P
  obtain ⟨ρ, hρ, hi, _hr, _hm⟩ := RetainedOpenEqEvaluation.all_proposition_inputs ν P
  obtain ⟨C, he⟩ := closed P ρ hρ hi
  rcases he with ⟨e⟩
  exact ⟨⟨ρ, hρ, hi, C, e⟩⟩

end Rcic.Declarative.Ann.LR3.RCodeUniverseReadback

import rcic.RcicAnnLR3RetainedOpenEqEvaluation

/-!
# The logical strength of discrete readback for the actual guarded call

This is a new readback boundary for retained universe elements, not the
old impossibility of recovering retained codes from erased environments.
Every proposition below has an actual admitted open-Eq source input,
all inherited input-image premises, and the concrete retained evaluator.

The first proposed readback is uniform on the conversion universe.  It
respects its PER and interprets the normal forms of two fixed branch codes
with their actual type images.  Those two normal forms must differ because
the source Pi minor and named neutral fallback have different finite raw
observations.  Decidable equality of normal forms then decides the
negation of every guard, yielding `not P or not not P`.

The normal-form type is arbitrary.  Thus the implication applies to
finite proof-erased syntax too; no distinct proof-neutral quotations are
required.  Only the two branch image laws are assumed, not a general
normalization theorem or the desired conclusion.  The output is a
logical-strength implication, not a proof of `not RCode`, excluded
middle, or a source-language counterexample.

The final local variant removes any comparison across retained worlds:
for each proposition, it compares the call with that world's own minor
and fallback.  Both quotation and its image interpretation may vary with
the world.  Having these three objects in a future restricted `RCode`
universe remains a separate generator-closure obligation.  The actual
open-call fragment is supplied here; a whole-source typed evaluator and
the future `RCode` source-realizability theorem are not supplied.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.RCodeGuardedReadback

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER GuardedTaggedCode

universe u

/-- A single reference for the actual source minor.  The existing
`openMinorIso` transports every other admitted input's minor to it. -/
def referenceMinor (ν : Valuation) : Code.{0} 1 :=
  Code.legacy (GuardedOpenEqCall.minorCode ν
    (GuardedReaderSource.propositionAssignment True 0))

def referenceFallback : Code.{0} 1 :=
  Code.legacy (TaggedSaturatedTower.Code.neutral.{0} 1
    GuardedOpenEqCall.callName)

def propositionReading (ν : Valuation) (P : Prop) : Code.{0} 1 :=
  GuardedSuspendedRead.reading ν
    (GuardedReaderSource.propositionAssignment P 0) GuardedOpenEqCall.callName

theorem minor_converts_reference (ν : Valuation)
    (a : GuardedReaderSource.IndexAssignment) :
    Converts (Code.legacy (GuardedOpenEqCall.minorCode ν a))
      (referenceMinor ν) :=
  ⟨GuardedMinorTransport.openMinorIso ν ν a
    (GuardedReaderSource.propositionAssignment True 0)⟩

theorem reading_converts_true (ν : Valuation) (P : Prop) (hP : P) :
    Converts (propositionReading ν P) (referenceMinor ν) :=
  converts_trans
    (GuardedSuspendedRead.converts_true
      ((GuardedReaderSource.proposition_guard_iff P 0).mpr hP))
    (minor_converts_reference ν
      (GuardedReaderSource.propositionAssignment P 0))

theorem reading_converts_false (ν : Valuation) (P : Prop) (hP : ¬ P) :
    Converts (propositionReading ν P) referenceFallback :=
  GuardedSuspendedRead.converts_false
    (fun hG => hP ((GuardedReaderSource.proposition_guard_iff P 0).mp hG))

theorem branch_images_differ (ν : Valuation) :
    ¬ ValueEq (referenceMinor ν).view.value referenceFallback.view.value :=
  GuardedImageBoundary.open_minor_not_neutral ν
    (GuardedReaderSource.propositionAssignment True 0)
    GuardedOpenEqCall.callName

theorem propositionReading_member (ν : Valuation) (P : Prop) :
    (GuardedConversionUniverse.conversionUniverse.{0} 1).view.relation
      (propositionReading ν P) (propositionReading ν P) :=
  GuardedConversionUniverse.member 1 (propositionReading ν P)

/-- This is the concrete retained source evaluator, not an arbitrary
caller-supplied map into codes.  Source admission and call typing are
fields of `rho.input`; all additional interpreted premises are supplied. -/
theorem actual_source_output (ν : Valuation) (P : Prop) :
    ∃ ρ : RetainedOpenEqEvaluation.SemEnv,
      ρ.assignment = GuardedReaderSource.propositionAssignment P 0 ∧
      GuardedOpenEqCall.InputImages ν ρ.input ∧
      RetainedOpenEqEvaluation.read
        (RetainedOpenEqEvaluation.evalOpenEq ν ρ) = propositionReading ν P ∧
      RetainedOpenEqEvaluation.erase
        (RetainedOpenEqEvaluation.evalOpenEq ν ρ) =
        TaggedKEvaluation.image ν (RetainedOpenEqEvaluation.eraseEnv ρ)
          (GuardedOpenEqCall.call GuardedReaderSource.proofTerm) ∧
      (GuardedConversionUniverse.conversionUniverse.{0} 1).view.relation
        (RetainedOpenEqEvaluation.read
          (RetainedOpenEqEvaluation.evalOpenEq ν ρ))
        (RetainedOpenEqEvaluation.read
          (RetainedOpenEqEvaluation.evalOpenEq ν ρ)) := by
  obtain ⟨ρ, hρ, himages, _hread, hmember⟩ :=
    RetainedOpenEqEvaluation.all_proposition_inputs ν P
  refine ⟨ρ, hρ, himages, ?_,
    RetainedOpenEqEvaluation.erase_evalOpenEq ν ρ, hmember⟩
  rw [RetainedOpenEqEvaluation.read_evalOpenEq, hρ]
  rfl

/-- The two branch soundness fields are consequences of a full sound
universe readback, but only this weaker interface is used here.  No law
is imposed on proof-level neutral names.  A world-indexed reader meets
this interface only if it has this uniform universe quotation. -/
structure DiscreteReadback (ν : Valuation) (NF : Type u) where
  quote : (GuardedConversionUniverse.conversionUniverse.{0} 1).Element → NF
  image : NF → Value
  respect : ∀ C D : (GuardedConversionUniverse.conversionUniverse.{0} 1).Element,
    (GuardedConversionUniverse.conversionUniverse.{0} 1).view.relation C D →
      quote C = quote D
  minor_image : ValueEq (image (quote (referenceMinor ν)))
    (referenceMinor ν).view.value
  fallback_image : ValueEq (image (quote referenceFallback))
    referenceFallback.view.value

theorem branch_quotes_differ {ν : Valuation} {NF : Type u}
    (r : DiscreteReadback ν NF) :
    r.quote (referenceMinor ν) ≠ r.quote referenceFallback := by
  intro h
  have hm := r.minor_image
  rw [h] at hm
  exact branch_images_differ ν (hm.symm.trans r.fallback_image)

theorem quote_true {ν : Valuation} {NF : Type u}
    (r : DiscreteReadback ν NF) (P : Prop) (hP : P) :
    r.quote (propositionReading ν P) = r.quote (referenceMinor ν) :=
  r.respect _ _ (reading_converts_true ν P hP)

theorem quote_false {ν : Valuation} {NF : Type u}
    (r : DiscreteReadback ν NF) (P : Prop) (hP : ¬ P) :
    r.quote (propositionReading ν P) = r.quote referenceFallback :=
  r.respect _ _ (reading_converts_false ν P hP)

/-- Deciding equality with the Pi normal form decides `not P`.
The equality branch yields only `not not P`, not a proof of `P`. -/
def negationDecision {ν : Valuation} {NF : Type u} [DecidableEq NF]
    (r : DiscreteReadback ν NF) (P : Prop) : Decidable (¬ P) :=
  if h : r.quote (propositionReading ν P) = r.quote (referenceMinor ν) then
    isFalse (fun hn => branch_quotes_differ r
      (h.symm.trans (quote_false r P hn)))
  else
    isTrue (fun hp => h (quote_true r P hp))

theorem discrete_readback_implies_weak_em {ν : Valuation} {NF : Type u}
    [DecidableEq NF] (r : DiscreteReadback ν NF) (P : Prop) :
    ¬ P ∨ ¬ ¬ P := by
  cases negationDecision r P with
  | isTrue hn => exact Or.inl hn
  | isFalse hnn => exact Or.inr hnn

theorem uniform_discrete_readback_implies_weak_em {ν : Valuation} {NF : Type u}
    [DecidableEq NF] (r : DiscreteReadback ν NF) :
    ∀ P : Prop, ¬ P ∨ ¬ ¬ P :=
  discrete_readback_implies_weak_em r

/-- The same implication packaged with an actual inhabited source input
for the proposition in question, its image premises, and its retained
evaluation.  No counterexample to the source language is asserted. -/
theorem inhabited_source_readback_boundary {ν : Valuation} {NF : Type u}
    [DecidableEq NF] (r : DiscreteReadback ν NF) (P : Prop) :
    ∃ ρ : RetainedOpenEqEvaluation.SemEnv,
      ρ.assignment = GuardedReaderSource.propositionAssignment P 0 ∧
      GuardedOpenEqCall.InputImages ν ρ.input ∧
      r.quote (RetainedOpenEqEvaluation.read
        (RetainedOpenEqEvaluation.evalOpenEq ν ρ)) =
        r.quote (propositionReading ν P) ∧
      (¬ P ∨ ¬ ¬ P) := by
  obtain ⟨ρ, hρ, himages, hread, _herase, _hmember⟩ := actual_source_output ν P
  exact ⟨ρ, hρ, himages, congrArg r.quote hread,
    discrete_readback_implies_weak_em r P⟩

/-- Three elements of a single retained world.  This finite indexing type
does not restrict the syntax or number of possible normal forms. -/
inductive LocalObject where
  | call
  | minor
  | fallback
  deriving DecidableEq

def localCode (ν : Valuation) (P : Prop) : LocalObject → Code.{0} 1
  | .call => propositionReading ν P
  | .minor => Code.legacy (GuardedOpenEqCall.minorCode ν
      (GuardedReaderSource.propositionAssignment P 0))
  | .fallback => referenceFallback

theorem local_member (ν : Valuation) (P : Prop) (o : LocalObject) :
    (GuardedConversionUniverse.conversionUniverse.{0} 1).view.relation
      (localCode ν P o) (localCode ν P o) :=
  GuardedConversionUniverse.member 1 (localCode ν P o)

theorem local_true (ν : Valuation) (P : Prop) (hP : P) :
    Converts (localCode ν P .call) (localCode ν P .minor) :=
  GuardedSuspendedRead.converts_true
    ((GuardedReaderSource.proposition_guard_iff P 0).mpr hP)

theorem local_false (ν : Valuation) (P : Prop) (hP : ¬ P) :
    Converts (localCode ν P .call) (localCode ν P .fallback) :=
  reading_converts_false ν P hP

/-- A restriction of a universe reifier to three admitted semantic
objects in this one P-world.  `quote` and `image` are allowed to depend
on P.  PER respect is requested only within that world.  The structure
does not assert that a future restricted RCode already contains them. -/
structure LocalReadback (ν : Valuation) (P : Prop) (NF : Type u) where
  quote : LocalObject → NF
  image : NF → Value
  respect : ∀ o p : LocalObject,
    (GuardedConversionUniverse.conversionUniverse.{0} 1).view.relation
      (localCode ν P o) (localCode ν P p) → quote o = quote p
  minor_image : ValueEq (image (quote .minor)) (localCode ν P .minor).view.value
  fallback_image : ValueEq (image (quote .fallback))
    (localCode ν P .fallback).view.value

theorem local_branch_quotes_differ {ν : Valuation} {P : Prop} {NF : Type u}
    (r : LocalReadback ν P NF) : r.quote .minor ≠ r.quote .fallback := by
  intro h
  have hm := r.minor_image
  rw [h] at hm
  exact GuardedImageBoundary.open_minor_not_neutral ν
    (GuardedReaderSource.propositionAssignment P 0) GuardedOpenEqCall.callName
    (hm.symm.trans r.fallback_image)

/-- Both comparisons use this world's quotation and image interpreter. -/
def localNegationDecision {ν : Valuation} {P : Prop} {NF : Type u}
    [DecidableEq NF] (r : LocalReadback ν P NF) : Decidable (¬ P) :=
  if h : r.quote .call = r.quote .minor then
    isFalse (fun hn => local_branch_quotes_differ r
      (h.symm.trans (r.respect .call .fallback (local_false ν P hn))))
  else
    isTrue (fun hp => h (r.respect .call .minor (local_true ν P hp)))

theorem local_readback_implies_weak_em {ν : Valuation} {P : Prop} {NF : Type u}
    [DecidableEq NF] (r : LocalReadback ν P NF) : ¬ P ∨ ¬ ¬ P := by
  cases localNegationDecision r with
  | isTrue hn => exact Or.inl hn
  | isFalse hnn => exact Or.inr hnn

/-- Even the NF type, decidable equality, quotation and image semantics
may vary with the P-world.  No cross-world quotation equation is used. -/
theorem worldwise_readback_implies_weak_em (ν : Valuation)
    (NF : Prop → Type u) (dec : ∀ P : Prop, DecidableEq (NF P))
    (readbacks : ∀ P : Prop, Nonempty (LocalReadback ν P (NF P))) :
    ∀ P : Prop, ¬ P ∨ ¬ ¬ P := by
  intro P
  letI := dec P
  rcases readbacks P with ⟨r⟩
  exact local_readback_implies_weak_em r

theorem inhabited_local_readback_boundary {ν : Valuation} {P : Prop} {NF : Type u}
    [DecidableEq NF] (r : LocalReadback ν P NF) :
    ∃ ρ : RetainedOpenEqEvaluation.SemEnv,
      ρ.assignment = GuardedReaderSource.propositionAssignment P 0 ∧
      GuardedOpenEqCall.InputImages ν ρ.input ∧
      RetainedOpenEqEvaluation.read
        (RetainedOpenEqEvaluation.evalOpenEq ν ρ) = localCode ν P .call ∧
      (∀ o : LocalObject,
        (GuardedConversionUniverse.conversionUniverse.{0} 1).view.relation
          (localCode ν P o) (localCode ν P o)) ∧
      (¬ P ∨ ¬ ¬ P) := by
  obtain ⟨ρ, hρ, himages, hread, _herase, _hmember⟩ := actual_source_output ν P
  exact ⟨ρ, hρ, himages, hread, local_member ν P,
    local_readback_implies_weak_em r⟩

end Rcic.Declarative.Ann.LR3.RCodeGuardedReadback

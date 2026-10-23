import rcic.RcicAnnLR3GuardedReaderSource
import rcic.RcicAnnLR3SourceFamilyReading

/-!
# A source-bound Eq decoder for the open proposition-index class

The source expression is the actual admitted Eq family at X and Y in
`[p : Eq X Y, Y : Prop, X : Prop]`. Its proposition code has exactly the
actual evaluator image. Its completed candidate is the canonical proof PER
on the retained index relation, not a caller-supplied candidate or signature.
The catalog reading retains the actual refl constructor and its result index.

This is a scoped interpretation of this Eq source expression. It is not a
general family producer, a whole-language fundamental lemma, or an evaluator
image law for false-guard recursor calls. Eq stays at Code 0; no positive
familyCode producer is applied to its proofs. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Rcic.Declarative.Ann.LR3.GuardedEqFamily

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TaggedSaturatedTower
open GuardedReaderSource

/-- The source family is selected from the constructive admission catalog. -/
def sourceReading : SourceFamilyReading.CatalogReading
    (AdmittedFamilyExtractor.catalog EqLargeFixture.prefixWf) liftedEqualityType where
  group := SourceFamilyReading.eqGroup
  inCatalog := by
    rw [SourceFamilyReading.eq_catalog_singleton]
    exact List.mem_singleton.mpr rfl
  shape := by constructor <;> rfl

theorem sourceReading_selected :
    SourceFamilyReading.readerOf EqLargeFixture.prefixWf liftedEqualityType =
      some sourceReading := rfl

theorem family_in_final_environment :
    EqLargeFixture.env.members sourceReading.signature.familyRef =
      some EqLargeFixture.fam := rfl

theorem refl_in_final_environment :
    EqLargeFixture.env.members 64 = some EqLargeFixture.reflMember := rfl

def sourceConstructor : SourceFamilyReading.Constructor sourceReading.group :=
  SourceFamilyReading.eqConstructor

theorem source_family_ref : sourceReading.signature.familyRef = 63 := rfl

theorem source_constructor_refs : sourceReading.signature.constructorRefs = [64] := rfl

theorem source_constructor_fields :
    SourceFamilyReading.constructorFields sourceReading.group sourceConstructor = [] := rfl

theorem source_constructor_result_index :
    (SourceFamilyReading.constructorIndicesAt sourceReading.group sourceConstructor).map
      (fun t => t.arguments) = [[.bvar 0]] :=
  SourceFamilyReading.eq_constructor_indices

/-- The actual source Eq term reduces to this tagged payload. -/
def eqPayload (ν : Valuation) : Expr Nat :=
  .app (.app (.app (.const 12 []) (sortTerm (eval ν .zero))) (.bvar 2)) (.bvar 1)

theorem eq_normalizes (ν : Valuation) :
    betaRun 3 (UnitModel.translate ν liftedEqualityType) =
      taggedTerm (some 0) (eqPayload ν) := rfl

theorem eq_image_tagged (ν : Valuation) (ρ : EnvI) :
    ValueEq (TaggedKEvaluation.image ν ρ liftedEqualityType)
      (denI ρ (taggedTerm (some 0) (eqPayload ν))) := by
  have hβ : ValueEq (UnitModel.denote ν ρ liftedEqualityType)
      (denI ρ (taggedTerm (some 0) (eqPayload ν))) :=
    eq_of_betaRun (ρ := ρ) (eq_normalizes ν)
  exact (TaggedKEvaluation.denote_agrees ν ρ
    (e := liftedEqualityType) (by trivial)).trans hβ

theorem eq_image_level (ν : Valuation) (ρ : EnvI) :
    SortMember (some 0) (TaggedKEvaluation.image ν ρ liftedEqualityType) :=
  sortMember_congr (eq_image_tagged ν ρ).symm (tagged_member ρ (some 0) (eqPayload ν))

theorem eq_image_defined (ν : Valuation) (ρ : EnvI) :
    TypeDefined (TaggedKEvaluation.image ν ρ liftedEqualityType) :=
  typeDefined_congr (eq_image_tagged ν ρ).symm (tagged_defined ρ (some 0) (eqPayload ν))

/-- The value is forced by evaluation; the proof candidate is forced by the
retained universe relation of the two actual source index variables. -/
def element (ν : Valuation) (a : IndexAssignment) : CandidatePi.Element where
  value := TaggedKEvaluation.image ν (rawEnvironment a) liftedEqualityType
  candidate := (CandidateUniverse.proofCandidate (guard a)).toCandidate
  level := eq_image_level ν (rawEnvironment a)
  defined := eq_image_defined ν (rawEnvironment a)

def code (ν : Valuation) (a : IndexAssignment) : Code.{0} 0 :=
  Code.proposition (element ν a)

theorem code_actual_image (ν : Valuation) (a : IndexAssignment) :
    ValueEq (code ν a).view.value
      (TaggedKEvaluation.image ν (rawEnvironment a) liftedEqualityType) := by
  intro c
  rfl

/-- Completion adds exactly the new neutral cases to this proof candidate. -/
theorem completed_proof_point_iff (P : Prop) (x : Value) :
    (Member (CandidateUniverse.proofCandidate P).toCandidate.relation x ∨
      CandidatePi.Neutral x) ↔
      NeutralPER.ProofMember CandidatePi.Neutral P x := by
  constructor
  · rintro (h | hn)
    · change NeutralPER.ProofPER NeutralCodes.Neutral P x x at h
      rcases h.1 with hunit | hold
      · exact Or.inl hunit
      · exact Or.inr (CandidatePi.old_neutral_included hold)
    · exact Or.inr hn
  · intro h
    rcases h with hunit | hn
    · exact Or.inl ⟨Or.inl hunit, Or.inl hunit⟩
    · exact Or.inr hn

theorem decoder_iff (ν : Valuation) (a : IndexAssignment) (x y : Value) :
    CandidatePi.decode (element ν a) x y ↔
      NeutralPER.ProofPER CandidatePi.Neutral (guard a) x y := by
  change
    ((Member (CandidateUniverse.proofCandidate (guard a)).toCandidate.relation x ∨
        CandidatePi.Neutral x) ∧
      (Member (CandidateUniverse.proofCandidate (guard a)).toCandidate.relation y ∨
        CandidatePi.Neutral y)) ↔
      (NeutralPER.ProofMember CandidatePi.Neutral (guard a) x ∧
        NeutralPER.ProofMember CandidatePi.Neutral (guard a) y)
  exact and_congr (completed_proof_point_iff (guard a) x)
    (completed_proof_point_iff (guard a) y)

theorem code_relation_iff (ν : Valuation) (a : IndexAssignment)
    (x y : (code ν a).Element) :
    (code ν a).view.relation x y ↔
      NeutralPER.ProofPER CandidatePi.Neutral (guard a) x.down y.down :=
  decoder_iff ν a x.down y.down

theorem major_member (ν : Valuation) (a : IndexAssignment) :
    (code ν a).view.relation
      (⟨a.major⟩ : (code ν a).Element) (⟨a.major⟩ : (code ν a).Element) :=
  (code_relation_iff ν a _ _).mpr a.major_member

theorem unit_member_iff (ν : Valuation) (a : IndexAssignment) :
    (code ν a).view.relation
      (⟨GuardDecision.unit⟩ : (code ν a).Element)
      (⟨GuardDecision.unit⟩ : (code ν a).Element) ↔ guard a :=
  GuardDecision.propElement_unit_iff (guard a)

theorem unit_member_of_guard (ν : Valuation) (a : IndexAssignment) (h : guard a) :
    (code ν a).view.relation
      (⟨GuardDecision.unit⟩ : (code ν a).Element)
      (⟨GuardDecision.unit⟩ : (code ν a).Element) :=
  (unit_member_iff ν a).mpr h

theorem neutral_member (ν : Valuation) (a : IndexAssignment) (name : Nat) :
    (code ν a).view.relation
      (⟨NeutralPER.neutralAtom name⟩ : (code ν a).Element)
      (⟨NeutralPER.neutralAtom name⟩ : (code ν a).Element) :=
  CandidatePi.decode_reflection (element ν a) (.atom name)

/-- At the actual refl index pattern the retained indices coincide. -/
def reflexiveAssignment (C : Code.{0} 0) : IndexAssignment where
  left := C
  right := C
  major := GuardDecision.unit
  major_member :=
    ⟨Or.inl ⟨codeRelated_refl C, fun _ => Iff.rfl⟩,
      Or.inl ⟨codeRelated_refl C, fun _ => Iff.rfl⟩⟩

theorem reflexivity_unit_member (ν : Valuation) (C : Code.{0} 0) :
    (code ν (reflexiveAssignment C)).view.relation
      (⟨GuardDecision.unit⟩ : (code ν (reflexiveAssignment C)).Element)
      (⟨GuardDecision.unit⟩ : (code ν (reflexiveAssignment C)).Element) :=
  unit_member_of_guard ν _ (codeRelated_refl C)

/-- Here the semantic major is the actual evaluator output of the source
variable, not just the supplied raw assignment. -/
theorem proposition_actual_major_member (ν : Valuation) (P : Prop) (name : Nat) :
    (code ν (propositionAssignment P name)).view.relation
      (⟨TaggedKEvaluation.image ν
        (rawEnvironment (propositionAssignment P name)) proofTerm⟩ :
          (code ν (propositionAssignment P name)).Element)
      (⟨TaggedKEvaluation.image ν
        (rawEnvironment (propositionAssignment P name)) proofTerm⟩ :
          (code ν (propositionAssignment P name)).Element) := by
  rw [NeutralCodes.valueEq_eq (proposition_major_image ν P name)]
  exact major_member ν (propositionAssignment P name)

theorem proposition_unit_member_iff (ν : Valuation) (P : Prop) (name : Nat) :
    (code ν (propositionAssignment P name)).view.relation
      (⟨GuardDecision.unit⟩ : (code ν (propositionAssignment P name)).Element)
      (⟨GuardDecision.unit⟩ : (code ν (propositionAssignment P name)).Element) ↔ P :=
  (unit_member_iff ν _).trans (proposition_guard_iff P name)

theorem proposition_code_values_same (ν : Valuation) (P Q : Prop) (name : Nat) :
    (code ν (propositionAssignment P name)).view.value =
      (code ν (propositionAssignment Q name)).view.value := rfl

/-- Every proposition has an admitted source instance and a constructed Eq
code with the actual type image and an actual evaluated neutral major. -/
theorem inhabited_interpreted_source (ν : Valuation) (P : Prop) (name : Nat) :
    ∃ i : OpenEqInput,
      i.assignment = propositionAssignment P name ∧
      ValueEq (code ν i.assignment).view.value
        (TaggedKEvaluation.image ν (rawEnvironment i.assignment) liftedEqualityType) ∧
      (code ν i.assignment).view.relation
        (⟨TaggedKEvaluation.image ν (rawEnvironment i.assignment) proofTerm⟩ :
          (code ν i.assignment).Element)
        (⟨TaggedKEvaluation.image ν (rawEnvironment i.assignment) proofTerm⟩ :
          (code ν i.assignment).Element) ∧
      (guard i.assignment ↔ P) := by
  obtain ⟨i, hi⟩ := inhabited_proposition_input P name
  refine ⟨i, hi, code_actual_image ν i.assignment, ?_, ?_⟩
  · rw [hi]
    exact proposition_actual_major_member ν P name
  · rw [hi]
    exact proposition_guard_iff P name

end Rcic.Declarative.Ann.LR3.GuardedEqFamily

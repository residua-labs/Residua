import rcic.RcicAnnLR3TaggedKSeedBoundary
import rcic.RcicAnnLR3PairedStatements

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.GuardDecision

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TaggedSaturatedTower

/-! Arbitrary propositions occur in the existing, certified candidate carrier.
This module classifies the logical strength of uniformly deciding its guards.
It does not assert `¬ Decidable P` or that every such candidate is the reading
of a closed source expression. closure_claim = 0. -/

def propElement (P : Prop) :=
  CandidatePi.ofCandidate (CandidateUniverse.proofCandidate P).toCandidate

def propCode (P : Prop) : Code.{0} 0 :=
  Code.proposition (propElement P)

def unit : Value := UnitModel.unitValue EnvI.bot

theorem propCode_eq_of_iff {P Q : Prop} (h : P ↔ Q) :
    propCode P = propCode Q := by
  have e : P = Q := propext h
  cases e
  rfl

theorem propCode_same_tag (P Q : Prop) :
    (propCode P).tag = (propCode Q).tag := rfl

theorem propCode_same_value (P Q : Prop) :
    (propCode P).view.value = (propCode Q).view.value := rfl

theorem propCode_raw_eq (P Q : Prop) :
    ValueEq (propCode P).view.value (propCode Q).view.value := by
  intro c
  rfl

theorem propCode_universe_member (P : Prop) :
    (universeCode.{0} 0).view.relation (propCode P) (propCode P) :=
  universe_member 0 (propCode P)

theorem propCode_neutral_member (P : Prop) (name : Nat) :
    (propCode P).view.relation
      (⟨NeutralPER.neutralAtom name⟩ : (propCode P).Element)
      (⟨NeutralPER.neutralAtom name⟩ : (propCode P).Element) :=
  CandidatePi.decode_reflection _ (.atom name)

theorem propCode_inhabited (P : Prop) :
    ∃ a : (propCode P).Element, (propCode P).view.relation a a :=
  ⟨⟨NeutralPER.neutralAtom 0⟩, propCode_neutral_member P 0⟩

theorem propElement_unit_iff (P : Prop) :
    CandidatePi.decode (propElement P) unit unit ↔ P := by
  constructor
  · intro h
    have h0 := (CandidatePi.complete_non_neutral
      (C := (CandidateUniverse.proofCandidate P).toCandidate)
      (CandidatePi.unit_not_neutral EnvI.bot)).mp h
    rcases h0.1 with ⟨hp, _⟩ | hn
    · exact hp
    · exact False.elim (CandidatePi.unit_not_neutral EnvI.bot
        (CandidatePi.old_neutral_included hn))
  · intro hp
    apply (CandidatePi.complete_non_neutral
      (C := (CandidateUniverse.proofCandidate P).toCandidate)
      (CandidatePi.unit_not_neutral EnvI.bot)).mpr
    change NeutralPER.ProofPER NeutralCodes.Neutral P unit unit
    constructor
    · exact Or.inl ⟨hp, fun c => Iff.rfl⟩
    · exact Or.inl ⟨hp, fun c => Iff.rfl⟩

theorem propCode_good_unit_iff (P : Prop) :
    TaggedKClosure.Good (propCode P) unit ↔ P := by
  constructor
  · rintro ⟨a, ha, he⟩
    change CandidatePi.decode (propElement P)
      ((propCode P).erase a) ((propCode P).erase a) at ha
    rw [NeutralCodes.valueEq_eq he] at ha
    exact (propElement_unit_iff P).mp ha
  · intro hp
    refine ⟨⟨unit⟩, (propElement_unit_iff P).mpr hp, ?_⟩
    intro c
    rfl

theorem propCode_decoded_unit_iff (P : Prop) :
    TaggedKClosure.Decoded (propCode P) unit unit ↔ P :=
  (TaggedKClosure.decoded_member_iff (propCode P) unit).trans
    (propCode_good_unit_iff P)

theorem propCode_related_iff (P Q : Prop) :
    CodeRelated (propCode P) (propCode Q) ↔ (P ↔ Q) := by
  constructor
  · intro h
    have hs := TaggedKClosure.codeRelated_decoded_same h
    constructor
    · intro hp
      exact (propCode_decoded_unit_iff Q).mp
        ((hs unit unit).mp ((propCode_decoded_unit_iff P).mpr hp))
    · intro hq
      exact (propCode_decoded_unit_iff P).mp
        ((hs unit unit).mpr ((propCode_decoded_unit_iff Q).mpr hq))
  · intro h
    rw [propCode_eq_of_iff h]
    exact TaggedSaturatedTower.codeRelated_refl _

theorem propCode_related_true_iff (P : Prop) :
    CodeRelated (propCode P) (propCode True) ↔ P := by
  constructor
  · intro h
    exact ((propCode_related_iff P True).mp h).mpr True.intro
  · intro hp
    exact (propCode_related_iff P True).mpr
      ⟨fun _ => True.intro, fun _ => hp⟩

theorem propCode_false_true_not_related :
    ¬ CodeRelated (propCode False) (propCode True) := by
  intro h
  exact (propCode_related_true_iff False).mp h

theorem propCode_true_related :
    CodeRelated (propCode True) (propCode True) :=
  (propCode_related_true_iff True).mpr True.intro

def propGuardDecision (P Q : Prop) [Decidable (P ↔ Q)] :
    Decidable (CodeRelated (propCode P) (propCode Q)) :=
  if h : P ↔ Q then
    isTrue ((propCode_related_iff P Q).mpr h)
  else
    isFalse (fun hc => h ((propCode_related_iff P Q).mp hc))

theorem uniform_prop_guard_decisions_imply_em
    (dec : ∀ P : Prop,
      Decidable (CodeRelated (propCode P) (propCode True)))
    (P : Prop) : P ∨ ¬ P := by
  cases dec P with
  | isTrue h => exact Or.inl ((propCode_related_true_iff P).mp h)
  | isFalse h =>
      exact Or.inr (fun hp => h ((propCode_related_true_iff P).mpr hp))

theorem all_prop_guards_decided_iff_em :
    (∀ P Q : Prop,
      CodeRelated (propCode P) (propCode Q) ∨
        ¬ CodeRelated (propCode P) (propCode Q)) ↔
    (∀ P : Prop, P ∨ ¬ P) := by
  constructor
  · intro h P
    rcases h P True with hp | hn
    · exact Or.inl ((propCode_related_true_iff P).mp hp)
    · exact Or.inr (fun hp => hn ((propCode_related_true_iff P).mpr hp))
  · intro h P Q
    rcases h (P ↔ Q) with hp | hn
    · exact Or.inl ((propCode_related_iff P Q).mpr hp)
    · exact Or.inr (fun hc => hn ((propCode_related_iff P Q).mp hc))

theorem no_raw_image_only_guard :
    ¬ ∃ R : Value → Value → Prop, ∀ P Q : Prop,
      R (propCode P).view.value (propCode Q).view.value ↔
        CodeRelated (propCode P) (propCode Q) := by
  rintro ⟨R, hR⟩
  have hgood := (hR True True).mpr propCode_true_related
  have hbad : R (propCode False).view.value (propCode True).view.value := hgood
  exact propCode_false_true_not_related ((hR False True).mp hbad)

/-- The parameter exhibits the nonempty observation domain explicitly. -/
theorem constant_valueEq_true_iff (c : CptI) (P : Prop) :
    ValueEq (fun _ => P) (fun _ => True) ↔ P := by
  constructor
  · intro h
    exact (h c).mpr True.intro
  · intro hp
    intro _
    exact ⟨fun _ => True.intro, fun _ => hp⟩

theorem uniform_valueEq_decisions_imply_em (c : CptI)
    (dec : ∀ x y : Value, Decidable (ValueEq x y))
    (P : Prop) : P ∨ ¬ P := by
  cases dec (fun _ => P) (fun _ => True) with
  | isTrue h => exact Or.inl ((constant_valueEq_true_iff c P).mp h)
  | isFalse h =>
      exact Or.inr (fun hp => h ((constant_valueEq_true_iff c P).mpr hp))

end Rcic.Declarative.Ann.LR3.GuardDecision

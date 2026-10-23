import rcic.RcicAnnLR3TaggedKClosure

/-!
# Same-tag raw equality does not preserve decoded candidates

The two endpoints are existing certified proposition codes. Their tags
and actual raw type images agree, and both completed candidates contain
every neutral atom. Only the true candidate contains the unit value.
The bare same-tag/raw-equality seed already prevents decoded coherence;
no K edge is needed for this independent base obstruction.

The existing strong CodeRelated relation retains actual carrier transport
and separates these endpoints. This concerns a proposed relation on all
certified codes, not source conversion or a source SortUniq theorem.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TaggedKSeedBoundary
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements TaggedSaturatedTower TaggedKClosure

def falseCode : Code.{0} 0 := Code.proposition CandidatePi.falseElement
def trueCode : Code.{0} 0 := Code.proposition CandidatePi.trueElement

theorem same_tag : falseCode.tag = trueCode.tag := rfl

theorem same_raw_image : falseCode.view.value = trueCode.view.value :=
  CandidatePi.collision_same_value

theorem same_type_image : ValueEq falseCode.view.value trueCode.view.value :=
  ValueEq.refl _

theorem bare_base : Base falseCode trueCode := ⟨same_tag, same_type_image⟩

theorem false_neutral_member (name : Nat) :
    falseCode.view.relation
      (⟨NeutralPER.neutralAtom name⟩ : falseCode.Element)
      (⟨NeutralPER.neutralAtom name⟩ : falseCode.Element) :=
  CandidatePi.decode_reflection _ (.atom name)

theorem true_neutral_member (name : Nat) :
    trueCode.view.relation
      (⟨NeutralPER.neutralAtom name⟩ : trueCode.Element)
      (⟨NeutralPER.neutralAtom name⟩ : trueCode.Element) :=
  CandidatePi.decode_reflection _ (.atom name)

theorem false_good_neutral (name : Nat) :
    Good falseCode (NeutralPER.neutralAtom name) :=
  ⟨⟨NeutralPER.neutralAtom name⟩, false_neutral_member name, ValueEq.refl _⟩

theorem true_good_neutral (name : Nat) :
    Good trueCode (NeutralPER.neutralAtom name) :=
  ⟨⟨NeutralPER.neutralAtom name⟩, true_neutral_member name, ValueEq.refl _⟩

theorem true_unit_member :
    trueCode.view.relation
      (⟨unitValue EnvI.bot⟩ : trueCode.Element)
      (⟨unitValue EnvI.bot⟩ : trueCode.Element) :=
  CandidatePi.trueElement_unit

theorem false_unit_not_member :
    ¬ falseCode.view.relation
      (⟨unitValue EnvI.bot⟩ : falseCode.Element)
      (⟨unitValue EnvI.bot⟩ : falseCode.Element) :=
  CandidatePi.falseElement_no_unit

theorem true_good_unit : Good trueCode (unitValue EnvI.bot) :=
  ⟨⟨unitValue EnvI.bot⟩, true_unit_member, ValueEq.refl _⟩

theorem false_not_good_unit : ¬ Good falseCode (unitValue EnvI.bot) := by
  rintro ⟨a, ha, he⟩
  change CandidatePi.decode CandidatePi.falseElement
    (falseCode.erase a) (falseCode.erase a) at ha
  rw [NeutralCodes.valueEq_eq he] at ha
  exact CandidatePi.falseElement_no_unit ha

theorem true_decoded_unit :
    Decoded trueCode (unitValue EnvI.bot) (unitValue EnvI.bot) :=
  (decoded_member_iff trueCode (unitValue EnvI.bot)).mpr true_good_unit

theorem false_not_decoded_unit :
    ¬ Decoded falseCode (unitValue EnvI.bot) (unitValue EnvI.bot) :=
  fun h => false_not_good_unit
    ((decoded_member_iff falseCode (unitValue EnvI.bot)).mp h)

theorem decoded_not_same :
    ¬ NeutralK.Same (Decoded falseCode) (Decoded trueCode) := by
  intro h
  exact false_not_decoded_unit ((h _ _).mpr true_decoded_unit)

theorem strong_not_related : ¬ CodeRelated falseCode trueCode :=
  fun h => decoded_not_same (codeRelated_decoded_same h)

theorem universe_members :
    (universeCode.{0} 0).view.relation falseCode falseCode ∧
    (universeCode.{0} 0).view.relation trueCode trueCode :=
  ⟨universe_member 0 falseCode, universe_member 0 trueCode⟩

theorem no_coherent_extension
    (R : Code.{0} 0 → Code.{0} 0 → Prop)
    (includes : ∀ C D, Base C D → R C D) :
    ¬ (∀ C D, R C D → NeutralK.Same (Decoded C) (Decoded D)) := by
  intro coherent
  exact decoded_not_same
    (coherent falseCode trueCode (includes falseCode trueCode bare_base))

theorem weak_closure_not_coherent (AtTarget : Frame.{0} 0 → Prop) :
    ¬ Coherent AtTarget := by
  intro h
  exact decoded_not_same (h falseCode trueCode (base_related AtTarget bare_base))

theorem inhabited_base_boundary (name : Nat) :
    Good falseCode (NeutralPER.neutralAtom name) ∧
    Good trueCode (NeutralPER.neutralAtom name) ∧
    Base falseCode trueCode ∧
    Decoded trueCode (unitValue EnvI.bot) (unitValue EnvI.bot) ∧
    ¬ Decoded falseCode (unitValue EnvI.bot) (unitValue EnvI.bot) ∧
    ¬ CodeRelated falseCode trueCode :=
  ⟨false_good_neutral name, true_good_neutral name, bare_base,
    true_decoded_unit, false_not_decoded_unit, strong_not_related⟩

end Rcic.Declarative.Ann.LR3.TaggedKSeedBoundary

import rcic.RcicAnnLR3GuardedTaggedCode
import rcic.RcicAnnLR3InductiveCodes

/-!
# A certified universe without typed neutral-spine closure

The arbitrary-carrier universe witness supplies named reflection, not
closure under arbitrary typed neutral spines. The universe below is an
actual inhabited Code 1, with carrier Nat, equality relation, decoder
the native neutral Code 0, and identity reflection of names.

Its carrier contains no element whose erasure is the correctly tagged
image of a genuine neutral application. Thus even the universe clause of
type-directed reflection needs an additional closure condition if the
old carriers and their erasures are retained. This is distinct from
asking a universe member to erase to an untagged raw atom.
-/
set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.UniverseSpineBoundary

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open TaggedSaturatedTower (Kernel KernelRelated)

universe u

def nameDecode (name : Nat) : Kernel.{0} 0 :=
  TaggedSaturatedTower.neutralKernel 0 name

def nameLaws : RelLaws (@Eq Nat) where
  symm := fun h => h.symm
  trans := fun h j => h.trans j

def nameLegacy : TaggedSaturatedTower.Code.{0} 1 where
  kernel := TaggedSaturatedTower.universeKernel 0 Nat nameDecode Eq
    nameLaws id (fun _ => rfl)
  tag := .univ
  witness := .univ 0 Nat nameDecode Eq nameLaws id (fun _ => rfl)
    (fun x y h => by
      cases h
      exact TaggedSaturatedTower.kernelRelated_refl _)
    (fun _ => ValueEq.refl _)

def nameUniverse : GuardedTaggedCode.Code.{0} 1 := .legacy nameLegacy

def nameReflect (name : Nat) : nameUniverse.Element := name

theorem nameReflect_member (name : Nat) :
    nameUniverse.view.relation (nameReflect name) (nameReflect name) := rfl

theorem tagged_atom_native (k : Option Nat) (name : Nat) :
    ValueEq (InductiveCodes.taggedValue k (NeutralPER.neutralAtom name))
      (NativeMemberValues.value k name) :=
  InductiveCodes.taggedValue_denI EnvI.bot k (.const name [])

theorem nameReflect_image (name : Nat) :
    ValueEq (nameUniverse.erase (nameReflect name))
      (InductiveCodes.taggedValue (some 0) (NeutralPER.neutralAtom name)) :=
  (tagged_atom_native (some 0) name).symm

theorem tagged_application_not_native (k : Option Nat) (head name : Nat)
    (a : Value) (ha : CandidatePi.NonemptyValue a) :
    ¬ ValueEq
      (InductiveCodes.taggedValue k
        (NeutralPi.applyValue (NeutralPER.neutralAtom head) a))
      (NativeMemberValues.value k name) := by
  obtain ⟨z, hz⟩ := ha
  intro he
  have hp : NeutralPi.applyValue (NeutralPER.neutralAtom head) a
      (.spine head [z]) :=
    Or.inr (Or.inr ⟨head, [], z, rfl,
      NeutralPER.neutralAtom_observed head, hz⟩)
  have ht := (InductiveCodes.taggedValue_full k _ (.spine head [z])).mpr hp
  have hn := (he (NeutralCodes.fullTag k (.spine head [z]))).mp ht
  have ht' := ((tagged_atom_native k name)
    (NeutralCodes.fullTag k (.spine head [z]))).mpr hn
  have ha' := (InductiveCodes.taggedValue_full k _ (.spine head [z])).mp ht'
  rcases approxI_const_inv ha' with h | h <;> cases h

/-- Minimal universe reflection at the correct type-directed raw image.
The failed law includes the level tag; it is not raw-neutral identity. -/
structure SpineReflection {k : Nat} (C : GuardedTaggedCode.Code.{u} (k+1)) where
  reflect : (n : Value) → CandidatePi.Neutral n → C.Element
  member : ∀ n hn, C.view.relation (reflect n hn) (reflect n hn)
  image : ∀ n hn, ValueEq (C.erase (reflect n hn))
    (InductiveCodes.taggedValue (some k) n)

def application : Value :=
  NeutralPi.applyValue (NeutralPER.neutralAtom 0) (NeutralPER.neutralAtom 1)

theorem application_neutral : CandidatePi.Neutral application :=
  .app (.atom 0) _ (CandidatePi.neutral_nonempty (.atom 1))

theorem application_type_level :
    SortMember (some 0) (InductiveCodes.taggedValue (some 0) application) := by
  rintro c (rfl | ⟨a, p, rfl, ha, _⟩)
  · exact .bot
  · exact .tagged a p ha

theorem application_type_defined :
    TypeDefined (InductiveCodes.taggedValue (some 0) application) :=
  ⟨some 0, .bot,
    (InductiveCodes.taggedValue_full (some 0) application .bot).mpr (Or.inl rfl)⟩

theorem no_application_member (x : nameUniverse.Element) :
    ¬ ValueEq (nameUniverse.erase x)
      (InductiveCodes.taggedValue (some 0) application) := by
  intro h
  exact tagged_application_not_native (some 0) 0 x
    (NeutralPER.neutralAtom 1) (CandidatePi.neutral_nonempty (.atom 1)) h.symm

theorem no_spine_reflection : ¬ Nonempty (SpineReflection nameUniverse) := by
  rintro ⟨r⟩
  exact no_application_member (r.reflect application application_neutral)
    (r.image application application_neutral)

theorem inhabited_universe_spine_boundary :
    (∃ x : nameUniverse.Element, nameUniverse.view.relation x x) ∧
    (∀ name, nameUniverse.view.relation (nameReflect name) (nameReflect name)) ∧
    (∀ name, ValueEq (nameUniverse.erase (nameReflect name))
      (InductiveCodes.taggedValue (some 0) (NeutralPER.neutralAtom name))) ∧
    CandidatePi.Neutral application ∧
    SortMember (some 0) (InductiveCodes.taggedValue (some 0) application) ∧
    TypeDefined (InductiveCodes.taggedValue (some 0) application) ∧
    (¬ ∃ x : nameUniverse.Element, nameUniverse.view.relation x x ∧
      ValueEq (nameUniverse.erase x)
        (InductiveCodes.taggedValue (some 0) application)) ∧
    ¬ Nonempty (SpineReflection nameUniverse) := by
  refine ⟨⟨nameReflect 0, nameReflect_member 0⟩,
    nameReflect_member, nameReflect_image, application_neutral,
    application_type_level, application_type_defined, ?_, no_spine_reflection⟩
  rintro ⟨x, _, hx⟩
  exact no_application_member x hx

end Rcic.Declarative.Ann.LR3.UniverseSpineBoundary

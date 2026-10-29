import rcic.RcicAnnLR3OptionLevelKernel

/-!
# A named none universe with an explicit self decoder

The carrier has a distinguished self code and every native named code.
The universe kernel is defined directly, before its decoder. Decoding
self therefore returns an already-defined object; no recursive decoder
constructor, level decrease, or choice is involved. Named ordinary term
fibres remain chaotic. The universe relation retains code identity and
the exact images needed by universe elimination.

The raw none code algebra below represents this same carrier. The next
module combines it with the existing finite algebra and supplies the
unchanged original sort arm. This is not a whole-language model and is
not an extension of the Nat-indexed RCodeSound record. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.NoneSelfUniverse

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open UnitModel TypedPER TypedStatements

universe u

/-- none is the universe's own name; some n is its native named code. -/
def image : Option Nat → Value
  | none => universeValue none
  | some n => NativeMemberValues.value none n

theorem image_level (a : Option Nat) : SortMember none (image a) := by
  cases a with
  | none => exact sort_member _ none
  | some n => exact NativeMemberValues.value_level none n

theorem image_defined (a : Option Nat) : TypeDefined (image a) := by
  cases a with
  | none => exact sort_defined _ none
  | some n => exact NativeMemberValues.value_defined none n

def selfUniverse : OptionLevelKernel.Kernel.{u} none where
  Element := ULift.{u} (Option Nat)
  erase := fun a => image a.down
  value := universeValue none
  level := sort_member _ none
  defined := sort_defined _ none
  relation := fun a b => a = b
  lawful := ⟨Eq.symm, Eq.trans⟩
  point := fun n => ⟨some n⟩
  point_member := fun _ => rfl
  irrelevant := fun h => by cases h

def self : selfUniverse.{u}.Element := ULift.up.{u} none
def named (n : Nat) : selfUniverse.{u}.Element := ULift.up.{u} (some n)

def decode (a : selfUniverse.{u}.Element) : OptionLevelKernel.Kernel.{u} none :=
  match a.down with
  | none => selfUniverse
  | some n => OptionLevelKernel.noneNamed n

theorem decode_self : decode self = selfUniverse.{u} := rfl
theorem decode_named (n : Nat) :
    decode (named.{u} n) = OptionLevelKernel.noneNamed n := rfl
theorem self_member : selfUniverse.relation self.{u} self := rfl
theorem named_member (n : Nat) : selfUniverse.relation (named.{u} n) (named n) := rfl
theorem self_erasure : selfUniverse.erase self.{u} = universeValue none := rfl
theorem named_erasure (n : Nat) :
    selfUniverse.erase (named.{u} n) = NativeMemberValues.value none n := rfl

theorem decode_image (a : selfUniverse.{u}.Element) :
    (decode a).value = selfUniverse.erase a := by
  rcases a with ⟨a⟩
  cases a <;> rfl

theorem decode_coherent (a b : selfUniverse.{u}.Element) (h : selfUniverse.relation a b) :
    OptionLevelKernel.Related (decode a) (decode b) := by
  cases h
  exact ⟨OptionLevelKernel.Iso.refl _⟩

theorem witness : OptionLevelKernel.UniverseWitness none selfUniverse.{u}.Element
    decode selfUniverse.relation selfUniverse.point :=
  ⟨decode_coherent, fun _ => ValueEq.refl _⟩

theorem named_terms_chaotic (n : Nat) (x y : Value) :
    (decode (named.{u} n)).relation ⟨x⟩ ⟨y⟩ := True.intro

theorem universe_elimination (a : selfUniverse.{u}.Element) :
    SortMember none (selfUniverse.erase a) ∧ TypeDefined (selfUniverse.erase a) :=
  ⟨image_level a.down, image_defined a.down⟩

/-- These two actual reflected codes retain different type images, even
after adding the self member. Universal decoder relatedness is impossible. -/
theorem no_universal_decoder_coherence :
    ¬ (∀ a b : selfUniverse.{u}.Element,
      OptionLevelKernel.Related (decode a) (decode b)) := by
  intro h
  have he : (0 : Nat) = 1 :=
    (OptionLevelKernel.noneNamed_related_iff.{u} 0 1).mp (h (named 0) (named 1))
  cases he

/-! ## The matching raw none algebra -/

private def rootProbe : CptI := .spine 10 [.bot, .spine 11 [.bot]]

private theorem rootProbe_member : universeValue none rootProbe := by
  exact approxI_famApp 10 []
    (.cons (.bot _ _) (.cons (approxI_famApp 11 [] (.cons (.bot _ _) .nil)) .nil))

private theorem rootProbe_not_named (n : Nat) :
    ¬ NativeMemberValues.value none n rootProbe := by
  intro hc
  have h := approxI_foldApps_const_inv
    (r := 10) (ls := []) (xs := [levelTerm none, .const n []]) hc
  rcases h with hbot | ⟨us, he, hs⟩
  · cases hbot
  · change (.spine 10 [.bot, .spine 11 [.bot]] : CptI) = .spine 10 us at he
    cases he
    cases hs with
    | cons ha hs =>
      cases hs with
      | cons hb hs =>
        rcases approxI_const_inv hb with hbot | heq
        · cases hbot
        · cases heq

theorem self_not_named (n : Nat) :
    ¬ ValueEq (image none) (image (some n)) := by
  intro h
  exact rootProbe_not_named n ((h rootProbe).mp rootProbe_member)

theorem image_injective {a b : Option Nat} (h : ValueEq (image a) (image b)) : a = b := by
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some n => exact (self_not_named n h).elim
  | some m =>
      cases b with
      | none => exact (self_not_named m h.symm).elim
      | some n =>
          exact congrArg some (TaggedSaturatedTower.native_value_name_injective none m n h)

def UniversePER (V W : Value) : Prop :=
  ∃ a : Option Nat, ValueEq V (image a) ∧ ValueEq W (image a)

theorem universePER_laws : Laws UniversePER where
  symm := fun ⟨a, hv, hw⟩ => ⟨a, hw, hv⟩
  trans := by
    rintro V W Z ⟨a, hv, hw⟩ ⟨b, hw', hz⟩
    have hab := image_injective (hw.symm.trans hw')
    cases hab
    exact ⟨a, hv, hz⟩

def elementPER : Option Nat → Relation
  | none => UniversePER
  | some _ => NoneUniverseBoundary.Chaos

theorem elementPER_laws (a : Option Nat) : Laws (elementPER a) := by
  cases a with
  | none => exact universePER_laws
  | some _ => exact NoneUniverseBoundary.chaos_laws

def NoneCode (V : Value) (R : Relation) : Prop :=
  ∃ a : Option Nat, ValueEq V (image a) ∧ Same R (elementPER a)

theorem noneCode (a : Option Nat) : NoneCode (image a) (elementPER a) :=
  ⟨a, ValueEq.refl _, fun _ _ => Iff.rfl⟩

theorem noneCode_lawful {V : Value} {R : Relation} (h : NoneCode V R) : Laws R := by
  obtain ⟨a, _, hr⟩ := h
  exact ⟨fun hxy => (hr _ _).mpr ((elementPER_laws a).symm ((hr _ _).mp hxy)),
    fun hxy hyz => (hr _ _).mpr
      ((elementPER_laws a).trans ((hr _ _).mp hxy) ((hr _ _).mp hyz))⟩

theorem noneCode_level {V : Value} {R : Relation} (h : NoneCode V R) :
    SortMember none V := by
  obtain ⟨a, hv, _⟩ := h
  exact sortMember_congr hv.symm (image_level a)

theorem noneCode_defined {V : Value} {R : Relation} (h : NoneCode V R) :
    TypeDefined V := by
  obtain ⟨a, hv, _⟩ := h
  exact typeDefined_congr hv.symm (image_defined a)

theorem noneCode_coherent {V : Value} {R S : Relation}
    (h : NoneCode V R) (g : NoneCode V S) : Same R S := by
  obtain ⟨a, hv, hr⟩ := h
  obtain ⟨b, hw, hs⟩ := g
  have hab := image_injective (hv.symm.trans hw)
  cases hab
  exact fun x y => (hr x y).trans (hs x y).symm

theorem self_code : NoneCode (universeValue none) UniversePER := noneCode none
theorem raw_self_member : Member UniversePER (universeValue none) :=
  ⟨none, ValueEq.refl _, ValueEq.refl _⟩

theorem raw_named_member (n : Nat) : Member UniversePER (NativeMemberValues.value none n) :=
  ⟨some n, ValueEq.refl _, ValueEq.refl _⟩

theorem raw_named_terms_chaotic (n : Nat) (x y : Value) :
    NoneCode (NativeMemberValues.value none n) NoneUniverseBoundary.Chaos ∧
      NoneUniverseBoundary.Chaos x y :=
  ⟨noneCode (some n), True.intro⟩

theorem raw_elimination {x : Value} (h : Member UniversePER x) :
    SortMember none x ∧ TypeDefined x := by
  obtain ⟨a, hx, _⟩ := h
  exact ⟨sortMember_congr hx.symm (image_level a),
    typeDefined_congr hx.symm (image_defined a)⟩

/-- A real decoder exists for the self member as well as every name. -/
theorem raw_decode {x : Value} (h : Member UniversePER x) :
    ∃ R : Relation, NoneCode x R := by
  obtain ⟨a, hx, _⟩ := h
  exact ⟨elementPER a, a, hx, fun _ _ => Iff.rfl⟩

theorem raw_transport {V W : Value} (h : UniversePER V W) :
    ∃ R : Relation, NoneCode V R ∧ NoneCode W R := by
  obtain ⟨a, hv, hw⟩ := h
  exact ⟨elementPER a, ⟨a, hv, fun _ _ => Iff.rfl⟩,
    ⟨a, hw, fun _ _ => Iff.rfl⟩⟩

/-- The raw universe relation agrees with the retained carrier relation. -/
theorem raw_relation_iff (a b : selfUniverse.{u}.Element) :
    UniversePER (selfUniverse.erase a) (selfUniverse.erase b) ↔ selfUniverse.relation a b := by
  constructor
  · rintro ⟨c, ha, hb⟩
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    exact congrArg (fun d : Option Nat => ULift.up.{u} d)
      (image_injective (ha.trans hb.symm))
  · intro h
    cases h
    exact ⟨a.down, ValueEq.refl _, ValueEq.refl _⟩

end Rcic.Declarative.Ann.LR3.NoneSelfUniverse

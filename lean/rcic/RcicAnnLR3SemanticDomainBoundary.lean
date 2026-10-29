import rcic.RcicAnnLR3GuardedTaggedCode

/-!
# Certified semantic carriers and the domain of readback

The existing arbitrary-carrier universe constructor certifies carriers
with semantic information invisible to erasure. A concrete inhabited
Code 1 below records an arbitrary Boolean stream in addition to its
native neutral name. Its relation is equality; its decoder ignores the
stream. All universe-certificate premises are constructed.

Two precise boundaries follow. Erasure equality cannot recover the
semantic relation. Moreover no readback of *every* carrier element into
countably enumerated syntax can have an evaluation left inverse modulo
that relation. The latter is a constructive diagonal argument.

These facts do not obstruct a new glued domain indexed by every Code,
nor readback of source-generated elements carrying representability
data. They identify which stronger theorem does not follow from the
present certificates. No raw-neutral reflector is involved.
-/
set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.SemanticDomainBoundary

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open TaggedSaturatedTower (Kernel KernelRelated)

universe v

abbrev Stream := Nat → Bool
abbrev Carrier := Nat × Stream

def quiet : Stream := fun _ => false
def loud : Stream := fun _ => true

def decode (x : Carrier) : Kernel.{0} 0 :=
  TaggedSaturatedTower.neutralKernel 0 x.1

def relation : Carrier → Carrier → Prop := Eq

def laws : RelLaws relation where
  symm := fun h => h.symm
  trans := fun h j => h.trans j

def point (name : Nat) : Carrier := (name, quiet)

theorem all_members (x : Carrier) : relation x x := rfl

theorem coherent (x y : Carrier) (h : relation x y) :
    KernelRelated (decode x) (decode y) := by
  cases h
  exact TaggedSaturatedTower.kernelRelated_refl _

theorem reflection_image (name : Nat) :
    ValueEq (decode (point name)).per.value
      (NativeMemberValues.value (some 0) name) :=
  ValueEq.refl _

def legacy : TaggedSaturatedTower.Code.{0} 1 where
  kernel := TaggedSaturatedTower.universeKernel 0 Carrier decode
    relation laws point all_members
  tag := .univ
  witness := .univ 0 Carrier decode relation laws point all_members
    coherent reflection_image

def code : GuardedTaggedCode.Code.{0} 1 := .legacy legacy

theorem relation_iff (x y : code.Element) :
    code.view.relation x y ↔ x = y := Iff.rfl

/-- The opaque carrier still has constructive type-directed universe
reflection. The readback boundary below does not refute this operation. -/
def reflect (name : Nat) : code.Element := point name

theorem reflect_member (name : Nat) :
    code.view.relation (reflect name) (reflect name) := rfl

theorem reflect_image (name : Nat) :
    ValueEq (code.erase (reflect name))
      (NativeMemberValues.value (some 0) name) := ValueEq.refl _

theorem reflect_related_iff (r s : Nat) :
    code.view.relation (reflect r) (reflect s) ↔ r = s := by
  constructor
  · exact fun h => congrArg Prod.fst h
  · intro h
    cases h
    rfl

def low : code.Element := (0, quiet)
def high : code.Element := (0, loud)

theorem low_member : code.view.relation low low := rfl
theorem high_member : code.view.relation high high := rfl

theorem low_high_same_erasure : ValueEq (code.erase low) (code.erase high) :=
  ValueEq.refl _

theorem low_high_not_related : ¬ code.view.relation low high := by
  intro h
  have h0 : false = true := congrArg (fun x : Carrier => x.2 0) h
  cases h0

/-- An erasure-only quotient cannot faithfully recover this semantic PER. -/
theorem erasure_does_not_reflect_relation :
    ¬ (∀ x y : code.Element,
      ValueEq (code.erase x) (code.erase y) → code.view.relation x y) := by
  intro h
  exact low_high_not_related (h low high low_high_same_erasure)

/-- A dependent certified family can genuinely use retained semantic
data. Respect of the domain relation is an explicit constructive
KernelIso, since the domain relation here is equality. -/
def fibre (x : code.Element) : GuardedTaggedCode.Code.{0} 1 :=
  .legacy (TaggedSaturatedTower.Code.neutral 1 (if x.2 0 then 1 else 0))

def fibreTransport (x y : code.Element) (h : code.view.relation x y) :
    TaggedSaturatedTower.KernelIso (fibre x).kernel (fibre y).kernel := by
  cases h
  exact TaggedSaturatedTower.KernelIso.refl _

theorem fibre_images_distinct :
    ¬ ValueEq (fibre low).view.value (fibre high).view.value := by
  intro h
  have hn : (0 : Nat) = 1 :=
    TaggedSaturatedTower.native_value_name_injective (some 1) 0 1 h
  cases hn

/-- A raw-Value-only evaluator cannot represent every coherent family
over every certified carrier. A semantic evaluator retaining the stream
does have the total operation `fibre` above. -/
theorem fibre_not_raw_factorable :
    ¬ ∃ run : Value → Value,
      ∀ x : code.Element, ValueEq (run (code.erase x)) (fibre x).view.value := by
  rintro ⟨run, hrun⟩
  exact fibre_images_distinct ((hrun low).symm.trans (hrun high))

/-- A deliberately weak readback interface: no normality, completeness,
syntax equality decision, or neutrality law is required. -/
structure CountedReadback (C : GuardedTaggedCode.Code.{0} 1) where
  quote : C.Element → Nat
  evaluate : Nat → C.Element
  sound : ∀ x, C.view.relation (evaluate (quote x)) x

theorem bool_not_self (b : Bool) : (!b) ≠ b := by
  cases b <;> decide

/-- The certificate is fully inhabited, but its arbitrary semantic
elements cannot all be represented by a countably enumerated syntax. -/
theorem no_counted_readback : ¬ Nonempty (CountedReadback code) := by
  rintro ⟨r⟩
  let diagonal : code.Element := (0, fun n => !((r.evaluate n).2 n))
  have hs : r.evaluate (r.quote diagonal) = diagonal := r.sound diagonal
  have hn := congrArg (fun x : Carrier => x.2 (r.quote diagonal)) hs
  exact bool_not_self ((r.evaluate (r.quote diagonal)).2 (r.quote diagonal)) hn.symm

/-- Constructive enumeration data. Finite source/normal syntax typically
has this interface after adjoining a default inhabitant. -/
structure Enumeration (N : Type v) where
  enumerate : Nat → N
  number : N → Nat
  enumerate_number : ∀ n, enumerate (number n) = n

structure Readback (C : GuardedTaggedCode.Code.{0} 1) (N : Type v) where
  reify : C.Element → N
  evaluate : N → C.Element
  sound : ∀ x, C.view.relation (evaluate (reify x)) x

def Readback.counted {C : GuardedTaggedCode.Code.{0} 1} {N : Type v}
    (e : Enumeration N) (r : Readback C N) : CountedReadback C where
  quote := fun x => e.number (r.reify x)
  evaluate := fun n => r.evaluate (e.enumerate n)
  sound := fun x => by
    change C.view.relation
      (r.evaluate (e.enumerate (e.number (r.reify x)))) x
    rw [e.enumerate_number]
    exact r.sound x

theorem no_enumerated_readback {N : Type v} (e : Enumeration N) :
    ¬ Nonempty (Readback code N) := by
  rintro ⟨r⟩
  exact no_counted_readback ⟨r.counted e⟩

theorem inhabited_readback_boundary :
    (∃ x : code.Element, code.view.relation x x) ∧
    (∃ x y : code.Element,
      code.view.relation x x ∧ code.view.relation y y ∧
      ValueEq (code.erase x) (code.erase y) ∧ ¬ code.view.relation x y) ∧
    ¬ Nonempty (CountedReadback code) :=
  ⟨⟨low, low_member⟩,
    ⟨low, high, low_member, high_member,
      low_high_same_erasure, low_high_not_related⟩,
    no_counted_readback⟩

theorem inhabited_retained_index_boundary :
    (∀ name, code.view.relation (reflect name) (reflect name)) ∧
    (∀ name, ValueEq (code.erase (reflect name))
      (NativeMemberValues.value (some 0) name)) ∧
    code.view.relation low low ∧ code.view.relation high high ∧
    ValueEq (code.erase low) (code.erase high) ∧
    (∀ x y, code.view.relation x y →
      Nonempty (TaggedSaturatedTower.KernelIso (fibre x).kernel (fibre y).kernel)) ∧
    ¬ ∃ run : Value → Value,
      ∀ x : code.Element, ValueEq (run (code.erase x)) (fibre x).view.value :=
  ⟨reflect_member, reflect_image, low_member, high_member,
    low_high_same_erasure, fun x y h => ⟨fibreTransport x y h⟩,
    fibre_not_raw_factorable⟩

end Rcic.Declarative.Ann.LR3.SemanticDomainBoundary

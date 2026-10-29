import rcic.RcicAnnLR3TaggedSaturatedTower

/-!
# Exact Option-indexed retained kernels

The finite tagged kernels embed without changing their carriers, erasures,
or relations. At `none`, an ordinary term fibre can be chaotic while its
type image retains the exact `none` tag. A universe fibre has a different
obligation: its elements decode to actual type codes and its relation
must respect their retained type images. The named fragment below gives
an inhabited example of both fibres and proves that universal relatedness
of universe elements would violate that obligation.

This is an additive kernel layer and a named none-universe fragment. It
does not supply source soundness or a closed recursive universe of all
none codes. The original all-valuation sort-separation theorem is retained
unchanged. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.OptionLevelKernel

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily

universe u v

structure Kernel (k : Option Nat) where
  Element : Type u
  erase : Element → Value
  value : Value
  level : SortMember k value
  defined : TypeDefined value
  relation : Element → Element → Prop
  lawful : RelLaws relation
  point : Nat → Element
  point_member : ∀ name, relation (point name) (point name)
  irrelevant : k = some 0 → ∀ x y,
    relation x x → relation y y → relation x y

/-- All finite constructor-certified kernels have a direct embedding.
Certification is retained in the input, not inferred from a raw image. -/
def ofFinite {k : Nat} (C : TaggedSaturatedTower.Kernel.{u} k) :
    Kernel.{u} (some k) where
  Element := C.Element
  erase := C.erase
  value := C.per.value
  level := C.per.level
  defined := C.per.defined
  relation := C.per.relation
  lawful := C.per.lawful
  point := C.per.point
  point_member := C.per.point_member
  irrelevant := fun h => C.per.irrelevant (Option.some.inj h)

theorem ofFinite_value {k : Nat} (C : TaggedSaturatedTower.Kernel.{u} k) :
    (ofFinite C).value = C.per.value := rfl

theorem ofFinite_erase {k : Nat} (C : TaggedSaturatedTower.Kernel.{u} k)
    (x : C.Element) : (ofFinite C).erase x = C.erase x := rfl

theorem ofFinite_relation {k : Nat} (C : TaggedSaturatedTower.Kernel.{u} k)
    (x y : C.Element) :
    (ofFinite C).relation x y ↔ C.per.relation x y := Iff.rfl

/-- An exact type image cannot acquire a different Option index. -/
theorem index_unique {k l : Option Nat} (C : Kernel.{u} k) (D : Kernel.{v} l)
    (h : ValueEq C.value D.value) : k = l :=
  sortMember_unique C.level (sortMember_congr h.symm D.level) C.defined

structure Iso {k : Option Nat} (C : Kernel.{u} k) (D : Kernel.{v} k) where
  forward : C.Element → D.Element
  backward : D.Element → C.Element
  left_inv : ∀ x, backward (forward x) = x
  right_inv : ∀ y, forward (backward y) = y
  type_image : ValueEq C.value D.value
  element_image : ∀ x, ValueEq (D.erase (forward x)) (C.erase x)
  point_image : ∀ name, forward (C.point name) = D.point name
  relation : ∀ x y, C.relation x y ↔ D.relation (forward x) (forward y)

def Iso.refl {k : Option Nat} (C : Kernel.{u} k) : Iso C C where
  forward := fun x => x
  backward := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  type_image := ValueEq.refl _
  element_image := fun _ => ValueEq.refl _
  point_image := fun _ => rfl
  relation := fun _ _ => Iff.rfl

def Related {k : Option Nat} (C : Kernel.{u} k) (D : Kernel.{v} k) : Prop :=
  Nonempty (Iso C D)

theorem related_type_image {k : Option Nat} {C : Kernel.{u} k}
    {D : Kernel.{v} k} (h : Related C D) : ValueEq C.value D.value := by
  rcases h with ⟨h⟩
  exact h.type_image

/-- Chaotic term fibres retain arbitrary raw term images. This constructor
is not a global rule assigning the same relation to every none code. -/
def noneTerm (V : Value) (hV : SortMember none V) (hd : TypeDefined V) :
    Kernel.{u} none where
  Element := ULift.{u} Value
  erase := ULift.down
  value := V
  level := hV
  defined := hd
  relation := fun _ _ => True
  lawful := ⟨fun _ => True.intro, fun _ _ => True.intro⟩
  point := fun name => ⟨NeutralPER.neutralAtom name⟩
  point_member := fun _ => True.intro
  irrelevant := fun h => by cases h

theorem noneTerm_member (V : Value) (hV : SortMember none V)
    (hd : TypeDefined V) (x y : Value) :
    (noneTerm.{u} V hV hd).relation ⟨x⟩ ⟨y⟩ := True.intro

theorem noneTerm_erasure (V : Value) (hV : SortMember none V)
    (hd : TypeDefined V) (x : Value) :
    (noneTerm.{u} V hV hd).erase ⟨x⟩ = x := rfl

def noneNamed (name : Nat) : Kernel.{u} none :=
  noneTerm (NativeMemberValues.value none name)
    (NativeMemberValues.value_level none name)
    (NativeMemberValues.value_defined none name)

theorem noneNamed_related_iff (r s : Nat) :
    Related (noneNamed.{u} r) (noneNamed.{u} s) ↔ r = s := by
  constructor
  · intro h
    exact TaggedSaturatedTower.native_value_name_injective none r s
      (related_type_image h)
  · intro h
    cases h
    exact ⟨Iso.refl _⟩

/-- A universe constructor over an explicitly supplied decoded carrier.
It also works at none; the index alone does not supply the decoder. -/
def universeKernel (k : Option Nat) (κ : Type u)
    (decode : κ → Kernel.{u} k) (R : κ → κ → Prop)
    (laws : RelLaws R) (q : Nat → κ) (members : ∀ x, R x x) :
    Kernel.{u} (k.map Nat.succ) where
  Element := κ
  erase := fun x => (decode x).value
  value := universeValue k
  level := sort_member _ _
  defined := sort_defined _ _
  relation := R
  lawful := laws
  point := q
  point_member := fun name => members (q name)
  irrelevant := by
    intro h
    cases k <;> simp at h

structure UniverseWitness (k : Option Nat) (κ : Type u)
    (decode : κ → Kernel.{u} k) (R : κ → κ → Prop) (q : Nat → κ) : Prop where
  coherent : ∀ x y, R x y → Related (decode x) (decode y)
  reflection_image : ∀ name,
    ValueEq (decode (q name)).value (NativeMemberValues.value k name)

theorem universe_elimination (k : Option Nat) (κ : Type u)
    (decode : κ → Kernel.{u} k) (R : κ → κ → Prop)
    (laws : RelLaws R) (q : Nat → κ) (members : ∀ x, R x x) (x : κ) :
    SortMember k ((universeKernel k κ decode R laws q members).erase x) ∧
      TypeDefined ((universeKernel k κ decode R laws q members).erase x) :=
  ⟨(decode x).level, (decode x).defined⟩

def noneNamedUniverse : Kernel.{u} none :=
  universeKernel none (ULift.{u} Nat) (fun x => noneNamed x.down)
    (fun x y => x = y) ⟨Eq.symm, Eq.trans⟩
    (fun name => ⟨name⟩) (fun _ => rfl)

theorem noneNamedUniverse_witness :
    UniverseWitness none (ULift.{u} Nat) (fun x => noneNamed.{u} x.down)
      (fun x y => x = y) (fun name => ⟨name⟩) := by
  constructor
  · intro x y h
    cases h
    exact ⟨Iso.refl _⟩
  · intro name
    exact ValueEq.refl _

theorem noneNamedUniverse_member (name : Nat) :
    noneNamedUniverse.relation (ULift.up.{u} name) (ULift.up.{u} name) := rfl

theorem noneNamedUniverse_erasure (name : Nat) :
    noneNamedUniverse.erase (ULift.up.{u} name) =
      NativeMemberValues.value none name := rfl

theorem noneNamedUniverse_relation_iff (r s : Nat) :
    noneNamedUniverse.relation (ULift.up.{u} r) (ULift.up.{u} s) ↔ r = s := by
  constructor
  · exact congrArg ULift.down
  · intro h
    cases h
    rfl

/-- The premises are realized by the two constructed named fibres.
Giving their universe the universal relation would destroy the required
type-image coherence, despite each term fibre being chaotic. -/
theorem no_chaotic_named_universe :
    ¬ (∀ r s : Nat, Related (noneNamed.{u} r) (noneNamed.{u} s)) := by
  intro h
  have hz : (0 : Nat) = 1 := (noneNamed_related_iff 0 1).mp (h 0 1)
  cases hz

theorem none_not_finite_image (C : Kernel.{u} none) (k : Nat)
    (D : Kernel.{v} (some k)) : ¬ ValueEq C.value D.value := by
  intro h
  have hi := index_unique C D h
  cases hi

/-- Raw sort comparison is still over all Option-valued valuations. -/
theorem evaluated_sort_eq_iff_eqN (ρ : EnvI) (a b : Level) :
    (∀ ν : Valuation, InterpretedEq ν ρ (.sort a) (.sort b)) ↔ eqN a b :=
  UnitModel.evaluated_sort_eq_iff_eqN ρ a b

theorem none_sort_not_finite_sort (ρ : EnvI) (k : Nat) :
    ¬ ValueEq (denI ρ (sortTerm none)) (denI ρ (sortTerm (some k))) := by
  intro h
  have hi := sort_code_injective h
  cases hi

end Rcic.Declarative.Ann.LR3.OptionLevelKernel

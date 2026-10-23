import rcic.RcicAnnLR3GuardedTaggedCode

/-! A separate conversion-based universe for the extended carrier.

Both existing tag-sensitive CodeRelated definitions and their universes
remain unchanged. This alternative universe relates its code elements by
actual KernelIso existence. Thus guarded branch conversion is also a
relation of its universe elements, while native neutral names remain
separated by their actual type images.

The new interface does not transfer the eleven old source suppliers,
reinterpret the existing source Eq decoder, or establish source conversion
or a Fundamental theorem. closure_claim = 0. -/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.GuardedConversionUniverse

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open TaggedSaturatedTower (Kernel KernelRelated)
open GuardedTaggedCode

universe u

theorem converts_laws (k : Nat) :
    RelLaws (fun C D : Code.{u} k => Converts C D) := by
  constructor
  · intro C D h
    exact converts_symm h
  · intro C D E h j
    exact converts_trans h j

/-- Kernel conversion is invariant under conversion of both indices.
This is the guard appropriate to the separate universe below; it does not
identify the old tag-sensitive guard with this one. -/
theorem converts_congr {k : Nat} {a a' b b' : Code.{u} k}
    (ha : Converts a a') (hb : Converts b b') :
    Converts a b ↔ Converts a' b' :=
  ⟨fun h => converts_trans (converts_symm ha) (converts_trans h hb),
    fun h => converts_trans ha (converts_trans h (converts_symm hb))⟩

def conversionUniverseKernel (k : Nat) : Kernel.{u+1} (k+1) :=
  TaggedSaturatedTower.universeKernel k (Code.{u} k)
    (fun C => TaggedSaturatedTower.raiseKernel.{u, u+1} C.kernel)
    (fun C D => Converts C D) (converts_laws k)
    (fun name => Code.legacy (TaggedSaturatedTower.Code.neutral.{u} k name))
    converts_refl

/-- The existing arbitrary-carrier universe witness certifies this
alternative interface. Coherence is the supplied KernelIso itself, raised
to the host universe of the code carrier. -/
def conversionUniverseLegacyCode (k : Nat) :
    TaggedSaturatedTower.Code.{u+1} (k+1) where
  kernel := conversionUniverseKernel.{u} k
  tag := .univ
  witness := TaggedSaturatedTower.Witness.univ k (Code.{u} k)
    (fun C => TaggedSaturatedTower.raiseKernel.{u, u+1} C.kernel)
    (fun C D => Converts C D) (converts_laws k)
    (fun name => Code.legacy (TaggedSaturatedTower.Code.neutral.{u} k name))
    converts_refl
    (fun _ _ h => TaggedSaturatedTower.kernelRelated_raise.{u, u, u+1} h)
    (fun _ => ValueEq.refl _)

def conversionUniverse (k : Nat) : Code.{u+1} (k+1) :=
  Code.legacy (conversionUniverseLegacyCode.{u} k)

abbrev encode (k : Nat) (C : Code.{u} k) :
    (conversionUniverse.{u} k).Element := C

def decode (k : Nat) (x : (conversionUniverse.{u} k).Element) : Code.{u} k := x

theorem decode_encode (k : Nat) (C : Code.{u} k) :
    decode k (encode k C) = C := rfl

theorem encode_decode (k : Nat) (x : (conversionUniverse.{u} k).Element) :
    encode k (decode k x) = x := rfl

theorem type_image (k : Nat) :
    (conversionUniverse.{u} k).view.value = universeValue (some k) := rfl

theorem erasure (k : Nat) (C : Code.{u} k) :
    (conversionUniverse.{u} k).erase (encode k C) = C.view.value := rfl

theorem relation_iff (k : Nat) (C D : Code.{u} k) :
    (conversionUniverse.{u} k).view.relation (encode k C) (encode k D) ↔
      Converts C D := Iff.rfl

theorem member (k : Nat) (C : Code.{u} k) :
    (conversionUniverse.{u} k).view.relation (encode k C) (encode k C) :=
  converts_refl C

theorem elimination (k : Nat) (x : (conversionUniverse.{u} k).Element) :
    SortMember (some k) ((conversionUniverse.{u} k).erase x) ∧
      TypeDefined ((conversionUniverse.{u} k).erase x) :=
  ⟨(decode k x).view.level, (decode k x).view.defined⟩

theorem transport (k : Nat) (x y : (conversionUniverse.{u} k).Element)
    (h : (conversionUniverse.{u} k).view.relation x y) :
    Converts (decode k x) (decode k y) := h

theorem decoded_transport (k : Nat) (x y : (conversionUniverse.{u} k).Element)
    (h : (conversionUniverse.{u} k).view.relation x y) :
    NeutralK.Same (GuardedTaggedCode.Decoded (decode k x).kernel)
      (GuardedTaggedCode.Decoded (decode k y).kernel) :=
  converts_decoded_same (transport k x y h)

theorem relation_congr {k : Nat} {a a' b b' : Code.{u} k}
    (ha : (conversionUniverse.{u} k).view.relation (encode k a) (encode k a'))
    (hb : (conversionUniverse.{u} k).view.relation (encode k b) (encode k b')) :
    (conversionUniverse.{u} k).view.relation (encode k a) (encode k b) ↔
      (conversionUniverse.{u} k).view.relation (encode k a') (encode k b') :=
  converts_congr ha hb

theorem reflection_member (k name : Nat) :
    (conversionUniverse.{u} k).view.relation
      ((conversionUniverse.{u} k).view.point name)
      ((conversionUniverse.{u} k).view.point name) :=
  (conversionUniverse.{u} k).view.point_member name

theorem reflection_erasure (k name : Nat) :
    (conversionUniverse.{u} k).erase ((conversionUniverse.{u} k).view.point name) =
      NativeMemberValues.value (some k) name := rfl

theorem reflection_decode (k name : Nat) :
    decode k ((conversionUniverse.{u} k).view.point name) =
      Code.legacy (TaggedSaturatedTower.Code.neutral.{u} k name) := rfl

/-- Name separation survives removal of the outer tag-equality conjunct:
actual KernelIso still preserves the native type image. -/
theorem reflection_related_iff (k r s : Nat) :
    (conversionUniverse.{u} k).view.relation
      ((conversionUniverse.{u} k).view.point r)
      ((conversionUniverse.{u} k).view.point s) ↔ r = s :=
  neutral_converts_iff k r s

theorem guarded_related_true {k : Nat} {G : Prop} (M F : Code.{u} k)
    (I : GuardedKernel.TypeImage G M.kernel F.kernel) (hG : G) :
    (conversionUniverse.{u} k).view.relation
      (encode k (Code.guarded G M F I)) (encode k M) :=
  guarded_converts_true M F I hG

theorem guarded_related_false {k : Nat} {G : Prop} (M F : Code.{u} k)
    (I : GuardedKernel.TypeImage G M.kernel F.kernel) (hG : ¬ G) :
    (conversionUniverse.{u} k).view.relation
      (encode k (Code.guarded G M F I)) (encode k F) :=
  guarded_converts_false M F I hG

/-- The retained tag-sensitive universe has a different element relation.
Branch conversion cannot be silently promoted to that relation. -/
theorem guarded_not_strong_universe_related {k : Nat}
    (G : Prop) (M F : Code.{u} k)
    (I : GuardedKernel.TypeImage G M.kernel F.kernel)
    (D : TaggedSaturatedTower.Code.{u} k) :
    ¬ (GuardedTaggedCode.universeCode.{u} k).view.relation
      (GuardedTaggedCode.universeEncode k (Code.guarded G M F I))
      (GuardedTaggedCode.universeEncode k (Code.legacy D)) :=
  guarded_not_legacy_related G M F I D

/-- Concrete data for the strong-tag boundary. Both branch kernels are the
same actual native code; the guard is True and all point obligations hold. -/
def boundaryMinor (name : Nat) : Code.{0} 0 :=
  Code.legacy (TaggedSaturatedTower.Code.neutral.{0} 0 name)

def boundaryImage (name : Nat) :
    GuardedKernel.TypeImage True (boundaryMinor name).kernel (boundaryMinor name).kernel :=
  GuardedKernel.TypeImage.ofCommon True _ _ (ValueEq.refl _)

def boundaryGuarded (name : Nat) : Code.{0} 0 :=
  Code.guarded True (boundaryMinor name) (boundaryMinor name) (boundaryImage name)

theorem boundary_member (name : Nat) :
    ∃ x : (boundaryGuarded name).Element,
      (boundaryGuarded name).view.relation x x :=
  ⟨(boundaryGuarded name).view.point 0, (boundaryGuarded name).view.point_member 0⟩

theorem boundary_converts (name : Nat) :
    Converts (boundaryGuarded name) (boundaryMinor name) :=
  guarded_converts_true _ _ (boundaryImage name) True.intro

theorem boundary_not_related (name : Nat) :
    ¬ CodeRelated (boundaryGuarded name) (boundaryMinor name) :=
  guarded_not_legacy_related True _ _ (boundaryImage name)
    (TaggedSaturatedTower.Code.neutral.{0} 0 name)

theorem boundary_not_strong_universe_related (name : Nat) :
    ¬ (GuardedTaggedCode.universeCode.{0} 0).view.relation
      (boundaryGuarded name) (boundaryMinor name) :=
  boundary_not_related name

theorem boundary_conversion_universe_related (name : Nat) :
    (conversionUniverse.{0} 0).view.relation
      (boundaryGuarded name) (boundaryMinor name) :=
  boundary_converts name

theorem boundary_packet (name : Nat) :
    True ∧
    (∃ x : (boundaryGuarded name).Element,
      (boundaryGuarded name).view.relation x x) ∧
    Converts (boundaryGuarded name) (boundaryMinor name) ∧
    ¬ CodeRelated (boundaryGuarded name) (boundaryMinor name) ∧
    ¬ (GuardedTaggedCode.universeCode.{0} 0).view.relation
      (boundaryGuarded name) (boundaryMinor name) ∧
    (conversionUniverse.{0} 0).view.relation
      (boundaryGuarded name) (boundaryMinor name) :=
  ⟨True.intro, boundary_member name, boundary_converts name,
    boundary_not_related name, boundary_not_strong_universe_related name,
    boundary_conversion_universe_related name⟩

end Rcic.Declarative.Ann.LR3.GuardedConversionUniverse

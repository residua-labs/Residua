import rcic.RcicAnnLR3CertifiedUniverseEta
import rcic.RcicAnnLR3UniverseSpineBoundary

/-!
# A certified conversion universe whose points use typed neutral reflection

The carrier remains every extended proposition code, the relation remains
kernel conversion, and the raw type image remains the actual Prop universe.
The designated points are produced by the same complete typed-neutral-spine
reflection as arbitrary neutrals. The existing universe witness certifies
this new pointed universe directly.

The old pointed conversion universe is unchanged. The equality of its
carrier, relation and erasure with the present ones is stated explicitly;
no isomorphism preserving its different designated points is claimed.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.ReflectiveConversionUniverse

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open TaggedSaturatedTower (Kernel)
open GuardedTaggedCode

universe u

def zeroKernel : Kernel.{u+1} 1 :=
  TaggedSaturatedTower.universeKernel 0 (Code.{u} 0)
    (fun C => TaggedSaturatedTower.raiseKernel.{u, u+1} C.kernel)
    (fun C D => Converts C D) (GuardedConversionUniverse.converts_laws 0)
    (fun name => CertifiedUniverseEta.reflectCode (NeutralPER.neutralAtom name) (.atom name))
    converts_refl

/-- The existing certified universe producer is used, including its actual
native type-image law for each new designated point. -/
def zeroLegacyCode : TaggedSaturatedTower.Code.{u+1} 1 where
  kernel := zeroKernel.{u}
  tag := .univ
  witness := TaggedSaturatedTower.Witness.univ 0 (Code.{u} 0)
    (fun C => TaggedSaturatedTower.raiseKernel.{u, u+1} C.kernel)
    (fun C D => Converts C D) (GuardedConversionUniverse.converts_laws 0)
    (fun name => CertifiedUniverseEta.reflectCode (NeutralPER.neutralAtom name) (.atom name))
    converts_refl
    (fun _ _ h => TaggedSaturatedTower.kernelRelated_raise.{u, u, u+1} h)
    (fun name => UniverseSpineBoundary.tagged_atom_native (some 0) name)

def zero : Code.{u+1} 1 := Code.legacy zeroLegacyCode.{u}

abbrev encode (C : Code.{u} 0) : zero.{u}.Element := C

def decode (x : zero.{u}.Element) : Code.{u} 0 := x

theorem decode_encode (C : Code.{u} 0) : decode (encode C) = C := rfl

theorem encode_decode (x : zero.{u}.Element) : encode (decode x) = x := rfl

theorem member (C : Code.{u} 0) : zero.{u}.view.relation (encode C) (encode C) :=
  converts_refl C

theorem relation_iff (C D : Code.{u} 0) :
    zero.{u}.view.relation (encode C) (encode D) ↔ Converts C D := Iff.rfl

theorem erasure (C : Code.{u} 0) : zero.{u}.erase (encode C) = C.view.value := rfl

theorem type_image : zero.{u}.view.value = universeValue (some 0) := rfl

def reflect (n : Value) (hn : CandidatePi.Neutral n) : zero.{u}.Element :=
  CertifiedUniverseEta.reflectCode n hn

theorem reflect_member (n : Value) (hn : CandidatePi.Neutral n) :
    zero.{u}.view.relation (reflect n hn) (reflect n hn) :=
  converts_refl _

theorem reflect_reify (n : Value) (hn : CandidatePi.Neutral n) :
    zero.{u}.erase (reflect n hn) = InductiveCodes.taggedValue (some 0) n := rfl

theorem reflect_relation_iff (n m : Value)
    (hn : CandidatePi.Neutral n) (hm : CandidatePi.Neutral m) :
    zero.{u}.view.relation (reflect n hn) (reflect m hm) ↔ ValueEq n m :=
  CertifiedUniverseEta.reflect_converts_iff n m hn hm

/-- Named reflection is exactly the arbitrary-neutral construction at atoms. -/
theorem point_reflect (name : Nat) :
    zero.{u}.view.point name = reflect (NeutralPER.neutralAtom name) (.atom name) := rfl

theorem point_reify (name : Nat) :
    ValueEq (zero.{u}.erase (zero.{u}.view.point name))
      (NativeMemberValues.value (some 0) name) :=
  UniverseSpineBoundary.tagged_atom_native (some 0) name

/-- A data-producing instance of the exact typed-spine law that fails for
the inhabited atom-only universe in UniverseSpineBoundary. -/
def spineReflection : UniverseSpineBoundary.SpineReflection zero.{u} where
  reflect := reflect
  member := reflect_member
  image := fun _ _ => ValueEq.refl _

theorem existing_relation (C D : Code.{u} 0) :
    zero.{u}.view.relation (encode C) (encode D) ↔
      (GuardedConversionUniverse.conversionUniverse.{u} 0).view.relation C D := Iff.rfl

theorem existing_erasure (C : Code.{u} 0) :
    zero.{u}.erase (encode C) =
      (GuardedConversionUniverse.conversionUniverse.{u} 0).erase C := rfl

theorem paired_reflection (n m : Value)
    (hn : CandidatePi.Neutral n) (hm : CandidatePi.Neutral m) (h : ValueEq n m) :
    zero.{u}.view.relation (reflect n hn) (reflect m hm) :=
  (reflect_relation_iff n m hn hm).mpr h

end Rcic.Declarative.Ann.LR3.ReflectiveConversionUniverse

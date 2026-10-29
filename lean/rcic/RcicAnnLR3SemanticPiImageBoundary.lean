import rcic.RcicAnnLR3SemanticDomainBoundary

/-!
# A semantic dependent section without a raw application realizer

The domain is an actual certified Code 1 with retained semantic data.
The family consists of actual certified Code 1 fibres, with explicit
KernelIso transport. Its designated dependent point section is total,
self-related and coherent. Two legal inputs have the same erasure but
force different raw result images. Consequently the section has no raw
Value satisfying the old ElementAction application-erasure equation.

This is a boundary for arbitrary certified semantic families, not for
actual source-admitted functions. A semantic evaluator can retain the
section; its raw application bridge requires a separately established
realizability property or a distinction between the term projection and
type-directed reification.
-/
set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.SemanticPiImageBoundary

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open SemanticDomainBoundary

/-- This family uses a universe-valued carrier in one fibre and a
neutral carrier in the other. Both are certified positive codes. -/
def mixedFibre (x : code.Element) : GuardedTaggedCode.Code.{0} 1 :=
  if x.2 0 then .legacy (TaggedSaturatedTower.Code.neutral 1 0) else code

def mixedTransport (x y : code.Element) (h : code.view.relation x y) :
    TaggedSaturatedTower.KernelIso (mixedFibre x).kernel (mixedFibre y).kernel := by
  cases h
  exact TaggedSaturatedTower.KernelIso.refl _

def pointSection (x : code.Element) : (mixedFibre x).Element :=
  (mixedFibre x).view.point 0

theorem pointSection_member (x : code.Element) :
    (mixedFibre x).view.relation (pointSection x) (pointSection x) :=
  (mixedFibre x).view.point_member 0

theorem pointSection_transport (x y : code.Element)
    (h : code.view.relation x y) :
    (mixedTransport x y h).forward (pointSection x) = pointSection y :=
  (mixedTransport x y h).point_image 0

theorem native_type_not_atom (k : Option Nat) (name atom : Nat) :
    ¬ ValueEq (NativeMemberValues.value k name) (NeutralPER.neutralAtom atom) := by
  intro h
  have hs := sortMember_congr h (NativeMemberValues.value_level k name)
  have ht := hs (.spine atom []) (NeutralPER.neutralAtom_observed atom)
  cases ht

/-- The coherent semantic section exists, but its application cannot be
realized by one raw function on erased arguments. This scopes the old
ElementAction.erased requirement when semantic arguments retain data
that erasure forgets; it does not refute source-generated families. -/
theorem no_raw_point_section :
    ¬ ∃ value : Value, ∀ x : code.Element,
      ValueEq (NeutralPi.applyValue value (code.erase x))
        ((mixedFibre x).erase (pointSection x)) := by
  rintro ⟨value, h⟩
  have hl : ValueEq (NeutralPi.applyValue value (code.erase low))
      (NativeMemberValues.value (some 0) 0) := h low
  have hh : ValueEq (NeutralPi.applyValue value (code.erase high))
      (NeutralPER.neutralAtom 0) := h high
  exact native_type_not_atom (some 0) 0 0 (hl.symm.trans hh)

theorem inhabited_semantic_section_boundary :
    code.view.relation low low ∧ code.view.relation high high ∧
    ValueEq (code.erase low) (code.erase high) ∧
    (∀ x, (mixedFibre x).view.relation (pointSection x) (pointSection x)) ∧
    (∀ x y (h : code.view.relation x y),
      (mixedTransport x y h).forward (pointSection x) = pointSection y) ∧
    ¬ ∃ value : Value, ∀ x : code.Element,
      ValueEq (NeutralPi.applyValue value (code.erase x))
        ((mixedFibre x).erase (pointSection x)) :=
  ⟨low_member, high_member, low_high_same_erasure,
    pointSection_member, pointSection_transport, no_raw_point_section⟩


end Rcic.Declarative.Ann.LR3.SemanticPiImageBoundary

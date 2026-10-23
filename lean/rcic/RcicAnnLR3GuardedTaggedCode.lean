import rcic.RcicAnnLR3GuardedKernelTransport
import rcic.RcicAnnLR3TaggedKClosure

/-!
# An additive tagged carrier for suspended codes

Legacy producers and their strong relation are retained verbatim. A fresh
guarded producer records its two certified branches and actual type-image
data. Conversion has a separate KernelIso-level arm; it does not manufacture
tag equality. The new universe really contains the extended carrier.

The raw decoder is the least PER of retained element images, with exact
membership and conversion transport. These constructions do not transfer
the eleven legacy source suppliers to a new model. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.GuardedTaggedCode

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily StratifiedCandidates
open TaggedSaturatedTower (Kernel KernelIso KernelRelated)

universe u v

inductive Tag where
  | legacy : TaggedSaturatedTower.ConstructorTag → Tag
  | guarded : Tag
  deriving DecidableEq

/-- There is no constructor from an arbitrary pointed PER. -/
inductive Producer : Tag → {k : Nat} → Kernel.{u} k → Type (u+1) where
  | legacy {k : Nat} (C : TaggedSaturatedTower.Code.{u} k) :
      Producer (.legacy C.tag) C.kernel
  | guarded {k : Nat} {tm tf : Tag} (G : Prop)
      (M F : Kernel.{u} k) (hm : Producer tm M) (hf : Producer tf F)
      (I : GuardedKernel.TypeImage G M F) :
      Producer .guarded (GuardedKernel.kernel G M F I)

structure Code (k : Nat) where
  kernel : Kernel.{u} k
  tag : Tag
  producer : Producer tag kernel

abbrev Code.Element {k : Nat} (C : Code.{u} k) := C.kernel.Element
def Code.erase {k : Nat} (C : Code.{u} k) : C.Element → Value := C.kernel.erase
def Code.view {k : Nat} (C : Code.{u} k) : PointedPER k C.Element := C.kernel.per

def Code.legacy {k : Nat} (C : TaggedSaturatedTower.Code.{u} k) : Code.{u} k :=
  ⟨C.kernel, .legacy C.tag, .legacy C⟩

def Code.guarded {k : Nat} (G : Prop) (M F : Code.{u} k)
    (I : GuardedKernel.TypeImage G M.kernel F.kernel) : Code.{u} k :=
  ⟨GuardedKernel.kernel G M.kernel F.kernel I, .guarded,
    .guarded G M.kernel F.kernel M.producer F.producer I⟩

def CodeRelated {k : Nat} (C D : Code.{u} k) : Prop :=
  C.tag = D.tag ∧ KernelRelated C.kernel D.kernel

def Converts {k : Nat} (C : Code.{u} k) (D : Code.{v} k) : Prop :=
  KernelRelated C.kernel D.kernel

theorem related_refl {k : Nat} (C : Code.{u} k) : CodeRelated C C :=
  ⟨rfl, TaggedSaturatedTower.kernelRelated_refl C.kernel⟩

theorem related_symm {k : Nat} {C D : Code.{u} k}
    (h : CodeRelated C D) : CodeRelated D C :=
  ⟨h.1.symm, TaggedSaturatedTower.kernelRelated_symm h.2⟩

theorem related_trans {k : Nat} {C D E : Code.{u} k}
    (h : CodeRelated C D) (j : CodeRelated D E) : CodeRelated C E :=
  ⟨h.1.trans j.1, TaggedSaturatedTower.kernelRelated_trans h.2 j.2⟩

theorem related_laws (k : Nat) : RelLaws (@CodeRelated.{u} k) :=
  ⟨related_symm, related_trans⟩

theorem legacy_related_iff {k : Nat} (C D : TaggedSaturatedTower.Code.{u} k) :
    CodeRelated (Code.legacy C) (Code.legacy D) ↔
      TaggedSaturatedTower.CodeRelated C D := by
  constructor
  · intro h
    exact ⟨Tag.legacy.inj h.1, h.2⟩
  · intro h
    exact ⟨congrArg Tag.legacy h.1, h.2⟩

theorem related_converts {k : Nat} {C D : Code.{u} k}
    (h : CodeRelated C D) : Converts C D := h.2

theorem converts_refl {k : Nat} (C : Code.{u} k) : Converts C C :=
  TaggedSaturatedTower.kernelRelated_refl C.kernel

theorem converts_symm {k : Nat} {C : Code.{u} k} {D : Code.{v} k}
    (h : Converts C D) : Converts D C := TaggedSaturatedTower.kernelRelated_symm h

theorem converts_trans {k : Nat} {C D E : Code.{u} k}
    (h : Converts C D) (j : Converts D E) : Converts C E :=
  TaggedSaturatedTower.kernelRelated_trans h j

theorem converts_type_image {k : Nat} {C : Code.{u} k} {D : Code.{v} k}
    (h : Converts C D) : ValueEq C.view.value D.view.value := by
  obtain ⟨e⟩ := h
  exact e.type_image

def guardedIsoTrue {k : Nat} {G : Prop} (M F : Code.{u} k)
    (I : GuardedKernel.TypeImage G M.kernel F.kernel) (hG : G) :
    KernelIso (Code.guarded G M F I).kernel M.kernel := GuardedKernel.isoTrue I hG

def guardedIsoFalse {k : Nat} {G : Prop} (M F : Code.{u} k)
    (I : GuardedKernel.TypeImage G M.kernel F.kernel) (hG : ¬ G) :
    KernelIso (Code.guarded G M F I).kernel F.kernel := GuardedKernel.isoFalse I hG

/-- The guarded conversion arm transports actual heterogeneous elements. -/
theorem guarded_converts_true {k : Nat} {G : Prop} (M F : Code.{u} k)
    (I : GuardedKernel.TypeImage G M.kernel F.kernel) (hG : G) :
    Converts (Code.guarded G M F I) M := ⟨guardedIsoTrue M F I hG⟩

theorem guarded_converts_false {k : Nat} {G : Prop} (M F : Code.{u} k)
    (I : GuardedKernel.TypeImage G M.kernel F.kernel) (hG : ¬ G) :
    Converts (Code.guarded G M F I) F := ⟨guardedIsoFalse M F I hG⟩

theorem guarded_not_legacy_related {k : Nat} (G : Prop) (M F : Code.{u} k)
    (I : GuardedKernel.TypeImage G M.kernel F.kernel)
    (D : TaggedSaturatedTower.Code.{u} k) :
    ¬ CodeRelated (Code.guarded G M F I) (Code.legacy D) := by
  intro h
  cases h.1

theorem neutral_converts_iff (k r s : Nat) :
    Converts (Code.legacy (TaggedSaturatedTower.Code.neutral.{u} k r))
      (Code.legacy (TaggedSaturatedTower.Code.neutral.{u} k s)) ↔ r = s := by
  constructor
  · rintro ⟨e⟩
    exact TaggedSaturatedTower.native_value_name_injective (some k) r s e.type_image
  · intro h
    cases h
    exact converts_refl _

def El {k : Nat} (K : Kernel.{u} k) (x y : Value) : Prop :=
  ∃ a b : K.Element, K.per.relation a b ∧
    ValueEq (K.erase a) x ∧ ValueEq (K.erase b) y

def Good {k : Nat} (K : Kernel.{u} k) (x : Value) : Prop :=
  ∃ a : K.Element, K.per.relation a a ∧ ValueEq (K.erase a) x

def Decoded {k : Nat} (K : Kernel.{u} k) (x y : Value) : Prop :=
  NeutralK.Path (El K) x y

theorem el_good {k : Nat} {K : Kernel.{u} k} {x y : Value}
    (h : El K x y) : Good K x ∧ Good K y := by
  obtain ⟨a, b, hab, ha, hb⟩ := h
  exact ⟨⟨a, K.per.lawful.trans hab (K.per.lawful.symm hab), ha⟩,
    ⟨b, K.per.lawful.trans (K.per.lawful.symm hab) hab, hb⟩⟩

theorem decoded_good {k : Nat} {K : Kernel.{u} k} {x y : Value}
    (h : Decoded K x y) : Good K x ∧ Good K y := by
  induction h with
  | forward h => exact el_good h
  | backward h => exact ⟨(el_good h).2, (el_good h).1⟩
  | append _ _ ih jh => exact ⟨ih.1, jh.2⟩

theorem decoded_member_iff {k : Nat} (K : Kernel.{u} k) (x : Value) :
    Decoded K x x ↔ Good K x := by
  constructor
  · exact fun h => (decoded_good h).1
  · rintro ⟨a, ha, he⟩
    exact .forward ⟨a, a, ha, he, he⟩

theorem decoded_laws {k : Nat} (K : Kernel.{u} k) :
    TypedPER.Laws (Decoded K) := NeutralK.path_typed_laws (El K)

theorem el_transport {k : Nat} {A : Kernel.{u} k} {B : Kernel.{v} k}
    (e : KernelIso A B) {x y : Value} (h : El A x y) : El B x y := by
  obtain ⟨a, b, hab, ha, hb⟩ := h
  exact ⟨e.forward a, e.forward b, (e.relation a b).mp hab,
    (e.element_image a).trans ha, (e.element_image b).trans hb⟩

theorem decoded_same {k : Nat} {A : Kernel.{u} k} {B : Kernel.{v} k}
    (e : KernelIso A B) : NeutralK.Same (Decoded A) (Decoded B) :=
  NeutralK.path_same (fun _ _ => ⟨el_transport e, el_transport e.symm⟩)

theorem converts_decoded_same {k : Nat} {C : Code.{u} k} {D : Code.{v} k}
    (h : Converts C D) : NeutralK.Same (Decoded C.kernel) (Decoded D.kernel) := by
  obtain ⟨e⟩ := h
  exact decoded_same e

theorem legacy_decoded_iff {k : Nat} (C : TaggedSaturatedTower.Code.{u} k)
    (x y : Value) :
    Decoded (Code.legacy C).kernel x y ↔ TaggedKClosure.Decoded C x y := Iff.rfl

theorem guarded_decoded_true {k : Nat} {G : Prop} (M F : Code.{u} k)
    (I : GuardedKernel.TypeImage G M.kernel F.kernel) (hG : G) :
    NeutralK.Same (Decoded (Code.guarded G M F I).kernel) (Decoded M.kernel) :=
  decoded_same (guardedIsoTrue M F I hG)

theorem guarded_decoded_false {k : Nat} {G : Prop} (M F : Code.{u} k)
    (I : GuardedKernel.TypeImage G M.kernel F.kernel) (hG : ¬ G) :
    NeutralK.Same (Decoded (Code.guarded G M F I).kernel) (Decoded F.kernel) :=
  decoded_same (guardedIsoFalse M F I hG)

theorem guarded_exact_reflection {k : Nat} (G : Prop) (M F : Code.{u} k)
    (I : GuardedKernel.TypeImage G M.kernel F.kernel)
    (rM : GuardedKernel.Reflector M.kernel) (rF : GuardedKernel.Reflector F.kernel)
    (x : Value) (hx : CandidatePi.Neutral x) :
    Decoded (Code.guarded G M F I).kernel x x :=
  (decoded_member_iff _ _).mpr (GuardedKernel.reflected_member_exists I rM rF x hx)

def universeKernel (k : Nat) : Kernel.{u+1} (k+1) :=
  TaggedSaturatedTower.universeKernel k (Code.{u} k)
    (fun C => TaggedSaturatedTower.raiseKernel.{u, u+1} C.kernel)
    (@CodeRelated.{u} k) (related_laws k)
    (fun name => Code.legacy (TaggedSaturatedTower.Code.neutral.{u} k name)) related_refl

/-- The existing universe producer accepts the new carrier and its proven
coherence. This does not identify it with the smaller old universe. -/
def universeLegacyCode (k : Nat) : TaggedSaturatedTower.Code.{u+1} (k+1) where
  kernel := universeKernel.{u} k
  tag := .univ
  witness := TaggedSaturatedTower.Witness.univ k (Code.{u} k)
    (fun C => TaggedSaturatedTower.raiseKernel.{u, u+1} C.kernel)
    (@CodeRelated.{u} k) (related_laws k)
    (fun name => Code.legacy (TaggedSaturatedTower.Code.neutral.{u} k name)) related_refl
    (fun _ _ h => TaggedSaturatedTower.kernelRelated_raise.{u, u, u+1} h.2)
    (fun _ => ValueEq.refl _)

def universeCode (k : Nat) : Code.{u+1} (k+1) := Code.legacy (universeLegacyCode.{u} k)

abbrev universeEncode (k : Nat) (C : Code.{u} k) : (universeCode.{u} k).Element := C
def universeDecode (k : Nat) (x : (universeCode.{u} k).Element) : Code.{u} k := x

theorem universe_decode_encode (k : Nat) (C : Code.{u} k) :
    universeDecode k (universeEncode k C) = C := rfl

theorem universe_encode_decode (k : Nat) (x : (universeCode.{u} k).Element) :
    universeEncode k (universeDecode k x) = x := rfl

theorem universe_type_image (k : Nat) :
    (universeCode.{u} k).view.value = universeValue (some k) := rfl

theorem universe_erasure (k : Nat) (C : Code.{u} k) :
    (universeCode.{u} k).erase (universeEncode k C) = C.view.value := rfl

theorem universe_member (k : Nat) (C : Code.{u} k) :
    (universeCode.{u} k).view.relation (universeEncode k C) (universeEncode k C) :=
  related_refl C

theorem universe_elimination (k : Nat) (x : (universeCode.{u} k).Element) :
    SortMember (some k) ((universeCode.{u} k).erase x) ∧
      TypeDefined ((universeCode.{u} k).erase x) :=
  ⟨(universeDecode k x).view.level, (universeDecode k x).view.defined⟩

theorem universe_transport (k : Nat) (x y : (universeCode.{u} k).Element)
    (h : (universeCode.{u} k).view.relation x y) :
    CodeRelated (universeDecode k x) (universeDecode k y) := h

theorem universe_reflection_erasure (k name : Nat) :
    (universeCode.{u} k).erase ((universeCode.{u} k).view.point name) =
      NativeMemberValues.value (some k) name := rfl

theorem guarded_universe_member {k : Nat} (G : Prop) (M F : Code.{u} k)
    (I : GuardedKernel.TypeImage G M.kernel F.kernel) :
    (universeCode.{u} k).view.relation (Code.guarded G M F I) (Code.guarded G M F I) :=
  universe_member k (Code.guarded G M F I)

end Rcic.Declarative.Ann.LR3.GuardedTaggedCode

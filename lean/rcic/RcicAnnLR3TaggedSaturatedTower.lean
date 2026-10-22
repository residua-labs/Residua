import rcic.RcicAnnLR3TaggedCarrier

/-!
# Canonical universes of certified interpreted codes

The payload of universeCode.{u} k is exactly every Code.{u} k.
The relation retains the constructor tag and an actual carrier, PER and
erasure isomorphism. No raw-erasure quotient chooses an interpretation.

The object index k : Nat covers defined levels. Code.{u} k lives in
Type (u+1), so the universe constructor explicitly raises its host universe.
No fixed-host Nat-indexed closure or Option.none model is claimed.
Source conversion must still supply the corresponding carrier isomorphisms.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TaggedSaturatedTower
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily StratifiedCandidates
universe u v

def CodeRelated {k : Nat} (C D : Code.{u} k) : Prop :=
  C.tag = D.tag ∧ KernelRelated C.kernel D.kernel

theorem codeRelated_iff {k : Nat} (C D : Code.{u} k) :
    CodeRelated C D ↔ C.tag = D.tag ∧ Nonempty (KernelIso C.kernel D.kernel) := Iff.rfl

theorem codeRelated_refl {k : Nat} (C : Code.{u} k) : CodeRelated C C :=
  ⟨rfl, kernelRelated_refl C.kernel⟩

theorem codeRelated_laws (k : Nat) : RelLaws (@CodeRelated.{u} k) where
  symm := fun h => ⟨h.1.symm, kernelRelated_symm h.2⟩
  trans := fun h h' => ⟨h.1.trans h'.1, kernelRelated_trans h.2 h'.2⟩

theorem codeRelated_tag {k : Nat} {C D : Code.{u} k}
    (h : CodeRelated C D) : C.tag = D.tag := h.1

theorem codeRelated_type_image {k : Nat} {C D : Code.{u} k}
    (h : CodeRelated C D) : ValueEq C.view.value D.view.value := by
  rcases h.2 with ⟨e⟩
  exact e.type_image

theorem codeRelated_faithfulness {k : Nat} {C D : Code.{u} k}
    (h : CodeRelated C D) :
    ∃ (f : C.Element → D.Element) (g : D.Element → C.Element),
      (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y) ∧
      (∀ x, ValueEq (D.erase (f x)) (C.erase x)) ∧
      (∀ x y, C.view.relation x y ↔ D.view.relation (f x) (f y)) := by
  rcases h.2 with ⟨e⟩
  exact ⟨e.forward, e.backward, e.left_inv, e.right_inv, e.element_image, e.relation⟩

def canonicalUniverseKernel (k : Nat) : Kernel.{u+1} (k+1) :=
  universeKernel k (Code.{u} k)
    (fun C => raiseKernel.{u, u+1} C.kernel)
    (@CodeRelated.{u} k) (codeRelated_laws k)
    (fun name => Code.neutral.{u} k name) codeRelated_refl

def universeCode (k : Nat) : Code.{u+1} (k+1) where
  kernel := canonicalUniverseKernel.{u} k
  tag := .univ
  witness := Witness.univ k (Code.{u} k)
    (fun C => raiseKernel.{u, u+1} C.kernel)
    (@CodeRelated.{u} k) (codeRelated_laws k)
    (fun name => Code.neutral.{u} k name) codeRelated_refl
    (fun _ _ h => kernelRelated_raise.{u, u, u+1} h.2)
    (fun _ => ValueEq.refl _)

theorem universe_tag (k : Nat) : (universeCode.{u} k).tag = .univ := rfl

theorem universe_type_image (k : Nat) :
    (universeCode.{u} k).view.value = universeValue (some k) := rfl

abbrev universeEncode (k : Nat) (C : Code.{u} k) :
    (universeCode.{u} k).Element := C

def universeDecode (k : Nat) (x : (universeCode.{u} k).Element) : Code.{u} k := x

theorem universe_decode_encode (k : Nat) (C : Code.{u} k) :
    universeDecode k (universeEncode k C) = C := rfl

theorem universe_encode_decode (k : Nat) (x : (universeCode.{u} k).Element) :
    universeEncode k (universeDecode k x) = x := rfl

theorem universe_erasure (k : Nat) (C : Code.{u} k) :
    (universeCode.{u} k).erase (universeEncode k C) = C.view.value := rfl

theorem universe_relation_iff (k : Nat) (x y : (universeCode.{u} k).Element) :
    (universeCode.{u} k).view.relation x y ↔
      CodeRelated (universeDecode k x) (universeDecode k y) := Iff.rfl

/-- Universe-tag saturation takes an actual typed code, with no target
membership premise or selection from a raw-value existential. -/
theorem universe_cr3 (k : Nat) (C : Code.{u} k) :
    (universeCode.{u} k).view.relation (universeEncode k C) (universeEncode k C) :=
  codeRelated_refl C

theorem universe_member (k : Nat) (C : Code.{u} k) :
    (universeCode.{u} k).view.relation (universeEncode k C) (universeEncode k C) :=
  universe_cr3 k C

theorem universe_elimination (k : Nat) (x : (universeCode.{u} k).Element) :
    SortMember (some k) ((universeCode.{u} k).erase x) ∧
    TypeDefined ((universeCode.{u} k).erase x) :=
  ⟨(universeDecode k x).view.level, (universeDecode k x).view.defined⟩

theorem universe_transport (k : Nat) (x y : (universeCode.{u} k).Element)
    (h : (universeCode.{u} k).view.relation x y) :
    CodeRelated (universeDecode k x) (universeDecode k y) := h

theorem universe_transport_image (k : Nat) (x y : (universeCode.{u} k).Element)
    (h : (universeCode.{u} k).view.relation x y) :
    ValueEq ((universeCode.{u} k).erase x) ((universeCode.{u} k).erase y) :=
  codeRelated_type_image h

theorem universe_reflection (k name : Nat) :
    (universeCode.{u} k).view.point name = Code.neutral.{u} k name := rfl

theorem universe_reflection_member (k name : Nat) :
    (universeCode.{u} k).view.relation
      ((universeCode.{u} k).view.point name) ((universeCode.{u} k).view.point name) :=
  codeRelated_refl (Code.neutral.{u} k name)

theorem universe_reflection_erasure (k name : Nat) :
    (universeCode.{u} k).erase ((universeCode.{u} k).view.point name) =
      NativeMemberValues.value (some k) name := rfl

abbrev UniverseMember (k : Nat) :=
  {x : (universeCode.{u} k).Element // (universeCode.{u} k).view.relation x x}

def encodeMember (k : Nat) (C : Code.{u} k) : UniverseMember.{u} k :=
  ⟨universeEncode k C, universe_member k C⟩

def decodeMember (k : Nat) (x : UniverseMember.{u} k) : Code.{u} k :=
  universeDecode k x.val

theorem decodeMember_encode (k : Nat) (C : Code.{u} k) :
    decodeMember k (encodeMember k C) = C := rfl

theorem encodeMember_decode (k : Nat) (x : UniverseMember.{u} k) :
    encodeMember k (decodeMember k x) = x := by
  apply Subtype.ext
  rfl

theorem universe_successor_member (k : Nat) :
    (universeCode.{u+1} (k+1)).view.relation
      (universeCode.{u} k) (universeCode.{u} k) :=
  codeRelated_refl (universeCode.{u} k)

theorem universe_successor_decode (k : Nat) :
    universeDecode (k+1) (universeCode.{u} k) = universeCode.{u} k := rfl

theorem code2_member (C : Code.{u} 2) :
    (universeCode.{u} 2).view.relation (universeEncode 2 C) (universeEncode 2 C) :=
  universe_member 2 C

theorem code2_decode (C : Code.{u} 2) :
    universeDecode 2 (universeEncode 2 C) = C := rfl

theorem codeRelated_reflection_image {k : Nat} {C D : Code.{u} k}
    (h : CodeRelated C D) (name : Nat) :
    ValueEq (C.erase (C.view.point name)) (D.erase (D.view.point name)) :=
  kernelRelated_point_image h.2 name

theorem witness_univ_reflection_image {k : Nat} {K : Kernel.{u} (k+1)}
    (w : Witness .univ K) (name : Nat) :
    ValueEq (K.erase (K.per.point name)) (NativeMemberValues.value (some k) name) := by
  cases w with
  | univ j κ decode R laws q all_members coherent reflection_image =>
      exact reflection_image name

theorem code_univ_reflection_image {k : Nat} (C : Code.{u} (k+1))
    (h : C.tag = .univ) (name : Nat) :
    ValueEq (C.erase (C.view.point name)) (NativeMemberValues.value (some k) name) := by
  have w : Witness .univ C.kernel := h ▸ C.witness
  exact witness_univ_reflection_image w name

theorem code_univ_reflection_coherent {k : Nat}
    (C : Code.{u} (k+1)) (D : Code.{v} (k+1))
    (hC : C.tag = .univ) (hD : D.tag = .univ) (name : Nat) :
    ValueEq (C.erase (C.view.point name)) (D.erase (D.view.point name)) :=
  (code_univ_reflection_image C hC name).trans (code_univ_reflection_image D hD name).symm


/-- A compact observation that retains the native neutral type's name. -/
def nativeNameProbe (name : Nat) : CptI :=
  .spine 10 [.bot, .spine name []]

theorem nativeNameProbe_member (k : Option Nat) (name : Nat) :
    NativeMemberValues.value k name (nativeNameProbe name) := by
  exact Rcic.Declarative.NativeValleys.FamModelAudit.approxI_famApp 10 []
    (.cons (.bot _ _) (.cons (.const _ name []) .nil))

theorem nativeNameProbe_inv (k : Option Nat) (r s : Nat)
    (hc : NativeMemberValues.value k s (nativeNameProbe r)) : r = s := by
  have h := Rcic.Declarative.NativeValleys.FamModelAudit.approxI_foldApps_const_inv
    (r := 10) (ls := []) (xs := [levelTerm k, .const s []]) hc
  rcases h with hbot | ⟨us, he, hs⟩
  · cases hbot
  · change (.spine 10 [.bot, .spine r []] : CptI) = .spine 10 us at he
    cases he
    cases hs with
    | cons ha hs =>
      cases hs with
      | cons hb hs =>
        have hp := approxI_const_inv hb
        rcases hp with hbot | heq
        · cases hbot
        · cases heq
          rfl

theorem native_value_name_injective (k : Option Nat) (r s : Nat)
    (h : ValueEq (NativeMemberValues.value k r) (NativeMemberValues.value k s)) :
    r = s := by
  apply nativeNameProbe_inv k r s
  exact (h (nativeNameProbe r)).mp (nativeNameProbe_member k r)

theorem native_value_name_iff (k : Option Nat) (r s : Nat) :
    ValueEq (NativeMemberValues.value k r) (NativeMemberValues.value k s) ↔ r = s := by
  constructor
  · exact native_value_name_injective k r s
  · intro h
    cases h
    exact ValueEq.refl _

/-- Name separation follows from the raw type image, not merely constructor tags.
This is the free neutral-code producer; a general conversion/gluing layer is
still a separate obligation. -/
theorem neutral_codeRelated_iff (k r s : Nat) :
    CodeRelated (Code.neutral.{u} k r) (Code.neutral.{u} k s) ↔ r = s := by
  constructor
  · intro h
    exact native_value_name_injective (some k) r s (codeRelated_type_image h)
  · intro h
    cases h
    exact codeRelated_refl _

theorem neutral_not_related (k r s : Nat) (hrs : r ≠ s) :
    ¬ CodeRelated (Code.neutral.{u} k r) (Code.neutral.{u} k s) := by
  intro h
  exact hrs ((neutral_codeRelated_iff k r s).mp h)

/-- Canonical universe membership retains distinct neutral type names. -/
theorem universe_neutral_relation_iff (k r s : Nat) :
    (universeCode.{u} k).view.relation
      (universeEncode k (Code.neutral.{u} k r))
      (universeEncode k (Code.neutral.{u} k s)) ↔ r = s :=
  neutral_codeRelated_iff k r s

theorem universe_neutral_not_related (k r s : Nat) (hrs : r ≠ s) :
    ¬ (universeCode.{u} k).view.relation
      (universeEncode k (Code.neutral.{u} k r))
      (universeEncode k (Code.neutral.{u} k s)) :=
  neutral_not_related k r s hrs

/-- A tag constraint on this relation, not an inversion theorem for source conversion. -/
theorem neutral_universe_not_related (k r : Nat) :
    ¬ CodeRelated (Code.neutral.{u+1} (k+1) r) (universeCode.{u} k) := by
  intro h
  have ht := h.1
  change ConstructorTag.neutral = ConstructorTag.univ at ht
  cases ht

end Rcic.Declarative.Ann.LR3.TaggedSaturatedTower

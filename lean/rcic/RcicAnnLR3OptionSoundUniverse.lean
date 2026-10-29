import rcic.RcicAnnLR3NoneSortSupply
import rcic.RcicAnnLR3GuardedConversionUniverse
import rcic.RcicAnnLR3NeutralControls
import rcic.RcicAnnLR3TaggedKCoherenceBoundary

/-!
# One Option-indexed code universe: finite conversion codes and the none level

`OCode k` is indexed by the evaluated level `k : Option Nat`. Its finite
codes are exactly the existing constructor-certified `GuardedTaggedCode`
codes, unchanged. Its `none` codes are the none universe itself and one
chaotic code for every ordinary level-none type image, i.e. every defined
`SortMember none` value other than the none universe's own image. There is
no constructor from an arbitrary pointed PER at any level.

Every code has an `OptionLevelKernel.Kernel`; conversion of codes is the
existence of an `OptionLevelKernel.Iso`. The universe at an Option level is
again a code one level up: at `some k` it is the existing conversion
universe, at `none` the self-containing none universe. Its decoder is total,
its element relation is exactly conversion of the decoded codes, ordinary
none fibres are chaotic, and at `none` conversion is code identity. The
universe images separate exactly as `evaluated_sort_eq_iff_eqN` requires.

The finite branch of the all-Option sort algebra is replaced by the decoded
conversion universes. Its none branch extends the named none algebra to all
ordinary none images. The original `Ty_sort` is supplied for the attached
`EnvironmentEval` semantics with its original all-Option quantification;
no `FiniteOn` premise is added. No `UniverseTransport` is claimed for this
algebra: a raw image does not determine a retained element relation. This is
not a whole-language model, and the source-realized interface built on
these codes is in `RcicAnnLR3OptionSoundInterface`. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.OptionSoundUniverse

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements

universe u v

/-! ## Ordinary none type images -/

/-- A defined level-none type image other than the none universe itself. -/
structure NoneOrdinary where
  value : Value
  level : SortMember none value
  defined : TypeDefined value
  not_universe : ¬ ValueEq value (universeValue none)

def NoneOrdinary.named (name : Nat) : NoneOrdinary where
  value := NativeMemberValues.value none name
  level := NativeMemberValues.value_level none name
  defined := NativeMemberValues.value_defined none name
  not_universe := fun h => NoneSelfUniverse.self_not_named name h.symm

theorem NoneOrdinary.eq_of_valueEq {a b : NoneOrdinary}
    (h : ValueEq a.value b.value) : a = b := by
  have hv := NeutralCodes.valueEq_eq h
  cases a
  cases b
  cases hv
  rfl

/-- `none` is the none universe, `some V` an ordinary none type. -/
def noneImage : Option NoneOrdinary → Value
  | none => universeValue none
  | some V => V.value

theorem noneImage_level (a : Option NoneOrdinary) : SortMember none (noneImage a) := by
  cases a with
  | none => exact sort_member _ none
  | some V => exact V.level

theorem noneImage_defined (a : Option NoneOrdinary) : TypeDefined (noneImage a) := by
  cases a with
  | none => exact sort_defined _ none
  | some V => exact V.defined

theorem noneImage_injective {a b : Option NoneOrdinary}
    (h : ValueEq (noneImage a) (noneImage b)) : a = b := by
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some W => exact (W.not_universe h.symm).elim
  | some V =>
      cases b with
      | none => exact (V.not_universe h).elim
      | some W => exact congrArg some (NoneOrdinary.eq_of_valueEq h)

/-! ## The retained none kernels -/

/-- The none universe's carrier is defined before its decoder; its relation
is identity of codes. -/
def noneUniverseKernel : OptionLevelKernel.Kernel.{u} none where
  Element := ULift.{u} (Option NoneOrdinary)
  erase := fun a => noneImage a.down
  value := universeValue none
  level := sort_member _ none
  defined := sort_defined _ none
  relation := fun a b => a = b
  lawful := ⟨Eq.symm, Eq.trans⟩
  point := fun name => ⟨some (NoneOrdinary.named name)⟩
  point_member := fun _ => rfl
  irrelevant := fun h => by cases h

/-- Ordinary none term fibres are chaotic and keep exact raw term images. -/
def ordinaryKernel (V : NoneOrdinary) : OptionLevelKernel.Kernel.{u} none :=
  OptionLevelKernel.noneTerm V.value V.level V.defined

/-! ## Option-indexed certified codes -/

/-- Finite codes are the existing certified conversion codes. The none
level has its universe and one chaotic code per ordinary none image. -/
inductive OCode : Option Nat → Type (u+1) where
  | finite {k : Nat} (C : GuardedTaggedCode.Code.{u} k) : OCode (some k)
  | noneUniverse : OCode none
  | noneOrdinary (V : NoneOrdinary) : OCode none

def OCode.kernel : {k : Option Nat} → OCode.{u} k → OptionLevelKernel.Kernel.{u} k
  | _, .finite C => OptionLevelKernel.ofFinite C.kernel
  | _, .noneUniverse => noneUniverseKernel
  | _, .noneOrdinary V => ordinaryKernel V

abbrev OCode.Element {k : Option Nat} (C : OCode.{u} k) := C.kernel.Element

/-- Conversion is an actual retained kernel isomorphism. -/
def OCode.Converts {k : Option Nat} (C D : OCode.{u} k) : Prop :=
  OptionLevelKernel.Related C.kernel D.kernel

theorem OCode.finite_kernel {k : Nat} (C : GuardedTaggedCode.Code.{u} k) :
    (OCode.finite C).kernel = OptionLevelKernel.ofFinite C.kernel := rfl

/-- Every code at a finite level is one of the existing finite codes. -/
def OCode.finiteCode {k : Nat} : OCode.{u} (some k) → GuardedTaggedCode.Code.{u} k
  | .finite C => C

theorem OCode.finite_finiteCode {k : Nat} (C : OCode.{u} (some k)) :
    OCode.finite C.finiteCode = C := by
  cases C
  rfl

/-! ### Finite kernel isomorphisms are exactly Option-kernel isomorphisms -/

def isoOfKernelIso {k : Nat} {A : TaggedSaturatedTower.Kernel.{u} k}
    {B : TaggedSaturatedTower.Kernel.{v} k} (e : TaggedSaturatedTower.KernelIso A B) :
    OptionLevelKernel.Iso (OptionLevelKernel.ofFinite A) (OptionLevelKernel.ofFinite B) where
  forward := e.forward
  backward := e.backward
  left_inv := e.left_inv
  right_inv := e.right_inv
  type_image := e.type_image
  element_image := e.element_image
  point_image := e.point_image
  relation := e.relation

def kernelIsoOfIso {k : Nat} {A : TaggedSaturatedTower.Kernel.{u} k}
    {B : TaggedSaturatedTower.Kernel.{v} k}
    (e : OptionLevelKernel.Iso (OptionLevelKernel.ofFinite A) (OptionLevelKernel.ofFinite B)) :
    TaggedSaturatedTower.KernelIso A B where
  forward := e.forward
  backward := e.backward
  left_inv := e.left_inv
  right_inv := e.right_inv
  type_image := e.type_image
  element_image := e.element_image
  point_image := e.point_image
  relation := e.relation

theorem ofFinite_related_iff {k : Nat} (A : TaggedSaturatedTower.Kernel.{u} k)
    (B : TaggedSaturatedTower.Kernel.{v} k) :
    OptionLevelKernel.Related (OptionLevelKernel.ofFinite A) (OptionLevelKernel.ofFinite B) ↔
      TaggedSaturatedTower.KernelRelated A B :=
  ⟨fun ⟨e⟩ => ⟨kernelIsoOfIso e⟩, fun ⟨e⟩ => ⟨isoOfKernelIso e⟩⟩

theorem finite_converts_iff {k : Nat} (C D : GuardedTaggedCode.Code.{u} k) :
    (OCode.finite C).Converts (OCode.finite D) ↔ GuardedTaggedCode.Converts C D :=
  ofFinite_related_iff C.kernel D.kernel

/-! ### Conversion at none is identity -/

/-- The none index of a code, recovered from the code itself. -/
def noneIndex : OCode.{u} none → Option NoneOrdinary
  | .noneUniverse => none
  | .noneOrdinary V => some V

theorem noneIndex_value (C : OCode.{u} none) : C.kernel.value = noneImage (noneIndex C) := by
  cases C <;> rfl

theorem noneIndex_injective {C D : OCode.{u} none} (h : noneIndex C = noneIndex D) :
    C = D := by
  cases C <;> cases D <;> first | rfl | (cases h; rfl) | cases h

theorem none_converts_iff (C D : OCode.{u} none) : C.Converts D ↔ C = D := by
  constructor
  · intro h
    have hv := OptionLevelKernel.related_type_image h
    rw [noneIndex_value, noneIndex_value] at hv
    exact noneIndex_injective (noneImage_injective hv)
  · intro h
    cases h
    exact ⟨OptionLevelKernel.Iso.refl _⟩

theorem converts_laws (k : Option Nat) :
    NeutralDataFamily.RelLaws (fun C D : OCode.{u} k => C.Converts D) := by
  cases k with
  | none =>
      exact ⟨fun h => ((none_converts_iff _ _).mpr ((none_converts_iff _ _).mp h).symm),
        fun h g => (none_converts_iff _ _).mpr
          (((none_converts_iff _ _).mp h).trans ((none_converts_iff _ _).mp g))⟩
  | some k =>
      constructor
      · intro C D h
        rw [← OCode.finite_finiteCode C, ← OCode.finite_finiteCode D] at h ⊢
        exact (finite_converts_iff _ _).mpr
          (GuardedTaggedCode.converts_symm ((finite_converts_iff _ _).mp h))
      · intro C D E h g
        rw [← OCode.finite_finiteCode C, ← OCode.finite_finiteCode D] at h
        rw [← OCode.finite_finiteCode D, ← OCode.finite_finiteCode E] at g
        rw [← OCode.finite_finiteCode C, ← OCode.finite_finiteCode E]
        exact (finite_converts_iff _ _).mpr
          (GuardedTaggedCode.converts_trans ((finite_converts_iff _ _).mp h)
            ((finite_converts_iff _ _).mp g))

/-- Ordinary none fibres are chaotic. -/
theorem ordinary_chaotic (V : NoneOrdinary) (x y : (OCode.noneOrdinary.{u} V).Element) :
    (OCode.noneOrdinary.{u} V).kernel.relation x y := True.intro

theorem ordinary_erasure (V : NoneOrdinary) (x : Value) :
    (OCode.noneOrdinary.{u} V).kernel.erase ⟨x⟩ = x := rfl

/-! ## The universe at every Option level -/

def universeCode : (k : Option Nat) → OCode.{u+1} (k.map Nat.succ)
  | some k => .finite (GuardedConversionUniverse.conversionUniverse.{u} k)
  | none => .noneUniverse

def decodeNone : Option NoneOrdinary → OCode.{u} none
  | none => .noneUniverse
  | some V => .noneOrdinary V

theorem decodeNone_value (a : Option NoneOrdinary) :
    (decodeNone.{u} a).kernel.value = noneImage a := by
  cases a <;> rfl

theorem noneIndex_decodeNone (a : Option NoneOrdinary) :
    noneIndex (decodeNone.{u} a) = a := by
  cases a <;> rfl

/-- The universe decoder is total at every Option level. -/
def decode : (k : Option Nat) → (universeCode.{u} k).Element → OCode.{u} k
  | some k, x => .finite (GuardedConversionUniverse.decode k x)
  | none, x => decodeNone x.down

/-- Every code is decoded from some universe element. -/
def encode : (k : Option Nat) → OCode.{u} k → (universeCode.{u} k).Element
  | some k, C => GuardedConversionUniverse.encode k C.finiteCode
  | none, C => ⟨noneIndex C⟩

theorem decode_encode (k : Option Nat) (C : OCode.{u} k) : decode k (encode k C) = C := by
  cases k with
  | none => cases C <;> rfl
  | some k => exact OCode.finite_finiteCode C

theorem universe_value (k : Option Nat) :
    (universeCode.{u} k).kernel.value = universeValue k := by
  cases k <;> rfl

/-- The universe image at an Option level is exactly the evaluated sort. -/
theorem universe_value_eq_iff (a b : Option Nat) :
    ValueEq (universeCode.{u} a).kernel.value (universeCode.{v} b).kernel.value ↔ a = b := by
  rw [universe_value, universe_value]
  constructor
  · exact sort_code_injective
  · intro h
    cases h
    exact ValueEq.refl _

/-- Consistency with the unchanged all-valuation sort comparison. -/
theorem sort_universe_eq_iff_eqN (a b : Level) :
    (∀ ν : Valuation, ValueEq (universeCode.{u} (eval ν a)).kernel.value
      (universeCode.{u} (eval ν b)).kernel.value) ↔ eqN a b := by
  constructor
  · intro h ν
    exact (universe_value_eq_iff _ _).mp (h ν)
  · intro h ν
    exact (universe_value_eq_iff _ _).mpr (h ν)

theorem universe_erasure (k : Option Nat) (x : (universeCode.{u} k).Element) :
    (universeCode.{u} k).kernel.erase x = (decode k x).kernel.value := by
  cases k with
  | none => exact (decodeNone_value x.down).symm
  | some k => rfl

/-- Universe elements are related exactly when their decoded codes convert.
At none this is identity of codes; ordinary none fibres stay chaotic. -/
theorem universe_relation_iff (k : Option Nat) (x y : (universeCode.{u} k).Element) :
    (universeCode.{u} k).kernel.relation x y ↔ (decode k x).Converts (decode k y) := by
  cases k with
  | none =>
      rw [none_converts_iff]
      constructor
      · intro h
        cases h
        rfl
      · intro h
        have hi := congrArg noneIndex h
        rw [show decode none x = decodeNone x.down from rfl,
          show decode none y = decodeNone y.down from rfl,
          noneIndex_decodeNone, noneIndex_decodeNone] at hi
        cases x
        cases y
        cases hi
        rfl
  | some k => exact (finite_converts_iff _ _).symm

theorem universe_member (k : Option Nat) (C : OCode.{u} k) :
    (universeCode.{u} k).kernel.relation (encode k C) (encode k C) :=
  (universe_relation_iff k _ _).mpr ((converts_laws k).trans
    ((converts_laws k).symm (by rw [decode_encode]; exact ⟨OptionLevelKernel.Iso.refl _⟩))
    (by rw [decode_encode]; exact ⟨OptionLevelKernel.Iso.refl _⟩))

theorem none_universe_relation_iff_eq (x y : (universeCode.{u} none).Element) :
    (universeCode.{u} none).kernel.relation x y ↔ decode none x = decode none y :=
  (universe_relation_iff none x y).trans (none_converts_iff _ _)

theorem universe_elimination (k : Option Nat) (x : (universeCode.{u} k).Element) :
    SortMember k ((universeCode.{u} k).kernel.erase x) ∧
      TypeDefined ((universeCode.{u} k).kernel.erase x) := by
  rw [universe_erasure]
  exact ⟨(decode k x).kernel.level, (decode k x).kernel.defined⟩

theorem universe_point_image (k : Option Nat) (name : Nat) :
    ValueEq ((universeCode.{u} k).kernel.erase ((universeCode.{u} k).kernel.point name))
      (NativeMemberValues.value k name) := by
  cases k <;> exact ValueEq.refl _

/-- The none universe contains itself; the finite universe at `k` is an
element of the universe at `k+1`. -/
theorem universe_in_next (k : Option Nat) :
    ∃ x : (universeCode.{u+1} (k.map Nat.succ)).Element,
      decode (k.map Nat.succ) x = universeCode.{u} k := by
  cases k with
  | none => exact ⟨⟨none⟩, rfl⟩
  | some k => exact ⟨GuardedConversionUniverse.conversionUniverse.{u} k, rfl⟩

theorem none_self_member :
    decode none (⟨none⟩ : (universeCode.{u} none).Element) = OCode.noneUniverse.{u} := rfl

/-! ## The all-Option raw sort algebra -/

/-- A certified universe at finite level `j+1` whose carrier is the native
names, at every host universe. It witnesses that `Sort j` is a member of
the decoded conversion universe at `j+1`. -/
def namedUniverseLegacy (j : Nat) : TaggedSaturatedTower.Code.{u} (j+1) where
  kernel := TaggedSaturatedTower.universeKernel j (ULift.{u} Nat)
    (fun n => TaggedSaturatedTower.neutralKernel j n.down) Eq
    ⟨fun h => h.symm, fun h g => h.trans g⟩ (fun n => ⟨n⟩) (fun _ => rfl)
  tag := .univ
  witness := .univ j (ULift.{u} Nat) (fun n => TaggedSaturatedTower.neutralKernel j n.down) Eq
    ⟨fun h => h.symm, fun h g => h.trans g⟩ (fun n => ⟨n⟩) (fun _ => rfl)
    (fun x y h => by
      cases h
      exact TaggedSaturatedTower.kernelRelated_refl _)
    (fun _ => ValueEq.refl _)

def namedUniverse (j : Nat) : GuardedTaggedCode.Code.{u} (j+1) :=
  .legacy (namedUniverseLegacy.{u} j)

theorem namedUniverse_value (j : Nat) :
    (namedUniverse.{u} j).view.value = universeValue (some j) := rfl

/-- The finite raw universe relation is the least PER of retained images of
the conversion universe: images of converting finite codes. -/
def finiteUniversePER (j : Nat) : Relation :=
  GuardedTaggedCode.Decoded (GuardedConversionUniverse.conversionUniverse.{u} j).kernel

theorem finiteUniversePER_laws (j : Nat) : Laws (finiteUniversePER.{u} j) :=
  GuardedTaggedCode.decoded_laws _

def NoneUniversePER (V W : Value) : Prop :=
  ∃ a : Option NoneOrdinary, ValueEq V (noneImage a) ∧ ValueEq W (noneImage a)

theorem noneUniversePER_laws : Laws NoneUniversePER where
  symm := fun ⟨a, hv, hw⟩ => ⟨a, hw, hv⟩
  trans := by
    rintro V W Z ⟨a, hv, hw⟩ ⟨b, hw', hz⟩
    have hab := noneImage_injective (hw.symm.trans hw')
    cases hab
    exact ⟨a, hv, hz⟩

/-- The least retained-image relation of an Option kernel. -/
def El {k : Option Nat} (K : OptionLevelKernel.Kernel.{u} k) (x y : Value) : Prop :=
  ∃ a b : K.Element, K.relation a b ∧ ValueEq (K.erase a) x ∧ ValueEq (K.erase b) y

/-- The raw none relation is exactly the El of the retained none universe. -/
theorem noneUniversePER_iff_el (V W : Value) :
    NoneUniversePER V W ↔ El (OCode.noneUniverse.{u}).kernel V W := by
  constructor
  · rintro ⟨a, hv, hw⟩
    exact ⟨⟨a⟩, ⟨a⟩, rfl, hv.symm, hw.symm⟩
  · rintro ⟨x, y, hxy, hx, hy⟩
    cases hxy
    exact ⟨x.down, hx.symm, hy.symm⟩

/-- Ordinary none fibres have the chaotic El. -/
theorem ordinary_el (V : NoneOrdinary) (x y : Value) :
    El (OCode.noneOrdinary.{u} V).kernel x y :=
  ⟨⟨x⟩, ⟨y⟩, True.intro, ValueEq.refl _, ValueEq.refl _⟩

def noneElementPER : Option NoneOrdinary → Relation
  | none => NoneUniversePER
  | some _ => NoneUniverseBoundary.Chaos

theorem noneElementPER_laws (a : Option NoneOrdinary) : Laws (noneElementPER a) := by
  cases a with
  | none => exact noneUniversePER_laws
  | some _ => exact NoneUniverseBoundary.chaos_laws

def NoneRawCode (V : Value) (R : Relation) : Prop :=
  ∃ a : Option NoneOrdinary, ValueEq V (noneImage a) ∧ Same R (noneElementPER a)

def FiniteRawCode (k : Nat) (V : Value) (R : Relation) : Prop :=
  ∃ j : Nat, k = j + 1 ∧ ValueEq V (universeValue (some j)) ∧ Same R (finiteUniversePER.{u} j)

def RawCode : Option Nat → Value → Relation → Prop
  | none, V, R => NoneRawCode V R
  | some k, V, R => FiniteRawCode.{u} k V R

def RawUniversePER : Option Nat → Relation
  | none => NoneUniversePER
  | some j => finiteUniversePER.{u} j

theorem rawCode_lawful {k : Option Nat} {V : Value} {R : Relation}
    (h : RawCode.{u} k V R) : Laws R := by
  cases k with
  | none =>
      obtain ⟨a, _, hr⟩ := h
      exact NeutralControls.laws_of_same hr (noneElementPER_laws a)
  | some k =>
      obtain ⟨j, _, _, hr⟩ := h
      exact NeutralControls.laws_of_same hr (finiteUniversePER_laws j)

theorem rawCode_level {k : Option Nat} {V : Value} {R : Relation}
    (h : RawCode.{u} k V R) : SortMember k V := by
  cases k with
  | none =>
      obtain ⟨a, hv, _⟩ := h
      exact sortMember_congr hv.symm (noneImage_level a)
  | some k =>
      obtain ⟨j, hk, hv, _⟩ := h
      cases hk
      exact sortMember_congr hv.symm (sort_member _ (some j))

theorem rawCode_defined {k : Option Nat} {V : Value} {R : Relation}
    (h : RawCode.{u} k V R) : TypeDefined V := by
  cases k with
  | none =>
      obtain ⟨a, hv, _⟩ := h
      exact typeDefined_congr hv.symm (noneImage_defined a)
  | some k =>
      obtain ⟨j, _, hv, _⟩ := h
      exact typeDefined_congr hv.symm (sort_defined _ (some j))

theorem rawCode_coherent {k l : Option Nat} {V : Value} {R S : Relation}
    (h : RawCode.{u} k V R) (g : RawCode.{u} l V S) : Same R S := by
  have hkl := sortMember_unique (rawCode_level h) (rawCode_level g) (rawCode_defined h)
  cases hkl
  cases k with
  | none =>
      obtain ⟨a, hv, hr⟩ := h
      obtain ⟨b, hw, hs⟩ := g
      have hab := noneImage_injective (hv.symm.trans hw)
      cases hab
      exact fun x y => (hr x y).trans (hs x y).symm
  | some k =>
      obtain ⟨j, hj, hv, hr⟩ := h
      obtain ⟨i, hi, hw, hs⟩ := g
      have hij : some j = some i := sort_code_injective (hv.symm.trans hw)
      cases hij
      exact fun x y => (hr x y).trans (hs x y).symm

theorem rawCode_universe (k : Option Nat) :
    RawCode.{u} (k.map Nat.succ) (universeValue k) (RawUniversePER.{u} k) := by
  cases k with
  | none => exact ⟨none, ValueEq.refl _, fun _ _ => Iff.rfl⟩
  | some j => exact ⟨j, rfl, ValueEq.refl _, fun _ _ => Iff.rfl⟩

theorem rawUniverse_member (k : Option Nat) :
    Member (RawUniversePER.{u} (k.map Nat.succ)) (universeValue k) := by
  cases k with
  | none => exact ⟨none, ValueEq.refl _, ValueEq.refl _⟩
  | some j =>
      exact (GuardedTaggedCode.decoded_member_iff _ _).mpr
        ⟨GuardedConversionUniverse.encode (j+1) (namedUniverse.{u} j),
          GuardedConversionUniverse.member (j+1) _, ValueEq.refl _⟩

theorem rawUniverse_elim {k l : Option Nat} {R : Relation} {x : Value}
    (h : RawCode.{u} l (universeValue k) R) (hx : Member R x) :
    SortMember k x ∧ TypeDefined x := by
  have hu : Member (RawUniversePER.{u} k) x :=
    (rawCode_coherent h (rawCode_universe k) x x).mp hx
  cases k with
  | none =>
      obtain ⟨a, hx, _⟩ := hu
      exact ⟨sortMember_congr hx.symm (noneImage_level a),
        typeDefined_congr hx.symm (noneImage_defined a)⟩
  | some j =>
      obtain ⟨a, _, he⟩ := (GuardedTaggedCode.decoded_member_iff _ _).mp hu
      exact ⟨sortMember_congr he (GuardedConversionUniverse.elimination j a).1,
        typeDefined_congr he (GuardedConversionUniverse.elimination j a).2⟩

def codeSystem : CodeSystem where
  Code := RawCode.{u}
  universePER := RawUniversePER.{u}
  lawful := rawCode_lawful
  defined := rawCode_defined
  level := rawCode_level
  coherent := rawCode_coherent
  universe_code := rawCode_universe
  universe_member := rawUniverse_member
  universe_elim := rawUniverse_elim

/-- At none, the raw algebra is exactly the retained one: every raw none code
is the El of an actual none code with the same image, and conversely. -/
theorem noneRawCode_iff_retained (V : Value) (R : Relation) :
    NoneRawCode V R ↔
      ∃ C : OCode.{u} none, ValueEq V C.kernel.value ∧ Same R (El C.kernel) := by
  constructor
  · rintro ⟨a, hv, hr⟩
    refine ⟨decodeNone a, by rw [decodeNone_value]; exact hv, fun x y => (hr x y).trans ?_⟩
    cases a with
    | none => exact noneUniversePER_iff_el x y
    | some W => exact ⟨fun _ => ordinary_el W x y, fun _ => True.intro⟩
  · rintro ⟨C, hv, hr⟩
    refine ⟨noneIndex C, by rw [← noneIndex_value]; exact hv, fun x y => (hr x y).trans ?_⟩
    cases C with
    | noneUniverse => exact (noneUniversePER_iff_el x y).symm
    | noneOrdinary W => exact ⟨fun _ => True.intro, fun _ => ordinary_el W x y⟩

/-- At a finite level the raw universe relation is the decoded retained
conversion universe itself, with no image-keyed restriction. -/
theorem finiteUniversePER_retained (j : Nat) :
    finiteUniversePER.{u} j =
      GuardedTaggedCode.Decoded (universeCode.{u} (some j)).finiteCode.kernel := rfl

theorem named_universePER_extends {V W : Value}
    (h : NoneSelfUniverse.UniversePER V W) : NoneUniversePER V W := by
  obtain ⟨a, hv, hw⟩ := h
  cases a with
  | none => exact ⟨none, hv, hw⟩
  | some n => exact ⟨some (NoneOrdinary.named n), hv, hw⟩

/-- The named none algebra embeds into the ordinary none algebra: each of its
codes has a code here with a relation containing its own. The named ordinary
codes keep their chaotic relation; the universe relation grows. -/
theorem named_noneCode_extends {V : Value} {R : Relation}
    (h : NoneSelfUniverse.NoneCode V R) :
    ∃ S : Relation, NoneRawCode V S ∧ ∀ x y, R x y → S x y := by
  obtain ⟨a, hv, hr⟩ := h
  cases a with
  | none =>
      exact ⟨NoneUniversePER, ⟨none, hv, fun _ _ => Iff.rfl⟩,
        fun x y hxy => named_universePER_extends ((hr x y).mp hxy)⟩
  | some n =>
      exact ⟨NoneUniverseBoundary.Chaos, ⟨some (NoneOrdinary.named n), hv, fun _ _ => Iff.rfl⟩,
        fun _ _ _ => True.intro⟩

/-- Why the finite branch keeps only the universes: no image-keyed code system
can give every finite conversion code its own decoded relation. The certified
K call and minor codes have one actual raw image and different decoded PERs
for every valuation. -/
theorem no_image_keyed_finite_codes :
    ¬ ∃ C : CodeSystem, ∀ D : GuardedTaggedCode.Code.{0} 1,
      C.Code (some 1) D.view.value (GuardedTaggedCode.Decoded D.kernel) := by
  rintro ⟨C, hC⟩
  let ν : Valuation := fun _ => some 0
  have hcall := hC (GuardedTaggedCode.Code.legacy (TaggedKCoherenceBoundary.callCode ν))
  have hminor := hC (GuardedTaggedCode.Code.legacy (TaggedKCoherenceBoundary.minorCode ν))
  have hminor' : C.Code (some 1)
      (GuardedTaggedCode.Code.legacy (TaggedKCoherenceBoundary.callCode ν)).view.value
      (GuardedTaggedCode.Decoded
        (GuardedTaggedCode.Code.legacy (TaggedKCoherenceBoundary.minorCode ν)).kernel) := by
    have he : (GuardedTaggedCode.Code.legacy (TaggedKCoherenceBoundary.callCode ν)).view.value =
        (GuardedTaggedCode.Code.legacy (TaggedKCoherenceBoundary.minorCode ν)).view.value :=
      NeutralCodes.valueEq_eq (TaggedKCoherenceBoundary.endpoint_images_agree ν)
    rw [he]
    exact hminor
  exact TaggedKCoherenceBoundary.decoded_not_same ν (C.coherent hcall hminor')

/-! ## The original sort arm over the new algebra -/

def semantics (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax) : AnnSemantics :=
  EnvironmentEval.annSemantics codeSystem.{u} E F

/-- The original PairedTyGoal for sorts, with no valuation restriction. -/
theorem paired_sort_goal (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (l : Level) :
    PairedTyGoal (semantics.{u} E F) E I n Γ (.sort l) (.sort (.succ l)) :=
  PairedArms.paired_sort_goal (semantics E F) E I n Γ l

theorem ty_sort_supplied (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (I : IotaIfaceA) (n : Nat) : PairedArms.Ty_sort (semantics.{u} E F) E I n :=
  paired_sort_goal E F I n

/-- At every evaluated level the paired sort judgment uses the retained
universe's raw relation: the decoded conversion universe at finite levels
and the none universe's own relation at none. -/
theorem sort_judgment (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (Γ : LCtxA) (ν μ : Valuation) (ρ σ : EnvI) (l : Level)
    (hν : ValuationRel ν μ) :
    PairedJudgment (semantics.{u} E F) ν μ Γ ρ σ (.sort l) (.sort l) (.sort (.succ l)) := by
  have hm : eval μ l = eval ν l := (eval_of_valuationRel hν l).symm
  have hsl : eval ν (.succ l) = (eval ν l).map Nat.succ := by
    cases h : eval ν l <;> simp [eval, h]
  have hsm : eval μ (.succ l) = (eval ν l).map Nat.succ := by
    cases h : eval ν l <;> simp [eval, h, hm]
  unfold PairedJudgment
  simp only [(semantics E F).sort_image, hm, hsl, hsm]
  exact ⟨((eval ν l).map Nat.succ).map Nat.succ, RawUniversePER ((eval ν l).map Nat.succ),
    RawUniversePER ((eval ν l).map Nat.succ),
    CodePair.diagonal (rawCode_universe ((eval ν l).map Nat.succ)), rawUniverse_member (eval ν l)⟩

/-- The attached semantics keeps the full original sort comparison. -/
theorem evaluated_sort_eq_iff_eqN (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (Γ : LCtxA) (ρ : EnvI) (a b : Level) :
    (∀ ν : Valuation,
      ValueEq ((semantics.{u} E F).image ν Γ ρ (.sort a))
        ((semantics.{u} E F).image ν Γ ρ (.sort b))) ↔ eqN a b := by
  constructor
  · intro h ν
    have hv := h ν
    rw [(semantics E F).sort_image, (semantics E F).sort_image] at hv
    exact sort_code_injective hv
  · intro h ν
    rw [(semantics E F).sort_image, (semantics E F).sort_image, h ν]
    exact ValueEq.refl _

/-- The sort image is the retained universe code's type image, at every
Option level, for every valuation. -/
theorem sort_image_retained (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (Γ : LCtxA) (ρ : EnvI) (l : Level) :
    (semantics.{u} E F).image ν Γ ρ (.sort l) = (universeCode.{u} (eval ν l)).kernel.value := by
  rw [(semantics E F).sort_image, universe_value]

/-- Admission, source typing and the paired none sort judgment for the
concrete partial valuation, now over the ordinary none algebra. -/
theorem admitted_none_sort (F : EnvironmentEval.FamilySyntax) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 1 []) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 1 []
      UniverseDecoderBoundary.noneSort (.sort (.succ (.param 0)))) ∧
    eval UniverseDecoderBoundary.noneValuation (.param 0) = none ∧
    PairedRealises (semantics.{u} emptyEnvA F) UniverseDecoderBoundary.noneValuation
      UniverseDecoderBoundary.noneValuation [] EnvI.bot EnvI.bot ∧
    PairedJudgment (semantics.{u} emptyEnvA F) UniverseDecoderBoundary.noneValuation
      UniverseDecoderBoundary.noneValuation [] EnvI.bot EnvI.bot
      UniverseDecoderBoundary.noneSort UniverseDecoderBoundary.noneSort
      (.sort (.succ (.param 0))) :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨UniverseDecoderBoundary.source_none_sort⟩, rfl, .nil _ _,
    sort_judgment emptyEnvA F [] _ _ _ _ (.param 0) (ValuationRel.refl _)⟩

end Rcic.Declarative.Ann.LR3.OptionSoundUniverse

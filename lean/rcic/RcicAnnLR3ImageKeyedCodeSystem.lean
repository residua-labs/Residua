import rcic.RcicAnnLR3OptionSoundUniverse

/-!
# Option-indexed code systems from image-keyed code families

An image-keyed code family has, at each Nat level, codes as data. Each code
has a raw type image and a relation, and a well-formedness predicate `ok`.
Well-formed relations are PERs, well-formed images have the right level and
are defined, and equal images of well-formed codes give the same relation
(coherence). The family must also have a universe code at every level with
the evaluated sort image, a member at the next level, and a decoder from
universe-related values to well-formed codes with the same relation.

From such data the builder produces one `CodeSystem` over all Option
levels. At a finite level, a raw value gets the relation of every
well-formed code with that image; at `none` it is the ordinary none
algebra. The builder supplies every field, `UniverseTransport`, and the
original `Ty_sort` over any attached evaluator semantics. Families
instantiate it without restating these proofs. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.ImageKeyedCodeSystem

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements

structure Family where
  Cd : Nat → Type
  ok : {k : Nat} → Cd k → Prop
  img : {k : Nat} → Cd k → Value
  rel : {k : Nat} → Cd k → Relation
  laws : ∀ {k : Nat} (c : Cd k), ok c → Laws (rel c)
  level : ∀ {k : Nat} (c : Cd k), ok c → SortMember (some k) (img c)
  defined : ∀ {k : Nat} (c : Cd k), ok c → TypeDefined (img c)
  coherent : ∀ {k l : Nat} (c : Cd k) (d : Cd l), ok c → ok d →
    ValueEq (img c) (img d) → Same (rel c) (rel d)
  univ : (k : Nat) → Cd (k + 1)
  univ_ok : ∀ k, ok (univ k)
  univ_img : ∀ k, ValueEq (img (univ k)) (universeValue (some k))
  univ_member : ∀ k, rel (univ (k + 1)) (universeValue (some k)) (universeValue (some k))
  univ_decode : ∀ {k : Nat} {V W : Value}, rel (univ k) V W →
    ∃ c d : Cd k, ok c ∧ ok d ∧ ValueEq V (img c) ∧ ValueEq W (img d) ∧ Same (rel c) (rel d)

namespace Family

variable (F : Family)

/-- The relation of every well-formed code with image `V`. -/
def Dec (k : Nat) (V x y : Value) : Prop := ∃ c : F.Cd k, F.ok c ∧ ValueEq V (F.img c) ∧ F.rel c x y

theorem dec_of_ok {k : Nat} {c : F.Cd k} (hc : F.ok c) {V : Value} (hV : ValueEq V (F.img c)) :
    Same (F.Dec k V) (F.rel c) := by
  intro x y
  constructor
  · rintro ⟨d, hd, hVd, hxy⟩
    exact (F.coherent d c hd hc (hVd.symm.trans hV) x y).mp hxy
  · intro h
    exact ⟨c, hc, hV, h⟩

theorem dec_laws (k : Nat) (V : Value) : Laws (F.Dec k V) := by
  refine ⟨?_, ?_⟩
  · rintro x y ⟨c, hc, hv, hxy⟩
    exact ⟨c, hc, hv, (F.laws c hc).symm hxy⟩
  · rintro x y z ⟨c, hc, hv, hxy⟩ ⟨d, hd, hw, hyz⟩
    exact ⟨c, hc, hv, (F.laws c hc).trans hxy ((F.coherent d c hd hc (hw.symm.trans hv) y z).mp hyz)⟩

theorem dec_congr {k : Nat} {V W : Value} (h : ValueEq V W) : Same (F.Dec k V) (F.Dec k W) := by
  rw [NeutralCodes.valueEq_eq h]
  exact fun _ _ => Iff.rfl

def FCode (k : Nat) (V : Value) (R : Relation) : Prop :=
  (∃ c : F.Cd k, F.ok c ∧ ValueEq V (F.img c)) ∧ Same R (F.Dec k V)

def Code : Option Nat → Value → Relation → Prop
  | none, V, R => OptionSoundUniverse.NoneRawCode V R
  | some k, V, R => F.FCode k V R

def UniversePER : Option Nat → Relation
  | none => OptionSoundUniverse.NoneUniversePER
  | some k => F.rel (F.univ k)

theorem code_lawful {k : Option Nat} {V : Value} {R : Relation} (h : F.Code k V R) : Laws R := by
  cases k with
  | none => exact OptionSoundUniverse.rawCode_lawful.{0} (k := none) h
  | some k => exact NeutralControls.laws_of_same h.2 (F.dec_laws k V)

theorem code_level {k : Option Nat} {V : Value} {R : Relation} (h : F.Code k V R) :
    SortMember k V := by
  cases k with
  | none => exact OptionSoundUniverse.rawCode_level.{0} (k := none) h
  | some k =>
      obtain ⟨⟨c, hc, hV⟩, _⟩ := h
      exact sortMember_congr hV.symm (F.level c hc)

theorem code_defined {k : Option Nat} {V : Value} {R : Relation} (h : F.Code k V R) :
    TypeDefined V := by
  cases k with
  | none => exact OptionSoundUniverse.rawCode_defined.{0} (k := none) h
  | some k =>
      obtain ⟨⟨c, hc, hV⟩, _⟩ := h
      exact typeDefined_congr hV.symm (F.defined c hc)

theorem code_coherent {k l : Option Nat} {V : Value} {R S : Relation}
    (h : F.Code k V R) (g : F.Code l V S) : Same R S := by
  have hkl := sortMember_unique (F.code_level h) (F.code_level g) (F.code_defined h)
  cases hkl
  cases k with
  | none => exact OptionSoundUniverse.rawCode_coherent.{0} (k := none) (l := none) h g
  | some k => exact fun x y => (h.2 x y).trans (g.2 x y).symm

theorem universe_code (k : Option Nat) :
    F.Code (k.map Nat.succ) (universeValue k) (F.UniversePER k) := by
  cases k with
  | none => exact OptionSoundUniverse.rawCode_universe.{0} none
  | some k =>
      exact ⟨⟨F.univ k, F.univ_ok k, (F.univ_img k).symm⟩,
        fun x y => ((F.dec_of_ok (F.univ_ok k) (F.univ_img k).symm) x y).symm⟩

theorem universe_member (k : Option Nat) :
    Member (F.UniversePER (k.map Nat.succ)) (universeValue k) := by
  cases k with
  | none => exact OptionSoundUniverse.rawUniverse_member.{0} none
  | some k => exact F.univ_member k

theorem universe_elim {k l : Option Nat} {R : Relation} {x : Value}
    (h : F.Code l (universeValue k) R) (hx : Member R x) : SortMember k x ∧ TypeDefined x := by
  have hu : Member (F.UniversePER k) x := (F.code_coherent h (F.universe_code k) x x).mp hx
  cases k with
  | none =>
      obtain ⟨a, hx, _⟩ := hu
      exact ⟨sortMember_congr hx.symm (OptionSoundUniverse.noneImage_level a),
        typeDefined_congr hx.symm (OptionSoundUniverse.noneImage_defined a)⟩
  | some k =>
      obtain ⟨c, _, hc, _, hx, _, _⟩ := F.univ_decode hu
      exact ⟨sortMember_congr hx.symm (F.level c hc), typeDefined_congr hx.symm (F.defined c hc)⟩

def codeSystem : CodeSystem where
  Code := F.Code
  universePER := F.UniversePER
  lawful := F.code_lawful
  defined := F.code_defined
  level := F.code_level
  coherent := F.code_coherent
  universe_code := F.universe_code
  universe_member := F.universe_member
  universe_elim := F.universe_elim

/-- Every universe edge has actual well-formed codes on both sides. -/
theorem universeTransport : UniverseTransport F.codeSystem where
  relate := by
    intro k V W h
    cases k with
    | none =>
        obtain ⟨a, hv, hw⟩ := h
        exact ⟨OptionSoundUniverse.noneElementPER a, OptionSoundUniverse.noneElementPER a,
          ⟨a, hv, fun _ _ => Iff.rfl⟩, ⟨a, hw, fun _ _ => Iff.rfl⟩, fun _ _ => Iff.rfl⟩
    | some k =>
        obtain ⟨c, d, hc, hd, hV, hW, hs⟩ := F.univ_decode h
        refine ⟨F.Dec k V, F.Dec k W, ⟨⟨c, hc, hV⟩, fun _ _ => Iff.rfl⟩,
          ⟨⟨d, hd, hW⟩, fun _ _ => Iff.rfl⟩, fun x y => ?_⟩
        exact ((F.dec_of_ok hc hV) x y).trans ((hs x y).trans ((F.dec_of_ok hd hW) x y).symm)

/-- A well-formed code is a code of the system at its level with its relation. -/
theorem ok_code {k : Nat} {c : F.Cd k} (hc : F.ok c) {V : Value} (hV : ValueEq V (F.img c)) :
    F.codeSystem.Code (some k) V (F.rel c) :=
  ⟨⟨c, hc, hV⟩, fun x y => ((F.dec_of_ok hc hV) x y).symm⟩

/-- Well-formed level-zero relations that are proof-irrelevant make the
system proof-irrelevant. -/
theorem propIrrelevance
    (hirr : ∀ c : F.Cd 0, F.ok c → ∀ x y, F.rel c x x → F.rel c y y → F.rel c x y) :
    PropIrrelevance F.codeSystem where
  relate := by
    intro V R x y h hx hy
    obtain ⟨_, hR⟩ := (h : F.FCode 0 V R)
    obtain ⟨c, hc, hV, hxx⟩ := (hR x x).mp hx
    obtain ⟨d, hd, hV', hyy⟩ := (hR y y).mp hy
    have hs := F.coherent d c hd hc (hV'.symm.trans hV)
    exact (hR x y).mpr ⟨c, hc, hV, hirr c hc x y hxx ((hs y y).mp hyy)⟩

theorem ty_sort_supplied (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax)
    (I : IotaIfaceA) (n : Nat) :
    PairedArms.Ty_sort (EnvironmentEval.annSemantics F.codeSystem E H) E I n :=
  fun Γ l => PairedArms.paired_sort_goal _ E I n Γ l

end Family

end Rcic.Declarative.Ann.LR3.ImageKeyedCodeSystem

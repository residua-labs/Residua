import rcic.RcicAnnLR3CandidatePi

/-!
# A predicative tower retaining its element PERs

The semantic carrier at a successor stage contains raw realizers and the
preceding stage's explicit codes. This is ordinary recursion on Nat.
Universe membership retains a code as data, so its decoder is a case
split, never a selection from an existential proposition. Related codes
transport their element PERs and their designated members.

The zero-stage codes are exactly CandidatePi.Element, including the
completion of every proposition candidate. Thus the universe at zero
has precisely the retained candidate data quantified by forallProp.
Successor stages admit the neutral completion of every lawful PER on
their carrier. The actual universe codes, decoding, exact raw sort tags
and universe-neutral reflection are supplied at every defined level.

This is a universe-carrier producer. It does not provide the semantic
action of a raw function on enriched results, full source Pi closure,
undefined-level source interpretation or a Fundamental theorem.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.StratifiedCandidates

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily

universe u

/-- The relation and designated members are retained data. The members
of an arbitrary record are not claimed to be neutral reflections.
No uniqueness from the raw type value is required. -/
structure PointedPER (k : Nat) (A : Type u) where
  value : Value
  level : SortMember (some k) value
  defined : TypeDefined value
  relation : A → A → Prop
  lawful : RelLaws relation
  point : Nat → A
  point_member : ∀ name, relation (point name) (point name)
  irrelevant : k = 0 → ∀ x y, relation x x → relation y y → relation x y

/-- The zero-stage data is exactly the candidate-pair carrier. Higher
stages are defined by ordinary recursion, with no inductive recursion. -/
def CodeData : Nat → Type
  | 0 => CandidatePi.Element
  | k + 1 => PointedPER (k + 1) (Sum Value (CodeData k))

/-- Raw realizers are retained at every stage; codes used as universe
elements retain their relation data. -/
def Carrier : Nat → Type
  | 0 => Value
  | k + 1 => Sum Value (CodeData k)

abbrev Code (k : Nat) := CodeData k

/-- This view supplies the actual application-closed completion at zero.
Its designated members are the concrete neutral atoms. -/
def candidateView (A : CandidatePi.Element) : PointedPER 0 Value where
  value := A.value
  level := A.level
  defined := A.defined
  relation := CandidatePi.decode A
  lawful := ⟨(CandidatePi.complete A.candidate).lawful.symm,
    (CandidatePi.complete A.candidate).lawful.trans⟩
  point := NeutralPER.neutralAtom
  point_member := fun name => (CandidatePi.complete A.candidate).reflect (.atom name)
  irrelevant := fun _ _ _ hx hy => (CandidatePi.complete A.candidate).irrelevant hx hy

def view : (k : Nat) → Code k → PointedPER k (Carrier k)
  | 0, A => candidateView A
  | _ + 1, A => A

theorem view_zero_relation (A : CandidatePi.Element) :
    (view 0 A).relation = CandidatePi.decode A := rfl

def raw : (k : Nat) → Value → Carrier k
  | 0, v => v
  | _ + 1, v => .inl v

def erase : (k : Nat) → Carrier k → Value
  | 0, v => v
  | _ + 1, .inl v => v
  | k + 1, .inr A => (view k A).value

theorem erase_raw (k : Nat) (v : Value) : erase k (raw k v) = v := by
  cases k <;> rfl

def encode (k : Nat) (A : Code k) : Carrier (k + 1) := .inr A

theorem erase_encode (k : Nat) (A : Code k) :
    erase (k + 1) (encode k A) = (view k A).value := rfl

/-- Same fibres suffice for element transport. Designated-member
agreement is also retained. -/
structure Related {k : Nat} {A : Type u} (C D : PointedPER k A) : Prop where
  transport : ∀ x y, C.relation x y ↔ D.relation x y
  points : ∀ name, C.relation (C.point name) (D.point name)

theorem related_refl {k : Nat} {A : Type u} (C : PointedPER k A) : Related C C :=
  ⟨fun _ _ => Iff.rfl, C.point_member⟩

theorem related_symm {k : Nat} {A : Type u} {C D : PointedPER k A}
    (h : Related C D) : Related D C :=
  ⟨fun x y => (h.transport x y).symm,
    fun name => (h.transport _ _).mp (C.lawful.symm (h.points name))⟩

theorem related_trans {k : Nat} {A : Type u} {C D E : PointedPER k A}
    (h : Related C D) (g : Related D E) : Related C E :=
  ⟨fun x y => (h.transport x y).trans (g.transport x y),
    fun name => C.lawful.trans (h.points name)
      ((h.transport _ _).mpr (g.points name))⟩

theorem related_laws {k : Nat} {A : Type u} :
    RelLaws (fun C D : PointedPER k A => Related C D) :=
  ⟨related_symm, related_trans⟩

def CodeRelated (k : Nat) (A B : Code k) : Prop := Related (view k A) (view k B)

theorem code_level_unique {k l : Nat} (A : Code k) (B : Code l)
    (h : ValueEq (view k A).value (view l B).value) : k = l :=
  Option.some.inj (sortMember_unique (view k A).level
    (sortMember_congr h.symm (view l B).level) (view k A).defined)

/-- The actual zero-stage producer accepts every original candidate.
Its completion is the application-closed, nonbottom-neutral completion. -/
def ofCandidate (A : CandidatePi.Element) : Code 0 := A

theorem ofCandidate_transport {A B : CandidatePi.Element}
    (h : CandidatePi.ElementRel A B) : CodeRelated 0 (ofCandidate A) (ofCandidate B) :=
  ⟨h, fun name => (CandidatePi.complete A.candidate).reflect (.atom name)⟩

theorem zero_related_iff (A B : CandidatePi.Element) :
    CodeRelated 0 A B ↔ CandidatePi.ElementRel A B :=
  ⟨fun h => h.transport, ofCandidate_transport⟩

/-- Adding only neutral self-edges preserves the original relation among
distinct values, so it does not collapse unrelated data classes. -/
def Extend {A : Type u} (R : A → A → Prop) (N : A → Prop) (x y : A) : Prop :=
  R x y ∨ (x = y ∧ N x)

theorem extend_laws {A : Type u} {R : A → A → Prop} (hR : RelLaws R)
    (N : A → Prop) : RelLaws (Extend R N) := by
  constructor
  · intro x y h
    rcases h with h | ⟨rfl, hn⟩
    · exact Or.inl (hR.symm h)
    · exact Or.inr ⟨rfl, hn⟩
  · intro x y z h g
    rcases h with h | ⟨rfl, hn⟩
    · rcases g with g | ⟨rfl, _⟩
      · exact Or.inl (hR.trans h g)
      · exact Or.inl h
    · exact g

theorem extend_distinct {A : Type u} {R : A → A → Prop} {N : A → Prop}
    {x y : A} (h : x ≠ y) : Extend R N x y ↔ R x y :=
  ⟨fun hr => hr.elim id (fun he => False.elim (h he.1)), Or.inl⟩

def RawNeutral (k : Nat) (x : Carrier k) : Prop :=
  ∃ name : Nat, x = raw k (NeutralPER.neutralAtom name)

/-- An actual successor-stage code from any supplied lawful carrier PER.
The only new members are the explicit raw neutral values. -/
def predicative (k : Nat) (V : Value) (hk : SortMember (some (k + 1)) V)
    (hd : TypeDefined V) (R : Carrier (k + 1) → Carrier (k + 1) → Prop)
    (hR : RelLaws R) : Code (k + 1) where
  value := V
  level := hk
  defined := hd
  relation := Extend R (RawNeutral (k + 1))
  lawful := extend_laws hR _
  point := fun name => raw (k + 1) (NeutralPER.neutralAtom name)
  point_member := fun name => Or.inr ⟨rfl, name, rfl⟩
  irrelevant := fun h => False.elim (Nat.noConfusion h)

theorem predicative_preserves (k : Nat) (V : Value)
    (hk : SortMember (some (k + 1)) V) (hd : TypeDefined V)
    (R : Carrier (k + 1) → Carrier (k + 1) → Prop) (hR : RelLaws R)
    {x y : Carrier (k + 1)} (h : R x y) :
    (predicative k V hk hd R hR).relation x y := Or.inl h

/-- A neutral type code is constructed at every finite stage. -/
def neutralCode : (k : Nat) → Nat → Code k
  | 0, name => ofCandidate
      ⟨NeutralCodes.neutralTypeValue (some 0) name,
        CandidateUniverse.predicateCandidate (fun _ => False),
        NeutralCodes.reify_level (.neutralType (some 0) name),
        NeutralCodes.reify_defined (.neutralType (some 0) name)⟩
  | k + 1, name => predicative k
      (NeutralCodes.neutralTypeValue (some (k + 1)) name)
      (NeutralCodes.reify_level (.neutralType (some (k + 1)) name))
      (NeutralCodes.reify_defined (.neutralType (some (k + 1)) name))
      (fun _ _ => False) ⟨False.elim, fun h _ => False.elim h⟩

theorem neutralCode_value (k name : Nat) :
    (view k (neutralCode k name)).value = NeutralCodes.neutralTypeValue (some k) name := by
  cases k <;> rfl

/-- The universe relation inspects retained code data, never just erasure. -/
def UniverseRel (k : Nat) : Carrier (k + 1) → Carrier (k + 1) → Prop
  | .inr A, .inr B => CodeRelated k A B
  | _, _ => False

theorem universeRel_laws (k : Nat) : RelLaws (UniverseRel k) := by
  constructor
  · intro x y h
    cases x with
    | inl v => exact False.elim h
    | inr A =>
      cases y with
      | inl v => exact False.elim h
      | inr B => exact related_symm h
  · intro x y z h g
    cases x with
    | inl v => exact False.elim h
    | inr A =>
      cases y with
      | inl v => exact False.elim h
      | inr B =>
        cases z with
        | inl v => exact False.elim g
        | inr C => exact related_trans h g

/-- The universe at k is a code at k+1. This construction refers only to
the already defined carrier and codes at k. -/
def universeCode (k : Nat) : Code (k + 1) where
  value := universeValue (some k)
  level := sort_member _ _
  defined := sort_defined _ _
  relation := UniverseRel k
  lawful := universeRel_laws k
  point := fun name => encode k (neutralCode k name)
  point_member := fun name => related_refl (view k (neutralCode k name))
  irrelevant := fun h => False.elim (Nat.noConfusion h)

theorem universe_member (k : Nat) (A : Code k) :
    (universeCode k).relation (encode k A) (encode k A) := related_refl (view k A)

theorem universe_successor_member (k : Nat) :
    (universeCode (k + 1)).relation
      (encode (k + 1) (universeCode k)) (encode (k + 1) (universeCode k)) :=
  universe_member _ _

/-- A total data-valued decoder for an actual universe member. False is
eliminated only in the impossible raw-realizer case. -/
def decodeMember (k : Nat) (x : Carrier (k + 1))
    (hx : (universeCode k).relation x x) : Code k := by
  cases x with
  | inl v => exact False.elim hx
  | inr A => exact A

theorem decodeMember_encode (k : Nat) (A : Code k) :
    decodeMember k (encode k A) (universe_member k A) = A := rfl

theorem encode_decodeMember (k : Nat) (x : Carrier (k + 1))
    (hx : (universeCode k).relation x x) : encode k (decodeMember k x hx) = x := by
  cases x with
  | inl v => exact False.elim hx
  | inr A => rfl

theorem universe_elimination (k : Nat) (x : Carrier (k + 1))
    (hx : (universeCode k).relation x x) :
    SortMember (some k) (erase (k + 1) x) ∧ TypeDefined (erase (k + 1) x) := by
  cases x with
  | inl v => exact False.elim hx
  | inr A => exact ⟨(view k A).level, (view k A).defined⟩

theorem universe_transport (k : Nat) {x y : Carrier (k + 1)}
    (h : (universeCode k).relation x y) :
    CodeRelated k
      (decodeMember k x ((universeRel_laws k).trans h ((universeRel_laws k).symm h)))
      (decodeMember k y ((universeRel_laws k).trans ((universeRel_laws k).symm h) h)) := by
  cases x with
  | inl v => exact False.elim h
  | inr A =>
    cases y with
    | inl v => exact False.elim h
    | inr B => exact h

theorem universe_reflection (k name : Nat) :
    (universeCode k).relation ((universeCode k).point name)
      ((universeCode k).point name) ∧
    SortMember (some k) (erase (k + 1) ((universeCode k).point name)) ∧
    TypeDefined (erase (k + 1) ((universeCode k).point name)) :=
  ⟨(universeCode k).point_member name,
    universe_elimination k _ ((universeCode k).point_member name)⟩

/-- At level zero the completed proof-valued product is an actual code,
with its original source Pi image retained. -/
def forallPropCode (ν : Valuation) (ρ : EnvI) : Code 0 :=
  ofCandidate (CandidatePi.forallPropCode ν ρ)

theorem forallPropCode_decode (ν : Valuation) (ρ : EnvI) :
    Same (view 0 (forallPropCode ν ρ)).relation CandidatePi.forallProp.relation :=
  CandidatePi.forallPropCode_decode ν ρ

/-- Every actual member of universe zero is decoded to exactly the
candidate data used by the impredicative product. The paired application
law therefore covers the entire universe, including neutral type codes. -/
theorem forallProp_universe_apply {f g : Value} {x y : Carrier 1}
    (hfg : CandidatePi.forallProp.relation f g)
    (hxy : (universeCode 0).relation x y) :
    (view 0 (decodeMember 0 x
      ((universeRel_laws 0).trans hxy ((universeRel_laws 0).symm hxy)))).relation
      (NeutralPi.applyValue f (erase 1 x)) (NeutralPi.applyValue g (erase 1 y)) := by
  cases x with
  | inl v => exact False.elim hxy
  | inr A =>
    cases y with
    | inl v => exact False.elim hxy
    | inr B => exact CandidatePi.forallProp_apply hfg ((zero_related_iff A B).mp hxy)

theorem forallProp_universe_apply_member {f : Value}
    (hf : Member CandidatePi.forallProp.relation f) (x : Carrier 1)
    (hx : (universeCode 0).relation x x) :
    Member (view 0 (decodeMember 0 x hx)).relation
      (NeutralPi.applyValue f (erase 1 x)) :=
  forallProp_universe_apply hf hx

/-- The source Pi image is retained in the product code, and its actual
element PER has the same paired application law over universe zero. -/
theorem forallPropCode_universe_apply (ν : Valuation) (ρ : EnvI)
    {f g : Value} {x y : Carrier 1}
    (hfg : (view 0 (forallPropCode ν ρ)).relation f g)
    (hxy : (universeCode 0).relation x y) :
    (view 0 (decodeMember 0 x
      ((universeRel_laws 0).trans hxy ((universeRel_laws 0).symm hxy)))).relation
      (NeutralPi.applyValue f (erase 1 x)) (NeutralPi.applyValue g (erase 1 y)) :=
  forallProp_universe_apply ((forallPropCode_decode ν ρ f g).mp hfg) hxy

theorem every_candidate_universe_control (C : CandidateUniverse.Candidate) (name : Nat) :
    (universeCode 0).relation
      (encode 0 (CandidatePi.ofCandidate C)) (encode 0 (CandidatePi.ofCandidate C)) ∧
    decodeMember 0 (encode 0 (CandidatePi.ofCandidate C))
      (universe_member 0 (CandidatePi.ofCandidate C)) = CandidatePi.ofCandidate C ∧
    Member (view 0 (CandidatePi.ofCandidate C)).relation
      (NeutralPi.applyValue (NeutralPER.neutralAtom name)
        (erase 1 (encode 0 (CandidatePi.ofCandidate C)))) :=
  ⟨universe_member _ _, rfl,
    forallProp_universe_apply_member (CandidatePi.forallProp_atom_member name)
      (encode 0 (CandidatePi.ofCandidate C)) (universe_member 0 (CandidatePi.ofCandidate C))⟩

end Rcic.Declarative.Ann.LR3.StratifiedCandidates

import rcic.RcicAnnLR3NativeMemberValues

/-!
# A recursively restricted tower of neutral-saturated retained codes

At positive stage k+1 the canonical reflected element retains a saturated
code at stage k. Saturation is an explicit semantic admission condition;
the new universe decodes only such admitted codes. The construction keeps
all stage-zero candidates, preserves every completed fibre's old edges,
and retains exact universe tags and data-valued decoding.

This is a finite-stage tower closed under its explicit named typed
reflections. It does not assert all elimination-neutral closure, dependent
function-PER closure, or a source evaluator attachment. In particular,
adding the shared typed points is not itself a proof that their raw
applications satisfy a product codomain. The undefined level is not
silently included in this Nat-indexed result. closure_claim = 0.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.Declarative.Ann.LR3.SaturatedTower

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily

namespace Old
abbrev Code := StratifiedCandidates.Code
abbrev Carrier := StratifiedCandidates.Carrier
end Old

/-- Only self-edges are added; every old relation edge is retained. -/
def extend (k : Nat) (points : Nat → Old.Carrier (k + 1))
    (C : Old.Code (k + 1)) : Old.Code (k + 1) where
  value := C.value
  level := C.level
  defined := C.defined
  relation := StratifiedCandidates.Extend C.relation (fun x => ∃ name, x = points name)
  lawful := StratifiedCandidates.extend_laws C.lawful _
  point := points
  point_member := fun name => Or.inr ⟨rfl, name, rfl⟩
  irrelevant := fun h => False.elim (Nat.noConfusion h)

/-- Positive-stage reflected type codes are themselves completed using
the already constructed preceding stage. No unsaturated payload is used
as a canonical universe reflection. -/
def neutralCode : (k : Nat) → Nat → Old.Code k
  | 0, name => NativeMemberValues.neutralCode 0 name
  | k + 1, name => extend k
      (fun j => StratifiedCandidates.encode k (neutralCode k j))
      (NativeMemberValues.neutralCode (k + 1) name)

def reflect : (k : Nat) → Nat → Old.Carrier k
  | 0, name => NeutralPER.neutralAtom name
  | k + 1, name => StratifiedCandidates.encode k (neutralCode k name)

def Closed (k : Nat) (C : Old.Code k) : Prop :=
  ∀ name, (StratifiedCandidates.view k C).relation (reflect k name) (reflect k name)

theorem zero_closed (C : Old.Code 0) : Closed 0 C :=
  fun name => CandidatePi.decode_reflection C (.atom name)

theorem neutralCode_closed (k name : Nat) : Closed k (neutralCode k name) := by
  cases k with
  | zero => exact zero_closed _
  | succ k => exact fun j => Or.inr ⟨rfl, j, rfl⟩

theorem neutralCode_value (k name : Nat) :
    (StratifiedCandidates.view k (neutralCode k name)).value =
      NativeMemberValues.value (some k) name := by
  cases k <;> rfl

theorem reflect_erasure (k name : Nat) :
    StratifiedCandidates.erase (k + 1) (reflect (k + 1) name) =
      NativeMemberValues.value (some k) name :=
  neutralCode_value k name

def complete : (k : Nat) → Old.Code k → Old.Code k
  | 0, C => C
  | k + 1, C => extend k (reflect (k + 1)) C

theorem complete_closed (k : Nat) (C : Old.Code k) : Closed k (complete k C) := by
  cases k with
  | zero => exact zero_closed _
  | succ k => exact fun name => Or.inr ⟨rfl, name, rfl⟩

theorem complete_preserves (k : Nat) (C : Old.Code k) {x y : Old.Carrier k}
    (h : (StratifiedCandidates.view k C).relation x y) :
    (StratifiedCandidates.view k (complete k C)).relation x y := by
  cases k with
  | zero => exact h
  | succ k => exact Or.inl h

theorem complete_value (k : Nat) (C : Old.Code k) :
    (StratifiedCandidates.view k (complete k C)).value =
      (StratifiedCandidates.view k C).value := by
  cases k <;> rfl

theorem complete_transport {k : Nat} {C D : Old.Code k}
    (h : StratifiedCandidates.CodeRelated k C D) :
    StratifiedCandidates.CodeRelated k (complete k C) (complete k D) := by
  cases k with
  | zero => exact h
  | succ k =>
      refine ⟨?_, fun name => Or.inr ⟨rfl, name, rfl⟩⟩
      intro x y
      exact or_congr (h.transport x y) Iff.rfl

/-- Semantic admission is restricted to the proved saturation condition. -/
abbrev Code (k : Nat) := {C : Old.Code k // Closed k C}

def completed (k : Nat) (C : Old.Code k) : Code k := ⟨complete k C, complete_closed k C⟩

def Relation (k : Nat) (C D : Code k) : Prop :=
  StratifiedCandidates.CodeRelated k C.1 D.1

theorem relation_laws (k : Nat) : RelLaws (Relation k) :=
  ⟨StratifiedCandidates.related_symm, StratifiedCandidates.related_trans⟩

def encode (k : Nat) (C : Code k) : Old.Carrier (k + 1) :=
  StratifiedCandidates.encode k C.1

def PayloadClosed (k : Nat) : Old.Carrier (k + 1) → Prop
  | .inl _ => False
  | .inr C => Closed k C

def UniverseRel (k : Nat) (x y : Old.Carrier (k + 1)) : Prop :=
  StratifiedCandidates.UniverseRel k x y ∧ PayloadClosed k x ∧ PayloadClosed k y

theorem universeRel_laws (k : Nat) : RelLaws (UniverseRel k) :=
  ⟨fun h => ⟨(StratifiedCandidates.universeRel_laws k).symm h.1, h.2.2, h.2.1⟩,
    fun h g => ⟨(StratifiedCandidates.universeRel_laws k).trans h.1 g.1, h.2.1, g.2.2⟩⟩

def universeBase (k : Nat) : Old.Code (k + 1) where
  value := universeValue (some k)
  level := sort_member _ _
  defined := sort_defined _ _
  relation := UniverseRel k
  lawful := universeRel_laws k
  point := reflect (k + 1)
  point_member := fun name =>
    ⟨StratifiedCandidates.universe_member k (neutralCode k name),
      neutralCode_closed k name, neutralCode_closed k name⟩
  irrelevant := fun h => False.elim (Nat.noConfusion h)

theorem universe_closed (k : Nat) : Closed (k + 1) (universeBase k) :=
  (universeBase k).point_member

def universeCode (k : Nat) : Code (k + 1) := ⟨universeBase k, universe_closed k⟩

theorem universe_member (k : Nat) (C : Code k) :
    UniverseRel k (encode k C) (encode k C) :=
  ⟨StratifiedCandidates.universe_member k C.1, C.2, C.2⟩

theorem universe_successor_member (k : Nat) :
    UniverseRel (k + 1) (encode (k + 1) (universeCode k))
      (encode (k + 1) (universeCode k)) :=
  universe_member (k + 1) (universeCode k)

/-- Every decoded payload carries the saturation proof, as data. -/
def decodeMember (k : Nat) (x : Old.Carrier (k + 1))
    (hx : UniverseRel k x x) : Code k := by
  cases x with
  | inl v => exact False.elim hx.1
  | inr C => exact ⟨C, hx.2.1⟩

theorem decode_encode (k : Nat) (C : Code k) :
    decodeMember k (encode k C) (universe_member k C) = C := rfl

theorem encode_decode (k : Nat) (x : Old.Carrier (k + 1))
    (hx : UniverseRel k x x) : encode k (decodeMember k x hx) = x := by
  cases x with
  | inl v => exact False.elim hx.1
  | inr C => rfl

theorem universe_elimination (k : Nat) (x : Old.Carrier (k + 1))
    (hx : UniverseRel k x x) :
    SortMember (some k) (StratifiedCandidates.erase (k + 1) x) ∧
      TypeDefined (StratifiedCandidates.erase (k + 1) x) :=
  StratifiedCandidates.universe_elimination k x hx.1

theorem universe_transport (k : Nat) {x y : Old.Carrier (k + 1)}
    (h : UniverseRel k x y) :
    Relation k
      (decodeMember k x ((universeRel_laws k).trans h ((universeRel_laws k).symm h)))
      (decodeMember k y ((universeRel_laws k).trans ((universeRel_laws k).symm h) h)) := by
  cases x with
  | inl v => exact False.elim h.1
  | inr C =>
      cases y with
      | inl v => exact False.elim h.1
      | inr D => exact h.1

theorem reflection_member (k : Nat) (C : Code k) (name : Nat) :
    (StratifiedCandidates.view k C.1).relation (reflect k name) (reflect k name) :=
  C.2 name

/-- Every two admitted fibres at a positive stage share the same explicit
reflected element and its exactly tagged raw image. -/
theorem shared_reflection (k : Nat) (C D : Code (k + 1)) (name : Nat) :
    (StratifiedCandidates.view (k + 1) C.1).relation
      (reflect (k + 1) name) (reflect (k + 1) name) ∧
    (StratifiedCandidates.view (k + 1) D.1).relation
      (reflect (k + 1) name) (reflect (k + 1) name) ∧
    StratifiedCandidates.erase (k + 1) (reflect (k + 1) name) =
      NativeMemberValues.value (some k) name :=
  ⟨C.2 name, D.2 name, reflect_erasure k name⟩

theorem every_candidate_retained (C : CandidatePi.Element) :
    (completed 0 C).1 = C ∧
    UniverseRel 0 (encode 0 (completed 0 C)) (encode 0 (completed 0 C)) :=
  ⟨rfl, universe_member 0 (completed 0 C)⟩

end Rcic.Declarative.Ann.LR3.SaturatedTower

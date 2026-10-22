import rcic.RcicAnnLR3IndexedFamilyDecoder
import rcic.RcicAnnLR3SelectedFamilyElimination
import rcic.RcicAnnLR3NativeMemberValues

/-!
# An indexed Acc signature over retained proposition codes

The index quotient relates retained codes, rather than their raw images.
Consequently the admitted Acc shape retains distinct recursive indices
even when those indices have equal erasures. Its functional positions
carry an actual retained guard code and legal guard values. Result and
child maps descend to quotient labels with no representative choice.

The finite source extractor supplies the actual Acc field/index pattern.
The semantic signature, neutral members, constructor trees and a
major-dependent paired eliminator are constructed here. Source evaluator
connections are stated separately; no generic source family decoder or
Conv_iota/Conv_structIota arm is asserted. `closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.Declarative.Ann.LR3.RetainedAccFamily

open Rcic.Declarative
open UnitModel TypedPER TypedStatements TypedInductive NeutralDataFamily

abbrev IndexCode := StratifiedCandidates.Code 0

def indexSetoid : Setoid IndexCode where
  r := StratifiedCandidates.CodeRelated 0
  iseqv := ⟨fun A => StratifiedCandidates.related_refl (StratifiedCandidates.view 0 A),
    StratifiedCandidates.related_symm, StratifiedCandidates.related_trans⟩

abbrev Index := Quotient indexSetoid
def classify (A : IndexCode) : Index := Quotient.mk indexSetoid A

theorem classify_related {A B : IndexCode}
    (h : StratifiedCandidates.CodeRelated 0 A B) : classify A = classify B :=
  Quotient.sound h

def falseIndex : Index := classify CandidatePi.falseElement
def trueIndex : Index := classify CandidatePi.trueElement

theorem indices_distinct : falseIndex ≠ trueIndex := by
  intro h
  exact CandidatePi.collision_not_related
    ((StratifiedCandidates.zero_related_iff _ _).mp (Quotient.exact h))

theorem distinct_indices_same_erasure :
    falseIndex ≠ trueIndex ∧
    StratifiedCandidates.erase 1 (StratifiedCandidates.encode 0 CandidatePi.falseElement) =
      StratifiedCandidates.erase 1 (StratifiedCandidates.encode 0 CandidatePi.trueElement) :=
  ⟨indices_distinct, CandidatePi.collision_same_value⟩

/-- The actual native proposition code returned by the two-argument
typed-neutral member policy at the admitted relation constant R. -/
def guardCode : IndexCode := NativeMemberValues.neutralCode 0 9
abbrev guardPER : Relation := (StratifiedCandidates.view 0 guardCode).relation

theorem guard_laws : RelLaws guardPER := (StratifiedCandidates.view 0 guardCode).lawful

theorem guard_reflection (name : Nat) : Member guardPER (NeutralPER.neutralAtom name) :=
  (StratifiedCandidates.view 0 guardCode).point_member name

theorem guard_irrelevant {x y : Value} (hx : Member guardPER x) (hy : Member guardPER y) :
    guardPER x y := (StratifiedCandidates.view 0 guardCode).irrelevant rfl x y hx hy

theorem guard_universe_member :
    (StratifiedCandidates.universeCode 0).relation
      (StratifiedCandidates.encode 0 guardCode) (StratifiedCandidates.encode 0 guardCode) :=
  StratifiedCandidates.universe_member 0 guardCode

/-- Both inner binders are retained as data. The guard member is a
proof value at the actual native retained proposition code. -/
structure Position (_q : Index) where
  recursiveCode : IndexCode
  guardValue : Value
  guardMember : Member guardPER guardValue

def positionIndex {q : Index} (p : Position q) : Index := classify p.recursiveCode

def PositionPER {q : Index} (p r : Position q) : Prop :=
  StratifiedCandidates.CodeRelated 0 p.recursiveCode r.recursiveCode ∧
    guardPER p.guardValue r.guardValue

theorem position_laws (q : Index) : RelLaws (@PositionPER q) where
  symm := fun h => ⟨StratifiedCandidates.related_symm h.1, guard_laws.symm h.2⟩
  trans := fun h g =>
    ⟨StratifiedCandidates.related_trans h.1 g.1, guard_laws.trans h.2 g.2⟩

theorem position_member {q : Index} (p : Position q) : PositionPER p p :=
  ⟨StratifiedCandidates.related_refl (StratifiedCandidates.view 0 p.recursiveCode), p.guardMember⟩

theorem positionIndex_related {q : Index} {p r : Position q} (h : PositionPER p r) :
    positionIndex p = positionIndex r := classify_related h.1

theorem positionIndex_transport {q r : Index} (h : q = r) (p : Position q) :
    positionIndex (DependentFamily.transport Position h p) = positionIndex p := by
  cases h
  rfl

theorem position_transport_value {q r : Index} (h : q = r) (p : Position q) :
    (DependentFamily.transport Position h p).recursiveCode = p.recursiveCode ∧
    (DependentFamily.transport Position h p).guardValue = p.guardValue := by
  cases h
  exact ⟨rfl, rfl⟩

def position (q : Index) (B : IndexCode) (name : Nat) : Position q :=
  ⟨B, NeutralPER.neutralAtom name, guard_reflection name⟩

def semanticData : IndexedFamilyDecoder.RawData indexSetoid Position Index where
  result := classify
  result_coherent := fun _ _ h => classify_related h
  child := fun _ p => positionIndex p
  child_coherent := fun _ _ h p => (positionIndex_transport (Quotient.sound h) p).symm

abbrev signature := IndexedFamilyDecoder.signature semanticData

theorem result_index (A : IndexCode) :
    IndexedFamilyDecoder.result semanticData (classify A) = classify A := rfl

theorem child_index (A B : IndexCode) (name : Nat) :
    IndexedFamilyDecoder.child semanticData (classify A) (position (classify A) B name) =
      classify B := rfl

def leafRel (_i : Index) (a b : Nat) : Prop := a = b
theorem leaf_laws (i : Index) : RelLaws (leafRel i) := ⟨Eq.symm, Eq.trans⟩
abbrev Legal (i : Index) := LegalTree signature (fun _ => Nat) leafRel i

def neutral (i : Index) (name : Nat) : Legal i :=
  legalNeutral signature (fun _ => Nat) leafRel i name rfl

def children (q : Index) :
    IndexedFamilyDecoder.Children semanticData (fun _ => Nat) leafRel q :=
  fun p => neutral (IndexedFamilyDecoder.child semanticData q p) 7

def major (A : IndexCode) : Legal (classify A) :=
  IndexedFamilyDecoder.nodeClass semanticData (fun _ => Nat) leafRel (classify A)
    (children (classify A))

def selected (_i : Index) (r : signature.Rule _i) : signature.Premise _i r :=
  position r.1 CandidatePi.trueElement 7

noncomputable def motive := SelectedFamilyElimination.Motive leaf_laws selected

def leafValue (_i : Index) (name : Nat) : Value := NeutralPER.neutralAtom name
def constructorValue : NeutralFamily.ConstructorOp signature :=
  fun i r children => NeutralFamily.unarySpine 11 (children (selected i r))

def pairedMajor (A : IndexCode) :
    Paired signature (fun _ => Nat) leafRel leafValue constructorValue (classify A) :=
  pair leafValue constructorValue (major A)

theorem family_laws (i : Index) :
    RelLaws (fun x y : Paired signature (fun _ => Nat) leafRel leafValue constructorValue i =>
      PairPER x y) := pairPER_laws leaf_laws i

def reflected (i : Index) (name : Nat) :
    Paired signature (fun _ => Nat) leafRel leafValue constructorValue i :=
  pair leafValue constructorValue (neutral i name)

theorem reflected_member (i : Index) (name : Nat) :
    PairPER (reflected i name) (reflected i name) := (neutral i name).2

noncomputable def eliminate {i : Index}
    (p : Paired signature (fun _ => Nat) leafRel leafValue constructorValue i) :
    motive i (pairedClass leaf_laws p) :=
  SelectedFamilyElimination.pairedPosition leaf_laws selected p

theorem eliminate_transport {i : Index}
    {p q : Paired signature (fun _ => Nat) leafRel leafValue constructorValue i}
    (h : PairPER p q) :
    DependentFamily.transport (motive i) (Quotient.sound h) (eliminate p) = eliminate q :=
  SelectedFamilyElimination.pairedPosition_transport leaf_laws selected h

theorem eliminate_major (A : IndexCode) : (eliminate (pairedMajor A)).val = 1 := rfl

/-- The admitted source has the actual indexed functional field shape
used by this construction. No arbitrary signature premise occurs here. -/
theorem source_pattern :
    Nonempty (EnvWfA noIotaA pinAccGroupEnvA) ∧
    (AdmittedFamilyExtractor.domains (pinAccIntroViewA noIotaA).typed).map
      AdmittedFamilyExtractor.DomainTask.type = [.sort .zero, .sort .zero, pinAccGuardA] ∧
    (AdmittedFamilyExtractor.indices (pinAccIntroViewA noIotaA).typed).map
      AdmittedFamilyExtractor.IndexTask.arguments = [[.bvar 1], [.bvar 0]] :=
  ⟨⟨pinAccGroupWfA noIotaA⟩, rfl, rfl⟩

/-- Every guard, recursive index, tree and eliminator input is retained
and inhabited, including distinct indices with equal raw values. -/
theorem retained_indexed_control :
    falseIndex ≠ trueIndex ∧
    StratifiedCandidates.erase 1 (StratifiedCandidates.encode 0 CandidatePi.falseElement) =
      StratifiedCandidates.erase 1 (StratifiedCandidates.encode 0 CandidatePi.trueElement) ∧
    Member guardPER (NeutralPER.neutralAtom 7) ∧
    IndexedFamilyDecoder.child semanticData falseIndex
      (position falseIndex CandidatePi.trueElement 7) = trueIndex ∧
    PairPER (pairedMajor CandidatePi.falseElement) (pairedMajor CandidatePi.falseElement) ∧
    (eliminate (pairedMajor CandidatePi.falseElement)).val = 1 :=
  ⟨indices_distinct, CandidatePi.collision_same_value, guard_reflection 7,
    rfl, (major CandidatePi.falseElement).2, rfl⟩

end Rcic.Declarative.Ann.LR3.RetainedAccFamily

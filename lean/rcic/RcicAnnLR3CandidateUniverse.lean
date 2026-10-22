import rcic.RcicAnnLR3NeutralCodes

/-!
# Constructive proposition candidates with their relations retained

Subsingleton PER candidates form an ordinary Lean type. Arbitrary
intersections, including quantification over all candidates, live in Lean
Prop. Legal-domain dependent function PERs are again candidates. These
are actual algebraic producers and require no induction-recursion.

A universe element below retains its candidate as data beside the raw
value. Its relation transports the retained element PER. Forgetting that
data cannot preserve arbitrary candidates in the existing CodeSystem:
two inhabited, neutral-extended candidates may have the same raw value
and different element relations. The final obstruction is to this erasure
interface, not to candidate semantics or to an admitted source class.

This module does not assert source fundamental soundness, complete
function reflection, or a stratified source universe. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.CandidateUniverse

open Rcic.Declarative
open UnitModel TypedPER TypedStatements
open Rcic.Declarative.NativeValleys.PiModelIdealAudit

universe u

/-- All subsingleton PERs on the existing raw value carrier. No coding
predicate, source typing derivation, or truth decision is a field. -/
structure Candidate where
  relation : Relation
  lawful : Laws relation
  irrelevant : ∀ {x y : Value}, Member relation x → Member relation y → relation x y

/-- A candidate is exactly the full relation on its membership predicate. -/
theorem candidate_iff_members (C : Candidate) (x y : Value) :
    C.relation x y ↔ Member C.relation x ∧ Member C.relation y :=
  ⟨fun h => ⟨left_member C.lawful h, right_member C.lawful h⟩,
    fun h => C.irrelevant h.1 h.2⟩

/-- An arbitrary predicate supplies a subsingleton PER constructively. -/
def predicateCandidate (P : Value → Prop) : Candidate where
  relation x y := P x ∧ P y
  lawful := ⟨fun h => ⟨h.2, h.1⟩, fun h g => ⟨h.1, g.2⟩⟩
  irrelevant := fun h g => ⟨h.1, g.1⟩

theorem predicateCandidate_member (P : Value → Prop) (x : Value) :
    Member (predicateCandidate P).relation x ↔ P x :=
  ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

/-- The index may itself be a type of candidates. The result relation is
still Prop, by Lean's impredicativity. -/
def intersection {ι : Sort u} (C : ι → Candidate) : Candidate where
  relation x y := ∀ i : ι, (C i).relation x y
  lawful :=
    ⟨fun h i => (C i).lawful.symm (h i),
      fun h g i => (C i).lawful.trans (h i) (g i)⟩
  irrelevant := fun h g i => (C i).irrelevant (h i) (g i)

theorem intersection_member_iff {ι : Sort u} (C : ι → Candidate) (x : Value) :
    Member (intersection C).relation x ↔ ∀ i : ι, Member (C i).relation x :=
  Iff.rfl

theorem intersection_apply {ι : Sort u} {C : ι → Candidate} {x y : Value}
    (h : (intersection C).relation x y) (i : ι) : (C i).relation x y := h i

theorem intersection_same {ι : Sort u} {C D : ι → Candidate}
    (h : ∀ i : ι, Same (C i).relation (D i).relation) :
    Same (intersection C).relation (intersection D).relation := by
  intro x y
  exact ⟨fun hc i => (h i x y).mp (hc i), fun hd i => (h i x y).mpr (hd i)⟩

/-- A dependent legal-domain function relation is subsingleton when all
its fibres are. No quantification over illegal raw arguments is added. -/
def functionCandidate (app : Value → Value → Value) (D : Relation)
    (hD : Laws D) (C : Value → Candidate)
    (coherent : FamilyCoherent D (fun x => (C x).relation)) : Candidate where
  relation := FunctionPER app D (fun x => (C x).relation)
  lawful := functionPER_laws app hD (fun x _ => (C x).lawful) coherent
  irrelevant := by
    intro f g hf hg x y hxy
    have hx := left_member hD hxy
    have hy := right_member hD hxy
    have hfx : Member (C x).relation (app f x) := hf x x hx
    have hgy : Member (C x).relation (app g y) :=
      (coherent x y hxy _ _).mpr (hg y y hy)
    exact (C x).irrelevant hfx hgy

theorem functionCandidate_apply {app : Value → Value → Value} {D : Relation}
    {hD : Laws D} {C : Value → Candidate}
    {coherent : FamilyCoherent D (fun x => (C x).relation)}
    {f g x y : Value}
    (hfg : (functionCandidate app D hD C coherent).relation f g)
    (hxy : D x y) : (C x).relation (app f x) (app g y) := hfg x y hxy

/-- The neutral support used here is common atom support. It is weaker
than complete reflection of eliminations and dependent function values. -/
structure NeutralCandidate extends Candidate where
  reflect : ∀ name : Nat, Member relation (NeutralPER.neutralAtom name)

def neutralIntersection {ι : Sort u} (C : ι → NeutralCandidate) : NeutralCandidate where
  toCandidate := intersection (fun i => (C i).toCandidate)
  reflect := fun name i => (C i).reflect name

/-- Quantification over every neutral candidate is a genuine constructive
intersection, with one supplied common neutral member at every name. -/
def allNeutralCandidates : NeutralCandidate := neutralIntersection (fun C : NeutralCandidate => C)

theorem allNeutralCandidates_member (name : Nat) :
    Member allNeutralCandidates.relation (NeutralPER.neutralAtom name) :=
  allNeutralCandidates.reflect name

def proofCandidate (P : Prop) : NeutralCandidate where
  relation := NeutralPER.ProofPER NeutralCodes.Neutral P
  lawful := NeutralPER.proofPER_laws _ _
  irrelevant := NeutralPER.proofPER_irrelevant
  reflect := fun name => NeutralPER.neutral_member _ _
    ⟨name, NeutralPER.neutralAtom_is_neutral name⟩

theorem proofCandidate_unit :
    Member (proofCandidate True).relation (unitValue EnvI.bot) :=
  NeutralPER.unit_member_of_truth _ True.intro

theorem proofCandidate_false_no_unit :
    ¬ Member (proofCandidate False).relation (unitValue EnvI.bot) := by
  intro h
  obtain ⟨name, hn⟩ := (NeutralPER.false_member_iff NeutralCodes.Neutral _).mp h
  exact NeutralPER.unit_not_atomNeutral name hn

theorem proofCandidates_not_same :
    ¬ Same (proofCandidate False).relation (proofCandidate True).relation := by
  intro h
  exact proofCandidate_false_no_unit ((h _ _).mpr proofCandidate_unit)

theorem allNeutralCandidates_no_unit :
    ¬ Member allNeutralCandidates.relation (unitValue EnvI.bot) :=
  fun h => proofCandidate_false_no_unit (h (proofCandidate False))

/-- A candidate-bearing universe element retains the exact proposition
tag and the chosen PER as ordinary data, without selecting it from Prop. -/
structure Element where
  value : Value
  candidate : NeutralCandidate
  level : SortMember (some 0) value
  defined : TypeDefined value

def ElementRel (x y : Element) : Prop := Same x.candidate.relation y.candidate.relation

theorem elementRel_refl (x : Element) : ElementRel x x := fun _ _ => Iff.rfl

theorem elementRel_symm {x y : Element} (h : ElementRel x y) : ElementRel y x :=
  fun a b => (h a b).symm

theorem elementRel_trans {x y z : Element} (h : ElementRel x y)
    (g : ElementRel y z) : ElementRel x z := fun a b => (h a b).trans (g a b)

def decode (x : Element) : Relation := x.candidate.relation

theorem decode_laws (x : Element) : Laws (decode x) := x.candidate.lawful

theorem decode_transport {x y : Element} (h : ElementRel x y) :
    Same (decode x) (decode y) := h

theorem decode_reflection (x : Element) (name : Nat) :
    Member (decode x) (NeutralPER.neutralAtom name) := x.candidate.reflect name

/-- Both candidates below have this same exact-level, defined raw code.
The semantic pair, rather than its erased value, distinguishes them. -/
def collisionValue : Value := NeutralCodes.neutralTypeValue (some 0) 902

theorem collisionValue_level : SortMember (some 0) collisionValue :=
  NeutralCodes.reify_level (.neutralType (some 0) 902)

theorem collisionValue_defined : TypeDefined collisionValue :=
  NeutralCodes.reify_defined (.neutralType (some 0) 902)

def falseElement : Element :=
  ⟨collisionValue, proofCandidate False, collisionValue_level, collisionValue_defined⟩

def trueElement : Element :=
  ⟨collisionValue, proofCandidate True, collisionValue_level, collisionValue_defined⟩

theorem collision_same_value : falseElement.value = trueElement.value := rfl

theorem collision_not_related : ¬ ElementRel falseElement trueElement :=
  proofCandidates_not_same

/-- Precisely the extra demand made when candidate data is erased before
the old CodeSystem sees it. No source fundamental theorem is a premise. -/
def ErasureSupply (C : CodeSystem) : Prop :=
  ∀ x : Element, C.Code (some 0) x.value (decode x)

theorem no_erasureSupply (C : CodeSystem) : ¬ ErasureSupply C := by
  intro supply
  exact collision_not_related (C.coherent (supply falseElement) (supply trueElement))

theorem concrete_erasure_boundary : ¬ ErasureSupply NeutralCodes.codeSystem :=
  no_erasureSupply NeutralCodes.codeSystem

/-- All non-obstructed data in the erasure counterinstance are supplied:
exact tags, definedness, PER laws, irrelevance and neutral inhabitants of
both candidates. The distinguishing unit also genuinely exists. -/
theorem collision_inhabited (name : Nat) :
    SortMember (some 0) falseElement.value ∧ TypeDefined falseElement.value ∧
    SortMember (some 0) trueElement.value ∧ TypeDefined trueElement.value ∧
    Laws (decode falseElement) ∧ Laws (decode trueElement) ∧
    Member (decode falseElement) (NeutralPER.neutralAtom name) ∧
    Member (decode trueElement) (NeutralPER.neutralAtom name) ∧
    Member (decode trueElement) (unitValue EnvI.bot) ∧
    ¬ Member (decode falseElement) (unitValue EnvI.bot) ∧
    falseElement.value = trueElement.value ∧ ¬ ElementRel falseElement trueElement :=
  ⟨falseElement.level, falseElement.defined, trueElement.level, trueElement.defined,
    decode_laws _, decode_laws _, decode_reflection _ name, decode_reflection _ name,
    proofCandidate_unit, proofCandidate_false_no_unit, collision_same_value,
    collision_not_related⟩

/-- Minimal candidate assignment data for proposition variables. This is
not yet a realization of all source contexts. -/
abbrev Assignment := Nat → Element

def Assignment.erase (ρ : Assignment) : EnvI := fun i => (ρ i).value

def AssignmentRel (ρ σ : Assignment) : Prop := ∀ i : Nat, ElementRel (ρ i) (σ i)

theorem assignmentRel_refl (ρ : Assignment) : AssignmentRel ρ ρ :=
  fun i => elementRel_refl (ρ i)

theorem assignmentRel_symm {ρ σ : Assignment} (h : AssignmentRel ρ σ) :
    AssignmentRel σ ρ := fun i => elementRel_symm (h i)

theorem assignmentRel_trans {ρ σ τ : Assignment} (h : AssignmentRel ρ σ)
    (g : AssignmentRel σ τ) : AssignmentRel ρ τ :=
  fun i => elementRel_trans (h i) (g i)

def Assignment.cons (x : Element) (ρ : Assignment) : Assignment
  | 0 => x
  | i + 1 => ρ i

theorem assignmentRel_cons {ρ σ : Assignment} {x y : Element}
    (hxy : ElementRel x y) (h : AssignmentRel ρ σ) :
    AssignmentRel (Assignment.cons x ρ) (Assignment.cons y σ) := by
  intro i
  cases i with
  | zero => exact hxy
  | succ i => exact h i

theorem assignment_erase_cons (x : Element) (ρ : Assignment) :
    (Assignment.cons x ρ).erase = EnvI.cons x.value ρ.erase := by
  funext i
  cases i <;> rfl

theorem assignment_lookup_transport {ρ σ : Assignment} (h : AssignmentRel ρ σ)
    (i : Nat) : Same (decode (ρ i)) (decode (σ i)) := h i

theorem assignment_lookup_reflection (ρ : Assignment) (i name : Nat) :
    Member (decode (ρ i)) (NeutralPER.neutralAtom name) := decode_reflection _ _

def falseAssignment : Assignment := fun _ => falseElement
def trueAssignment : Assignment := fun _ => trueElement

theorem assignment_collision_erasure : falseAssignment.erase = trueAssignment.erase := rfl

theorem assignment_collision_not_related : ¬ AssignmentRel falseAssignment trueAssignment :=
  fun h => collision_not_related (h 0)

/-- A lookup decoder that sees only the old EnvI has lost information
needed to recover the PER retained by the candidate assignment. -/
def RawAssignmentDecoder (D : EnvI → Nat → Relation) : Prop :=
  ∀ (ρ : Assignment) (i : Nat), Same (D ρ.erase i) (decode (ρ i))

theorem no_rawAssignmentDecoder (D : EnvI → Nat → Relation) :
    ¬ RawAssignmentDecoder D := by
  intro h
  have hf := h falseAssignment 0
  have ht := h trueAssignment 0
  apply collision_not_related
  intro x y
  exact (hf x y).symm.trans (ht x y)

/-- The source context at issue is admitted and well formed. These source
facts do not assert that either candidate assignment has already been
connected to the complete source realization interface. -/
def propContext : LCtxA := [.assumption (.sort .zero)]

def propContext_admitted : EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA := .empty

def propContext_wf : CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 propContext :=
  .assumption .nil (.sort [] .zero)

def propVariable_typed :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 propContext (.bvar 0) (.sort .zero) :=
  .bvar _ 0 (.sort .zero) (.succ .zero) rfl (.sort _ .zero)

theorem assignment_variable_images_equal (ν : Valuation) :
    UnitModel.denote ν falseAssignment.erase (.bvar 0) =
      UnitModel.denote ν trueAssignment.erase (.bvar 0) := rfl

theorem assignment_source_control :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 propContext) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 propContext
      (.bvar 0) (.sort .zero)) ∧
    AssignmentRel falseAssignment falseAssignment ∧
    AssignmentRel trueAssignment trueAssignment ∧
    falseAssignment.erase = trueAssignment.erase ∧
    ¬ AssignmentRel falseAssignment trueAssignment :=
  ⟨⟨propContext_admitted⟩, ⟨propContext_wf⟩, ⟨propVariable_typed⟩,
    assignmentRel_refl _, assignmentRel_refl _, assignment_collision_erasure,
    assignment_collision_not_related⟩

end Rcic.Declarative.Ann.LR3.CandidateUniverse

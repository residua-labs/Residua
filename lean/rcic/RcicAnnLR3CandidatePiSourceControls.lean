import rcic.RcicAnnLR3CandidatePi
import rcic.RcicAnnLR3EnvironmentEvalComposition

/-!
# An admitted open application with retained proposition candidates

The concrete context is `P : Prop, f : (forall Q : Prop, Q)` and the
application is `f P : P`. Every original subsingleton candidate supplies
an interpretation of P, including the empty candidate. The function is
an actual neutral value. Source formation, both exact variable images,
the actual evaluator application image and its result PER membership
are supplied together. Related retained candidates give the paired
application relation.

These are finite source controls, not the general variable or application
constructor arms. No global source realization, dependent substitution,
universe-valued semantic function or Fundamental theorem is supplied or
assumed. `closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Rcic.Declarative.Ann.LR3.CandidatePiSourceControls

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open CandidateUniverse (Candidate)

abbrev context : LCtxA :=
  [.assumption EqLargeFixture.parameter, .assumption (.sort .zero)]

abbrev proposition : ExprA := .bvar 1
abbrev function : ExprA := .bvar 0
abbrev application : ExprA := .app function proposition

def admitted : EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA := .empty

def context_wf : CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 context :=
  .assumption (.assumption .nil (.sort [] .zero)) EqLargeFixture.parameterTyped

def proposition_typed :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 context proposition (.sort .zero) :=
  .bvar context 1 (.sort .zero) EqLargeFixture.one rfl (.sort context .zero)

def function_typed :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 context function EqLargeFixture.parameter :=
  .bvar context 0 EqLargeFixture.parameter .zero rfl EqLargeFixture.parameterTyped

def application_typed :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 context application proposition :=
  .app context function proposition (.sort .zero) (.bvar 0)
    EqLargeFixture.one .zero .zero
    (.bvar _ 0 (.sort .zero) EqLargeFixture.one rfl (.sort _ .zero))
    proposition_typed function_typed proposition_typed

/-- The candidate remains a separate parameter of the semantic assignment,
even though every candidate here has the same raw proposition image. -/
def rawEnvironment (C : Candidate) (name : Nat) : EnvI :=
  EnvI.cons (NeutralPER.neutralAtom name)
    (EnvI.cons (CandidatePi.ofCandidate C).value EnvI.bot)

theorem proposition_value_bot (C : Candidate) : (CandidatePi.ofCandidate C).value .bot :=
  Or.inl rfl

theorem function_value_bot (name : Nat) : NeutralPER.neutralAtom name .bot :=
  .bot EnvI.bot (.const name [])

/-- Exact lookup for this one concrete binding, including its supplied
bottom observation. This is not a general source variable arm. -/
theorem denote_function (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Candidate) (name : Nat) :
    ValueEq (EnvironmentEval.denote emptyEnvA F ν (rawEnvironment C name) function)
      (NeutralPER.neutralAtom name) := by
  apply (EnvironmentEval.denote_core emptyEnvA F ν (rawEnvironment C name)
    (e := function) True.intro).trans
  intro c
  constructor
  · intro hc
    rcases approxI_bvar_inv hc with h | h
    · cases h
      exact function_value_bot name
    · exact h
  · intro hc
    exact .bvar hc

theorem denote_proposition (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Candidate) (name : Nat) :
    ValueEq (EnvironmentEval.denote emptyEnvA F ν (rawEnvironment C name) proposition)
      (CandidatePi.ofCandidate C).value := by
  apply (EnvironmentEval.denote_core emptyEnvA F ν (rawEnvironment C name)
    (e := proposition) True.intro).trans
  intro c
  constructor
  · intro hc
    rcases approxI_bvar_inv hc with h | h
    · cases h
      exact proposition_value_bot C
    · exact h
  · intro hc
    exact .bvar hc

theorem denote_application (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Candidate) (name : Nat) :
    ValueEq (EnvironmentEval.denote emptyEnvA F ν (rawEnvironment C name) application)
      (NeutralPi.applyValue (NeutralPER.neutralAtom name) (CandidatePi.ofCandidate C).value) :=
  (EnvironmentEval.denote_application emptyEnvA F ν (rawEnvironment C name)
    function proposition).trans
      (NeutralPi.applyValue_congr (denote_function F ν C name) (denote_proposition F ν C name))

theorem proposition_image_level (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Candidate) (name : Nat) :
    SortMember (some 0)
      (EnvironmentEval.denote emptyEnvA F ν (rawEnvironment C name) proposition) :=
  sortMember_congr (denote_proposition F ν C name).symm (CandidatePi.ofCandidate C).level

theorem proposition_image_defined (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Candidate) (name : Nat) :
    TypeDefined (EnvironmentEval.denote emptyEnvA F ν (rawEnvironment C name) proposition) :=
  typeDefined_congr (denote_proposition F ν C name).symm (CandidatePi.ofCandidate C).defined

/-- The exact raw image of this fixed function type is attached to its
supplied candidate product. This remains a finite code attachment. -/
def functionTypeCode (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Candidate) (name : Nat) : CandidatePi.Element where
  value := EnvironmentEval.denote emptyEnvA F ν (rawEnvironment C name) EqLargeFixture.parameter
  candidate := CandidatePi.forallProp.toCandidate
  level := sortMember_congr
    (EnvironmentEval.denote_core emptyEnvA F ν (rawEnvironment C name)
      (e := EqLargeFixture.parameter) ⟨True.intro, True.intro⟩).symm
    (fixture_parameter_member ν (rawEnvironment C name))
  defined := typeDefined_congr
    (EnvironmentEval.denote_core emptyEnvA F ν (rawEnvironment C name)
      (e := EqLargeFixture.parameter) ⟨True.intro, True.intro⟩).symm
    (fixture_parameter_defined ν (rawEnvironment C name))

theorem functionTypeCode_decode (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Candidate) (name : Nat) :
    Same (CandidatePi.decode (functionTypeCode F ν C name)) CandidatePi.forallProp.relation :=
  CandidatePi.complete_fixed CandidatePi.forallProp

theorem function_image_member (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Candidate) (name : Nat) :
    Member (CandidatePi.decode (functionTypeCode F ν C name))
      (EnvironmentEval.denote emptyEnvA F ν (rawEnvironment C name) function) := by
  rw [NeutralCodes.valueEq_eq (denote_function F ν C name)]
  exact (functionTypeCode_decode F ν C name _ _).mpr (CandidatePi.forallProp_atom_member name)

/-- Paired support for this explicit assignment. Its diagonal is supplied
for every original candidate without a generic realization assumption. -/
def AssignmentRel (C D : Candidate) (leftName rightName : Nat) : Prop :=
  CandidatePi.ElementRel (CandidatePi.ofCandidate C) (CandidatePi.ofCandidate D) ∧
    CandidatePi.forallProp.relation (NeutralPER.neutralAtom leftName)
      (NeutralPER.neutralAtom rightName)

theorem assignmentRel_of_candidates {C D : Candidate}
    (hCD : Same (CandidatePi.complete C).relation (CandidatePi.complete D).relation)
    (leftName rightName : Nat) : AssignmentRel C D leftName rightName :=
  ⟨hCD, CandidatePi.forallProp_irrelevant (CandidatePi.forallProp_atom_member leftName)
    (CandidatePi.forallProp_atom_member rightName)⟩

theorem assignmentRel_self (C : Candidate) (name : Nat) : AssignmentRel C C name name :=
  assignmentRel_of_candidates (fun _ _ => Iff.rfl) name name

theorem paired_application_related (F G : EnvironmentEval.FamilySyntax)
    (ν μ : Valuation) {C D : Candidate} {leftName rightName : Nat}
    (h : AssignmentRel C D leftName rightName) :
    CandidatePi.decode (CandidatePi.ofCandidate C)
      (EnvironmentEval.denote emptyEnvA F ν (rawEnvironment C leftName) application)
      (EnvironmentEval.denote emptyEnvA G μ (rawEnvironment D rightName) application) := by
  rw [NeutralCodes.valueEq_eq (denote_application F ν C leftName),
    NeutralCodes.valueEq_eq (denote_application G μ D rightName)]
  exact CandidatePi.forallProp_apply h.2 h.1

theorem application_image_member (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Candidate) (name : Nat) :
    Member (CandidatePi.decode (CandidatePi.ofCandidate C))
      (EnvironmentEval.denote emptyEnvA F ν (rawEnvironment C name) application) :=
  paired_application_related F F ν ν (assignmentRel_self C name)

/-- Every premise in this admitted source application is supplied. The
semantic quantifier is the full type of original candidates, not a
selected inhabited subclass. -/
theorem every_candidate_source_control (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Candidate) (name : Nat) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 context) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 context proposition (.sort .zero)) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 context function EqLargeFixture.parameter) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 context application proposition) ∧
    AssignmentRel C C name name ∧
    ValueEq (EnvironmentEval.denote emptyEnvA F ν (rawEnvironment C name) proposition)
      (CandidatePi.ofCandidate C).value ∧
    Member (CandidatePi.decode (functionTypeCode F ν C name))
      (EnvironmentEval.denote emptyEnvA F ν (rawEnvironment C name) function) ∧
    Member (CandidatePi.decode (CandidatePi.ofCandidate C))
      (EnvironmentEval.denote emptyEnvA F ν (rawEnvironment C name) application) :=
  ⟨⟨admitted⟩, ⟨context_wf⟩, ⟨proposition_typed⟩, ⟨function_typed⟩,
    ⟨application_typed⟩, assignmentRel_self C name, denote_proposition F ν C name,
    function_image_member F ν C name, application_image_member F ν C name⟩

theorem same_raw_environment (C D : Candidate) (name : Nat) :
    rawEnvironment C name = rawEnvironment D name := rfl

/-- The same evaluator assignment supports both original candidates,
while the retained result fibres remain distinct and inhabited. -/
theorem collision_source_control (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (name : Nat) :
    AssignmentRel (CandidateUniverse.proofCandidate False).toCandidate
      (CandidateUniverse.proofCandidate False).toCandidate name name ∧
    AssignmentRel (CandidateUniverse.proofCandidate True).toCandidate
      (CandidateUniverse.proofCandidate True).toCandidate name name ∧
    rawEnvironment (CandidateUniverse.proofCandidate False).toCandidate name =
      rawEnvironment (CandidateUniverse.proofCandidate True).toCandidate name ∧
    Member (CandidatePi.decode CandidatePi.falseElement)
      (EnvironmentEval.denote emptyEnvA F ν
        (rawEnvironment (CandidateUniverse.proofCandidate False).toCandidate name) application) ∧
    Member (CandidatePi.decode CandidatePi.trueElement)
      (EnvironmentEval.denote emptyEnvA F ν
        (rawEnvironment (CandidateUniverse.proofCandidate True).toCandidate name) application) ∧
    ¬ CandidatePi.ElementRel CandidatePi.falseElement CandidatePi.trueElement :=
  ⟨assignmentRel_self _ _, assignmentRel_self _ _, rfl,
    application_image_member _ _ _ _, application_image_member _ _ _ _,
    CandidatePi.collision_not_related⟩

end Rcic.Declarative.Ann.LR3.CandidatePiSourceControls

import rcic.RcicAnnEqLargeFixture
import rcic.RcicAnnLR3GuardDecision
import rcic.RcicAnnLR3GuardedCodeRead
import rcic.RcicAnnLR3TaggedKPiFixture
import rcic.RcicAnnLR3TaggedKEvaluation

/- An admitted open Eq index context. closure_claim = 0.
   Source formation and retained semantic index assignments are constructed
   below. This does not yet prove their whole-language evaluation/reading
   adequacy or construct a reader for arbitrary source expressions. -/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.GuardedReaderSource

abbrev indexContext : LCtxA :=
  [.assumption (.sort .zero), .assumption (.sort .zero)]

abbrev leftIndex : ExprA := .bvar 1
abbrev rightIndex : ExprA := .bvar 0

def indexContextWf :
    CtxWfA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 indexContext :=
  .assumption
    (.assumption .nil (.sort [] .zero))
    (.sort [.assumption (.sort .zero)] .zero)

def leftIndexTyped :
    HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      indexContext leftIndex (.sort .zero) :=
  .bvar indexContext 1 (.sort .zero) (.succ .zero) rfl
    (.sort indexContext .zero)

def rightIndexTyped :
    HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      indexContext rightIndex (.sort .zero) :=
  .bvar indexContext 0 (.sort .zero) (.succ .zero) rfl
    (.sort indexContext .zero)

abbrev equalityType : ExprA := EqLargeFixture.eqAt leftIndex rightIndex

def equalityTypeTyped :
    HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      indexContext equalityType (.sort .zero) :=
  EqLargeFixture.eqTyped indexContextWf leftIndexTyped rightIndexTyped

abbrev proofContext : LCtxA :=
  [.assumption equalityType, .assumption (.sort .zero), .assumption (.sort .zero)]

def proofContextWf :
    CtxWfA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 proofContext :=
  .assumption indexContextWf equalityTypeTyped

abbrev liftedLeftIndex : ExprA := .bvar 2
abbrev liftedRightIndex : ExprA := .bvar 1
abbrev proofTerm : ExprA := .bvar 0
abbrev liftedEqualityType : ExprA :=
  EqLargeFixture.eqAt liftedLeftIndex liftedRightIndex

def liftedLeftIndexTyped :
    HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      proofContext liftedLeftIndex (.sort .zero) :=
  .bvar proofContext 2 (.sort .zero) (.succ .zero) rfl
    (.sort proofContext .zero)

def liftedRightIndexTyped :
    HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      proofContext liftedRightIndex (.sort .zero) :=
  .bvar proofContext 1 (.sort .zero) (.succ .zero) rfl
    (.sort proofContext .zero)

def liftedEqualityTypeTyped :
    HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      proofContext liftedEqualityType (.sort .zero) :=
  EqLargeFixture.eqTyped proofContextWf liftedLeftIndexTyped liftedRightIndexTyped

def proofTermTyped :
    HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      proofContext proofTerm liftedEqualityType :=
  .bvar proofContext 0 liftedEqualityType .zero rfl liftedEqualityTypeTyped

theorem source_indices_distinct : leftIndex ≠ rightIndex := by
  intro h
  cases h

theorem lifted_source_indices_distinct : liftedLeftIndex ≠ liftedRightIndex := by
  intro h
  cases h

/-- The Type-valued environment admission is retained as data. -/
structure OpenEqSource where
  admitted : EnvWfA (iotaIfaceA EqLargeFixture.env) EqLargeFixture.env
  contextWf :
    CtxWfA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 proofContext
  leftTyped :
    HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      proofContext liftedLeftIndex (.sort .zero)
  rightTyped :
    HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      proofContext liftedRightIndex (.sort .zero)
  equalityTyped :
    HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      proofContext liftedEqualityType (.sort .zero)
  majorTyped :
    HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0
      proofContext proofTerm liftedEqualityType

def sourceData (h : EnvWfA (iotaIfaceA EqLargeFixture.env) EqLargeFixture.env) : OpenEqSource :=
  ⟨h, proofContextWf, liftedLeftIndexTyped, liftedRightIndexTyped,
    liftedEqualityTypeTyped, proofTermTyped⟩

theorem inhabited_open_eq_source : Nonempty OpenEqSource := by
  rcases EqLargeFixture.wf with ⟨h⟩
  exact ⟨sourceData h⟩

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TaggedSaturatedTower

/-- Retained universe elements and a neutral-extended proof of their semantic
Eq. This is an explicit semantic input class, not a full context fundamental
lemma or an arbitrary attachment to the result of a source expression. -/
structure IndexAssignment where
  left : Code.{0} 0
  right : Code.{0} 0
  major : Value
  major_member : Member
    (NeutralPER.ProofPER CandidatePi.Neutral (CodeRelated left right)) major

def guard (a : IndexAssignment) : Prop :=
  (universeCode.{0} 0).view.relation a.left a.right

theorem indices_universe_members (a : IndexAssignment) :
    (universeCode.{0} 0).view.relation a.left a.left ∧
    (universeCode.{0} 0).view.relation a.right a.right :=
  ⟨universe_member 0 a.left, universe_member 0 a.right⟩

def propositionAssignment (P : Prop) (name : Nat) : IndexAssignment where
  left := GuardDecision.propCode P
  right := GuardDecision.propCode True
  major := NeutralPER.neutralAtom name
  major_member := NeutralPER.neutral_member _ _ (.atom name)

theorem proposition_guard_iff (P : Prop) (name : Nat) :
    guard (propositionAssignment P name) ↔ P :=
  GuardDecision.propCode_related_true_iff P

/-- The raw environment has the same order as proofContext. Retained codes
are separate data; erasing them does not determine their semantic equality. -/
def rawEnvironment (a : IndexAssignment) : EnvI :=
  EnvI.cons a.major (EnvI.cons a.right.view.value
    (EnvI.cons a.left.view.value EnvI.bot))

theorem raw_major (a : IndexAssignment) : rawEnvironment a 0 = a.major := rfl

theorem raw_right (a : IndexAssignment) : rawEnvironment a 1 = a.right.view.value := rfl

theorem raw_left (a : IndexAssignment) : rawEnvironment a 2 = a.left.view.value := rfl

theorem proposition_raw_environments_same (P Q : Prop) (name : Nat) :
    rawEnvironment (propositionAssignment P name) =
      rawEnvironment (propositionAssignment Q name) := rfl

/-- The type-variable part of the retained environment has ordinary variable
lookup. No result code is chosen from a raw image. -/
def retainedIndex (a : IndexAssignment) : Nat → Option (Code.{0} 0)
  | 1 => some a.right
  | 2 => some a.left
  | _ => none

def readIndex (a : IndexAssignment) : ExprA → Option (Code.{0} 0)
  | .bvar i => retainedIndex a i
  | _ => none

theorem read_left (a : IndexAssignment) :
    readIndex a liftedLeftIndex = some a.left := rfl

theorem read_right (a : IndexAssignment) :
    readIndex a liftedRightIndex = some a.right := rfl

/-- Actual evaluator agreement for a variable whose supplied value contains
bottom; the condition is proved for each concrete assignment below. -/
theorem variable_image (ν : Valuation) (ρ : EnvI) (i : Nat) (hb : ρ i .bot) :
    ValueEq (TaggedKEvaluation.image ν ρ (.bvar i)) (ρ i) := by
  apply (TaggedKEvaluation.denote_agrees ν ρ (e := .bvar i) True.intro).trans
  intro c
  change ApproxI ρ (.bvar i) c ↔ ρ i c
  constructor
  · intro h
    rcases approxI_bvar_inv h with he | hv
    · subst c
      exact hb
    · exact hv
  · exact ApproxI.bvar

theorem proposition_left_image (ν : Valuation) (P : Prop) (name : Nat) :
    ValueEq (TaggedKEvaluation.image ν
      (rawEnvironment (propositionAssignment P name)) liftedLeftIndex)
      (GuardDecision.propCode P).view.value :=
  variable_image ν _ 2 (Or.inl rfl)

theorem proposition_right_image (ν : Valuation) (P : Prop) (name : Nat) :
    ValueEq (TaggedKEvaluation.image ν
      (rawEnvironment (propositionAssignment P name)) liftedRightIndex)
      (GuardDecision.propCode True).view.value :=
  variable_image ν _ 1 (Or.inl rfl)

theorem proposition_major_image (ν : Valuation) (P : Prop) (name : Nat) :
    ValueEq (TaggedKEvaluation.image ν
      (rawEnvironment (propositionAssignment P name)) proofTerm)
      (NeutralPER.neutralAtom name) :=
  variable_image ν _ 0 (ApproxI.bot EnvI.bot (.const name []))

structure OpenEqInput where
  source : OpenEqSource
  assignment : IndexAssignment

def sourceInput (hE : EnvWfA (iotaIfaceA EqLargeFixture.env) EqLargeFixture.env)
    (P : Prop) (name : Nat) : OpenEqInput :=
  ⟨sourceData hE, propositionAssignment P name⟩

theorem inhabited_proposition_input (P : Prop) (name : Nat) :
    ∃ i : OpenEqInput, i.assignment = propositionAssignment P name := by
  obtain ⟨hE⟩ := EqLargeFixture.wf
  exact ⟨sourceInput hE P name, rfl⟩

/-- Related retained indices preserve the canonical guard, without assuming
that their raw images alone determine the retained code. -/
def IndexRel (a b : IndexAssignment) : Prop :=
  CodeRelated a.left b.left ∧ CodeRelated a.right b.right

theorem guard_congr {a b : IndexAssignment} (h : IndexRel a b) :
    guard a ↔ guard b := by
  change CodeRelated a.left a.right ↔ CodeRelated b.left b.right
  have laws := codeRelated_laws 0
  exact ⟨fun hg => laws.trans (laws.symm h.1) (laws.trans hg h.2),
    fun hg => laws.trans h.1 (laws.trans hg (laws.symm h.2))⟩

def Reads (a : IndexAssignment) (minor : Code.{0} 1) (name : Nat)
    (C : Code.{0} 1) : Prop :=
  GuardedCodeRead.Read (guard a) minor (Code.neutral 1 name) C

theorem reads_functional {a : IndexAssignment} {minor : Code.{0} 1}
    {name : Nat} {C D : Code.{0} 1}
    (hC : Reads a minor name C) (hD : Reads a minor name D) : C = D :=
  GuardedCodeRead.functional hC hD

theorem reads_related {a b : IndexAssignment} {minor other : Code.{0} 1}
    {name : Nat} {C D : Code.{0} 1}
    (h : IndexRel a b) (hm : CodeRelated minor other)
    (hC : Reads a minor name C) (hD : Reads b other name D) :
    CodeRelated C D :=
  GuardedCodeRead.related_of_components (guard_congr h) hm (codeRelated_refl _) hC hD

theorem proposition_read_exists_iff (P : Prop) (minor : Code.{0} 1)
    (majorName callName : Nat) :
    (∃ C, Reads (propositionAssignment P majorName) minor callName C) ↔ P ∨ ¬ P := by
  rw [show (∃ C, Reads (propositionAssignment P majorName) minor callName C) ↔
    guard (propositionAssignment P majorName) ∨
      ¬ guard (propositionAssignment P majorName) from
    GuardedCodeRead.exists_iff _ _ _]
  exact or_congr (proposition_guard_iff P majorName)
    (not_congr (proposition_guard_iff P majorName))

theorem all_proposition_readings_iff_em (minor : Code.{0} 1)
    (majorName callName : Nat) :
    (∀ P : Prop, ∃ C, Reads (propositionAssignment P majorName) minor callName C) ↔
      (∀ P : Prop, P ∨ ¬ P) :=
  ⟨fun h P => (proposition_read_exists_iff P minor majorName callName).mp (h P),
    fun h P => (proposition_read_exists_iff P minor majorName callName).mpr (h P)⟩

/-- Inspecting a returned Pi/neutral tag makes a data reader decide its guard.
This conditional theorem does not assert that any proposition is undecidable. -/
def decision_of_pi_read {a : IndexAssignment} {minor C : Code.{0} 1} {name : Nat}
    (hm : minor.tag = .pi) (hC : Reads a minor name C) : Decidable (guard a) :=
  GuardedCodeRead.guardDecisionOfRead
    (by rw [hm]; intro h; cases h) hC

theorem pi_readers_imply_em (minor : Code.{0} 1) (hm : minor.tag = .pi)
    (majorName callName : Nat) (run : Prop → Code.{0} 1)
    (sound : ∀ P, Reads (propositionAssignment P majorName) minor callName (run P)) :
    ∀ P : Prop, P ∨ ¬ P := by
  intro P
  cases decision_of_pi_read hm (sound P) with
  | isTrue h => exact Or.inl ((proposition_guard_iff P majorName).mp h)
  | isFalse h => exact Or.inr (fun hp => h ((proposition_guard_iff P majorName).mpr hp))

/-- The semantic index class is inhabited for every P, independently of P's
truth. Only the eager G/¬G branch selection asks for excluded middle. -/
theorem inhabited_guard_class (P : Prop) (name : Nat) :
    Nonempty OpenEqSource ∧
    (∃ i : OpenEqInput, i.assignment = propositionAssignment P name) ∧
    (universeCode.{0} 0).view.relation (GuardDecision.propCode P) (GuardDecision.propCode P) ∧
    (universeCode.{0} 0).view.relation (GuardDecision.propCode True) (GuardDecision.propCode True) ∧
    Member (NeutralPER.ProofPER CandidatePi.Neutral
      (CodeRelated (GuardDecision.propCode P) (GuardDecision.propCode True)))
      (NeutralPER.neutralAtom name) ∧
    (guard (propositionAssignment P name) ↔ P) :=
  ⟨inhabited_open_eq_source, inhabited_proposition_input P name,
    GuardDecision.propCode_universe_member P,
    GuardDecision.propCode_universe_member True,
    (propositionAssignment P name).major_member, proposition_guard_iff P name⟩

end Rcic.Declarative.Ann.LR3.GuardedReaderSource

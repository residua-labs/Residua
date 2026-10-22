import rcic.RcicAnnLR3CandidateUniverse

/-!
# Neutral completion of every proposition candidate

Every subsingleton PER, including the empty candidate, has a constructive
neutral completion. The quantifier in `allCompleted` ranges over all
candidates; no candidate is removed to obtain common neutral members.
The completed intersection agrees with the intersection of all already
neutral-supported candidates. Its members are exactly the common atom
neutrals. This supplies candidate algebra, not a source interpretation of
an impredicative product or complete function reflection. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.CandidateCompletion

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements CandidateUniverse

def complete (C : Candidate) : NeutralCandidate where
  toCandidate := predicateCandidate (fun x => Member C.relation x ∨ NeutralCodes.Neutral x)
  reflect := fun name => ⟨Or.inr ⟨name, NeutralPER.neutralAtom_is_neutral name⟩,
    Or.inr ⟨name, NeutralPER.neutralAtom_is_neutral name⟩⟩

theorem complete_member_iff (C : Candidate) (x : Value) :
    Member (complete C).relation x ↔ Member C.relation x ∨ NeutralCodes.Neutral x :=
  ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

theorem complete_includes {C : Candidate} {x y : Value} (h : C.relation x y) :
    (complete C).relation x y :=
  ⟨Or.inl (left_member C.lawful h), Or.inl (right_member C.lawful h)⟩

theorem complete_non_neutral {C : Candidate} {x : Value} (hn : ¬ NeutralCodes.Neutral x) :
    Member (complete C).relation x ↔ Member C.relation x := by
  constructor
  · intro h
    rcases h.1 with h | h
    · exact h
    · exact (hn h).elim
  · intro h
    exact ⟨Or.inl h, Or.inl h⟩

theorem complete_same {C D : Candidate} (h : Same C.relation D.relation) :
    Same (complete C).relation (complete D).relation := by
  have step : ∀ x, (Member C.relation x ∨ NeutralCodes.Neutral x) ↔
      (Member D.relation x ∨ NeutralCodes.Neutral x) := by
    intro x
    exact or_congr (h x x) Iff.rfl
  intro x y
  exact and_congr (step x) (step y)

theorem neutral_member (C : NeutralCandidate) {x : Value} (hx : NeutralCodes.Neutral x) :
    Member C.relation x := by
  obtain ⟨name, h⟩ := hx
  rw [NeutralCodes.valueEq_eq h]
  exact C.reflect name

theorem complete_fixed (C : NeutralCandidate) :
    Same (complete C.toCandidate).relation C.relation := by
  intro x y
  constructor
  · intro h
    have hx : Member C.relation x := h.1.elim id (neutral_member C)
    have hy : Member C.relation y := h.2.elim id (neutral_member C)
    exact C.irrelevant hx hy
  · exact complete_includes

theorem complete_idempotent (C : Candidate) :
    Same (complete (complete C).toCandidate).relation (complete C).relation :=
  complete_fixed (complete C)

/-- The domain is literally every subsingleton PER candidate. -/
def allCompleted : NeutralCandidate := neutralIntersection complete

theorem allCompleted_member (name : Nat) :
    Member allCompleted.relation (NeutralPER.neutralAtom name) := allCompleted.reflect name

theorem allCompleted_same : Same allCompleted.relation allNeutralCandidates.relation := by
  intro x y
  constructor
  · intro h C
    exact (complete_fixed C x y).mp (h C.toCandidate)
  · intro h C
    exact h (complete C)

def emptyCandidate : Candidate := predicateCandidate (fun _ => False)

theorem emptyCandidate_no_member (x : Value) : ¬ Member emptyCandidate.relation x :=
  fun h => h.1

theorem allCompleted_member_iff_neutral (x : Value) :
    Member allCompleted.relation x ↔ NeutralCodes.Neutral x := by
  constructor
  · intro h
    rcases (h emptyCandidate).1 with he | hn
    · exact (emptyCandidate_no_member x he).elim
    · exact hn
  · intro hn C
    exact ⟨Or.inr hn, Or.inr hn⟩

theorem allCompleted_relation_iff (x y : Value) :
    allCompleted.relation x y ↔ NeutralCodes.Neutral x ∧ NeutralCodes.Neutral y := by
  exact (candidate_iff_members allCompleted.toCandidate x y).trans
    (and_congr (allCompleted_member_iff_neutral x) (allCompleted_member_iff_neutral y))

theorem completed_empty_inhabited (name : Nat) :
    Laws (complete emptyCandidate).relation ∧
    Member (complete emptyCandidate).relation (NeutralPER.neutralAtom name) ∧
    Member allCompleted.relation (NeutralPER.neutralAtom name) :=
  ⟨(complete emptyCandidate).lawful, (complete emptyCandidate).reflect name,
    allCompleted_member name⟩

end Rcic.Declarative.Ann.LR3.CandidateCompletion

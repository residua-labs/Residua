import rcic.RcicAnnLR3CandidateAction

/-!
# Actual source identity acts on every retained finite-stage code

The admitted identity lambda is interpreted by EnvironmentEval. Its
application returns the retained input code, at every finite stage.
Every original code participates through the relation-preserving bottom
completion; no candidate is selected from an existential or from a raw
value. The collision control supplies both original candidates and shows
that their distinct fibres survive the actual source application.

This is a source supplier for this family of terms, not the dispatched
general variable, application or beta arm. closure_claim = 0.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.CandidateActionSource

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements StratifiedCandidates CandidateAction

def level : Nat → Level
  | 0 => .zero
  | k + 1 => .succ (level k)

theorem level_eval (ν : Valuation) (k : Nat) : eval ν (level k) = some k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (eval ν (level k)).map (fun x => x + 1) = some (k + 1)
      rw [ih]
      rfl

def context (k : Nat) : LCtxA := [.assumption (.sort (level k))]

def identitySource (k : Nat) : ExprA := identityTerm (.sort (level k)) (.succ (level k))

def identityType (k : Nat) : ExprA :=
  .pi (.sort (level k)) (.succ (level k)) (.sort (level k)) (.succ (level k))

def application (k : Nat) : ExprA := .app (identitySource k) (.bvar 0)

def context_wf (k : Nat) : CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 (context k) :=
  .assumption .nil (.sort [] (level k))

def identity_formed (Γ : LCtxA) (k : Nat) :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 Γ (identityType k)
      (.sort (.imax (.succ (level k)) (.succ (level k)))) :=
  .pi Γ _ _ _ _ (.sort Γ _) (.sort _ _)

def identity_typed (Γ : LCtxA) (k : Nat) :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 Γ (identitySource k) (identityType k) :=
  .lam Γ (.sort (level k)) (.succ (level k)) (.bvar 0) (.sort (level k))
    (.succ (level k)) (.sort Γ _) (.sort _ _)
    (.bvar _ 0 (.sort (level k)) (.succ (level k)) rfl (.sort _ _))

def argument_typed (k : Nat) :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 (context k) (.bvar 0) (.sort (level k)) :=
  .bvar _ 0 (.sort (level k)) (.succ (level k)) rfl (.sort _ _)

def application_typed (k : Nat) :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 (context k) (application k)
      (.sort (level k)) :=
  .app _ _ _ (.sort (level k)) (.sort (level k))
    (.succ (level k)) (.succ (level k)) (.succ (level k))
    (.sort _ _) (.sort _ _) (identity_typed _ k) (argument_typed k)

def environment {k : Nat} (C : ClosedCode k) : EnvI := EnvI.cons (eraseCode C) EnvI.bot

def action (F : EnvironmentEval.FamilySyntax) (ν : Valuation) {k : Nat}
    (C : ClosedCode k) : Action (ClosedCode k) eraseCode CodeRel k :=
  identity emptyEnvA F ν (environment C) (.sort (level k)) (.succ (level k)) k

theorem application_erasure (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    {k : Nat} (C : ClosedCode k) :
    ValueEq (EnvironmentEval.denote emptyEnvA F ν (environment C) (application k))
      (eraseCode ((action F ν C).run C)) := by
  apply (EnvironmentEval.denote_application emptyEnvA F ν (environment C)
    (identitySource k) (.bvar 0)).trans
  apply (NeutralPi.applyValue_congr (ValueEq.refl _)
    (bound_image emptyEnvA F ν (environment C) 0 (eraseCode C) rfl C.bot)).trans
  exact (action F ν C).erased C

theorem application_retains (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    {k : Nat} (C : ClosedCode k) : (action F ν C).run C = C := rfl

theorem paired_application (F G : EnvironmentEval.FamilySyntax) (ν μ : Valuation)
    {k : Nat} {C D : ClosedCode k} (h : CodeRel C D) :
    CodeRel ((action F ν C).run C) ((action G μ D).run D) := h

/-- Every original code is covered; completion preserves its entire El,
even when its original type value did not contain bottom. -/
theorem every_code_control (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (k : Nat) (C : Code k) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 (context k)) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 (context k)
      (identitySource k) (identityType k)) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 (context k)
      (application k) (.sort (level k))) ∧
    CodeRelated k C (close k C).code ∧
    (view k (close k C).code).relation = (view k C).relation ∧
    (universeCode k).relation (encode k (close k C).code) (encode k (close k C).code) ∧
    (action F ν (close k C)).run (close k C) = close k C ∧
    ValueEq (EnvironmentEval.denote emptyEnvA F ν (environment (close k C)) (application k))
      (eraseCode (close k C)) :=
  ⟨⟨.empty⟩, ⟨context_wf k⟩, ⟨identity_typed _ k⟩, ⟨application_typed k⟩,
    completeCode_related k C, close_preserves_fibre k C,
    universe_member k _, rfl, application_erasure F ν (close k C)⟩

def falseCode : ClosedCode 0 := close 0 CandidatePi.falseElement
def trueCode : ClosedCode 0 := close 0 CandidatePi.trueElement

theorem collision_same_erasure : eraseCode falseCode = eraseCode trueCode := rfl

theorem collision_not_related : ¬ CodeRel falseCode trueCode := by
  intro h
  exact CandidatePi.collision_not_related h.transport

theorem falseCode_no_unit : ¬ Member (view 0 falseCode.code).relation (unitValue EnvI.bot) :=
  CandidatePi.falseElement_no_unit

theorem trueCode_unit : Member (view 0 trueCode.code).relation (unitValue EnvI.bot) :=
  CandidatePi.trueElement_unit

/-- An inhabited source application keeps the candidate that its raw
value cannot identify. This is a positive control for the retained action. -/
theorem collision_control (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (name : Nat) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 (context 0)) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 (context 0)
      (identitySource 0) (identityType 0)) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 (context 0)
      (application 0) (.sort .zero)) ∧
    Member (view 0 falseCode.code).relation (NeutralPER.neutralAtom name) ∧
    Member (view 0 trueCode.code).relation (NeutralPER.neutralAtom name) ∧
    (action F ν falseCode).run falseCode = falseCode ∧
    (action F ν trueCode).run trueCode = trueCode ∧
    ValueEq (EnvironmentEval.denote emptyEnvA F ν (environment falseCode) (application 0))
      (EnvironmentEval.denote emptyEnvA F ν (environment trueCode) (application 0)) ∧
    ¬ CodeRel ((action F ν falseCode).run falseCode) ((action F ν trueCode).run trueCode) ∧
    Member (view 0 trueCode.code).relation (unitValue EnvI.bot) ∧
    ¬ Member (view 0 falseCode.code).relation (unitValue EnvI.bot) :=
  ⟨⟨.empty⟩, ⟨context_wf 0⟩, ⟨identity_typed _ 0⟩, ⟨application_typed 0⟩,
    CandidatePi.decode_reflection _ (.atom name), CandidatePi.decode_reflection _ (.atom name),
    rfl, rfl, ValueEq.refl _, collision_not_related, trueCode_unit, falseCode_no_unit⟩

end Rcic.Declarative.Ann.LR3.CandidateActionSource

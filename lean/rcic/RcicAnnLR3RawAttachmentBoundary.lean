import rcic.RcicAnnLR3CandidateActionSource

/-!
# Retained proposition candidates do not attach through raw-value coherence

The existing false and true candidates have equal type erasures, distinct
element PERs, and explicit neutral members. An old CodeSystem cannot retain
both element PERs at that raw type value: its coherence law would identify
their unit membership. The result allows arbitrary extensionally equivalent
presentations and arbitrary code levels.

The source control is the already constructed admitted identity/application
instance. This refutes an erasure-only attachment of these retained data,
not source admission, the paired fundamental theorem, or candidate-aware
semantics. No candidate interpretation or source class is removed.
closure_claim = 0.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.RawAttachmentBoundary

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements StratifiedCandidates CandidateAction
open CandidateActionSource

/-- Coherence at one raw value cannot preserve both retained fibres,
even when their chosen relation presentations are merely equivalent. -/
theorem no_exact_erased_attachment (C : CodeSystem) :
    ¬ ∃ (k l : Option Nat) (R S : Relation),
      C.Code k (eraseCode falseCode) R ∧
      C.Code l (eraseCode trueCode) S ∧
      Same R (view 0 falseCode.code).relation ∧
      Same S (view 0 trueCode.code).relation := by
  rintro ⟨k, l, R, S, hR, hS, hRf, hSt⟩
  have hS' : C.Code l (eraseCode falseCode) S :=
    collision_same_erasure.symm ▸ hS
  have huS : S (unitValue EnvI.bot) (unitValue EnvI.bot) :=
    (hSt _ _).mpr trueCode_unit
  have huR : R (unitValue EnvI.bot) (unitValue EnvI.bot) :=
    (C.coherent hR hS' _ _).mpr huS
  exact falseCode_no_unit ((hRf _ _).mp huR)

/-- In particular the entire zero-stage candidate universe cannot be
attached to the old raw-value interface while preserving its El. -/
theorem no_all_candidate_attachment (C : CodeSystem) :
    ¬ (∀ A : CandidatePi.Element, ∃ (k : Option Nat) (R : Relation),
      C.Code k (eraseCode (close 0 A)) R ∧
      Same R (view 0 (close 0 A).code).relation) := by
  intro h
  obtain ⟨k, R, hR, hRf⟩ := h CandidatePi.falseElement
  obtain ⟨l, S, hS, hSt⟩ := h CandidatePi.trueElement
  exact no_exact_erased_attachment C ⟨k, l, R, S, hR, hS, hRf, hSt⟩

/-- Both candidates have neutral inhabitants, and the existing source
identity applies to each in an admitted well-formed context. The same raw
application value retains different candidate data. The CodeSystem
parameter itself is inhabited by the supplied legacy instance. -/
theorem attachment_boundary_inhabited (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (name : Nat) :
    Nonempty CodeSystem ∧
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 (context 0)) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 (context 0)
      (identitySource 0) (identityType 0)) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 (context 0)
      (application 0) (.sort .zero)) ∧
    Member (view 0 falseCode.code).relation (NeutralPER.neutralAtom name) ∧
    Member (view 0 trueCode.code).relation (NeutralPER.neutralAtom name) ∧
    ValueEq (EnvironmentEval.denote emptyEnvA F ν (environment falseCode) (application 0))
      (EnvironmentEval.denote emptyEnvA F ν (environment trueCode) (application 0)) ∧
    (¬ CodeRel falseCode trueCode) ∧
    (∀ C : CodeSystem, ¬ ∃ (k l : Option Nat) (R S : Relation),
      C.Code k (eraseCode falseCode) R ∧
      C.Code l (eraseCode trueCode) S ∧
      Same R (view 0 falseCode.code).relation ∧
      Same S (view 0 trueCode.code).relation) :=
  ⟨⟨NeutralCodes.codeSystem⟩, ⟨.empty⟩, ⟨context_wf 0⟩,
    ⟨identity_typed _ 0⟩, ⟨application_typed 0⟩,
    CandidatePi.decode_reflection _ (.atom name),
    CandidatePi.decode_reflection _ (.atom name),
    ValueEq.refl _, collision_not_related, no_exact_erased_attachment⟩

end Rcic.Declarative.Ann.LR3.RawAttachmentBoundary

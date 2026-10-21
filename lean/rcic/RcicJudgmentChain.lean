/-
RCIC 01 §9/§11 and 03 §7–§8 — the generic judgment chain (Annex 26.2, GA-1).

01's `Judgment*` family and 03's `run`/`continue` budget machine as data,
generic over the kind's parameter types (`RcicGraphAdmitted` instantiates
the result/decision types over `GraphAdmissionState`; `StepMachine` itself
is instantiated nowhere — its `graphAdmission` runner is GA-2+'s unbuilt
stage, Annex 26.2a `unbuilt_stage`; nothing here is admission-specific).

TRANSCRIPTION TABLE (the law → the data):
  01:263 `JudgmentDecision A R I`            → `JudgmentDecision`
  01:270 `JudgmentRunResult S A R I`         → `JudgmentRunResult`
  01:314 `JudgmentStatement K`               → `JudgmentStatement`
  01:328 `JudgmentEvidenceBundle K`          → `JudgmentEvidenceBundle`
  01:345 `ValidatorExecutionEvidence`        → `ValidatorExecutionEvidence`
  01:357 `JudgmentReceipt K`                 → `JudgmentReceipt`
  01:372 `JudgmentOccurrence K`              → `JudgmentOccurrence`
  10 §8   the ten transition classes         → `TransitionClass`
  10 §8   `AuthorityTransitionStatement`     → `AuthorityTransitionStatement`
  03 §7   one global budget, final-check      → `StepMachine`
  03:217  `run : Nat → State → result`        → `run`
  03:221  `run 0 = suspended` unless final    → `run_zero_suspended`/`run_zero_done`
  03:229  `run(m+n,s) = continue(n,run(m,s))` → `run_decompose`
  03:235-7  decisions stable under more budget → `run_done_stable`
  03:238  suspension resumes the exact state   → `continue_suspended`
  §15/26.2-FC-13 suspended mints no receipt/occurrence → `publishable`, `not_publishable_suspended`

The `exact_*` bundle fields and every `*_ref` are content references (digests);
the object schemas they resolve to are each kind's own parameter. A record's
field ORDER is the canonical sorted-key order of its byte form.
-/

namespace Rcic.Judgment

/-- A digest reference (01 §5's `q`). -/
abbrev Ref := String

/-- 01:263 — the three-constructor decision. `refused` is a subject refusal;
    `integrityResidue` is a basis/codec/store/checker fault, never a subject
    verdict (01:277-282). -/
inductive JudgmentDecision (Accepted Refusal Integrity : Type) : Type
  | accepted : Accepted → JudgmentDecision Accepted Refusal Integrity
  | refused : Refusal → JudgmentDecision Accepted Refusal Integrity
  | integrityResidue : Integrity → JudgmentDecision Accepted Refusal Integrity
  deriving DecidableEq

/-- 01:270 — `done` carries a decision; `suspended` carries the resumable
    state and nothing else. The §15/26.2-FC-13 rule — a suspended run mints no
    receipt and no occurrence — is in the type: `suspended` has no field that
    could carry one. -/
inductive JudgmentRunResult (State Accepted Refusal Integrity : Type) : Type
  | done : JudgmentDecision Accepted Refusal Integrity →
      JudgmentRunResult State Accepted Refusal Integrity
  | suspended : State → JudgmentRunResult State Accepted Refusal Integrity
  deriving DecidableEq

/-- 01:314 `JudgmentStatement K` — a statement contains no verdict. The kind's
    subject ref stands in `judgment_ref`; `history_parent_ref` is optional
    (a genesis statement has no parent). -/
structure JudgmentStatement where
  judgment_ref : Ref
  institutional_basis_refs : List Ref
  history_parent_ref : Option Ref
  epoch : Nat
  sequence : Nat
  deriving DecidableEq

/-- 01:328 `JudgmentEvidenceBundle K` — no receipt, occurrence, current head,
    or future reservation result inside. The `exact_*` fields are content
    refs to canonical objects; their object schemas are each kind's own. -/
structure JudgmentEvidenceBundle where
  statement_ref : Ref
  exact_subject_objects : Ref
  exact_proofs_or_traces : Ref
  exact_validator_inputs : Ref
  deriving DecidableEq

/-- 01:345 `ValidatorExecutionEvidence` — raw validator execution evidence; a
    receipt may cite it without receipt-to-occurrence regress (01:349). -/
structure ValidatorExecutionEvidence where
  validator_spec_ref : Ref
  validator_artifact_ref : Ref
  request_ref : Ref
  initial_state_ref : Ref
  final_decision_ref : Ref
  trace_ref : Ref
  execution_relation_ref : Ref
  deriving DecidableEq

/-- 01:357 `JudgmentReceipt K` — the six fields; no future occurrence ref. -/
structure JudgmentReceipt (Accepted Refusal Integrity : Type) where
  statement_ref : Ref
  evidence_bundle_ref : Ref
  validator_spec_ref : Ref
  validator_artifact_ref : Ref
  validator_execution_evidence_ref : Ref
  decision : JudgmentDecision Accepted Refusal Integrity
  deriving DecidableEq

/-- 01:372 `JudgmentOccurrence K` — the occurrence ref is computed only after
    the receipt exists (01:375); the record carries no occurrence back-ref. -/
structure JudgmentOccurrence where
  statement_ref : Ref
  receipt_ref : Ref
  deriving DecidableEq

/-- 10 §8 — the ten transition classes, verbatim. The list is closed by the
    law: a nonconservative theory change creates a new genesis, not a class. -/
inductive TransitionClass where
  | implementationReplacement
  | algorithmReplacement
  | machineReplacement
  | policyRestriction
  | policyExpansion
  | conservativeTheoryExtension
  | semanticsRevision
  | recoveryRepair
  | reepoch
  | addressEpochChange
  deriving DecidableEq

/-- 10 §8 `AuthorityTransitionStatement` — the eight mandatory fields plus the
    two optional (`required_fixed_point_ref`, `required_bridge_ref`). "The
    statement contains no verdict or successor occurrence ref": no field's
    payload type is a `JudgmentDecision` (see `fieldValues` below); excluding
    a successor *reference* is a binding/chronology property of the decoded,
    stored object — `Ref` is `String` and carries no referent role (RF-014). -/
structure AuthorityTransitionStatement where
  predecessor_occurrence_ref : Ref
  candidate_authority_artifact_ref : Ref
  target_epoch : Nat
  target_sequence : Nat
  transition_class : TransitionClass
  constitution_ref : Ref
  master_profile_ref : Ref
  authority_policy_ref : Ref
  required_fixed_point_ref : Option Ref
  required_bridge_ref : Option Ref
  deriving DecidableEq

/-- The payload grammar of a 10 §8 transition statement. The `verdict`
    alternative exists so that "this payload is a `JudgmentDecision`" is a
    statable property; `AuthorityTransitionStatement.fieldValues` can never
    produce it because no field has that type. Retyping a field to
    `JudgmentDecision` (the audit mutant) makes the projection ill-typed —
    the exclusion bites at elaboration, not only at a checker's discretion. -/
inductive AuthorityTransitionFieldValue (A R I : Type) : Type where
  | ref : Ref → AuthorityTransitionFieldValue A R I
  | nat : Nat → AuthorityTransitionFieldValue A R I
  | tclass : TransitionClass → AuthorityTransitionFieldValue A R I
  | optRef : Option Ref → AuthorityTransitionFieldValue A R I
  | verdict : JudgmentDecision A R I → AuthorityTransitionFieldValue A R I

/-- The exhaustive projection — one payload per field, in §8 order. -/
def AuthorityTransitionStatement.fieldValues {A R I : Type}
    (s : AuthorityTransitionStatement) : List (AuthorityTransitionFieldValue A R I) :=
  [ .ref s.predecessor_occurrence_ref,
    .ref s.candidate_authority_artifact_ref,
    .nat s.target_epoch,
    .nat s.target_sequence,
    .tclass s.transition_class,
    .ref s.constitution_ref,
    .ref s.master_profile_ref,
    .ref s.authority_policy_ref,
    .optRef s.required_fixed_point_ref,
    .optRef s.required_bridge_ref ]

/-- 03 §7's machine shape: a state either already encodes a final decision or
    takes one `step`, consuming one unit of the single global budget. One
    transition function — no submachine mints fresh fuel (03:212). -/
structure StepMachine (State Accepted Refusal Integrity : Type) where
  final : State → Option (JudgmentDecision Accepted Refusal Integrity)
  step : State → State

/-- 03:217-224 `run : Nat → State → JudgmentRunResult`. The final check comes
    before the budget check: at fuel 0 a state encoding a decision is `done`,
    otherwise `suspended`. -/
def run (M : StepMachine S A R I) : Nat → S → JudgmentRunResult S A R I
  | 0, s => match M.final s with
    | some d => .done d
    | none => .suspended s
  | n+1, s => match M.final s with
    | some d => .done d
    | none => run M n (M.step s)

/-- `continue` — resume a suspended result inside the same budget; a `done`
    consumes nothing (03:229's right-hand side). (`continue` is a Lean
    keyword, hence the escaped identifier.) -/
def «continue» (M : StepMachine S A R I) (n : Nat) :
    JudgmentRunResult S A R I → JudgmentRunResult S A R I
  | .done d => .done d
  | .suspended s => run M n s

/-- `run 0 s = suspended s` when `s` encodes no final decision (03:221-224,
    first clause). -/
theorem run_zero_suspended (M : StepMachine S A R I) {s : S}
    (h : M.final s = none) : run M 0 s = .suspended s := by
  simp only [run, h]

/-- `run 0 s = done d` when `s` encodes `d` (03:224, the unless clause). -/
theorem run_zero_done (M : StepMachine S A R I) {s : S} {d : JudgmentDecision A R I}
    (h : M.final s = some d) : run M 0 s = .done d := by
  simp only [run, h]

/-- A state encoding a decision is `done` at every budget. -/
theorem run_done_of_final (M : StepMachine S A R I) {s : S} {d : JudgmentDecision A R I}
    (n : Nat) (h : M.final s = some d) : run M n s = .done d := by
  cases n <;> simp only [run, h]

/-- One step on the state consumes one unit of budget. -/
theorem run_succ (M : StepMachine S A R I) {s : S} (n : Nat)
    (h : M.final s = none) : run M (n + 1) s = run M n (M.step s) := by
  simp only [run, h]

/-- 03:229 — the decomposition law `run(m+n, s) = continue(n, run(m,s))`. -/
theorem run_decompose (M : StepMachine S A R I) (m n : Nat) (s : S) :
    run M (m + n) s = «continue» M n (run M m s) := by
  induction m generalizing s with
  | zero =>
      cases h : M.final s with
      | none =>
          rw [Nat.zero_add, run_zero_suspended M h]
          rfl
      | some d =>
          rw [Nat.zero_add, run_zero_done M h]
          exact run_done_of_final M n h
  | succ m ih =>
      cases h : M.final s with
      | some d =>
          have e : m + 1 + n = m + n + 1 := by omega
          rw [e, run_done_of_final M _ h, run_done_of_final M _ h]
          rfl
      | none =>
          have e : m + 1 + n = m + n + 1 := by omega
          rw [e, run_succ M _ h, run_succ M _ h, ih (M.step s)]

/-- 03:235-237 — a final result is stable under more budget. -/
theorem run_done_stable (M : StepMachine S A R I) (m n : Nat) (s : S)
    {d : JudgmentDecision A R I} (h : run M m s = .done d) :
    run M (m + n) s = .done d := by
  rw [run_decompose, h]
  rfl

/-- 03:238 — suspension resumes from the exact continuation: `continue` on a
    suspended result is `run` of the carried state. -/
theorem continue_suspended (M : StepMachine S A R I) (n : Nat) (s : S) :
    «continue» M n (.suspended s : JudgmentRunResult S A R I) = run M n s := rfl

/-- A `done` consumes no further budget. -/
theorem continue_done (M : StepMachine S A R I) (n : Nat)
    (d : JudgmentDecision A R I) :
    «continue» M n (.done d : JudgmentRunResult S A R I) = .done d := rfl

/-- `done` and `suspended` are disjoint outcomes — the §15/26.2-FC-13 split is
    in the type: a run result is never both. -/
theorem done_ne_suspended {d : JudgmentDecision A R I} {s : S} :
    (JudgmentRunResult.done d : JudgmentRunResult S A R I) ≠ .suspended s := by
  intro h; cases h

/-- A run result that mints publishable chain objects: only a `done` does.
    §15/26.2-FC-13 — a suspended run produces no receipt and no occurrence;
    this flag is `false` exactly there. -/
def publishable : JudgmentRunResult S A R I → Bool
  | .done _ => true
  | .suspended _ => false

/-- §15/26.2-FC-13's leg: suspension mints nothing. -/
theorem not_publishable_suspended (s : S) :
    publishable (.suspended s : JudgmentRunResult S A R I) = false := rfl

/-- The decision constructors are disjoint — an integrity residue is never a
    subject refusal (01:279). -/
theorem integrity_ne_refused {A Refusal Integrity : Type} {i : Integrity}
    {r : Refusal} :
    (JudgmentDecision.integrityResidue i : JudgmentDecision A Refusal Integrity)
      ≠ .refused r := by
  intro h; cases h

/-- An acceptance is never an integrity residue. -/
theorem accepted_ne_integrity {Accepted R Integrity : Type} {a : Accepted}
    {i : Integrity} :
    (JudgmentDecision.accepted a : JudgmentDecision Accepted R Integrity)
      ≠ .integrityResidue i := by
  intro h; cases h

#print axioms Rcic.Judgment.run_zero_suspended
#print axioms Rcic.Judgment.run_zero_done
#print axioms Rcic.Judgment.run_done_of_final
#print axioms Rcic.Judgment.run_succ
#print axioms Rcic.Judgment.run_decompose
#print axioms Rcic.Judgment.run_done_stable
#print axioms Rcic.Judgment.continue_suspended
#print axioms Rcic.Judgment.continue_done
#print axioms Rcic.Judgment.done_ne_suspended
#print axioms Rcic.Judgment.not_publishable_suspended
#print axioms Rcic.Judgment.integrity_ne_refused
#print axioms Rcic.Judgment.accepted_ne_integrity

end Rcic.Judgment

/-
RCIC 01 §9–§12 — the RF row propositions over the landed judgment chain
(`RcicJudgmentChain.lean`), same convention as `RcicRows.lean` (23.H.0).

Each row says "the record contains no X". Over the landed structures that is
field EXHAUSTION: the absent thing is not a field under any spelling, for
every judgment kind — the leg the app carriers cannot state, since they
refuse only the key names they know.

STATEMENTS QUOTED BEFORE THE LEAN:

  01 §15 row list (:461-468):
    RF-011 suspension_not_decision                  GT-OUT-003
    RF-014 statement_has_no_verdict                 GT-OCC-001
    RF-015 evidence_has_no_receipt_or_occurrence    GT-OCC-001
    RF-016 receipt_has_no_occurrence                GT-OCC-001
    RF-017 occurrence_identity_acyclic              GT-OCC-001

  01:279 — "`suspended`: the current machine budget ended before a
  decision." §15/26.2-FC-13: a suspended run mints no receipt and no
  occurrence.

  01:314-323 — `JudgmentStatement K` = `judgment_ref`,
  `institutional_basis_refs`, `history_parent_ref?`, `epoch`, `sequence`;
  "A statement contains no verdict."

  01:328-336 — `JudgmentEvidenceBundle K` = `statement_ref`,
  `exact_subject_objects`, `exact_proofs_or_traces`,
  `exact_validator_inputs`; "An evidence bundle contains no receipt,
  occurrence, current head, or future reservation result."

  01:357-366 — `JudgmentReceipt K` = `statement_ref`, `evidence_bundle_ref`,
  `validator_spec_ref`, `validator_artifact_ref`,
  `validator_execution_evidence_ref`, `decision`; "A receipt contains no
  future occurrence ref."

  01:372-377 — `JudgmentOccurrence K` = `statement_ref`, `receipt_ref`;
  "The occurrence ref is computed only after the receipt exists."
-/

import rcic.RcicJudgmentChain

namespace Rcic.Judgment

/-- RF-011 (GT-OUT-003). `suspended` is not a `JudgmentDecision`: it is a
    `JudgmentRunResult` constructor, never equal to a `done`, and it mints
    nothing publishable (§15/26.2-FC-13). Both halves are already proved;
    this names the row's proposition. -/
theorem RF011_suspension_not_decision {S A R I : Type} {s : S}
    {d : JudgmentDecision A R I} :
    (JudgmentRunResult.suspended s : JudgmentRunResult S A R I) ≠ .done d ∧
      publishable (.suspended s : JudgmentRunResult S A R I) = false :=
  ⟨Ne.symm done_ne_suspended, not_publishable_suspended s⟩

/-- RF-014 (GT-OCC-001). A statement contains no verdict: `JudgmentStatement`
    is exhausted by the five listed fields, for every K. No field — under
    `verdict`, `successor_occurrence_ref`, or any other spelling — can carry
    one. Covers the opens `other_judgment_kinds` and `verdict_other_key`;
    `non_verdict_decision_encoding` stays a blocked object. -/
theorem RF014_statement_has_no_verdict (s : JudgmentStatement) :
    s = { judgment_ref := s.judgment_ref,
          institutional_basis_refs := s.institutional_basis_refs,
          history_parent_ref := s.history_parent_ref,
          epoch := s.epoch,
          sequence := s.sequence } := rfl

/-- RF-014 (10 §8 remainder, transcription half). The authority-transition
    statement is exhausted by its ten spelled fields (eight mandatory, two
    optional): this proposition pins the field set — a missing or extra field
    fails to elaborate. Field-set exhaustion alone says nothing about what a
    field's payload can be; that exclusion is the companion theorem below. -/
theorem RF014_transition_statement_has_no_verdict
    (s : AuthorityTransitionStatement) :
    s = { predecessor_occurrence_ref := s.predecessor_occurrence_ref,
          candidate_authority_artifact_ref := s.candidate_authority_artifact_ref,
          target_epoch := s.target_epoch,
          target_sequence := s.target_sequence,
          transition_class := s.transition_class,
          constitution_ref := s.constitution_ref,
          master_profile_ref := s.master_profile_ref,
          authority_policy_ref := s.authority_policy_ref,
          required_fixed_point_ref := s.required_fixed_point_ref,
          required_bridge_ref := s.required_bridge_ref } := rfl

/-- RF-014 (10 §8, exclusion half). Every projected field value of a
    transition statement is a `ref`/`nat`/`tclass`/`optRef` payload — never a
    `verdict`. `fieldValues` is exhaustive by construction (one slot per
    field, §8 order), so this decides "the statement contains no verdict" at
    the payload level, spelling-free. The residual it does NOT close: `Ref`
    is `String`, so a successor-occurrence *reference* is a
    binding/chronology property of a decoded, stored object — no codec/store
    bridge for this type exists on main; and the byte-level carrier's
    `[rcic_statement_has_verdict]` tooth names only the two verbatim keys. -/
theorem RF014_transition_statement_fields_verdict_free
    {A R I : Type} (s : AuthorityTransitionStatement) :
    ∀ v ∈ s.fieldValues (A := A) (R := R) (I := I),
      ∀ d : JudgmentDecision A R I,
        v ≠ AuthorityTransitionFieldValue.verdict d := by
  intro v hv d h
  simp [AuthorityTransitionStatement.fieldValues] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact AuthorityTransitionFieldValue.noConfusion h

/-- RF-015 (GT-OCC-001). An evidence bundle contains no receipt, occurrence,
    current head, or future reservation result: `JudgmentEvidenceBundle` is
    exhausted by the four listed fields, so none of those can appear under
    any spelling (`spelling_ambiguity` at the type level). -/
theorem RF015_evidence_has_no_receipt_or_occurrence
    (e : JudgmentEvidenceBundle) :
    e = { statement_ref := e.statement_ref,
          exact_subject_objects := e.exact_subject_objects,
          exact_proofs_or_traces := e.exact_proofs_or_traces,
          exact_validator_inputs := e.exact_validator_inputs } := rfl

/-- RF-016 (GT-OCC-001). A receipt contains no future occurrence ref:
    `JudgmentReceipt` is exhausted by the six listed fields, for every
    decision parameter — no field can carry an occurrence ref. The
    `archive_bundle` leg stays a blocked object (the bundle is not on
    main). -/
theorem RF016_receipt_has_no_occurrence {A R I : Type}
    (r : JudgmentReceipt A R I) :
    r = { statement_ref := r.statement_ref,
          evidence_bundle_ref := r.evidence_bundle_ref,
          validator_spec_ref := r.validator_spec_ref,
          validator_artifact_ref := r.validator_artifact_ref,
          validator_execution_evidence_ref := r.validator_execution_evidence_ref,
          decision := r.decision } := rfl

/-- RF-017 (GT-OCC-001). Occurrence identity is acyclic: `JudgmentOccurrence`
    is exhausted by its two backward refs, and its own ref is computed only
    after the receipt exists (01:375) — there is no field that could carry
    the occurrence's own identity. The receipt it names can name no
    occurrence back (RF-016's six fields). -/
theorem RF017_occurrence_identity_acyclic (o : JudgmentOccurrence) :
    o = { statement_ref := o.statement_ref, receipt_ref := o.receipt_ref } := rfl

#print axioms Rcic.Judgment.RF011_suspension_not_decision
#print axioms Rcic.Judgment.RF014_statement_has_no_verdict
#print axioms Rcic.Judgment.RF014_transition_statement_has_no_verdict
#print axioms Rcic.Judgment.RF014_transition_statement_fields_verdict_free
#print axioms Rcic.Judgment.RF015_evidence_has_no_receipt_or_occurrence
#print axioms Rcic.Judgment.RF016_receipt_has_no_occurrence
#print axioms Rcic.Judgment.RF017_occurrence_identity_acyclic

end Rcic.Judgment

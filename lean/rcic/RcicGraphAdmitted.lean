/-
RCIC Annex 26.2 (merged #6406) + 26.2a (cc on #6409) — `GraphAdmitted` /
CG-014, the pinned Lean model of `apps/rcic-graph-admitted`
(`rcic.graph_admitted store statement_ref receipt_ref occurrence_ref occurrence fuel`).

GA-1 builds the CG-014 judgment carrier over the generic 01 chain
(`RcicJudgmentChain`). The belief validates ONE RECORDED triple — a
statement, a receipt, and an occurrence over a caller-supplied store —
composing the landed carriers (cps_seam_ref_bound, judgment_receipt,
occurrence_identity, auth_statement_ref_past, judgment-decision spelling)
and adding the GraphAdmitted-specific arms. It is a triple validator, not
an admission runner: the stage machine (`GraphAdmissionState` below) is
GA-2+'s surface and is declared here only at the ruled shape. A stage
without a carrier is an `integrityResidue` of the additive kind
`unbuilt_stage` (26.2a) — never a subject refusal, never a stub acceptance.

CG-014 (the ruled tooth `judgment_untyped` → code `[rcic_cg014_judgment]`):
an `accepted` decision names an `AdmittedGraphJudgment` record; the carrier
enforces the decided half — the judgment resolves canonically with the five
ruled keys, coverage is `exact` or `soundOverapproximation` (`unknown` is
refused at `[rcic_cg014_coverage]`), the judgment's subject is the
statement's `closed_graph_bundle_ref`, and `typed_judgment_ref` resolves to
a two-key object naming the same `admitted_env_ref` and bundle. The
semantic half — that the typed-judgment object DECODES to a composite
`EnvWfT` — is stated over the `GraphAdmitObjects` decode seam; the
env-image codec (04 §9/25.11) is a named unbuilt surface, so
`TypedJudgmentBound` quantifies over decoders rather than smuggling one in.

TRANSCRIPTION TABLE (scm module → Lean):
  rcic.cps_seam_ref_bound             → `seamRefBound`      (vendored mirror)
  rcic.auth_activation_ref_bound      → `refBoundEarlier`   (vendored mirror)
  rcic.auth_statement_ref_past        → `statementRefPast`  (vendored mirror)
  rcic.judgment_receipt               → `judgmentReceiptCheck` (vendored)
  rcic.occurrence_identity            → `occurrenceIdentity`   (vendored)
  rcic.exact_keys                     → `exactKeys`            (vendored)
  rcic.exactly_one_name               → `exactlyOneName`       (vendored)
  rcic.authority_artifact_coords_ok   → `coordsOk`             (vendored)
  rcic.value_at_digits_ok             → `digitsOk`             (vendored)
  rcic.judgment_decision_names        → `decisionNames`        (vendored)
  rcic.occurrence_names               → `occurrenceNames`      (vendored)
  rcic.judgment_receipt_names         → `receiptNames`         (vendored)
  rcic.graph_admitted_statement_keys      → `statementKeys`
  rcic.graph_admitted_statement_mandatory → `statementMandatory`
  rcic.graph_admitted_judgment_keys       → `judgmentKeys`
  rcic.graph_admitted_typed_judgment_keys → `typedJudgmentKeys`
  rcic.graph_admitted_receipt_ref_keys    → `receiptRefKeys`
  rcic.graph_admitted_ref_bound           → `refBound`
  rcic.graph_admitted_receipt_refs_ok     → `receiptRefsOk`
  rcic.graph_admitted_history             → `historyOk`
  rcic.graph_admitted_decision_ctor       → `decisionCtor`
  rcic.graph_admitted_decision            → `decisionCheck`
  rcic.graph_admitted_coverage_ok         → `coverageOk`
  rcic.graph_admitted_typed_judgment_ok   → `typedJudgmentOk`
  rcic.graph_admitted_accepted            → `acceptedCheck`
  rcic.graph_admitted                     → `graphAdmitted`
-/

import rcic.RcicJudgmentChain
import rcic.ScmEmbed
import rcic.RcicTypedEnv

namespace Rcic.GraphAdmitted

open Rcic.BoundObject (StoreEntry canonBytesOk storeScan canonicalAt)
open Rcic.Scm.Embed (partAt keysOf covers EOut eRefuse)
open Rcic.Judgment
open Rcic.Declarative (ResolvedEnv EnvWfT)

/-! ## The ruled object layer (26.2, frozen) -/

/-- 26.2 `coverage_grade` — the two admissible values. `unknown` is ruled out
    (a judgment carrying it is refused), so it is not a constructor here. -/
inductive CoverageGrade : Type
  | exact | soundOverapproximation
  deriving DecidableEq, Repr

/-- 26.2 `GraphAdmissionState` — the runner's resumable state (FC-4): the
    cursor sits only at a stage boundary; in-stage continuation is owned by
    that stage's object and referenced by digest. The stage machine itself is
    GA-2+'s surface; the shape lands now so `JudgmentRunResult` can
    instantiate. -/
structure GraphAdmissionState where
  accumulated_stage_ref : String
  fuel_seen : Nat
  next_stage : Nat
  stage_cursor : String
  subject_bundle_ref : String
  deriving DecidableEq, Repr

/-- 26.2 `AdmittedGraphJudgment` — the CG-014 carrier record. `coverage_grade`
    is the ruled two-value enum; `unknown` cannot be constructed here and is
    refused at the byte layer (`coverageOk`). -/
structure AdmittedGraphJudgment where
  admitted_env_ref : String
  assumptions_ref : String
  coverage_grade : CoverageGrade
  subject_bundle_ref : String
  typed_judgment_ref : String
  deriving DecidableEq, Repr

/-- 26.2 `GraphRefusal` — the stage-tagged subject-refusal tags. Landed
    carrier teeth are re-surfaced inside the tag without renaming; CG-014's
    tooth is `judgment_untyped`. -/
inductive GraphRefusal : Type
  | bundle_invalid | kind_or_schema_invalid | seam_invalid
  | proof_replay_failed | certificate_replay_failed
  | binding_or_air_replay_failed | assumptions_mismatch
  | authority_policy_refused | authority_basis_invalid
  | challenge_open | availability_failed
  | judgment_untyped
  deriving DecidableEq, Repr

/-- 26.2 `GraphIntegrity` — the five ruled kinds plus 26.2a's additive sixth
    `unbuilt_stage` (cc on #6409: a stage without a carrier is an integrity
    residue — the checker lacks the stage; a basis fault, not a subject
    refusal — and must never stub-accept). Extensible additively. -/
inductive GraphIntegrity : Type
  | noncanonical_request | store_collision | codec_or_basis_mismatch
  | checker_invariant_failure | unreachable_state
  | unbuilt_stage
  deriving DecidableEq, Repr

/-- 26.2's judgment family instantiated on the generic 01 chain. -/
abbrev GraphAdmitDecision :=
  JudgmentDecision AdmittedGraphJudgment GraphRefusal GraphIntegrity

abbrev GraphAdmitResult :=
  JudgmentRunResult GraphAdmissionState AdmittedGraphJudgment GraphRefusal GraphIntegrity

/-- 26.2 statement: `closed_graph_bundle_ref|epoch|history_parent_ref|
    institutional_basis_refs|sequence` — a `JudgmentStatement` with the
    bundle as the kind's subject ref. -/
structure GraphAdmissionStatement where
  closed_graph_bundle_ref : String
  epoch : Nat
  history_parent_ref : Option String
  institutional_basis_refs : List String
  sequence : Nat
  deriving DecidableEq, Repr

def GraphAdmissionStatement.toJudgmentStatement (s : GraphAdmissionStatement) :
    JudgmentStatement where
  judgment_ref := s.closed_graph_bundle_ref
  institutional_basis_refs := s.institutional_basis_refs
  history_parent_ref := s.history_parent_ref
  epoch := s.epoch
  sequence := s.sequence

/-! ## Sub-check output records (the scm `{ok, code}` / `{ok, code, …}` shapes) -/

/-- `{ok, code}` — the sub-check record. -/
structure CodeOut where
  ok : Int
  code : String
  deriving BEq, Repr

def codeOk : CodeOut := ⟨1, ""⟩
def codeRefuse (c : String) : CodeOut := ⟨0, c⟩

/-- `{ok, code, ctor, value}` — `rcic.graph_admitted_decision`'s record. -/
structure DOut where
  ok : Int
  code : String
  ctor : String
  value : String
  deriving BEq, Repr

/-- `{ok, code, bytes, epoch, sequence}` — `rcic.auth_activation_ref_bound`'s
    record. -/
structure BRec where
  ok : Int
  code : String
  bytes : String
  epoch : Int
  sequence : Int
  deriving BEq

/-! ## The scm modules, mirrored -/

/-- `rcic.cps_seam_ref_bound`: scan-resolve then `canonical_at` at (class,
    kind) — the caller's `miss_code` on unbound or collision. -/
def seamRefBound (fuel cls knd : Int) (digest : String) (store : List StoreEntry)
    (miss : String) : CodeOut :=
  let s := storeScan store digest
  if !s.found then codeRefuse miss
  else if s.collision then codeRefuse miss
  else
    let cb := canonicalAt fuel cls knd digest s.bytes
    if cb.ok = 1 then codeOk else codeRefuse cb.code

/-- `rcic.auth_activation_ref_bound`: bound ref + optional strictly-earlier
    coordinate gate (epoch, then sequence at equal epoch). -/
def refBoundEarlier (fuel cls knd : Int) (ref : String) (store : List StoreEntry)
    (candEpoch candSeq : Int) (requireEarlier : Int) (miss : String) : BRec :=
  let s := storeScan store ref
  if !s.found then ⟨0, miss, "", 0, 0⟩
  else if s.collision then ⟨0, miss, "", 0, 0⟩
  else
    let cb := canonicalAt fuel cls knd ref s.bytes
    if cb.ok = 0 then ⟨0, cb.code, "", 0, 0⟩
    else
      let e : Int := (partAt s.bytes "epoch").toNat!
      let q : Int := (partAt s.bytes "sequence").toNat!
      if requireEarlier = 0 then ⟨1, "", s.bytes, e, q⟩
      else if e < candEpoch then ⟨1, "", s.bytes, e, q⟩
      else if e = candEpoch then
        if q < candSeq then ⟨1, "", s.bytes, e, q⟩
        else ⟨0, "[rcic_auth_activation_not_earlier]", "", e, q⟩
      else ⟨0, "[rcic_auth_activation_not_earlier]", "", e, q⟩

/-- `rcic.value_at_digits_ok`.
    `String.all` is well-founded (`anyAux`), so the kernel will not unfold it
    and `decide` cannot pass `coordsOk`. `data.all` is the same character
    predicate and reduces. -/
def digitsOk (s : String) : Bool := s.length > 0 && s.data.all Char.isDigit

/-- `rcic.authority_artifact_coords_ok`. -/
def coordsOk (bytes ek sq : String) : Bool :=
  digitsOk (partAt bytes ek) && digitsOk (partAt bytes sq)

/-- `rcic.auth_statement_ref_past`: a referenced `genesis`/`successor` object
    must be strictly earlier; anything else is not ordered by this step. -/
def statementRefPast (fuel : Int) (store : List StoreEntry) (te tq : Int)
    (v : String) : CodeOut :=
  let s := storeScan store v
  if !s.found then codeRefuse "[rcic_statement_ref_unbound]"
  else if s.collision then codeRefuse "[rcic_statement_ref_unbound]"
  else if !(["genesis", "successor"].contains (partAt s.bytes "kind")) then codeOk
  else if !coordsOk s.bytes "epoch" "sequence" then
    codeRefuse "[rcic_authority_artifact_coordinates]"
  else
    let pb := refBoundEarlier (fuel - 1) 3 0 v store te tq 1 "[rcic_statement_ref_unbound]"
    if pb.ok = 0 then codeRefuse pb.code else codeOk

/-- `rcic.exact_keys`: 0 exact, 1 missing, 2 extra. -/
def exactKeys (haveK wantK : List String) : Int :=
  if !covers haveK wantK then 1 else if !covers wantK haveK then 2 else 0

/-- `rcic.judgment_decision_names` — `accepted`, `integrityResidue`,
    `refused`. There is no `suspended` key: suspension is not a decision. -/
def decisionNames : List String := ["accepted", "integrityResidue", "refused"]

/-- `rcic.occurrence_names` — `receipt_ref`, `statement_ref`. -/
def occurrenceNames : List String := ["receipt_ref", "statement_ref"]

/-- `rcic.judgment_receipt_names` — the six ruled receipt keys. -/
def receiptNames : List String :=
  ["decision", "evidence_bundle_ref", "statement_ref",
   "validator_artifact_ref", "validator_execution_evidence_ref", "validator_spec_ref"]

/-- `rcic.exactly_one_name`: 1 missing, 2 two+, 3 extra, 4 noncanonical. -/
def exactlyOneName (bytes : String) (names : List String) : Int :=
  if bytes = "" then 1
  else if !canonBytesOk bytes then 4
  else
    let keys := keysOf bytes
    let n : Nat := names.foldl (fun acc e => if keys.contains e then acc + 1 else acc) 0
    if !covers names keys then 3
    else if n = 1 then 0 else if n = 0 then 1 else 2

/-- `rcic.judgment_receipt`: canonical bytes carrying exactly the six keys —
    it does not resolve the refs and does not typecheck `decision`. -/
def judgmentReceiptCheck (receipt : String) : CodeOut :=
  if !canonBytesOk receipt then codeRefuse "[rcic_judgment_receipt_noncanonical]"
  else
    let k := exactKeys (keysOf receipt) receiptNames
    if k = 1 then codeRefuse "[rcic_judgment_receipt_missing]"
    else if k = 2 then codeRefuse "[rcic_judgment_receipt_extra]"
    else codeOk

/-- `rcic.occurrence_identity`: occurrence_ref IS derive(8,0) of the receipt;
    occurrence bytes canonical with the two keys and `receipt_ref` matching. -/
def occurrenceIdentity (store : List StoreEntry)
    (receiptRef occurrenceRef occurrence : String) : EOut :=
  let b := seamRefBound 1 8 0 receiptRef store "[rcic_occurrence_unbound]"
  if b.ok = 0 then eRefuse b.code
  else
    let s := storeScan store receiptRef
    if Rcic.TypedRef.deriveDigest 8 0 s.bytes ≠ occurrenceRef then
      eRefuse "[rcic_occurrence_ref_mismatch]"
    else if !canonBytesOk occurrence then eRefuse "[rcic_occurrence_noncanonical]"
    else
      let k := exactKeys (keysOf occurrence) occurrenceNames
      if k = 1 then eRefuse "[rcic_occurrence_missing]"
      else if k = 2 then eRefuse "[rcic_occurrence_extra]"
      else if partAt occurrence "receipt_ref" = receiptRef then ⟨1, occurrence, ""⟩
      else eRefuse "[rcic_occurrence_receipt_mismatch]"

/-- `rcic.graph_admitted_statement_keys` — the five ruled statement keys. -/
def statementKeys : List String :=
  ["closed_graph_bundle_ref", "epoch", "history_parent_ref",
   "institutional_basis_refs", "sequence"]

/-- `rcic.graph_admitted_statement_mandatory` — `history_parent_ref` is
    optional (a genesis statement has no parent). -/
def statementMandatory : List String :=
  ["closed_graph_bundle_ref", "epoch", "institutional_basis_refs", "sequence"]

/-- `rcic.graph_admitted_judgment_keys` — the five ruled judgment keys. -/
def judgmentKeys : List String :=
  ["admitted_env_ref", "assumptions_ref", "coverage_grade",
   "subject_bundle_ref", "typed_judgment_ref"]

/-- `rcic.graph_admitted_typed_judgment_keys` — the recorded typed-judgment
    object's two binding keys. -/
def typedJudgmentKeys : List String := ["env_ref", "subject_bundle_ref"]

/-- `rcic.graph_admitted_receipt_ref_keys` — the four receipt ref parts that
    must resolve (statement_ref and decision are checked by their own arms). -/
def receiptRefKeys : List String :=
  ["evidence_bundle_ref", "validator_artifact_ref",
   "validator_execution_evidence_ref", "validator_spec_ref"]

/-- `rcic.graph_admitted_ref_bound`: resolve a ref to nonempty bytes in the
    store, else the caller's miss code. -/
def refBound (store : List StoreEntry) (r miss : String) : CodeOut :=
  let s := storeScan store r
  if !s.found then codeRefuse miss
  else if s.collision then codeRefuse miss
  else if s.bytes = "" then codeRefuse miss
  else codeOk

/-- `rcic.graph_admitted_receipt_refs_ok`: every receipt ref part resolves. -/
def receiptRefsOk (store : List StoreEntry) (receiptBytes : String) : CodeOut :=
  receiptRefKeys.foldl (fun acc k =>
    if acc.ok = 0 then acc
    else refBound store (partAt receiptBytes k)
      "[rcic_graph_admitted_receipt_ref_unbound]") codeOk

/-- `rcic.graph_admitted_history`: an absent `history_parent_ref` is a genesis
    statement; a present one is strictly-earlier by the vendored step. -/
def historyOk (fuel : Int) (store : List StoreEntry)
    (statementBytes : String) : CodeOut :=
  let hp := partAt statementBytes "history_parent_ref"
  if hp = "" then codeOk
  else statementRefPast fuel store
    ((partAt statementBytes "epoch").toNat!)
    ((partAt statementBytes "sequence").toNat!) hp

/-- `rcic.graph_admitted_decision_ctor`: the single present decision key —
    the caller's `exactlyOneName` already ruled 0 or 2+ out. -/
def decisionCtor (bytes : String) (names : List String) : String :=
  names.foldl (fun acc n =>
    if acc = "" then (if partAt bytes n = "" then acc else n) else acc) ""

/-- `rcic.graph_admitted_decision`: resolve the receipt's `decision` part to
    its bytes and spell exactly one of the three constructors. Landed teeth
    are re-surfaced without renaming. -/
def decisionCheck (store : List StoreEntry) (decisionRef : String) : DOut :=
  let s := storeScan store decisionRef
  if !s.found then ⟨0, "[rcic_graph_admitted_decision_unbound]", "", ""⟩
  else if s.collision then ⟨0, "[rcic_graph_admitted_decision_unbound]", "", ""⟩
  else
    let k := exactlyOneName s.bytes decisionNames
    if k = 1 then ⟨0, "[rcic_judgment_decision_missing]", "", ""⟩
    else if k = 2 then ⟨0, "[rcic_judgment_decision_two]", "", ""⟩
    else if k = 3 then ⟨0, "[rcic_judgment_decision_extra]", "", ""⟩
    else if k = 4 then ⟨0, "[rcic_judgment_decision_noncanonical]", "", ""⟩
    else
      let c := decisionCtor s.bytes decisionNames
      ⟨1, "", c, partAt s.bytes c⟩

/-- `rcic.graph_admitted_coverage_ok`. -/
def coverageOk (g : String) : Bool := g = "exact" || g = "soundOverapproximation"

/-- `rcic.graph_admitted_typed_judgment_ok`: the typed-judgment object
    resolves canonically with the two keys and names the judgment's
    `admitted_env_ref` and the statement's `closed_graph_bundle_ref`. -/
def typedJudgmentOk (store : List StoreEntry)
    (statementBytes judgmentBytes : String) : CodeOut :=
  let ts := storeScan store (partAt judgmentBytes "typed_judgment_ref")
  if !ts.found then codeRefuse "[rcic_cg014_judgment]"
  else if ts.collision then codeRefuse "[rcic_cg014_judgment]"
  else
    let tb := ts.bytes
    if !canonBytesOk tb then codeRefuse "[rcic_cg014_judgment]"
    else
      let tk := keysOf tb
      if !covers tk typedJudgmentKeys then codeRefuse "[rcic_cg014_judgment]"
      else if !covers typedJudgmentKeys tk then codeRefuse "[rcic_cg014_judgment]"
      else if partAt tb "env_ref" ≠ partAt judgmentBytes "admitted_env_ref" then
        codeRefuse "[rcic_cg014_judgment]"
      else if partAt tb "subject_bundle_ref" =
          partAt statementBytes "closed_graph_bundle_ref" then codeOk
      else codeRefuse "[rcic_cg014_judgment]"

/-- `rcic.graph_admitted_accepted`: the CG-014 arm. `unknown` coverage is
    refused at `[rcic_cg014_coverage]`; every other failure of the typed
    judgment to resolve or bind is the ruled tooth `[rcic_cg014_judgment]`
    (`judgment_untyped`). -/
def acceptedCheck (store : List StoreEntry)
    (statementBytes judgmentRef : String) : CodeOut :=
  let js := storeScan store judgmentRef
  if !js.found then codeRefuse "[rcic_cg014_judgment]"
  else if js.collision then codeRefuse "[rcic_cg014_judgment]"
  else
    let jb := js.bytes
    if !canonBytesOk jb then codeRefuse "[rcic_cg014_judgment]"
    else
      let jk := keysOf jb
      if !covers jk judgmentKeys then codeRefuse "[rcic_cg014_judgment]"
      else if !covers judgmentKeys jk then codeRefuse "[rcic_cg014_judgment]"
      else if !coverageOk (partAt jb "coverage_grade") then
        codeRefuse "[rcic_cg014_coverage]"
      else if partAt jb "subject_bundle_ref" ≠
          partAt statementBytes "closed_graph_bundle_ref" then
        codeRefuse "[rcic_cg014_judgment]"
      else
        let eb := refBound store (partAt jb "admitted_env_ref")
          "[rcic_graph_admitted_env_unbound]"
        if eb.ok = 1 then
          let ab := refBound store (partAt jb "assumptions_ref")
            "[rcic_graph_admitted_assumptions_unbound]"
          if ab.ok = 1 then typedJudgmentOk store statementBytes jb
          else codeRefuse ab.code
        else codeRefuse eb.code

/-- `rcic.graph_admitted`: one recorded triple — statement, receipt,
    occurrence — over the caller's store. Fail-closed: every check either
    passes the arm or returns its refusal code. -/
def graphAdmitted (store : List StoreEntry)
    (statementRef receiptRef occurrenceRef occurrence : String) (fuel : Int) :
    EOut :=
  let bs := seamRefBound fuel 3 0 statementRef store
    "[rcic_graph_admitted_statement_unbound]"
  if bs.ok = 0 then eRefuse bs.code
  else
    let sb := (storeScan store statementRef).bytes
    let sk := keysOf sb
    if !covers sk statementMandatory then eRefuse "[rcic_graph_admitted_statement_missing]"
    else if !covers statementKeys sk then eRefuse "[rcic_graph_admitted_statement_extra]"
    else if !coordsOk sb "epoch" "sequence" then eRefuse "[rcic_graph_admitted_statement_coords]"
    else
      let ph := historyOk fuel store sb
      if ph.ok = 0 then eRefuse ph.code
      else
        let br := seamRefBound fuel 8 0 receiptRef store
          "[rcic_graph_admitted_receipt_unbound]"
        if br.ok = 0 then eRefuse br.code
        else
          let rb := (storeScan store receiptRef).bytes
          let jr := judgmentReceiptCheck rb
          if jr.ok = 0 then eRefuse jr.code
          else if partAt rb "statement_ref" ≠ statementRef then
            eRefuse "[rcic_graph_admitted_statement_mismatch]"
          else
            let rr := receiptRefsOk store rb
            if rr.ok = 0 then eRefuse rr.code
            else
              let bb := refBound store (partAt sb "closed_graph_bundle_ref")
                "[rcic_graph_admitted_bundle_unbound]"
              if bb.ok = 0 then eRefuse bb.code
              else
                let oi := occurrenceIdentity store receiptRef occurrenceRef occurrence
                if oi.ok = 0 then eRefuse oi.code
                else if partAt occurrence "statement_ref" ≠ statementRef then
                  eRefuse "[rcic_graph_admitted_occurrence_statement]"
                else
                  let d := decisionCheck store (partAt rb "decision")
                  if d.ok = 0 then eRefuse d.code
                  else if d.ctor = "accepted" then
                    let ja := acceptedCheck store sb d.value
                    if ja.ok = 1 then ⟨1, occurrence, ""⟩ else eRefuse ja.code
                  else ⟨1, occurrence, ""⟩

/-! ## The semantic seam (CG-014's second half) -/

/-- The decode surfaces the byte layer defers to: the env-image codec
    (04 §9/25.11) and the typed-judgment codec. Named unbuilt surfaces — GA-1
    quantifies over them rather than claiming one exists. -/
structure GraphAdmitObjects where
  envAt : List StoreEntry → String → Option ResolvedEnv
  judgmentAt : (store : List StoreEntry) → (ref : String) →
    (E : ResolvedEnv) → Option (EnvWfT E)

/-- CG-014's positive content: the judgment's `admitted_env_ref` decodes to
    `E` and its `typed_judgment_ref` decodes to a composite `EnvWfT E` — one
    typed judgment over exactly that admitted environment, the judgment's
    subject being the statement's closed graph bundle. -/
def TypedJudgmentBound (O : GraphAdmitObjects) (store : List StoreEntry)
    (j : AdmittedGraphJudgment) : Prop :=
  ∃ E : ResolvedEnv, O.envAt store j.admitted_env_ref = some E ∧
    ∃ _wf : EnvWfT E, O.judgmentAt store j.typed_judgment_ref E = some _wf

/-- The decided half of CG-014, reified: everything `acceptedCheck`'s success
    path has established about the resolved bytes `jB` (the judgment record)
    and `tB` (the typed-judgment object). -/
structure AcceptedBindingFacts (store : List StoreEntry) (sb jref jB tB : String) : Prop where
  judgmentResolves : (storeScan store jref).found = true ∧
    (storeScan store jref).collision = false ∧
    (storeScan store jref).bytes = jB
  judgmentCanonical : canonBytesOk jB = true
  judgmentKeysExact : covers (keysOf jB) judgmentKeys = true ∧
    covers judgmentKeys (keysOf jB) = true
  coverageSound : coverageOk (partAt jB "coverage_grade") = true
  subjectMatches : partAt jB "subject_bundle_ref" =
    partAt sb "closed_graph_bundle_ref"
  envResolves : (storeScan store (partAt jB "admitted_env_ref")).found = true ∧
    (storeScan store (partAt jB "admitted_env_ref")).collision = false ∧
    (storeScan store (partAt jB "admitted_env_ref")).bytes ≠ ""
  assumptionsResolves :
    (storeScan store (partAt jB "assumptions_ref")).found = true ∧
    (storeScan store (partAt jB "assumptions_ref")).collision = false ∧
    (storeScan store (partAt jB "assumptions_ref")).bytes ≠ ""
  typedResolves : (storeScan store (partAt jB "typed_judgment_ref")).found = true ∧
    (storeScan store (partAt jB "typed_judgment_ref")).collision = false ∧
    (storeScan store (partAt jB "typed_judgment_ref")).bytes = tB
  typedCanonical : canonBytesOk tB = true
  typedKeysExact : covers (keysOf tB) typedJudgmentKeys = true ∧
    covers typedJudgmentKeys (keysOf tB) = true
  envMatches : partAt tB "env_ref" = partAt jB "admitted_env_ref"
  typedSubjectMatches : partAt tB "subject_bundle_ref" =
    partAt sb "closed_graph_bundle_ref"

/-- The record view of an `AdmittedGraphJudgment` read off canonical bytes.
    Under `coverageOk` the two-value decode is exact. -/
def judgmentOfBytes (bytes : String) : AdmittedGraphJudgment where
  admitted_env_ref := partAt bytes "admitted_env_ref"
  assumptions_ref := partAt bytes "assumptions_ref"
  coverage_grade := if partAt bytes "coverage_grade" = "exact"
    then .exact else .soundOverapproximation
  subject_bundle_ref := partAt bytes "subject_bundle_ref"
  typed_judgment_ref := partAt bytes "typed_judgment_ref"

/-! ## Inversion lemmas -/

/-- An `eRefuse` leaf can never mint the ok triple. -/
theorem eRefuse_ne_ok {c q : String} : eRefuse c ≠ ⟨1, q, ""⟩ := by
  intro h; simp [eRefuse] at h

/-- `ite` inversion over `EOut` results: a conditional result came from one of
    its branches. -/
theorem ite_eq_of {c : Prop} [Decidable c] {a b v : EOut}
    (h : (if c then a else b) = v) : (c ∧ a = v) ∨ (¬c ∧ b = v) := by
  by_cases hc : c
  · rw [if_pos hc] at h; exact Or.inl ⟨hc, h⟩
  · rw [if_neg hc] at h; exact Or.inr ⟨hc, h⟩

/-- A refuse-headed arm of the cascade mints the ok triple only through its
    else branch, with the arm's condition false. -/
theorem arm_ok {c : Prop} [Decidable c] {x : String} {next : EOut} {q : String}
    (h : (if c then eRefuse x else next) = ⟨1, q, ""⟩) :
    ¬c ∧ next = ⟨1, q, ""⟩ := by
  by_cases hc : c
  · rw [if_pos hc] at h; exact absurd h eRefuse_ne_ok
  · rw [if_neg hc] at h; exact ⟨hc, h⟩

/-- `refBound` ok ⇔ the scan resolved to nonempty bytes. -/
theorem refBound_ok {store : List StoreEntry} {r miss : String}
    (h : (refBound store r miss).ok = 1) :
    (storeScan store r).found = true ∧ (storeScan store r).collision = false ∧
      (storeScan store r).bytes ≠ "" := by
  simp only [refBound] at h
  repeat' split at h <;> simp_all [codeRefuse, codeOk]

/-- The typed-judgment arm is sound: `typedJudgmentOk = ok` gives every fact
    it enforces about the resolved object. -/
theorem typedJudgmentOk_sound {store : List StoreEntry} {sb jb : String}
    (h : (typedJudgmentOk store sb jb).ok = 1) :
    (storeScan store (partAt jb "typed_judgment_ref")).found = true ∧
    (storeScan store (partAt jb "typed_judgment_ref")).collision = false ∧
    canonBytesOk (storeScan store (partAt jb "typed_judgment_ref")).bytes = true ∧
    covers (keysOf (storeScan store (partAt jb "typed_judgment_ref")).bytes)
        typedJudgmentKeys = true ∧
    covers typedJudgmentKeys (keysOf (storeScan store
        (partAt jb "typed_judgment_ref")).bytes) = true ∧
    partAt (storeScan store (partAt jb "typed_judgment_ref")).bytes "env_ref" =
      partAt jb "admitted_env_ref" ∧
    partAt (storeScan store (partAt jb "typed_judgment_ref")).bytes
        "subject_bundle_ref" = partAt sb "closed_graph_bundle_ref" := by
  simp only [typedJudgmentOk] at h
  repeat' split at h <;> simp_all [codeRefuse, codeOk]

/-- The CG-014 arm is sound: `acceptedCheck = ok` yields resolved judgment and
    typed-judgment bytes carrying `AcceptedBindingFacts`. -/
theorem acceptedCheck_sound {store : List StoreEntry} {sb jref : String}
    (h : (acceptedCheck store sb jref).ok = 1) :
    ∃ jB tB, AcceptedBindingFacts store sb jref jB tB := by
  simp only [acceptedCheck] at h
  repeat' split at h <;> first | simp_all [codeRefuse, codeOk] | skip
  · rename_i hjf hjc hcb hk1 hk2 hcv hsm heb hab
    have ht := typedJudgmentOk_sound
      (jb := (storeScan store jref).bytes) h
    have he := refBound_ok
      (r := partAt (storeScan store jref).bytes "admitted_env_ref")
      (miss := "[rcic_graph_admitted_env_unbound]") heb
    have ha := refBound_ok
      (r := partAt (storeScan store jref).bytes "assumptions_ref")
      (miss := "[rcic_graph_admitted_assumptions_unbound]") hab
    obtain ⟨htf, htc, htbc, htk1, htk2, henv, htsub⟩ := ht
    exact ⟨_, _, {
      judgmentResolves := ⟨hjf, hjc, rfl⟩
      judgmentCanonical := hcb
      judgmentKeysExact := ⟨hk1, hk2⟩
      coverageSound := hcv
      subjectMatches := hsm
      envResolves := he
      assumptionsResolves := ha
      typedResolves := ⟨htf, htc, rfl⟩
      typedCanonical := htbc
      typedKeysExact := ⟨htk1, htk2⟩
      envMatches := henv
      typedSubjectMatches := htsub }⟩

/-- An `ok` triple whose decision spells `accepted` ran the CG-014 arm — the
    decided half of CG-014 at the recorded-triple level. -/
theorem graphAdmitted_accepted_binding {store : List StoreEntry}
    {statementRef receiptRef occurrenceRef occurrence : String} {fuel : Int}
    {jref : String}
    (hok : graphAdmitted store statementRef receiptRef occurrenceRef occurrence fuel =
      ⟨1, occurrence, ""⟩)
    (hdec : decisionCheck store
      (partAt (storeScan store receiptRef).bytes "decision") =
      ⟨1, "", "accepted", jref⟩) :
    ∃ jB tB, AcceptedBindingFacts store (storeScan store statementRef).bytes jref jB tB := by
  apply acceptedCheck_sound
  unfold graphAdmitted at hok
  simp only [] at hok
  repeat' (obtain ⟨_, hok⟩ := arm_ok hok)
  obtain ⟨bd, hok⟩ | ⟨bd, hok⟩ := ite_eq_of hok
  · obtain ⟨bj, hok⟩ | ⟨bj, hok⟩ := ite_eq_of hok
    · have hv : (decisionCheck store
          (partAt (storeScan store receiptRef).bytes "decision")).value = jref :=
        congrArg DOut.value hdec
      rw [hv] at bj
      exact bj
    · exact absurd hok eRefuse_ne_ok
  · have hc : (decisionCheck store
        (partAt (storeScan store receiptRef).bytes "decision")).ctor = "accepted" :=
      congrArg DOut.ctor hdec
    exact absurd hc bd

/-! ## CG-014 -/

/-- CG-014, the chain-level reading: wherever the decoders stand, a
    `done (accepted j)` carries the composite `EnvWfT`. -/
theorem cg014_typed_judgment (O : GraphAdmitObjects) (store : List StoreEntry)
    (j : AdmittedGraphJudgment) (E : ResolvedEnv)
    (henv : O.envAt store j.admitted_env_ref = some E) (wf : EnvWfT E)
    (htj : O.judgmentAt store j.typed_judgment_ref E = some wf) :
    TypedJudgmentBound O store j := ⟨E, henv, wf, htj⟩

/-- CG-014 composed: a validated accepted triple's decided binding, plus the
    (named unbuilt) decode surfaces, yields the typed judgment over the
    admitted environment. -/
theorem cg014_of_binding (O : GraphAdmitObjects) (store : List StoreEntry)
    {sb jref jB tB : String} (_hb : AcceptedBindingFacts store sb jref jB tB)
    (E : ResolvedEnv)
    (henv : O.envAt store (partAt jB "admitted_env_ref") = some E)
    (wf : EnvWfT E)
    (htj : O.judgmentAt store
      (partAt jB "typed_judgment_ref") E = some wf) :
    TypedJudgmentBound O store (judgmentOfBytes jB) :=
  ⟨E, henv, wf, htj⟩

/-! ## Teeth -/

/-- `coverage_grade` `unknown` is not a sound grade — the ruled refusal. -/
theorem tooth_coverage_unknown : coverageOk "unknown" = false := rfl

/-- The two admitted grades pass. -/
theorem coverageOk_exact : coverageOk "exact" = true := rfl
theorem coverageOk_soundOverapproximation :
    coverageOk "soundOverapproximation" = true := rfl

/-- A `suspended` key is not a decision constructor: it lands on the
    extra-name tooth, never on a fourth constructor. -/
theorem tooth_suspended_not_decision (names : List String)
    (h : names = decisionNames) : names.contains "suspended" = false := by
  rw [h]; decide

/-- Extra-keyed decision bytes spell outside the three constructors:
    `exactlyOneName` returns 3 (the `[rcic_judgment_decision_extra]` leg). -/
theorem tooth_decision_extra {bytes : String}
    (hb : bytes ≠ "") (hc : canonBytesOk bytes = true)
    (hk : covers decisionNames (keysOf bytes) = false) :
    exactlyOneName bytes decisionNames = 3 := by
  simp only [exactlyOneName]
  rw [if_neg hb, if_neg (by simp [hc]), if_pos (by simp [hk])]

/-- Empty decision bytes spell nothing: `missing` (leg 1). -/
theorem tooth_decision_empty : exactlyOneName "" decisionNames = 1 := rfl

/-- No decision constructor spelled: the `missing` leg. -/
theorem tooth_decision_missing {bytes : String}
    (hb : bytes ≠ "") (hc : canonBytesOk bytes = true)
    (hk : covers decisionNames (keysOf bytes) = true)
    (hn : decisionNames.foldl
      (fun acc e => if (keysOf bytes).contains e then acc + 1 else acc) 0 = 0) :
    exactlyOneName bytes decisionNames = 1 := by
  simp only [exactlyOneName]
  rw [if_neg hb, if_neg (by simp [hc]), if_neg (by simp [hk])]
  rw [if_neg (by omega), if_pos hn]

/-- Two or more constructors spelled at once land on the `two` tooth. -/
theorem tooth_decision_two {bytes : String}
    (hb : bytes ≠ "") (hc : canonBytesOk bytes = true)
    (hk : covers decisionNames (keysOf bytes) = true)
    (hn0 : decisionNames.foldl
      (fun acc e => if (keysOf bytes).contains e then acc + 1 else acc) 0 ≠ 0)
    (hn1 : decisionNames.foldl
      (fun acc e => if (keysOf bytes).contains e then acc + 1 else acc) 0 ≠ 1) :
    exactlyOneName bytes decisionNames = 2 := by
  simp only [exactlyOneName]
  rw [if_neg hb, if_neg (by simp [hc]), if_neg (by simp [hk])]
  rw [if_neg (by omega), if_neg (by omega)]

/-- An unbound judgment is the CG-014 tooth, not an acceptance. -/
theorem tooth_accepted_judgment_unbound {store : List StoreEntry} {sb jref : String}
    (h : (storeScan store jref).found = false) :
    acceptedCheck store sb jref = codeRefuse "[rcic_cg014_judgment]" := by
  simp only [acceptedCheck]
  rw [if_pos (by simp [h])]

/-- An unbound decision ref refuses at its own code, not as a subject. -/
theorem tooth_decision_unbound {store : List StoreEntry} {dref : String}
    (h : (storeScan store dref).found = false) :
    decisionCheck store dref =
      ⟨0, "[rcic_graph_admitted_decision_unbound]", "", ""⟩ := by
  simp only [decisionCheck]
  rw [if_pos (by simp [h])]

/-- An unbound typed judgment is the CG-014 tooth. -/
theorem tooth_typed_judgment_unbound {store : List StoreEntry} {sb jb : String}
    (h : (storeScan store (partAt jb "typed_judgment_ref")).found = false) :
    typedJudgmentOk store sb jb = codeRefuse "[rcic_cg014_judgment]" := by
  simp only [typedJudgmentOk]
  rw [if_pos (by simp [h])]

/-- A typed judgment whose `env_ref` differs from the judgment's
    `admitted_env_ref` is the CG-014 tooth — provided the earlier arms pass. -/
theorem tooth_typed_env_mismatch {store : List StoreEntry} {sb jb : String}
    (hres : (storeScan store (partAt jb "typed_judgment_ref")).found = true)
    (hcol : (storeScan store (partAt jb "typed_judgment_ref")).collision = false)
    (hcan : canonBytesOk (storeScan store
      (partAt jb "typed_judgment_ref")).bytes = true)
    (hk1 : covers (keysOf (storeScan store
      (partAt jb "typed_judgment_ref")).bytes) typedJudgmentKeys = true)
    (hk2 : covers typedJudgmentKeys (keysOf (storeScan store
      (partAt jb "typed_judgment_ref")).bytes) = true)
    (henv : partAt (storeScan store
      (partAt jb "typed_judgment_ref")).bytes "env_ref" ≠
      partAt jb "admitted_env_ref") :
    typedJudgmentOk store sb jb = codeRefuse "[rcic_cg014_judgment]" := by
  simp only [typedJudgmentOk]
  rw [if_neg (by simp [hres]), if_neg (by simp [hcol])]
  rw [if_neg (by simp [hcan]), if_neg (by simp [hk1]), if_neg (by simp [hk2])]
  rw [if_pos henv]

/-- 26.2a: an unbuilt stage is an integrity residue — disjoint from every
    subject refusal tag, and it is a `GraphIntegrity` constructor. -/
theorem tooth_unbuilt_stage_is_integrity {r : GraphRefusal} :
    (JudgmentDecision.integrityResidue GraphIntegrity.unbuilt_stage :
      GraphAdmitDecision) ≠ .refused r :=
  integrity_ne_refused

/-- §15/FC-13: a suspended run mints no receipt and no occurrence. -/
theorem tooth_suspended_mints_nothing (s : GraphAdmissionState) :
    publishable (.suspended s : GraphAdmitResult) = false := rfl

/-- §15/FC-13's second leg: a run result is `done` or `suspended`, never both. -/
theorem tooth_done_ne_suspended {d : GraphAdmitDecision} {s : GraphAdmissionState} :
    (JudgmentRunResult.done d : GraphAdmitResult) ≠ .suspended s :=
  done_ne_suspended

#print axioms Rcic.GraphAdmitted.refBound_ok
#print axioms Rcic.GraphAdmitted.typedJudgmentOk_sound
#print axioms Rcic.GraphAdmitted.acceptedCheck_sound
#print axioms Rcic.GraphAdmitted.graphAdmitted_accepted_binding
#print axioms Rcic.GraphAdmitted.cg014_typed_judgment
#print axioms Rcic.GraphAdmitted.cg014_of_binding
#print axioms Rcic.GraphAdmitted.tooth_coverage_unknown
#print axioms Rcic.GraphAdmitted.tooth_suspended_not_decision
#print axioms Rcic.GraphAdmitted.tooth_decision_extra
#print axioms Rcic.GraphAdmitted.tooth_decision_empty
#print axioms Rcic.GraphAdmitted.tooth_decision_missing
#print axioms Rcic.GraphAdmitted.tooth_decision_two
#print axioms Rcic.GraphAdmitted.tooth_accepted_judgment_unbound
#print axioms Rcic.GraphAdmitted.tooth_decision_unbound
#print axioms Rcic.GraphAdmitted.tooth_typed_judgment_unbound
#print axioms Rcic.GraphAdmitted.tooth_typed_env_mismatch
#print axioms Rcic.GraphAdmitted.tooth_unbuilt_stage_is_integrity
#print axioms Rcic.GraphAdmitted.tooth_suspended_mints_nothing
#print axioms Rcic.GraphAdmitted.tooth_done_ne_suspended

end Rcic.GraphAdmitted

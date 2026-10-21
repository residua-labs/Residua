/-
RCIC Annex 26.1 — the `ChallengeResolutionOccurrence` judge, the pinned
Lean model of `apps/rcic-challenge-resolution`
(`rcic.challenge_resolution fuel store occ_digest`).

The carrier judges ONE store-carried resolution occurrence (decided object,
`docs/rcic/00_ANNEX_26_OBJECT_DECISIONS.md`, #6406): canonical 01:372
occurrence shape with `kind:challenge_resolution`, the ruled five-key
statement `basis_ref|challenge_ref|disposition|realization_ref|validator_occ_ref`,
the landed three-key receipt `challenge_ref|decision|validator_occ_ref`,
every ref bound in the store, the 12:145 genesis-recovery-floor exclusion on
`validated` decisions, and the mechanical validator checks (strict
epoch/sequence ancestry, exclusion of the challenged checker and of
self-replay, and exclusion of the challenged target's descendant cone via
the `predecessor:` edge fixpoint). `closure_claim` stays 0 — the semantic
load-bearing-closure half (does `realization_ref` repair the defect) is a
named residual, same posture as Annex 25; nothing here evaluates evidence
semantics.

PIN: all 39 rows of
`apps/rcic-challenge-resolution/rcic_challenge_resolution_corpus.json`
below (M-002); each refusal is a named `[rcic_resol_*]` residue.

TRANSCRIPTION TABLE (the scm modules → Lean):
  rcic.challenge_keys / classes / class_ok / label_hit
                                    → `challengeKeys`/`challengeClasses`/
                                      `challengeClassOk`/`challengeLabelHit`
  rcic.challenge_record (form 0)    → `challengeAccepted`
  rcic.challenge_receipt_keys       → `challengeReceiptKeys`
  rcic.challenge_decision_ok        → `challengeDecisionOk`
  rcic.challenge_resolution_occ_keys  → `resolOccKeys`
  rcic.challenge_resolution_stmt_keys → `resolStmtKeys`
  rcic.challenge_resolution_dispositions → `resolDispositions`
  rcic.challenge_resolution_disposition_ok → `resolDispositionOk`
  rcic.challenge_resolution_suppressing → `resolSuppressing`
  rcic.challenge_resolution_genesis_refs → `genesisRefs`
  rcic.challenge_resolution_floor_refs   → `floorRefs`
  rcic.challenge_resolution_target_genesis → `targetGenesis`
  rcic.rec_independence_occ_edges   → `occEdges`
  rcic.cog_bundle_pass / fix        → `cogBundlePass`/`cogBundleFixN`
  rcic.auth_activation_ref_bound    → `Rcic.AuthorityCritical.refBound` (reused)
  rcic.challenge_resolution_validator_ok → `validatorOk`
  rcic.challenge_resolution_ok / refuse  → `resolOk`/`resolRefuse`
  rcic.challenge_resolution         → `evalChallengeResolution`
-/
import rcic.RcicAuthorityCriticalModel

namespace Rcic.ChallengeResolution

open Rcic.BoundObject (StoreEntry canonBytesOk storeScan)
open Rcic.Scm.Embed (partAt)
open Rcic.ScopeExact (keysOk listCanon listInsert edgeStr)
open Rcic.AuthorityCritical (strToInt digitsOk refBound)

/-! ## The challenge-record predicates (also `rcic.challenge_record` form 0,
    reused by the open-residues model) -/

/-- `rcic.challenge_keys`: the five required challenge-record keys. -/
def challengeKeys : List String :=
  ["basis_ref", "evidence_bytes", "evidence_class", "reproducer_ref", "target_ref"]

/-- `rcic.challenge_classes`: the eight admitted `evidence_class` values. -/
def challengeClasses : List String :=
  ["deterministic_divergence", "counterexample_refutation",
   "proof_of_contradiction", "artifact_binding_mismatch",
   "canonical_collision_witness", "independent_verifier_divergence",
   "cryptographic_assumption_withdrawal", "physical_execution_mismatch"]

/-- `rcic.challenge_class_ok`: membership in `challengeClasses`. -/
def challengeClassOk (c : String) : Bool := challengeClasses.contains c

/-- `rcic.challenge_label_hit`: any `,`-member of `evidence_bytes` in the
    label vocabulary `{label, severity, approved, broken=true}`. -/
def challengeLabelHit (ev : String) : Bool :=
  (ev.splitOn ",").any (fun m =>
    m = "label" || m = "severity" || m = "approved" || m = "broken=true")

/-- `rcic.challenge_record` form 0, the `ok = 1` bit: fuel head, canonical
    bytes, exactly the five challenge keys, a known `evidence_class`, and
    `evidence_bytes` not a label. -/
def challengeAccepted (fuel : Int) (bytes : String) : Bool :=
  decide (0 ≤ fuel) && canonBytesOk bytes && keysOk bytes challengeKeys &&
    challengeClassOk (partAt bytes "evidence_class") &&
    !challengeLabelHit (partAt bytes "evidence_bytes")

/-- `rcic.challenge_receipt_keys`: the landed three-key narrowing. -/
def challengeReceiptKeys : List String :=
  ["challenge_ref", "decision", "validator_occ_ref"]

/-- `rcic.challenge_decision_ok`: the closed receipt-decision enum. -/
def challengeDecisionOk (d : String) : Bool :=
  d = "validated" || d = "refuted"

/-! ## The Annex 26.1 carrier shape -/

/-- `rcic.challenge_resolution_occ_keys`: the 01:372 occurrence shape. -/
def resolOccKeys : List String :=
  ["epoch", "kind", "receipt_ref", "sequence", "statement_ref"]

/-- `rcic.challenge_resolution_stmt_keys`: the ruled five statement keys. -/
def resolStmtKeys : List String :=
  ["basis_ref", "challenge_ref", "disposition", "realization_ref",
   "validator_occ_ref"]

/-- `rcic.challenge_resolution_dispositions`: the closed §10 enum. -/
def resolDispositions : List String :=
  ["revalidated", "transported", "retired", "reopened"]

/-- `rcic.challenge_resolution_disposition_ok`. -/
def resolDispositionOk (d : String) : Bool := resolDispositions.contains d

/-- `rcic.challenge_resolution_suppressing`: the Annex 26.1 suppression
    subset — `revalidated` and `transported` only; `retired` is a permanent
    residue and `reopened` is an open residue (§10), so they never suppress. -/
def resolSuppressing (d : String) : Bool :=
  d = "revalidated" || d = "transported"

/-! ## 12:145 — the genesis-recovery-floor set -/

/-- `rcic.challenge_resolution_genesis_refs`: digests of `kind:genesis`
    entries with no `predecessor` part (the genesis roots). -/
def genesisRefs (store : List StoreEntry) : List String :=
  store.foldl (fun acc e =>
    if partAt e.bytes "kind" = "genesis" && partAt e.bytes "predecessor" = ""
    then acc ++ [e.digest] else acc) []

/-- `rcic.challenge_resolution_floor_refs`: every store entry's
    `genesis_recovery_floor_ref` value (named floor refs). -/
def floorRefs (store : List StoreEntry) : List String :=
  store.foldl (fun acc e =>
    let v := partAt e.bytes "genesis_recovery_floor_ref"
    if v = "" then acc else acc ++ [v]) []

/-- `rcic.challenge_resolution_target_genesis`: `target` names a genesis
    root or a recovery-floor ref — a `validated` resolution against it is
    refused (12:145; such a defect can only be refuted). -/
def targetGenesis (store : List StoreEntry) (target : String) : Bool :=
  (genesisRefs store).contains target || (floorRefs store).contains target

/-! ## The challenged-target descendant cone -/

/-- `rcic.rec_independence_occ_edge_one`: one `predecessor:` edge
    `p>occ>digest`, sorted-inserted. -/
def occEdgeOne (e : StoreEntry) (edges : List String) : List String :=
  let p := partAt e.bytes "predecessor"
  if p = "" then edges else listInsert edges (edgeStr p "occ" e.digest)

/-- `rcic.rec_independence_occ_edges`: all predecessor edges in the store. -/
def occEdges (store : List StoreEntry) : List String :=
  store.foldl (fun acc e => occEdgeOne e acc) []

/-- `rcic.cog_bundle_pass`: insert every edge target whose source is
    already in the table. -/
def cogBundlePass (edges table : List String) : List String :=
  edges.foldl (fun acc e =>
    let p := e.splitOn ">"
    match p.head? with
    | some src =>
        if acc.contains src then listInsert acc (p.getLastD "") else acc
    | none => acc) table

/-- `rcic.cog_bundle_fix` on a `Nat` fuel: iterate `cogBundlePass` to a
    fixpoint (`some table`) or exhaust fuel (`none` — the scm `{ok 0}`
    outcome). The fuel check order matches the scm: the pass/fixpoint test
    runs before the fuel test at every step. -/
def cogBundleFixN : Nat → List String → List String → Option (List String)
  | 0, edges, table =>
      let next := cogBundlePass edges table
      if next = table then some next else none
  | n + 1, edges, table =>
      let next := cogBundlePass edges table
      if next = table then some next else cogBundleFixN n edges next

/-- `rcic.challenge_resolution_validator_ok`, the Bool reading (the scm
    module's only failure code is `[rcic_resol_validator_dependent]`, so the
    `ok` bit carries the whole verdict): the validator occurrence resolves
    as a canonical class-3/kind-0 object strictly earlier than the
    resolution's own coordinates; it is not the challenged target, its
    `artifact` is present and not the target; its `receipt` resolves and its
    `validator_artifact_ref` is present and not the target (the validator
    did not run the challenged checker — no self-replay); and the validator
    is not in the challenged target's predecessor-descendant cone. -/
def validatorOk (fuel : Int) (store : List StoreEntry) (occBytes target : String)
    (validatorOccRef : String) : Bool :=
  let re := strToInt (partAt occBytes "epoch")
  let rq := strToInt (partAt occBytes "sequence")
  let vb := refBound (fuel - 1) 3 0 validatorOccRef store re rq 1
              "[rcic_resol_validator_dependent]"
  if vb.ok = 0 then false
  else if validatorOccRef = target then false
  else
    let vart := partAt vb.bytes "artifact"
    if vart = "" then false
    else if vart = target then false
    else
      let vr := partAt vb.bytes "receipt"
      let vrs := storeScan store vr
      if !vrs.found then false
      else if vrs.collision then false
      else
        let vchk := partAt vrs.bytes "validator_artifact_ref"
        if vchk = "" then false
        else if vchk = target then false
        else
          match cogBundleFixN (fuel - 1).toNat (occEdges store)
                (listCanon [target]) with
          | some table => !table.contains validatorOccRef
          | none => false

/-! ## The judge -/

/-- `rcic.challenge_resolution`'s sigma
    `{ok, occ, challenge_ref, decision, disposition, validator_occ_ref,
    code}`. -/
structure CROut where
  ok : Int
  occ : String
  challengeRef : String
  decision : String
  disposition : String
  validatorOccRef : String
  code : String
  deriving BEq

/-- `rcic.challenge_resolution_refuse`. -/
def resolRefuse (code : String) : CROut := ⟨0, "", "", "", "", "", code⟩

/-- `rcic.challenge_resolution_ok`'s record (the validator gate folded in:
    the accept record is only produced after `validatorOk`). -/
def resolOk (occ challengeRef decision disposition validatorOccRef : String) :
    CROut := ⟨1, occ, challengeRef, decision, disposition, validatorOccRef, ""⟩

/-- `rcic.challenge_resolution`: the full leg chain, in scm order. -/
def evalChallengeResolution (fuel : Int) (store : List StoreEntry)
    (occDigest : String) : CROut :=
  if fuel < 0 then resolRefuse "[rcic_resol_fuel]"
  else
    let os := storeScan store occDigest
    if !os.found then resolRefuse "[rcic_resol_occ_unbound]"
    else if os.collision then resolRefuse "[rcic_resol_occ_unbound]"
    else if !canonBytesOk os.bytes then resolRefuse "[rcic_resol_noncanonical]"
    else if !keysOk os.bytes resolOccKeys then resolRefuse "[rcic_resol_occ_shape]"
    else if partAt os.bytes "kind" ≠ "challenge_resolution" then
      resolRefuse "[rcic_resol_occ_kind]"
    else if !(digitsOk (partAt os.bytes "epoch") &&
              digitsOk (partAt os.bytes "sequence")) then
      resolRefuse "[rcic_resol_occ_coordinates]"
    else
      let sr := partAt os.bytes "statement_ref"
      let ss := storeScan store sr
      if !ss.found then resolRefuse "[rcic_resol_stmt_unbound]"
      else if ss.collision then resolRefuse "[rcic_resol_stmt_unbound]"
      else if !canonBytesOk ss.bytes then resolRefuse "[rcic_resol_noncanonical]"
      else if !keysOk ss.bytes resolStmtKeys then resolRefuse "[rcic_resol_shape]"
      else
        let disp := partAt ss.bytes "disposition"
        if !resolDispositionOk disp then
          resolRefuse "[rcic_resol_unknown_disposition]"
        else
          let rr := partAt os.bytes "receipt_ref"
          let rs := storeScan store rr
          if !rs.found then resolRefuse "[rcic_resol_receipt_unbound]"
          else if rs.collision then resolRefuse "[rcic_resol_receipt_unbound]"
          else if !canonBytesOk rs.bytes then
            resolRefuse "[rcic_resol_noncanonical]"
          else if !keysOk rs.bytes challengeReceiptKeys then
            resolRefuse "[rcic_resol_receipt_shape]"
          else
            let dec := partAt rs.bytes "decision"
            if !challengeDecisionOk dec then
              resolRefuse "[rcic_resol_unknown_decision]"
            else
              let cr := partAt ss.bytes "challenge_ref"
              if partAt rs.bytes "challenge_ref" ≠ cr then
                resolRefuse "[rcic_resol_receipt_mismatch]"
              else if partAt rs.bytes "validator_occ_ref" ≠
                      partAt ss.bytes "validator_occ_ref" then
                resolRefuse "[rcic_resol_receipt_mismatch]"
              else
                let cs := storeScan store cr
                if !cs.found then resolRefuse "[rcic_resol_challenge_absent]"
                else if cs.collision then
                  resolRefuse "[rcic_resol_challenge_absent]"
                else if !challengeAccepted (fuel - 1) cs.bytes then
                  resolRefuse "[rcic_resol_challenge_absent]"
                else
                  let bs := storeScan store (partAt ss.bytes "basis_ref")
                  if !bs.found then resolRefuse "[rcic_resol_basis_unbound]"
                  else if bs.collision then
                    resolRefuse "[rcic_resol_basis_unbound]"
                  else
                    let zs := storeScan store (partAt ss.bytes "realization_ref")
                    if !zs.found then resolRefuse "[rcic_resol_realization_unbound]"
                    else if zs.collision then
                      resolRefuse "[rcic_resol_realization_unbound]"
                    else
                      let target := partAt cs.bytes "target_ref"
                      let vo := partAt ss.bytes "validator_occ_ref"
                      if dec = "validated" && targetGenesis store target then
                        resolRefuse "[rcic_resol_target_genesis]"
                      else if !validatorOk (fuel - 1) store os.bytes target vo then
                        resolRefuse "[rcic_resol_validator_dependent]"
                      else resolOk occDigest cr dec disp vo

/-! ## Record-level statements -/

/-- Negative fuel refuses with the fuel residue. -/
theorem evalChallengeResolution_fuel (fuel : Int) (store : List StoreEntry)
    (occDigest : String) (h : fuel < 0) :
    evalChallengeResolution fuel store occDigest =
      resolRefuse "[rcic_resol_fuel]" := by
  unfold evalChallengeResolution; rw [if_pos h]

/-- The accept record reports every field the consumer needs: the
    occurrence, the resolved challenge, and BOTH the receipt decision and
    the §10 disposition (which dispositions suppress is the consumer's
    ruling — this judge reports, never subtracts). -/
def acceptReports' (o : CROut) : Prop :=
  o.ok = 1 →
    challengeDecisionOk o.decision = true ∧
    resolDispositionOk o.disposition = true

/-- Fail-closed reading: on a refusal the occ/challenge/decision/
    disposition/validator fields are all empty — a refused resolution can
    never be mistaken for evidence. -/
def refuseEmpty' (o : CROut) : Prop :=
  o.ok = 0 → o.occ = "" ∧ o.challengeRef = "" ∧ o.decision = "" ∧
    o.disposition = "" ∧ o.validatorOccRef = ""

theorem resolRefuse_empty (code : String) : refuseEmpty' (resolRefuse code) := by
  intro _; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A `resolves:` token entry can never be a resolution occurrence: it is
    not canonical challenge-record bytes and carries no
    `kind:challenge_resolution` part — and even read as bytes it is not
    `challenge_record`-accepted (one part, not five). -/
theorem not_accepted_of_part_count (fuel : Int) (bytes : String)
    (h : (bytes.splitOn "|").length ≠ challengeKeys.length) :
    challengeAccepted fuel bytes = false := by
  have hk : keysOk bytes challengeKeys = false := by
    unfold keysOk; simp [h]
  simp [challengeAccepted, hk]

#guard challengeAccepted 100 "resolves:c1" == false

/-! ## Corpus pins: all 39 rows of
    `apps/rcic-challenge-resolution/rcic_challenge_resolution_corpus.json`.
    Each `expected` is the carrier's full produced record (M-002). -/
-- row 0: validated revalidated resolution accepted
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨1, "o1", "c1", "validated", "revalidated", "464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", ""⟩

-- row 1: validated transported resolution accepted
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:transported|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨1, "o1", "c1", "validated", "transported", "464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", ""⟩

-- row 2: validated retired resolution accepted (no suppression decided here)
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨1, "o1", "c1", "validated", "retired", "464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", ""⟩

-- row 3: validated reopened resolution accepted (never suppresses)
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:reopened|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨1, "o1", "c1", "validated", "reopened", "464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", ""⟩

-- row 4: refuted resolution accepted (adjudicated refusal)
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:refuted|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨1, "o1", "c1", "refuted", "revalidated", "464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", ""⟩

-- row 5: refuted on genesis-root target accepted (12:145 blocks only validated)
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c2|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c2|decision:refuted|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨1, "o1", "c2", "refuted", "revalidated", "464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", ""⟩

-- row 6: validator with an unrelated predecessor accepted
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"30fc13259f1b2af2c91e69460f35eb7842d909406bc1855f147cd88095145869", "artifact:va|epoch:0|kind:successor|predecessor:x9|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:30fc13259f1b2af2c91e69460f35eb7842d909406bc1855f147cd88095145869"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:30fc13259f1b2af2c91e69460f35eb7842d909406bc1855f147cd88095145869"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"x9", "artifact:old|epoch:0|kind:successor|receipt:r9|sequence:0|statement:s9"⟩] "o1" == ⟨1, "o1", "c1", "validated", "revalidated", "30fc13259f1b2af2c91e69460f35eb7842d909406bc1855f147cd88095145869", ""⟩

-- row 7: negative fuel refused
#guard evalChallengeResolution (-1) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_fuel]"⟩

-- row 8: occurrence digest absent refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "oX" == ⟨0, "", "", "", "", "", "[rcic_resol_occ_unbound]"⟩

-- row 9: occurrence digest collision refused
#guard evalChallengeResolution (100) [⟨"o1", "different_bytes"⟩, ⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_occ_unbound]"⟩

-- row 10: occurrence noncanonical bytes refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "kind:challenge_resolution|epoch:0|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_noncanonical]"⟩

-- row 11: occurrence extra key refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1|zzz:1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_occ_shape]"⟩

-- row 12: occurrence wrong kind refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_occ_kind]"⟩

-- row 13: occurrence non-digit epoch refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:zero|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_occ_coordinates]"⟩

-- row 14: statement unbound refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:sX"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_stmt_unbound]"⟩

-- row 15: statement noncanonical refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "challenge_ref:c1|basis_ref:b1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_noncanonical]"⟩

-- row 16: statement missing key refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_shape]"⟩

-- row 17: unknown disposition refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:dissolved|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_unknown_disposition]"⟩

-- row 18: receipt unbound refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:rX|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_receipt_unbound]"⟩

-- row 19: receipt wrong keys refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|extra:1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_receipt_shape]"⟩

-- row 20: unknown decision refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:accepted|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_unknown_decision]"⟩

-- row 21: receipt challenge_ref mismatch refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c9|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_receipt_mismatch]"⟩

-- row 22: receipt validator_occ_ref mismatch refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:vX"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_receipt_mismatch]"⟩

-- row 23: challenge_ref absent refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:cX|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:cX|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_challenge_absent]"⟩

-- row 24: challenge_ref names a non-challenge object refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:b1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:b1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_challenge_absent]"⟩

-- row 25: basis_ref unbound refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:bX|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_basis_unbound]"⟩

-- row 26: realization_ref unbound refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:zX|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_realization_unbound]"⟩

-- row 27: validated resolution on genesis-root target refused (12:145)
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c2|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c2|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_target_genesis]"⟩

-- row 28: validated resolution on floor-ref target refused (12:145)
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c3|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c3|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_target_genesis]"⟩

-- row 29: validator occurrence unbound refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:vX"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:vX"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_validator_dependent]"⟩

-- row 30: validator not strictly earlier refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"87451fa9523f438d38dde80fde3942da5be26a8685405e51d8d3cb51086643f0", "artifact:va|epoch:1|kind:successor|receipt:vr|sequence:9|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:87451fa9523f438d38dde80fde3942da5be26a8685405e51d8d3cb51086643f0"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:87451fa9523f438d38dde80fde3942da5be26a8685405e51d8d3cb51086643f0"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_validator_dependent]"⟩

-- row 31: validator equal coordinates refused (not strictly earlier)
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"7555d6d9eeff2c28e8ef986dc3f8c9d47234b38492faeddbef4a7b84675f31a4", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:5|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:7555d6d9eeff2c28e8ef986dc3f8c9d47234b38492faeddbef4a7b84675f31a4"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:7555d6d9eeff2c28e8ef986dc3f8c9d47234b38492faeddbef4a7b84675f31a4"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_validator_dependent]"⟩

-- row 32: validator is the challenged target refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:t1"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:t1"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"t1", "artifact:t1a|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_validator_dependent]"⟩

-- row 33: validator artifact is the challenged target refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"84604b0555a90e63731ea495e3be186561c5a57ddfc42f82b99e7456bc2537bb", "artifact:t1|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:84604b0555a90e63731ea495e3be186561c5a57ddfc42f82b99e7456bc2537bb"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:84604b0555a90e63731ea495e3be186561c5a57ddfc42f82b99e7456bc2537bb"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_validator_dependent]"⟩

-- row 34: validator ran the challenged checker (self-replay) refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:t1"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_validator_dependent]"⟩

-- row 35: validator in the challenged occurrence descendant cone refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"fd5529a0e977202c27405e46398606928e14bca15d678480c10fc44ff6a90160", "artifact:va|epoch:0|kind:successor|predecessor:t1|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:fd5529a0e977202c27405e46398606928e14bca15d678480c10fc44ff6a90160"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:fd5529a0e977202c27405e46398606928e14bca15d678480c10fc44ff6a90160"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"t1", "artifact:t1|epoch:0|kind:successor|receipt:rt|sequence:0|statement:st"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_validator_dependent]"⟩

-- row 36: validator receipt unbound refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "gone"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_validator_dependent]"⟩

-- row 37: validator receipt missing validator_artifact_ref refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "other:1"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_validator_dependent]"⟩

-- row 38: validator artifact part empty refused
#guard evalChallengeResolution (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:g0"⟩, ⟨"c3", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:fl1"⟩, ⟨"g0", "artifact:ag|epoch:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩, ⟨"cap", "genesis_recovery_floor_ref:fl1|other:1"⟩, ⟨"fl1", "floor_object"⟩, ⟨"7529bd1ab83b2f53100152dedce6d65f18f05568952f7df255118d334f217a69", "epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:7529bd1ab83b2f53100152dedce6d65f18f05568952f7df255118d334f217a69"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:7529bd1ab83b2f53100152dedce6d65f18f05568952f7df255118d334f217a69"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "o1" == ⟨0, "", "", "", "", "", "[rcic_resol_validator_dependent]"⟩

#print axioms Rcic.ChallengeResolution.evalChallengeResolution_fuel
#print axioms Rcic.ChallengeResolution.resolRefuse_empty
#print axioms Rcic.ChallengeResolution.not_accepted_of_part_count

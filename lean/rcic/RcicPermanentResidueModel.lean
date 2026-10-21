/-
RCIC Annex 26.15 — the `PermanentResidueRecord` judge, the pinned Lean
model of `apps/rcic-permanent-residue`
(`rcic.permanent_residue fuel store digest`).

The carrier judges ONE store-carried permanent residue (decided object,
`docs/rcic/ANNEX_26_3_PERMANENT_RESIDUE_PROPOSAL.md`, accepted as Annex
26.15 on #6466): the canonical three-key record
`kind:permanent_residue|minted_by:<digest>|obligation_ref:<digest>` — a
record, not a 01:372 occurrence, since the minting occurrence already
carries the validator. Two admitted minter arms:

* **Arm A** — an accepted `challenge_resolution` occurrence whose
  `decision` is `validated` and `disposition` is `retired`; its
  statement's `realization_ref` must equal the residue digest and its
  `challenge_ref` must equal the residue's `obligation_ref`.
* **Arm B** — an accepted `effect_reconcile` disposition whose
  `constructor` is `irreparable`; its `permanent_residue_ref` must equal
  the residue digest and its `effect_ref` must equal the residue's
  `obligation_ref` (and the effect must itself be accepted by
  `rcic.effect_reconcile_effect`).

All other minter kinds and arms refuse; unbound/colliding digests,
noncanonical bytes, wrong key shapes, broken back-references, wrong
obligation references, and duplicate residues claiming one minter all
refuse. `closure_claim` stays 0.

PIN: all 28 rows of
`apps/rcic-permanent-residue/rcic_permanent_residue_corpus.json`
below; each refusal is a named `[rcic_permres_*]` residue.

TRANSCRIPTION TABLE (the scm modules → Lean):
  rcic.permanent_residue_keys            → `permResKeys`
  rcic.effect_reconcile_ctors            → `effectCtors`
  rcic.effect_reconcile_keys             → `effectKeys`
  rcic.effect_reconcile_class            → `effectClass`
  rcic.effect_reconcile_scan             → `effectScan`
  rcic.effect_reconcile_names            → `effectNames`
  rcic.effect_reconcile_exact            → `effectExact`
  rcic.effect_reconcile_is_disp          → `effectIsDisp`
  rcic.effect_reconcile_sole             → `effectSole`
  rcic.effect_reconcile_disp_fail        → `dispFail`
  rcic.effect_reconcile_disp             → `effectDisp`
  rcic.effect_reconcile_effect           → `effectEffect`
  rcic.effect_reconcile_class/ctor tables → `EffectClassOut`
  rcic.permanent_residue_minter_ok       → `minterOk`
  rcic.permanent_residue_duplicate       → `permResDuplicate`
  rcic.permanent_residue_minted_count    → `mintedCount`
  rcic.permanent_residue_refuse / ok     → `permRefuse`/`PROut`
  rcic.permanent_residue                 → `evalPermanentResidue`
  rcic.challenge_resolution              → `Rcic.ChallengeResolution.
                                          evalChallengeResolution` (reused)
-/
import rcic.RcicChallengeResolutionModel

namespace Rcic.PermanentResidue

open Rcic.BoundObject (StoreEntry canonBytesOk storeScan)
open Rcic.Scm.Embed (partAt keysOf covers)
open Rcic.ScopeExact (keysOk)
open Rcic.ChallengeResolution (evalChallengeResolution)

/-! ## The residue record shape -/

/-- `rcic.permanent_residue_keys`: the exact three-key record shape. -/
def permResKeys : List String := ["kind", "minted_by", "obligation_ref"]

/-! ## The effect-reconcile chain (arm B, transcribed from
    `scm/rcic/effect_reconcile_*.scm` — no prior Lean model existed) -/

/-- `rcic.effect_reconcile_ctors`: the closed disposition-constructor enum. -/
def effectCtors : List String :=
  ["acceptedAsHistorical", "compensatable", "compensated", "irreparable",
   "unaffected"]

/-- `rcic.effect_reconcile_keys`: the exact five-key effect shape. -/
def effectKeys : List String :=
  ["effect_kind", "observed_external_receipt_ref",
   "originating_execution_occurrence_ref", "payload_ref", "target_ref"]

/-- `rcic.effect_reconcile_class`'s output `{arm, ref, keys}`. -/
structure EffectClassOut where
  arm : String
  ref : String
  keys : List String
  deriving BEq

/-- `rcic.effect_reconcile_class`: each constructor's arm name, its
    obligation-specific ref key, and its exact key set. `irreparable`
    carries `permanent_residue_ref`. -/
def effectClass (ctor : String) : EffectClassOut :=
  if ctor = "unaffected" then
    ⟨"unaffected", "", ["constructor", "effect_ref"]⟩
  else if ctor = "compensatable" then
    ⟨"compensatable", "compensation_plan_ref",
     ["compensation_plan_ref", "constructor", "effect_ref"]⟩
  else if ctor = "compensated" then
    ⟨"compensated", "compensation_execution_ref",
     ["compensation_execution_ref", "constructor", "effect_ref"]⟩
  else if ctor = "acceptedAsHistorical" then
    ⟨"acceptedAsHistorical", "policy_decision_ref",
     ["constructor", "effect_ref", "policy_decision_ref"]⟩
  else
    ⟨"irreparable", "permanent_residue_ref",
     ["constructor", "effect_ref", "permanent_residue_ref"]⟩

/-- `rcic.effect_reconcile_scan`'s output `{ok, code, bytes}`: resolve one
    digest — `""` ref, missing, and colliding all fail with the passed
    codes. -/
structure EScanOut where
  ok : Int
  code : String
  bytes : String
  deriving BEq

/-- `rcic.effect_reconcile_scan`. -/
def effectScan (store : List StoreEntry) (ref emptyCode missCode collideCode : String) :
    EScanOut :=
  if ref = "" then ⟨0, emptyCode, ""⟩
  else
    let hit := storeScan store ref
    if !hit.found then ⟨0, missCode, ""⟩
    else if hit.collision then ⟨0, collideCode, ""⟩
    else ⟨1, "", hit.bytes⟩

/-- `rcic.effect_reconcile_names`'s output `{ok, code}`: the disposition's
    `effect_ref` must be present and equal the named effect. -/
structure OkCodeOut where
  ok : Int
  code : String
  deriving BEq

/-- `rcic.effect_reconcile_names`. -/
def effectNames (bytes effectRef code : String) : OkCodeOut :=
  let named := partAt bytes "effect_ref"
  if named = "" then ⟨0, code⟩
  else if named = effectRef then ⟨1, ""⟩
  else ⟨0, code⟩

/-- `rcic.effect_reconcile_exact`: the disposition's own key list is
    exactly the class key set — covers both ways. -/
def effectExact (haveKeys needKeys : List String) : Bool :=
  covers haveKeys needKeys && covers needKeys haveKeys

/-- `rcic.effect_reconcile_is_disp`: canonical bytes whose `constructor`
    is a known disposition naming `effectRef`. -/
def effectIsDisp (bytes effectRef : String) : Bool :=
  canonBytesOk bytes &&
    (effectCtors.contains (partAt bytes "constructor")) &&
    decide ((effectNames bytes effectRef "").ok = 1)

/-- `rcic.effect_reconcile_sole`: exactly one disposition names this
    effect in the store and it is `dispositionRef`. -/
def effectSole (store : List StoreEntry) (effectRef dispositionRef : String) :
    OkCodeOut :=
  let got := store.foldl (fun acc e =>
    if effectIsDisp e.bytes effectRef
    then (acc.1 + 1, e.digest) else acc) (0, "")
  if got.1 = 1 then
    if got.2 = dispositionRef then ⟨1, ""⟩
    else ⟨0, "[rcic_effect_disposition_not_unique]"⟩
  else ⟨0, "[rcic_effect_disposition_not_unique]"⟩

/-- `rcic.effect_reconcile_disp`'s output `{ok, code, bytes, ctor}`. -/
structure DispOut where
  ok : Int
  code : String
  bytes : String
  ctor : String
  deriving BEq

/-- `rcic.effect_reconcile_disp_fail`. -/
def dispFail (code : String) : DispOut := ⟨0, code, "", ""⟩

/-- `rcic.effect_reconcile_disp store effect_ref disposition_ref`: the
    disposition judge — resolves the disposition digest, canonical bytes,
    a `constructor` part (absent → sole-disposition check refuses), a
    known constructor, an `effect_ref` naming the effect, and the exact
    class key set. -/
def effectDisp (store : List StoreEntry) (effectRef dispositionRef : String) :
    DispOut :=
  let hit := effectScan store dispositionRef "[rcic_effect_unbound]"
    "[rcic_effect_unbound]" "[rcic_effect_unbound]"
  if hit.ok = 0 then dispFail hit.code
  else if !canonBytesOk hit.bytes then dispFail "[rcic_effect_noncanonical]"
  else
    let ctor := partAt hit.bytes "constructor"
    if ctor = "" then
      let one := effectSole store effectRef dispositionRef
      dispFail one.code
    else if !effectCtors.contains ctor then
      dispFail "[rcic_effect_unknown_disposition]"
    else
      let named := effectNames hit.bytes effectRef "[rcic_effect_not_this_effect]"
      if named.ok = 0 then dispFail named.code
      else
        let cls := effectClass ctor
        if !effectExact (keysOf hit.bytes) cls.keys then
          dispFail "[rcic_effect_disposition_not_exact]"
        else ⟨1, "", hit.bytes, ctor⟩

/-- `rcic.effect_reconcile_effect`'s output `{ok, code, bytes}` (the hit's
    own record shape — `{ok, code, bytes}`). -/
def effectEffect (store : List StoreEntry) (effectRef : String) : EScanOut :=
  let hit := effectScan store effectRef "[rcic_effect_unbound]"
    "[rcic_effect_unbound]" "[rcic_effect_unbound]"
  if hit.ok = 0 then hit
  else if !canonBytesOk hit.bytes then ⟨0, "[rcic_effect_noncanonical]", ""⟩
  else if !effectExact (keysOf hit.bytes) effectKeys then
    ⟨0, "[rcic_effect_not_exact]", ""⟩
  else
    match Rcic.Scm.Embed.refsBound hit.bytes
        ["observed_external_receipt_ref"] store with
    | some _ => ⟨0, "[rcic_effect_not_happened]", ""⟩
    | none => hit

/-! ## The two minter arms -/

/-- `rcic.permanent_residue_minter_ok`'s output `{ok, code}`: arm A — the
    minter is an accepted `challenge_resolution` with `decision=validated`
    and `disposition=retired`, its statement's `realization_ref` equals the
    residue digest and its `challenge_ref` equals the residue's
    `obligation_ref`. Arm B — the minter is an accepted `irreparable`
    effect disposition whose `permanent_residue_ref` equals the residue
    digest, `effect_ref` equals the residue's `obligation_ref`, and the
    effect is itself accepted. Any other kind or arm refuses. -/
def minterOk (fuel : Int) (store : List StoreEntry) (selfDigest minterBytes
    mintedBy obligationRef : String) : OkCodeOut :=
  let mk := partAt minterBytes "kind"
  if mk = "challenge_resolution" then
    let r := evalChallengeResolution fuel store mintedBy
    if r.ok = 0 then ⟨0, "[rcic_permres_minter_arm]"⟩
    else if r.decision ≠ "validated" then ⟨0, "[rcic_permres_minter_arm]"⟩
    else if r.disposition ≠ "retired" then ⟨0, "[rcic_permres_minter_arm]"⟩
    else
      let ss := storeScan store (partAt minterBytes "statement_ref")
      if !ss.found then ⟨0, "[rcic_permres_backref]"⟩
      else if ss.collision then ⟨0, "[rcic_permres_backref]"⟩
      else if partAt ss.bytes "realization_ref" ≠ selfDigest then
        ⟨0, "[rcic_permres_backref]"⟩
      else if obligationRef ≠ r.challengeRef then
        ⟨0, "[rcic_permres_obligation_unbound]"⟩
      else ⟨1, ""⟩
  else
    let ctor := partAt minterBytes "constructor"
    if ctor = "" then ⟨0, "[rcic_permres_minter_kind]"⟩
    else
      let er := partAt minterBytes "effect_ref"
      let disp := effectDisp store er mintedBy
      if disp.ok = 0 then ⟨0, "[rcic_permres_minter_arm]"⟩
      else if disp.ctor ≠ "irreparable" then ⟨0, "[rcic_permres_minter_arm]"⟩
      else if partAt minterBytes "permanent_residue_ref" ≠ selfDigest then
        ⟨0, "[rcic_permres_backref]"⟩
      else if obligationRef ≠ er then ⟨0, "[rcic_permres_obligation_unbound]"⟩
      else
        let eff := effectEffect store obligationRef
        if eff.ok = 0 then ⟨0, "[rcic_permres_obligation_unbound]"⟩
        else ⟨1, ""⟩

/-- `rcic.permanent_residue_duplicate`: a second store entry (not the
    residue itself) that claims `kind:permanent_residue` with the same
    `minted_by` refuses — exactly one residue per minter. -/
def permResDuplicate (store : List StoreEntry) (selfDigest mintedBy : String) :
    Bool :=
  store.foldl (fun acc e =>
    if acc then true
    else if e.digest = selfDigest then false
    else if partAt e.bytes "kind" ≠ "permanent_residue" then false
    else partAt e.bytes "minted_by" = mintedBy) false

/-! ## The judge -/

/-- `rcic.permanent_residue`'s sigma `{ok, digest, minted_by,
    obligation_ref, code}`. -/
structure PROut where
  ok : Int
  digest : String
  mintedBy : String
  obligationRef : String
  code : String
  deriving BEq

/-- `rcic.permanent_residue_refuse`. -/
def permRefuse (code : String) : PROut := ⟨0, "", "", "", code⟩

/-- `rcic.permanent_residue`: the full leg chain, in scm order — fuel,
    bound+unanimous digest, canonical bytes, exact keys, `kind`, bound
    minter, canonical minter, the two-arm minter judgment, the
    one-residue-per-minter rule. -/
def evalPermanentResidue (fuel : Int) (store : List StoreEntry)
    (digest : String) : PROut :=
  if fuel < 0 then permRefuse "[rcic_permres_fuel]"
  else
    let os := storeScan store digest
    if !os.found then permRefuse "[rcic_permres_unbound]"
    else if os.collision then permRefuse "[rcic_permres_collision]"
    else if !canonBytesOk os.bytes then permRefuse "[rcic_permres_noncanonical]"
    else if !keysOk os.bytes permResKeys then permRefuse "[rcic_permres_shape]"
    else if partAt os.bytes "kind" ≠ "permanent_residue" then
      permRefuse "[rcic_permres_kind]"
    else
      let mb := partAt os.bytes "minted_by"
      let ms := storeScan store mb
      if !ms.found then permRefuse "[rcic_permres_minter_unbound]"
      else if ms.collision then permRefuse "[rcic_permres_minter_unbound]"
      else if !canonBytesOk ms.bytes then
        permRefuse "[rcic_permres_noncanonical]"
      else
        let ob := partAt os.bytes "obligation_ref"
        let m := minterOk (fuel - 1) store digest ms.bytes mb ob
        if m.ok = 0 then permRefuse m.code
        else if permResDuplicate store digest mb then
          permRefuse "[rcic_permres_duplicate]"
        else ⟨1, digest, mb, ob, ""⟩

/-- `rcic.permanent_residue_minted_count`: accepted residues minted by
    `occ` — used by the retired-suppression arm in `rcic.open_residues`. -/
def mintedCount (perms : List PROut) (occ : String) : Int :=
  perms.foldl (fun acc p => if p.mintedBy = occ then acc + 1 else acc) 0

/-! ## Record-level statements -/

/-- Negative fuel refuses with `[rcic_permres_fuel]`. -/
theorem evalPermanentResidue_fuel (fuel : Int) (store : List StoreEntry)
    (digest : String) (h : fuel < 0) :
    evalPermanentResidue fuel store digest =
      permRefuse "[rcic_permres_fuel]" := by
  unfold evalPermanentResidue; rw [if_pos h]

/-! ## Corpus pins (28 rows, M-002) -/

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩] "p1" == ⟨1, "p1", "o1", "c1", ""⟩

#guard evalPermanentResidue (100) [⟨"rcpt", "kind:receipt"⟩, ⟨"eff", "effect_kind:secret-leakage|observed_external_receipt_ref:rcpt|originating_execution_occurrence_ref:orig|payload_ref:pay|target_ref:tgt"⟩, ⟨"disp", "constructor:irreparable|effect_ref:eff|permanent_residue_ref:p2"⟩, ⟨"p2", "kind:permanent_residue|minted_by:disp|obligation_ref:eff"⟩] "p2" == ⟨1, "p2", "disp", "eff", ""⟩

#guard evalPermanentResidue (-1) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_fuel]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] "p9" == ⟨0, "", "", "", "[rcic_permres_unbound]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o2|obligation_ref:c1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_collision]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p1", "obligation_ref:c1|kind:permanent_residue|minted_by:o1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_noncanonical]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p1", "extra:x|kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_shape]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_shape]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p1", "kind:residue|minted_by:o1|obligation_ref:c1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_kind]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:nope|obligation_ref:c1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_minter_unbound]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r9|sequence:5|statement_ref:s9"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_minter_unbound]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"x", "kind:other"⟩, ⟨"p1", "kind:permanent_residue|minted_by:x|obligation_ref:c1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_minter_kind]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"x", "foo:1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:x|obligation_ref:c1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_minter_kind]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p9", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:p9|obligation_ref:c1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_minter_kind]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_minter_arm]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:refuted|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_minter_arm]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:reopened|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_minter_arm]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "wrong:keys"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_minter_arm]"⟩

#guard evalPermanentResidue (100) [⟨"rcpt", "kind:receipt"⟩, ⟨"eff", "effect_kind:secret-leakage|observed_external_receipt_ref:rcpt|originating_execution_occurrence_ref:orig|payload_ref:pay|target_ref:tgt"⟩, ⟨"plan", "kind:plan"⟩, ⟨"disp", "compensation_plan_ref:plan|constructor:compensatable|effect_ref:eff"⟩, ⟨"p2", "kind:permanent_residue|minted_by:disp|obligation_ref:eff"⟩] "p2" == ⟨0, "", "", "", "[rcic_permres_minter_arm]"⟩

#guard evalPermanentResidue (100) [⟨"rcpt", "kind:receipt"⟩, ⟨"eff", "effect_kind:secret-leakage|observed_external_receipt_ref:rcpt|originating_execution_occurrence_ref:orig|payload_ref:pay|target_ref:tgt"⟩, ⟨"disp", "bogus:1|constructor:wobbled|effect_ref:eff"⟩, ⟨"p2", "kind:permanent_residue|minted_by:disp|obligation_ref:eff"⟩] "p2" == ⟨0, "", "", "", "[rcic_permres_minter_arm]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"z1", "realization_object"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_backref]"⟩

#guard evalPermanentResidue (100) [⟨"rcpt", "kind:receipt"⟩, ⟨"eff", "effect_kind:secret-leakage|observed_external_receipt_ref:rcpt|originating_execution_occurrence_ref:orig|payload_ref:pay|target_ref:tgt"⟩, ⟨"disp", "constructor:irreparable|effect_ref:eff|permanent_residue_ref:zz"⟩, ⟨"zz", "kind:residue"⟩, ⟨"p2", "kind:permanent_residue|minted_by:disp|obligation_ref:eff"⟩] "p2" == ⟨0, "", "", "", "[rcic_permres_backref]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"c9", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o1|obligation_ref:c9"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_obligation_unbound]"⟩

#guard evalPermanentResidue (100) [⟨"rcpt", "kind:receipt"⟩, ⟨"eff", "effect_kind:secret-leakage|observed_external_receipt_ref:rcpt|originating_execution_occurrence_ref:orig|payload_ref:pay|target_ref:tgt"⟩, ⟨"disp", "constructor:irreparable|effect_ref:eff|permanent_residue_ref:p2"⟩, ⟨"p2", "kind:permanent_residue|minted_by:disp|obligation_ref:other"⟩, ⟨"other", "kind:object"⟩] "p2" == ⟨0, "", "", "", "[rcic_permres_obligation_unbound]"⟩

#guard evalPermanentResidue (100) [⟨"rcpt", "kind:receipt"⟩, ⟨"disp", "constructor:irreparable|effect_ref:eff|permanent_residue_ref:p2"⟩, ⟨"p2", "kind:permanent_residue|minted_by:disp|obligation_ref:eff"⟩] "p2" == ⟨0, "", "", "", "[rcic_permres_obligation_unbound]"⟩

#guard evalPermanentResidue (100) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩, ⟨"p9", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_duplicate]"⟩

#guard evalPermanentResidue (1) [⟨"b1", "basis_object"⟩, ⟨"t1", "target_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩] "p1" == ⟨0, "", "", "", "[rcic_permres_minter_arm]"⟩

#guard evalPermanentResidue (100) [⟨"rcpt", "kind:receipt"⟩, ⟨"eff", "effect_kind:secret-leakage|observed_external_receipt_ref:rcpt|originating_execution_occurrence_ref:orig|payload_ref:pay|target_ref:tgt"⟩, ⟨"disp", "constructor:irreparable|effect_ref:eff|permanent_residue_ref:p2"⟩] "eff" == ⟨0, "", "", "", "[rcic_permres_shape]"⟩

end Rcic.PermanentResidue

/-! ## Axiom transparency -/

#print axioms Rcic.PermanentResidue.evalPermanentResidue_fuel

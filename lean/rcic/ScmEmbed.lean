/-
RCIC 06 §18, §20 — wire execution predicates and the logical embedding
artifact (K2 statement layer).

Owner text:
  §18 (06:345-402) "The R-CIC theorem language cannot dereference a bare
      `CoreProgramRef`. It uses bound canonical objects." Generic binding
      `CanonicalObjectAt` / `BoundObject` (01 §6, `RcicBoundObject`); wire
      execution predicates `ProgramAt ValueAt ConfigAt OutcomeAt SCMStepAt
      SCMRunsAt EntryRunsAt` "are R-CIC propositions over bound refs and
      canonical bytes. They never invoke an ambient object store."
  §20 (06:421-443) the eleven-field `SCMLogicalEmbeddingArtifact`; "A profile
      selects specifications; an artifact installs the declarations and
      proofs"; "`AuthorityArtifact` must bind this artifact and a conformance
      proof. The embedding profile ends at `EntryRunsAt`; it does not
      reference contract or `TotalCorrect` definitions."

PIN (M-002): `scmEmbed` is `rcic.scm_embed form fuel artifact profile
authority store` (#6047), 15 rows below; it calls `RcicBoundObject.exactEq`
and `RcicTypedRef.deriveDigest` (landed and pinned), not restatements.

TRANSCRIPTION TABLE (06 → Lean):
  §18 CanonicalObjectAt / BoundObject           → `Rcic.BoundObject` (01 §6)
  §18 the seven wire predicates                  → `WirePredicate` (closed
        list of their names) and `embedPredicates` (their profile keys, plus
        `canonical_object_at`, 06 §18 "Generic binding"; `program_bundle_at`
        stands for §18's `ProgramAt`, a recorded choice of the carrier). The
        predicates themselves as propositions are NOT TRANSCRIBED (M-002b,
        `ScmRawRelations` header; K3b/K3c)
  §20 SCMLogicalEmbeddingArtifact (11 refs)      → `embedSchema`
  §20 "A profile selects specifications"         → profile keys =
        `embedPredicates` exactly
  §20 "ends at EntryRunsAt; does not reference contract or TotalCorrect"
        → `embedBeyond` forbidden keys (the carrier's recorded
        `[spec_ambiguity]` reading)
  §20 "AuthorityArtifact must bind this artifact" → `scmEmbed` form 1
  §20 "… and a conformance proof"               → `Rcic.ScmEmbedProof`
        (`RcicScmEmbedProofModel.lean`, M-002b closed): the scm carrier
        `apps/rcic-scm-embed-proof` (#6586/#6591) decides whether the
        authority artifact's public-exact closure contains the proof;
        the Lean face transcribes the proposition, the member scan, and
        the decider.  Decided in 00 Annex 24 §24.6 (#6048, #6050): 10 §5
        is unchanged; the proof is a closure member identified by the
        proposition it proves, not a schema key.
-/
import rcic.RcicBoundObject

namespace Rcic.Scm.Embed
open Rcic.BoundObject

/-- 06 §18: the wire execution predicates (closed list, quoted order). -/
inductive WirePredicate where
  | programAt | valueAt | configAt | outcomeAt | scmStepAt | scmRunsAt | entryRunsAt

def embedSchema : List String :=
  ["canonical_object_at_ref", "config_at_ref", "entry_runs_at_ref", "intrinsic_wire_bridge_proof_ref",
   "outcome_at_ref", "program_bundle_at_ref", "rcic_environment_groups_ref",
   "scm_logical_embedding_profile_ref", "scm_runs_at_ref", "scm_step_at_ref", "value_at_ref"]

def embedPredicates : List String :=
  ["canonical_object_at", "config_at", "entry_runs_at", "outcome_at", "program_bundle_at",
   "scm_runs_at", "scm_step_at", "value_at"]

def embedBeyond : List String := ["contract", "contract_ref", "total_correct", "total_correct_ref"]

/-- `rcic.authority_artifact_keys_of`. -/
def keysOf (bytes : String) : List String := (bytes.splitOn "|").map (fun p => (p.splitOn ":").headD "")

/-- `rcic.auth_activation_part_at`: the value of the first well-formed part
    with the key, else "". -/
def partAt (bytes key : String) : String :=
  (bytes.splitOn "|").foldl (fun acc p =>
    if acc = "" then
      match p.splitOn ":" with
      | [k, v] => if k = key then v else acc
      | _ => acc
    else acc) ""

def covers (xs ys : List String) : Bool := ys.all (fun y => xs.contains y)
def forbiddenHit (keys forbidden : List String) : Bool := forbidden.any (fun f => keys.contains f)

/-- `rcic.authority_artifact_refs_bound`: every schema ref present and
    unanimously resolved in the explicit store. -/
def refsBound (bytes : String) (keys : List String) (store : List StoreEntry) : Option String :=
  keys.foldl (fun acc k =>
    match acc with
    | some c => some c
    | none =>
      let v := partAt bytes k
      if v = "" then some "[rcic_artifact_ref_unbound]"
      else
        let s := storeScan store v
        if s.found && !s.collision then none else some "[rcic_artifact_ref_unbound]") none

/-- The carrier's output `{ok, q, code}`. -/
structure EOut where
  ok : Int
  q : String
  code : String
  deriving BEq

def eRefuse (code : String) : EOut := ⟨0, "", code⟩

/-- 06 §20 artifact conformance (form 0). -/
def embedArtifact (fuel : Int) (artifact profile : String) (store : List StoreEntry) : EOut :=
  if !canonBytesOk artifact then eRefuse "[rcic_scm_embed_noncanonical]" else
  let ak := keysOf artifact
  if forbiddenHit ak embedBeyond then eRefuse "[rcic_scm_embed_beyond_entry_runs]"
  else if !covers ak embedSchema then eRefuse "[rcic_scm_embed_missing]"
  else if !covers embedSchema ak then eRefuse "[rcic_scm_embed_extra]"
  else match refsBound artifact embedSchema store with
  | some c => eRefuse c
  | none =>
    let pref := partAt artifact "scm_logical_embedding_profile_ref"
    let pb := exactEq fuel 3 0 pref pref store profile
    if pb.ok = 0 then eRefuse pb.code else
    let pk := keysOf profile
    if forbiddenHit pk embedBeyond then eRefuse "[rcic_scm_embed_beyond_entry_runs]"
    else if !covers pk embedPredicates then eRefuse "[rcic_scm_embed_profile_missing]"
    else if !covers embedPredicates pk then eRefuse "[rcic_scm_embed_profile_extra]"
    else ⟨1, Rcic.TypedRef.deriveDigest 3 0 artifact, ""⟩

def scmEmbed (form fuel : Int) (artifact profile authority : String) (store : List StoreEntry) : EOut :=
  if form = 0 then embedArtifact fuel artifact profile store
  else if form = 1 then
    let aref := partAt authority "scm_logical_embedding_artifact_ref"
    if aref = "" then eRefuse "[rcic_scm_embed_authority_unbound]" else
    let b := exactEq fuel 3 0 aref aref store artifact
    if b.ok = 0 then eRefuse b.code else embedArtifact fuel artifact profile store
  else eRefuse "[rcic_scm_embed_unknown_form]"

/-! ## Pins: apps/rcic-scm-embed/rcic_scm_embed_corpus.json, 15 rows

Hand-transcribed (§18.3 rule 4): the digests below are copied from the
corpus store; artifact and profile bytes are assembled from them with
`canon` (sorted `k:v` parts joined by `|`), in the order written. -/

namespace Pins
def canon (kvs : List (String × String)) : String := "|".intercalate (kvs.map (fun (k, v) => k ++ ":" ++ v))

def dProfile : String := "d9e3ec0de57854519daafb42f74beb0f695d526ce5a80ce16d0f7ecc1e93add4"
def dCanon : String := "c388f2829ed813003a33abf7ce9997bb4ed9a0d3e46aaa65d02d665ad7270f07"
def dConfig : String := "5d755c3121e2d64d93bc5df0f9f538928a7524ed573725ce332ce54a469d8682"
def dEntry : String := "095f7cf2a854188e391f81ace79a2681b87d89d639126bc12879b28fe00c670c"
def dBridge : String := "9ad7e78bc5f24ed87fe69c086ae82f037def3ebf52cdb731a812efddd6bda434"
def dOutcome : String := "a5e646fe72f8873d8f9d343b87c9324d7665d6b814e550fc41608cfacb0ab917"
def dBundle : String := "95414e4026d935db9e33411ce5e68f3fa4adf2bab05ac6842c72d17b0df08edf"
def dEnv : String := "1c09bb6d77ff15272e37e3bfaf55ff783ca4ace022017489052e4dcd8f82163c"
def dRuns : String := "74cd8c84a8b1f99f6c3d579cd7d4eccc345a3aedef7b1b14ccc59f5e10add408"
def dStep : String := "2da21fb44c65b31b5f24fc4fad43876e27ad96345771b0809f9be59151d6238a"
def dValue : String := "5429176e01d7ede28c459fe6abf6275a8791797e8b90735178ae1607aa71cccc"
def dArt : String := "7f1ff8ff1881e9f494dcf3b3586a7a37919c51f20e7dc61a1f2a92cc610341ff"
def dPMissing : String := "2b8e43aa3ab5baef6781d187d093f67d42ac127e1bb06894f585fef45e767a94"
def dPExtra : String := "e4e3b913a9c027cf0f05dfd1ae665fe000a3977a03d793204e0a23159c611d47"
def dPContract : String := "355984be3f18beb80bfc5c6ad6a788cb5db88e324d0397063df236ff391eb814"
def dOther : String := "5b61a1e5dd53cd770cb27279ead28acaa6441c162fc1ddd408b0c3c4329421db"

def pFull : List (String × String) :=
  [("canonical_object_at", "spec"), ("config_at", "spec"), ("entry_runs_at", "spec"), ("outcome_at", "spec"),
   ("program_bundle_at", "spec"), ("scm_runs_at", "spec"), ("scm_step_at", "spec"), ("value_at", "spec")]
def profile : String := canon pFull
def pMissing : String := canon (pFull.take 7)
def pExtra : String := canon (pFull ++ [("wasm_at", "spec")])
def pContract : String := canon (pFull.take 7 ++ [("total_correct", "spec"), ("value_at", "spec")])

/-- The eleven refs with a chosen profile ref and value ref. -/
def artKVs (prof value : String) (config : String := dConfig) : List (String × String) :=
  [("canonical_object_at_ref", dCanon), ("config_at_ref", config), ("entry_runs_at_ref", dEntry),
   ("intrinsic_wire_bridge_proof_ref", dBridge), ("outcome_at_ref", dOutcome),
   ("program_bundle_at_ref", dBundle), ("rcic_environment_groups_ref", dEnv),
   ("scm_logical_embedding_profile_ref", prof), ("scm_runs_at_ref", dRuns), ("scm_step_at_ref", dStep),
   ("value_at_ref", value)]
def art : String := canon (artKVs dProfile dValue)
def other : String := canon (artKVs dProfile dConfig)

def store : List StoreEntry :=
  [⟨dProfile, profile⟩,
   ⟨dCanon, "kind:decl|surface:canonical_object_at"⟩, ⟨dConfig, "kind:decl|surface:config_at"⟩,
   ⟨dEntry, "kind:decl|surface:entry_runs_at"⟩, ⟨dBridge, "kind:decl|surface:intrinsic_wire_bridge_proof"⟩,
   ⟨dOutcome, "kind:decl|surface:outcome_at"⟩, ⟨dBundle, "kind:decl|surface:program_bundle_at"⟩,
   ⟨dEnv, "kind:decl|surface:rcic_environment_groups"⟩, ⟨dRuns, "kind:decl|surface:scm_runs_at"⟩,
   ⟨dStep, "kind:decl|surface:scm_step_at"⟩, ⟨dValue, "kind:decl|surface:value_at"⟩,
   ⟨dArt, art⟩, ⟨dPMissing, pMissing⟩, ⟨dPExtra, pExtra⟩, ⟨dPContract, pContract⟩, ⟨dOther, other⟩]

def acc (q : String) : EOut := ⟨1, q, ""⟩

-- 0 embedding artifact with the eleven section 20 refs and a conforming profile accepted
#guard scmEmbed 0 8 art profile "" store == acc dArt
-- 1 artifact bytes not canonical refused
#guard scmEmbed 0 8 ("value_at_ref:x|" ++ art) profile "" store == eRefuse "[rcic_scm_embed_noncanonical]"
-- 2 artifact missing the value_at ref refused
#guard scmEmbed 0 8 (canon ((artKVs dProfile dValue).take 10)) profile "" store == eRefuse "[rcic_scm_embed_missing]"
-- 3 artifact with a ref outside section 20 refused
#guard scmEmbed 0 8 (canon (artKVs dProfile dValue ++ [("zz_extra_ref", dConfig)])) profile "" store
  == eRefuse "[rcic_scm_embed_extra]"
-- 4 artifact referencing a TotalCorrect definition refused, the profile ends at EntryRunsAt
#guard scmEmbed 0 8 (canon ((artKVs dProfile dValue).take 10 ++ [("total_correct_ref", dConfig), ("value_at_ref", dValue)]))
  profile "" store == eRefuse "[rcic_scm_embed_beyond_entry_runs]"
-- 5 artifact ref not in the store refused
#guard scmEmbed 0 8 (canon (artKVs dProfile dValue "0000000000000000000000000000000000000000000000000000000000000000"))
  profile "" store == eRefuse "[rcic_artifact_ref_unbound]"
-- 6 profile bytes are not the object the artifact names refused
#guard scmEmbed 0 8 art (canon (pFull.set 1 ("config_at", "spex"))) "" store
  == eRefuse "[rcic_bound_object_address_collision]"
-- 7 profile selecting fewer predicates than EntryRunsAt needs refused
#guard scmEmbed 0 8 (canon (artKVs dPMissing dValue)) pMissing "" store == eRefuse "[rcic_scm_embed_profile_missing]"
-- 8 profile selecting a predicate outside section 18 refused
#guard scmEmbed 0 8 (canon (artKVs dPExtra dValue)) pExtra "" store == eRefuse "[rcic_scm_embed_profile_extra]"
-- 9 profile selecting TotalCorrect refused, the embedding ends at EntryRunsAt
#guard scmEmbed 0 8 (canon (artKVs dPContract dValue)) pContract "" store
  == eRefuse "[rcic_scm_embed_beyond_entry_runs]"
-- 10 authority artifact binds exactly this embedding artifact accepted
#guard scmEmbed 1 8 art profile ("master_profile_ref:m1|scm_logical_embedding_artifact_ref:" ++ dArt) store == acc dArt
-- 11 authority artifact binding another stored embedding artifact refused
#guard scmEmbed 1 8 art profile ("master_profile_ref:m1|scm_logical_embedding_artifact_ref:" ++ dOther) store
  == eRefuse "[rcic_bound_object_address_collision]"
-- 12 authority artifact with no embedding artifact ref refused
#guard scmEmbed 1 8 art profile "master_profile_ref:m1" store == eRefuse "[rcic_scm_embed_authority_unbound]"
-- 13 fuel exhausted in the binding check refused not decided
#guard scmEmbed 0 0 art profile "" store == eRefuse "[rcic_bound_object_fuel]"
-- 14 unknown form refused
#guard scmEmbed 2 8 art profile "" store == eRefuse "[rcic_scm_embed_unknown_form]"
end Pins

end Rcic.Scm.Embed

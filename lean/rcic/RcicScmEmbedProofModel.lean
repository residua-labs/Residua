/-
RCIC 06 §20:443 — "`AuthorityArtifact` must bind this artifact and a
conformance proof", the pinned Lean model of `apps/rcic-scm-embed-proof`
(`rcic.scm_embed_proof fuel form store artifact_bytes`).

Owner text (06 §20:421-443): the eleven-field `SCMLogicalEmbeddingArtifact`;
"A profile selects specifications; an artifact installs the declarations and
proofs"; "`AuthorityArtifact` must bind this artifact and a conformance proof.
The embedding profile ends at `EntryRunsAt`; it does not reference contract
or `TotalCorrect` definitions."  Annex 24 §24.6 (#6048, #6050) rules the
proof's binding: 10 §5's 28 keys are unchanged; the proof is a member of the
artifact's public-exact closure, identified by **what it proves** — the
SCM-019 proposition for this artifact and its profile — not by a schema
slot.  Row: SCM-019 "logical embedding artifact conforms to profile"
(06:470); census `research/rcic/census/r4/OPEN_SCM.md` M-002b; S0 plan
`research/rcic/scm/S0_SCM019.md`; the carrier app landed in batch SCM-3v
(#6586/#6591, sealed 13/13 tri-substrate).

PIN (M-002): all 13 rows of
`apps/rcic-scm-embed-proof/rcic_scm_embed_proof_corpus.json` below
(§18.3 rule 4 — digests copied from the corpus store).

The proof-member check is membership-only: whether the member's body
*proves* the proposition is a different lane (the carrier's DOES NOT
DECIDE).  Artifact↔profile conformance itself is form 0/1 of
`apps/rcic-scm-embed`; the `conformance_proof_ref` of 10 §20 transition
statements is a different binding (Annex 24).

TRANSCRIPTION TABLE (the scm modules → Lean):
  rcic.authority_artifact_schema     → `authoritySchema` (the 28 keys)
  rcic.auth_closure_seeds            → `closureSeeds`
  rcic.authority_closure_walk        → `Rcic.ScopeExact.walk` (reused)
  rcic.cog_bundle_closure_bound      → `Rcic.Scm.ProgramBundle.closureBound`
        (reused — the same fold body, already landed)
  rcic.auth_closure_canon            → `closureCanon`
  rcic.auth_activation_part_at       → `Rcic.Scm.Embed.partAt` (reused)
  rcic.store_scan                    → `Rcic.BoundObject.storeScan` (reused)
  rcic.canon_bytes_ok                → `Rcic.BoundObject.canonBytesOk` (reused)
  rcic.canonical_at                  → `Rcic.BoundObject.canonicalAt` (reused)
  rcic.derive                        → `Rcic.TypedRef.deriveDigest` (reused)
  rcic.scm019_proposition            → `prop019`
  rcic.scm019_proof_scan             → `proofScan`
  rcic.authority_artifact_ok/refuse  → `okOut`/`refuseOut` (`EOut`)
  rcic.scm_embed_proof_run           → `embedProofRun`
  rcic.scm_embed_proof               → `scmEmbedProof`
-/
import rcic.RcicScopeExactModel
import rcic.ScmProgramBundle

namespace Rcic.ScmEmbedProof

open Rcic.BoundObject (StoreEntry storeScan canonBytesOk canonicalAt)
open Rcic.Scm.Embed (EOut partAt)
open Rcic.ScopeExact (walk)
open Rcic.Scm.ProgramBundle (closureBound)

/-! ## The scm modules, mirrored -/

/-- `rcic.authority_artifact_schema`: the 28 seed keys of 10 §5 (the
    canonical ascending order — the scm builds the same list
    append-wise). -/
def authoritySchema : List String :=
  ["air_checker_scm_artifact_ref", "air_checker_wasm_artifact_ref",
   "air_relation_spec_ref", "assumption_closure_ref",
   "authority_checker_scm_artifact_ref", "authority_checker_wasm_artifact_ref",
   "canonical_codec_ref", "compiler_scm_artifact_ref", "compiler_wasm_artifact_ref",
   "constitution_ref", "contract_checker_scm_artifact_ref",
   "contract_checker_wasm_artifact_ref", "environment_root_ref",
   "genesis_recovery_floor_ref", "graph_checker_scm_artifact_ref",
   "graph_checker_wasm_artifact_ref", "master_profile_ref", "proof_forest_ref",
   "rcic_kernel_scm_artifact_ref", "rcic_kernel_wasm_artifact_ref",
   "recovery_checker_scm_artifact_ref", "recovery_checker_wasm_artifact_ref",
   "recovery_floor_manifest_ref", "recovery_kernel_sound_ref",
   "scm_logical_embedding_artifact_ref", "scm_semantics_spec_ref",
   "source_forest_ref", "wasm_machine_spec_ref"]

/-- `rcic.auth_closure_seeds`: the nonempty part values of the 28 schema
    keys, in schema order. -/
def closureSeeds (bytes : String) : List String :=
  authoritySchema.foldl (fun acc k =>
    let v := partAt bytes k
    if v = "" then acc else acc ++ [v]) []

/-- `rcic.auth_closure_canon`'s output `{ok, code}` — every member
    canonical at its digest (`canonicalAt 3 0`); the first failure's
    `[rcic_bound_object_*]` code passes through unchanged. -/
structure CCOut where
  ok : Int
  code : String
  deriving BEq

def closureCanon (fuel : Int) (closure : List String)
    (store : List StoreEntry) : CCOut :=
  closure.foldl (fun acc d =>
    if acc.ok = 0 then acc
    else
      let c := canonicalAt (fuel - 1) 3 0 d (storeScan store d).bytes
      if c.ok = 0 then ⟨0, c.code⟩ else acc) ⟨1, ""⟩

/-- `rcic.scm019_proposition`: the canonical proposition image —
    `artifact_ref:<a>|claim:scm_artifact_conforms_to_profile|profile_ref:<p>`.
    Derived, never presented. -/
def prop019 (artifactRef profileRef : String) : String :=
  "artifact_ref:" ++ artifactRef ++
    "|claim:scm_artifact_conforms_to_profile|profile_ref:" ++ profileRef

/-- `rcic.scm019_proof_scan`'s output `{hits, first}`: the count of closure
    members whose stored `statement_ref` equals the proposition digest, and
    the digest of the first such member. -/
structure ScanOut where
  hits : Int
  first : String
  deriving BEq

/-- `scm019_proof_scan`'s fold step. -/
def scanStep (store : List StoreEntry) (prop : String)
    (acc : ScanOut) (d : String) : ScanOut :=
  let v := partAt (storeScan store d).bytes "statement_ref"
  if v = prop then
    if acc.first = "" then ⟨1, d⟩ else ⟨acc.hits + 1, acc.first⟩
  else acc

/-- `rcic.scm019_proof_scan`. -/
def proofScan (store : List StoreEntry) (closure : List String)
    (prop : String) : ScanOut :=
  closure.foldl (scanStep store prop) ⟨0, ""⟩

/-- `rcic.authority_artifact_ok` / `_refuse`: the shared `{ok, q, code}`
    envelope (the `EOut` shape). -/
def okOut (q : String) : EOut := ⟨1, q, ""⟩
def refuseOut (code : String) : EOut := ⟨0, "", code⟩

/-- `rcic.scm_embed_proof_run`: the form-0 clause chain — canonical
    authority bytes, the `refs`-closure walk over the 28-key seeds, member
    boundness and canonicity, the `scm_logical_embedding_artifact_ref`
    subject resolution, the derived proposition, and the unique-member
    scan. -/
def embedProofRun (fuel : Int) (store : List StoreEntry)
    (artifactBytes : String) : EOut :=
  if !canonBytesOk artifactBytes then
    refuseOut "[rcic_scm_embed_proof_noncanonical]" else
  let cl := walk store (closureSeeds artifactBytes) fuel
  if cl.length = 0 then refuseOut "[rcic_scm_embed_proof_fuel]" else
  if !closureBound cl store then refuseOut "[rcic_authority_closure_unbound]"
  else
    let cc := closureCanon fuel cl store
    if cc.ok = 0 then refuseOut cc.code else
    let aref := partAt artifactBytes "scm_logical_embedding_artifact_ref"
    if aref = "" then refuseOut "[rcic_scm_embed_proof_subject]" else
    let as := storeScan store aref
    if !as.found || as.collision then refuseOut "[rcic_artifact_ref_unbound]"
    else
      let pref := partAt as.bytes "scm_logical_embedding_profile_ref"
      if pref = "" then refuseOut "[rcic_scm_embed_proof_subject]" else
      let pd := Rcic.TypedRef.deriveDigest 3 0 (prop019 aref pref)
      let sc := proofScan store cl pd
      if sc.hits = 1 then okOut sc.first
      else refuseOut
        (if sc.hits = 0 then "[rcic_scm_embed_proof_missing]"
         else "[rcic_scm_embed_proof_ambiguous]")

/-- `rcic.scm_embed_proof`: the form dispatcher —
    `(call rcic.scm_embed_proof fuel form store artifact_bytes)`. -/
def scmEmbedProof (fuel form : Int) (store : List StoreEntry)
    (artifactBytes : String) : EOut :=
  if form = 0 then
    if fuel < 0 then refuseOut "[rcic_scm_embed_proof_fuel]"
    else embedProofRun fuel store artifactBytes
  else refuseOut "[rcic_scm_embed_proof_unknown_form]"

/-! ## Record-level statements -/

/-- The produced `first` is a closure member whose stored bytes carry
    `statement_ref` equal to the proposition digest — the accepted `q` IS
    the proof member, not an invented digest. -/
def memberOk' (s : ScanOut) (cl : List String) (store : List StoreEntry)
    (prop : String) : Prop :=
  s.hits = 1 → s.first ∈ cl ∧
    partAt (storeScan store s.first).bytes "statement_ref" = prop

/-- The fold invariant: hits never go negative; a zero-hit scan has no
    recorded member; a nonzero-hit scan's `first` is a universe member
    naming the proposition. -/
def scanInv (univ : List String) (store : List StoreEntry)
    (prop : String) (s : ScanOut) : Prop :=
  0 ≤ s.hits ∧
  (s.hits = 0 → s.first = "") ∧
  (s.hits ≠ 0 → s.first ∈ univ ∧
    partAt (storeScan store s.first).bytes "statement_ref" = prop)

/-- `scanStep` preserves `scanInv` over a member of the universe. -/
theorem scanStep_inv (univ : List String) (store : List StoreEntry)
    (prop : String) (acc : ScanOut) (d : String) (hd : d ∈ univ)
    (h : scanInv univ store prop acc) :
    scanInv univ store prop (scanStep store prop acc d) := by
  obtain ⟨hnn, hz, hnz⟩ := h
  unfold scanStep
  by_cases hv : partAt (storeScan store d).bytes "statement_ref" = prop
  · rw [if_pos hv]
    by_cases hf : acc.first = ""
    · rw [if_pos hf]
      refine ⟨?_, ?_, ?_⟩
      · show (0:Int) ≤ 1
        omega
      · intro habs
        exact absurd habs (by show ¬((1:Int) = 0); omega)
      · intro _
        exact ⟨hd, hv⟩
    · rw [if_neg hf]
      have hne : acc.hits ≠ 0 := fun hz0 => hf (hz hz0)
      refine ⟨?_, ?_, ?_⟩
      · show (0:Int) ≤ acc.hits + 1
        omega
      · intro habs
        exact absurd habs (by show ¬(acc.hits + 1 = 0); omega)
      · intro _
        exact hnz hne
  · rw [if_neg hv]
    exact ⟨hnn, hz, hnz⟩

/-- The scan fold preserves `scanInv` over a sublist of the universe. -/
theorem fold_inv (univ : List String) (store : List StoreEntry)
    (prop : String) (xs : List String) (hsub : ∀ d ∈ xs, d ∈ univ)
    (acc : ScanOut) (hacc : scanInv univ store prop acc) :
    scanInv univ store prop (xs.foldl (scanStep store prop) acc) := by
  induction xs generalizing acc with
  | nil => exact hacc
  | cons y ys ih =>
      rw [List.foldl_cons]
      exact ih (fun d hd => hsub d (List.mem_cons_of_mem y hd))
        _ (scanStep_inv univ store prop acc y (hsub y (List.mem_cons_self y ys)) hacc)

/-- `proofScan` is sound for the row's content: the unique hit's `first` is
    a closure member whose stored `statement_ref` names the proposition. -/
theorem proofScan_sound (cl : List String) (store : List StoreEntry)
    (prop : String) :
    memberOk' (proofScan store cl prop) cl store prop := by
  intro h1
  have h := fold_inv cl store prop cl (fun d hd => hd) ⟨0, ""⟩
    ⟨by show (0:Int) ≤ 0; omega, fun _ => rfl, fun h0 => absurd rfl h0⟩
  have hne : (proofScan store cl prop).hits ≠ 0 := by omega
  exact h.2.2 hne

/-! ## Pins: apps/rcic-scm-embed-proof/rcic_scm_embed_proof_corpus.json, 13 rows

Hand-transcribed (§18.3 rule 4): the digests below are copied from the
corpus store; the presented authority bytes, the store entries, and the
proposition/member objects are assembled from them, in the order written. -/

namespace Pins

/-- The bound profile object (the artifact's
    `scm_logical_embedding_profile_ref`). -/
def dProf : String := "5d9fea86b887db17f609076b7b6af7268fc5d40f0399df4beda098c1ad5fcce6"
/-- The embedding artifact (the authority's
    `scm_logical_embedding_artifact_ref`). -/
def dArt : String := "404e7e489585c1686a0215a3608422485fe38bc3e82285dc06f44dabd23a9097"
/-- The base proof forest (row 0 store). -/
def dForest : String := "a6a16e64e427e071a5dd811b435d55d63e5096d7855240c6cb9d7b9528e24811"
/-- The conformance-proof member (accepted `q`). -/
def dProof : String := "6c395b7eef7ec3e158ae0ac709096c29b34ea6cab0f56b707b4953df914a2e28"
/-- The proof body the members reference. -/
def dBody : String := "d3199be8033751a4ba054df942705469cc5c41c1ea7385c97fa9cdfa375c59a4"
/-- The SCM-019 proposition digest — `deriveDigest 3 0 (prop019 dArt dProf)`. -/
def dProp : String := "2772fd5b695a1da89a1d8a14054c195201801cdfd297b190160013498369a9be"
/-- The forest naming only a junk member (row 2). -/
def dForest2 : String := "9cbe2d8d475c4a3b22278957eb9be5eda70c0c7322a37201ff4b1ca0b6b51f32"
/-- The store member carrying no `statement_ref` (rows 1–2). -/
def dJunk : String := "9bcf7941837819fb47beb7fe943a0928b53648790a803079b2df7c3d96042cf1"
/-- The forest naming a different-proposition member (row 3). -/
def dForest3 : String := "44baf86ea7a8d8bb82c4c025dea77f257f8d34f7db9d36abb30eb3eb8e5552f0"
/-- The member naming a different proposition (row 3). -/
def dOther : String := "37e606903401686690a181d690d914bd75732fc516ebff45747ab31b0c202630"
/-- The other proposition's digest (row 3). -/
def dPropX : String := "5776bb9889565a217dd4bb1fe3c2015f599ad05b4ede35504e493e80d82a4eeb"
/-- The two-member forest (row 4). -/
def dForest4 : String := "4f012c8481d8e99fa76d3fa3434127d52b001d6dc4fd68939713dca7c706d939"
/-- The second member naming the proposition (row 4). -/
def dProof2 : String := "8610e51272680102882c7d5fad022a936a7d16ee19031b697db84dcbbc36da51"
/-- The forest with no `refs` part (row 6). -/
def dForest6 : String := "e69da2e18e7e7544f8c80150cb8665526251eefc675e3889ee104d4dadbd825a"
/-- The forest naming an absent member (row 7). -/
def dForest7 : String := "47de84fa137cb559b81ccbfccde49ac97de8fe0f3ce5140a828a677e3de3c4be"
/-- The absent member's digest (row 7). -/
def dGhost : String := "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"

def profB : String := "canonical_object_at:spec|entry_runs_at:spec"
def artB : String :=
  "id:scm-logical-embedding|scm_logical_embedding_profile_ref:" ++ dProf
def forestB (refs : String) : String := "id:proof-forest|refs:" ++ refs
def proofB : String := "proof_body_ref:" ++ dBody ++ "|statement_ref:" ++ dProp
def proofOtherB : String :=
  "id:proof-other|proof_body_ref:" ++ dBody ++ "|statement_ref:" ++ dPropX
def proof2B : String :=
  "id:proof-2|proof_body_ref:" ++ dBody ++ "|statement_ref:" ++ dProp
def bodyB : String := "id:proof-body"
def junkB : String := "id:junk-member"

/-- The presented authority bytes naming forest `f` and the artifact. -/
def authB (f : String) : String :=
  "proof_forest_ref:" ++ f ++ "|scm_logical_embedding_artifact_ref:" ++ dArt

/-- Row 0/1/8-10/12 store (row 1 adds the unreferenced junk member). -/
def store0 : List StoreEntry :=
  [⟨dProf, profB⟩, ⟨dArt, artB⟩, ⟨dForest, forestB dProof⟩,
   ⟨dProof, proofB⟩, ⟨dBody, bodyB⟩]
def store1 : List StoreEntry := store0 ++ [⟨dJunk, junkB⟩]
def store2 : List StoreEntry :=
  [⟨dProf, profB⟩, ⟨dArt, artB⟩, ⟨dForest2, forestB dJunk⟩,
   ⟨dJunk, junkB⟩, ⟨dBody, bodyB⟩]
def store3 : List StoreEntry :=
  [⟨dProf, profB⟩, ⟨dArt, artB⟩, ⟨dForest3, forestB dOther⟩,
   ⟨dOther, proofOtherB⟩, ⟨dBody, bodyB⟩]
def store4 : List StoreEntry :=
  [⟨dProf, profB⟩, ⟨dArt, artB⟩,
   ⟨dForest4, forestB (dProof ++ "," ++ dProof2)⟩,
   ⟨dProof, proofB⟩, ⟨dProof2, proof2B⟩, ⟨dBody, bodyB⟩]
/-- Rows 5/11: no artifact object in the store. -/
def store5 : List StoreEntry :=
  [⟨dForest, forestB dProof⟩, ⟨dProof, proofB⟩, ⟨dProf, profB⟩, ⟨dBody, bodyB⟩]
def store6 : List StoreEntry :=
  [⟨dProf, profB⟩, ⟨dArt, artB⟩, ⟨dForest6, "id:proof-forest"⟩,
   ⟨dProof, proofB⟩, ⟨dBody, bodyB⟩]
def store7 : List StoreEntry :=
  [⟨dProf, profB⟩, ⟨dArt, artB⟩, ⟨dForest7, forestB dGhost⟩, ⟨dBody, bodyB⟩]

def acc (q : String) : EOut := ⟨1, q, ""⟩

-- 0 proof member inside the authority closure accepted, q is the member
#guard scmEmbedProof 8 0 store0 (authB dForest) == acc dProof
-- 1 an unreferenced store member ignored (public-exact, not store-exact)
#guard scmEmbedProof 8 0 store1 (authB dForest) == acc dProof
-- 2 no closure member names the proposition refused
#guard scmEmbedProof 8 0 store2 (authB dForest2)
  == refuseOut "[rcic_scm_embed_proof_missing]"
-- 3 a member naming a different proposition refused
#guard scmEmbedProof 8 0 store3 (authB dForest3)
  == refuseOut "[rcic_scm_embed_proof_missing]"
-- 4 two members naming the proposition refused as ambiguous
#guard scmEmbedProof 8 0 store4 (authB dForest4)
  == refuseOut "[rcic_scm_embed_proof_ambiguous]"
-- 5 authority artifact without the embedding artifact ref refused
#guard scmEmbedProof 8 0 store5 ("proof_forest_ref:" ++ dForest)
  == refuseOut "[rcic_scm_embed_proof_subject]"
-- 6 a proof in the store but outside the closure refused
#guard scmEmbedProof 8 0 store6 (authB dForest6)
  == refuseOut "[rcic_scm_embed_proof_missing]"
-- 7 a closure member missing from the store refused unbound
#guard scmEmbedProof 8 0 store7 (authB dForest7)
  == refuseOut "[rcic_authority_closure_unbound]"
-- 8 noncanonical authority artifact bytes refused
#guard scmEmbedProof 8 0 store0 "a:1|a:2"
  == refuseOut "[rcic_scm_embed_proof_noncanonical]"
-- 9 negative fuel refused, not decided
#guard scmEmbedProof (-1) 0 store0 (authB dForest)
  == refuseOut "[rcic_scm_embed_proof_fuel]"
-- 10 fuel zero leaves the walk unclosed refused, not decided
#guard scmEmbedProof 0 0 store0 (authB dForest)
  == refuseOut "[rcic_scm_embed_proof_fuel]"
-- 11 the artifact ref not resolving in the store refused unbound
#guard scmEmbedProof 8 0 store5 (authB dForest)
  == refuseOut "[rcic_authority_closure_unbound]"
-- 12 unknown form refused
#guard scmEmbedProof 8 9 store0 (authB dForest)
  == refuseOut "[rcic_scm_embed_proof_unknown_form]"

end Pins

end Rcic.ScmEmbedProof

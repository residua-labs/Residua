/-
RCIC 06 §7 / §18 — the bound total-correctness subject (carrier
`apps/rcic-tc-subject`, SCM-002 / SCM-006 labels; 07 §2–§4 statement shape).

Owner text: 06 §7 "`CoreProgramRoot` is the unique owner of the entry
function. Downstream subjects derive the entry from this root and do not
duplicate it." 06 §18 "The R-CIC theorem language cannot dereference a bare
`CoreProgramRef`. It uses bound canonical objects." "The bundle witness is
mandatory because execution needs all transitive function groups, the residue
catalog, and profiles."

PIN (M-002): `tcSubject` is `rcic.tc_subject fuel form shape …`, 14 rows below.
It composes `RcicBoundObject.canonicalAt` / `storeScan` and
`RcicTypedRef.deriveDigest` (landed, pinned) — no restatement.

TRANSCRIPTION TABLE (06 → Lean):
  §7 root owns the entry; subjects derive it and do not duplicate it
        → entry = `deriveDigest 3 1 programRoot`; `entryDup` refusal
  §18 bound canonical objects, never a bare ref → `partBound` (derive, scan,
        exact bytes, canonical); form 1 shape 1 refusal (bare q)
  §18 bundle witness mandatory                   → empty bundle refusal,
        `partBound` of the bundle
  07 §3/§4 statement shape (host CoreVal quantification refused) → form 1
        shape 2 refusal
-/
import rcic.RcicBoundObject

namespace Rcic.Scm.TcSubject
open Rcic.BoundObject

structure TOut where
  ok : Int
  subjectDigest : String
  entry : String
  code : String
  deriving BEq

def tRefuse (d code : String) : TOut := ⟨0, d, "", code⟩

/-- `rcic.tc_subject_part_bound`: derive the ref of presented bytes, find
    it unanimously in the explicit store with exactly those bytes, and check
    it canonical. -/
def partBound (fuel c k : Int) (bytes : String) (store : List StoreEntry) (missCode : String) :
    Option String × String :=
  let d := Rcic.TypedRef.deriveDigest c.toNat k bytes
  let s := storeScan store d
  if s.collision || !s.found || s.bytes ≠ bytes then (some missCode, "")
  else
    let cr := canonicalAt fuel c k d bytes
    if cr.ok = 1 then (none, d) else (some cr.code, "")

def entryScan (bytes : String) : Bool :=
  (bytes.splitOn "|").any (fun p =>
    match p.splitOn ":" with
    | k :: _ => k = "entry" || k = "entries" || k = "Entry" || k = "entrypoint"
    | [] => false)

def entryDup (ownEntry subjectBytes : String) : Bool := ownEntry.length > 0 || entryScan subjectBytes

def tcSubject (fuel form shape sc sk : Int) (sd sb root bundle contract progSeam contractSeam ownEntry : String)
    (store : List StoreEntry) : TOut :=
  if form = 1 then
    if shape = 0 then ⟨1, sd, "", ""⟩
    else if shape = 1 then tRefuse sd "[rcic_tc_subject_bare_q_refused]"
    else if shape = 2 then tRefuse sd "[rcic_tc_subject_coreval_quantified_refused]"
    else tRefuse sd "[rcic_tc_subject_unknown_shape]"
  else if form = 0 then
    if fuel < 0 then tRefuse sd "[rcic_tc_subject_fuel]"
    else if entryDup ownEntry sb then tRefuse sd "[rcic_tc_subject_entry_duplicated]"
    else
    let scr := canonicalAt fuel sc sk sd sb
    if scr.ok = 0 then tRefuse sd scr.code else
    match partBound (fuel - 1) 3 0 root store "[rcic_tc_subject_program_not_bound]" with
    | (some c, _) => tRefuse sd c
    | (none, pd) =>
      if bundle.length = 0 then tRefuse sd "[rcic_tc_subject_bundle_witness_missing]" else
      match partBound (fuel - 1) 3 0 bundle store "[rcic_tc_subject_bundle_not_bound]" with
      | (some c, _) => tRefuse sd c
      | (none, _) =>
        match partBound (fuel - 1) 3 0 contract store "[rcic_tc_subject_contract_not_bound]" with
        | (some c, _) => tRefuse sd c
        | (none, cd) =>
          if pd = progSeam ∧ cd = contractSeam then ⟨1, sd, Rcic.TypedRef.deriveDigest 3 1 root, ""⟩
          else tRefuse sd "[rcic_tc_subject_seam_mismatch]"
  else tRefuse sd "[rcic_tc_subject_unknown_form]"

/-! ## Pins: apps/rcic-tc-subject/rcic_tc_subject_corpus.json, 14 rows -/

namespace Pins
def SD : String := "a5844f35f8d7ae84929119c1348f216ea80cb229cb79235f29e178cac35abd80"
def DP : String := "4be78d2eb1c9780cc9ed34fd2d82fd00b3c9086a479153170002dc1960482c6e"
def DB : String := "84a7e2a4798bbc5832ae3e79fb87f943034f6954113830839dad49b305204380"
def DC : String := "f531454a5c9c91cadc99f3817273c0010221809d1deb74e2a59e6394f6a42c57"
def ENTRY : String := "66eeb70aab88e1ce577d791bff580bb0f351ebebecc43eae047ca566503cfa09"
def SB : String := "class:0|kind:0|row:none"
def ROOT : String := "entry:run|root:prog"
def BUNDLE : String := "fns:two|root:prog"
def CONTRACT : String := "pre:tt|row:none"
def store3 : List StoreEntry := [⟨DP, ROOT⟩, ⟨DB, BUNDLE⟩, ⟨DC, CONTRACT⟩]
def run (fuel form shape : Int) (sd sb : String) (ps cs own : String := "") (store : List StoreEntry := store3) : TOut :=
  tcSubject fuel form shape 0 0 sd sb ROOT BUNDLE CONTRACT ps cs own store

-- 0 GT-SCM-002 CT-002 CT-003 fully bound subject accept entry derived from program root (07 section 4)
#guard run 32 0 0 SD SB DP DC == ⟨1, SD, ENTRY, ""⟩
-- 1 GM-SCM-006 caller-supplied program seam does not re-derive refused (07 section 4)
#guard run 32 0 0 SD SB DC DC == tRefuse SD "[rcic_tc_subject_seam_mismatch]"
-- 2 CT-003 bundle carries its own entry field duplicating the root refused (07 section 2/4)
#guard run 32 0 0 SD SB DP DC ENTRY == tRefuse SD "[rcic_tc_subject_entry_duplicated]"
-- 3 CT-002 program bytes missing in store refused (07 section 4)
#guard run 32 0 0 SD SB DP DC "" [⟨DB, BUNDLE⟩, ⟨DC, CONTRACT⟩] == tRefuse SD "[rcic_tc_subject_program_not_bound]"
-- 4 GM-SCM-006 bare-q statement shape refused (07 section 4)
#guard run 32 1 1 SD SB DP DC == tRefuse SD "[rcic_tc_subject_bare_q_refused]"
-- 5 GM-SCM-006 host CoreVal-quantified statement shape refused (07 section 3/4)
#guard run 32 1 2 SD SB DP DC == tRefuse SD "[rcic_tc_subject_coreval_quantified_refused]"
-- 6 GT-SCM-002 noncanonical subject bytes refused via CanonicalObjectAt name (07 section 4)
#guard run 32 0 0 "7432a6d09838fca877480f4cd7066d6f508ca1b3af66d33cb125ede3c2f074cf" "k:1|k:2" DP DC
  == tRefuse "7432a6d09838fca877480f4cd7066d6f508ca1b3af66d33cb125ede3c2f074cf" "[rcic_bound_object_noncanonical_bytes]"
-- 7 CT-002 contract bytes missing in store refused (07 section 4)
#guard run 32 0 0 SD SB DP DC "" [⟨DP, ROOT⟩, ⟨DB, BUNDLE⟩] == tRefuse SD "[rcic_tc_subject_contract_not_bound]"
-- 8 fuel negative form 0 refused
#guard run (-1) 0 0 SD SB DP DC == tRefuse SD "[rcic_tc_subject_fuel]"
-- 9 unknown form refused
#guard run 32 9 0 SD SB DP DC == tRefuse SD "[rcic_tc_subject_unknown_form]"
-- 10 GM-SCM-006 caller-supplied contract seam does not re-derive refused (07 section 4)
#guard run 32 0 0 SD SB DP DP == tRefuse SD "[rcic_tc_subject_seam_mismatch]"
-- 11 GT-SCM-002 bound-subject statement shape accepted (07 section 4)
#guard run 32 1 0 SD SB DP DC == ⟨1, SD, "", ""⟩
-- 12 R-13 T2 07 s2 entry duplication via bytes part (entry key)
#guard run 32 0 0 SD "entry:run|kind:subject" DP DC == tRefuse SD "[rcic_tc_subject_entry_duplicated]"
-- 13 R-13 T3 07 s2 entry duplication via near-miss key (entries)
#guard run 32 0 0 SD "entries:zz|kind:subject" DP DC == tRefuse SD "[rcic_tc_subject_entry_duplicated]"
end Pins

end Rcic.Scm.TcSubject

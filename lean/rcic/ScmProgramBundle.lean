/-
RCIC 06 §7 / §18 — the closed core-program bundle (carrier
`apps/rcic-program-bundle`, SCM-015).

Owner text: 06 §7 "A closed core-program bundle contains the root, residue
catalog, and the exact transitive closure of function groups and profiles."
"`CoreProgramRoot` is the unique owner of the entry function. Downstream
subjects derive the entry from this root and do not duplicate it." 06 §18
`BoundCoreProgram { … program_bundle_ref program_bundle_bytes
program_bundle_at bundle_root_exact }`: "The bundle witness is mandatory
because execution needs all transitive function groups, the residue catalog,
and profiles."

PIN (M-002): `programBundle` is `rcic.program_bundle form root_digest
registry claimed_index fuel`, 14 rows below. It reuses `ScmRows.rowInsert`
(the carrier reuses `rcic.residue_rows_insert`), `RcicBoundObject.storeScan`
/ `canonicalAt`, and `RcicTypedRef.deriveDigest`.

TRANSCRIPTION TABLE (06 → Lean):
  §7 exact transitive closure                    → `closureFix` from the root
        over the regenerated `refs` edges; `closureBound` (no object missing),
        `registryReachable` (no extra object)
  §7 root, catalog, groups are bound objects     → `membersBound`
        (`canonicalAt` at class 3 kind 0)
  §7 entry owned by the root, derived, never duplicated → `entryScan`
        refusal, entry = `deriveDigest 3 1 root`
  §18 bundle_root_exact (the claimed dependency index is the regenerated one)
        → `indexEq`
  acyclic closure (well-founded bundle)          → `acyclic`
-/
import rcic.RcicBoundObject
import rcic.ScmRows

namespace Rcic.Scm.ProgramBundle
open Rcic.BoundObject Rcic.Scm.Rows

structure ClaimedEdge where
  src : String
  role : String
  tgt : String

def edgeStr (src role tgt : String) : String := src ++ ">" ++ role ++ ">" ++ tgt

def refsPart (bytes : String) : String :=
  (bytes.splitOn "|").foldl (fun acc p =>
    if (p.splitOn ":").headD "" = "refs" then (p.splitOn ":").getLastD "" else acc) ""

def refsList (bytes : String) : List String :=
  let rv := refsPart bytes
  if rv = "" then [] else rv.splitOn ","

def regenEdges (registry : List StoreEntry) : List String :=
  registry.foldl (fun acc e => (refsList e.bytes).foldl (fun a t => rowInsert (edgeStr e.digest "dep" t) a) acc) []

def edgeSrc (e : String) : String := (e.splitOn ">").headD ""
def edgeTgt (e : String) : String := (e.splitOn ">").getLastD ""

def closurePass (edges table : List String) : List String :=
  edges.foldl (fun acc e => if acc.contains (edgeSrc e) then rowInsert (edgeTgt e) acc else acc) table

/-- Iterate the closure pass; equality first, then the fuel gate. -/
def closureFix (edges : List String) : List String → Nat → Option (List String)
  | table, n =>
    let next := closurePass edges table
    if table == next then some next
    else match n with
      | 0 => none
      | m + 1 => closureFix edges next m

def closureBound (closure : List String) (registry : List StoreEntry) : Bool :=
  closure.all (fun d => let s := storeScan registry d; s.found && !s.collision)

def registryReachable (registry : List StoreEntry) (closure : List String) : Bool :=
  registry.all (fun e => closure.contains e.digest)

def indexEq (claimed : List ClaimedEdge) (edges : List String) : Bool :=
  claimed.foldl (fun acc e => rowInsert (edgeStr e.src e.role e.tgt) acc) [] == edges

def safePass (edges closure safe : List String) : List String :=
  closure.foldl (fun sacc x =>
    if edges.all (fun e => edgeSrc e ≠ x || safe.contains (edgeTgt e)) then rowInsert x sacc else sacc) safe

/-- `none` when the fuel runs out; `some acyclic` otherwise. -/
def acyclic (edges closure : List String) : List String → Nat → Option Bool
  | safe, n =>
    let next := safePass edges closure safe
    if safe == next then some (next.length = closure.length)
    else match n with
      | 0 => none
      | m + 1 => acyclic edges closure next m

def membersBound (closure : List String) (registry : List StoreEntry) (fuel : Int) : Bool :=
  closure.all (fun d =>
    let s := storeScan registry d
    s.found && (canonicalAt fuel 3 0 d s.bytes).ok = 1)

def entryScan (bytes : String) : Bool :=
  (bytes.splitOn "|").any (fun p =>
    match p.splitOn ":" with
    | k :: _ => k = "entry" || k = "entries" || k = "Entry" || k = "entrypoint"
    | [] => false)

structure PBOut where
  ok : Int
  root : String
  entry : String
  regCount : Int
  closCount : Int
  code : String
  deriving BEq

def programBundle (form : Int) (root : String) (registry : List StoreEntry) (claimed : List ClaimedEdge)
    (fuel : Int) : PBOut :=
  let n : Int := registry.length
  let no (c : String) : PBOut := ⟨0, root, "", n, 0, c⟩
  if form ≠ 0 then no "[rcic_program_bundle_unknown_form]"
  else if fuel < 0 then no "[rcic_program_bundle_fuel]"
  else
  let edges := regenEdges registry
  match closureFix edges (rowCanon [root]) fuel.toNat with
  | none => no "[rcic_program_bundle_fuel]"
  | some closure =>
    if !closureBound closure registry then no "[rcic_program_bundle_object_missing]"
    else if !registryReachable registry closure then no "[rcic_program_bundle_extra_object]"
    else if !indexEq claimed edges then no "[rcic_program_bundle_index_mismatch]"
    else match acyclic edges closure [] fuel.toNat with
    | none => no "[rcic_program_bundle_fuel]"
    | some false => no "[rcic_program_bundle_cycle]"
    | some true =>
      if !membersBound closure registry fuel then no "[rcic_program_bundle_member_unbound]" else
      let rb := (storeScan registry root).bytes
      if entryScan rb then no "[rcic_program_bundle_entry_duplicated]"
      else ⟨1, root, Rcic.TypedRef.deriveDigest 3 1 rb, n, closure.length, ""⟩

/-! ## Pins: apps/rcic-program-bundle/rcic_program_bundle_corpus.json, 14 rows -/

namespace Pins
def dep (s t : String) : ClaimedEdge := ⟨s, "dep", t⟩
def no (root : String) (n : Int) (c : String) : PBOut := ⟨0, root, "", n, 0, c⟩
def R0 : String := "5ec3ed4c30b6b78b7241a48b49803fdb04ef85a5a1ab1af38adf26795e48f2d4"
def F1 : String := "8ca3f00e32fa723c9fa6cb3a7002a09b1f1f8a113c0c52a877a2f637c0991d83"
def F2 : String := "e2fe06aa16610eac052cca1bb7e9f091b73822bdf4f0d4dccdbbdaa1c1f3c4ab"
def F3 : String := "7307ce0537da9785d958715fc00519e6cb411c38f796b1aea0953e82285a501f"
def CAT : String := "00846bf771a0a9157f5c21dd43267fb4d0bc3c7956b2f15e7ab8a765d42c58b8"
def R3 : String := "db4de3633827563843147756ed6736567c4c72883d9432caf97dcfb9defdd2b9"
def G3 : String := "d7c91b83a41fda3364920e58b73bf2eee7088f76f151774ddbe81ecaace4ec12"
def R5 : String := "dc489169c6d9908abb0ee054a2a19466b492e6cd8cbc0b14bf97b4f25909a30c"
def DEAD : String := "dead000537da9785d958715fc00519e6cb411c38f796b1aea0953e82285a501f"
def R7 : String := "4c6aebde06c3db1974e4626ab5813976b8b08289f75c5dd3b8f4d3afce76b29e"
def R11 : String := "82d6369da8ec77849986cace92a77b10e5a86c1f37eb4b25b655c448cf2ed037"
def R12 : String := "dc49fdea74edaf59b5485127fdae1a860e28d34ac05722aba1d4e530e50258f5"
def R13 : String := "547a7ffb76d7366886f8ae9f20144aedbf0eb3d863e8febbf8daa45861b33ac2"
def chainD (i : Nat) : String := "d" ++ toString i ++ "e0000000000000000000000000000000000000000000000000000000000"

-- 0 SCM-015 06 section 7 exact bundle accept root 3-function chain plus residue catalog closure equals registry entry derive
#guard programBundle 0 R0
  [⟨R0, "kind:root|refs:" ++ F1 ++ "," ++ CAT⟩, ⟨F1, "kind:fn|refs:" ++ F2⟩, ⟨F2, "kind:fn|refs:" ++ F3⟩,
   ⟨F3, "kind:fn"⟩, ⟨CAT, "kind:catalog"⟩]
  [dep R0 F1, dep R0 CAT, dep F1 F2, dep F2 F3] 8
  == ⟨1, R0, "226c3a4e6d756caf53567a9b21b595ee46789d3802587232587905135e51c657", 5, 5, ""⟩
-- 1 GM-COG-003 06 section 7 closure object with no registry entry refused never fetched ambiently
#guard programBundle 0 "aa11" [⟨"aa11", "kind:root|refs:bb22"⟩, ⟨"bb22", "kind:fn|refs:cc33"⟩]
  [dep "aa11" "bb22", dep "bb22" "cc33"] 8 == no "aa11" 2 "[rcic_program_bundle_object_missing]"
-- 2 GM-COG-004 06 section 7 complete but overfull bundle unreachable extra object refused only here
#guard programBundle 0 "aa11"
  [⟨"aa11", "kind:root|refs:bb22"⟩, ⟨"bb22", "kind:fn|refs:cc33"⟩, ⟨"cc33", "kind:fn"⟩, ⟨"xx99", "kind:fn"⟩]
  [dep "aa11" "bb22", dep "bb22" "cc33"] 8 == no "aa11" 4 "[rcic_program_bundle_extra_object]"
-- 3 GM-DEP-001 06 section 7 claimed index omits real dep edge refused against regenerated edges
#guard programBundle 0 R3
  [⟨R3, "kind:root|refs:" ++ F2 ++ "," ++ G3⟩, ⟨F2, "kind:fn|refs:" ++ F3⟩, ⟨G3, "kind:gate|refs:" ++ F3⟩, ⟨F3, "kind:fn"⟩]
  [dep R3 F2, dep R3 G3, dep F2 F3] 8 == no R3 4 "[rcic_program_bundle_index_mismatch]"
-- 4 06 section 7 dependency cycle among reachable members refused
#guard programBundle 0 "aa11"
  [⟨"aa11", "kind:root|refs:bb22"⟩, ⟨"bb22", "kind:fn|refs:cc33"⟩, ⟨"cc33", "kind:fn|refs:bb22"⟩]
  [dep "aa11" "bb22", dep "bb22" "cc33", dep "cc33" "bb22"] 8 == no "aa11" 3 "[rcic_program_bundle_cycle]"
-- 5 06 section 7 closure member not canonical_at-bound digest mismatch refused
#guard programBundle 0 R5 [⟨R5, "kind:root|refs:" ++ DEAD⟩, ⟨DEAD, "kind:fn"⟩] [dep R5 DEAD] 8
  == no R5 2 "[rcic_program_bundle_member_unbound]"
-- 6 06 section 7 noncanonical root bytes refused at member binding
#guard programBundle 0 "aa11" [⟨"aa11", "refs:" ++ F3 ++ "|kind:root"⟩, ⟨F3, "kind:fn"⟩] [dep "aa11" F3] 8
  == no "aa11" 2 "[rcic_program_bundle_member_unbound]"
-- 7 06 section 7 root bytes duplicating the entry part refused entry only ever derived
#guard programBundle 0 R7 [⟨R7, "entry:SELFOWN|kind:root"⟩] [] 8 == no R7 1 "[rcic_program_bundle_entry_duplicated]"
-- 8 06 section 7 fuel exhaustion mid-closure is suspension with empty result never partial
#guard programBundle 0 (chainD 5)
  [⟨chainD 5, "kind:obj|refs:" ++ chainD 4⟩, ⟨chainD 4, "kind:obj|refs:" ++ chainD 3⟩,
   ⟨chainD 3, "kind:obj|refs:" ++ chainD 2⟩, ⟨chainD 2, "kind:obj|refs:" ++ chainD 1⟩,
   ⟨chainD 1, "kind:obj|refs:" ++ chainD 0⟩, ⟨chainD 0, "kind:obj"⟩]
  [dep (chainD 5) (chainD 4), dep (chainD 4) (chainD 3), dep (chainD 3) (chainD 2),
   dep (chainD 2) (chainD 1), dep (chainD 1) (chainD 0)] 2
  == no (chainD 5) 6 "[rcic_program_bundle_fuel]"
-- 9 negative fuel refused as suspension
#guard programBundle 0 "aa11" [⟨"aa11", "kind:root|refs:bb22"⟩] [dep "aa11" "bb22"] (-1)
  == no "aa11" 1 "[rcic_program_bundle_fuel]"
-- 10 unknown form refused by name
#guard programBundle 1 "aa11" [⟨"aa11", "kind:root|refs:bb22"⟩] [dep "aa11" "bb22"] 8
  == no "aa11" 1 "[rcic_program_bundle_unknown_form]"
-- 11 SCM-015 06 section 7 minimal bundle root plus residue catalog only accept zero function groups
#guard programBundle 0 R11 [⟨R11, "kind:root|refs:" ++ CAT⟩, ⟨CAT, "kind:catalog"⟩] [dep R11 CAT] 8
  == ⟨1, R11, "f488a6a5beea4151f4663c6e29a95a2700b6b0f1c9f09fad85b7e5fe58095fdd", 2, 2, ""⟩
-- 12 R-13 P1a entry duplication via near-miss key entries
#guard programBundle 0 R12 [⟨R12, "entries:SELFOWN|kind:root"⟩] [] 8 == no R12 1 "[rcic_program_bundle_entry_duplicated]"
-- 13 R-13 P1b entry duplication via near-miss key entrypoint
#guard programBundle 0 R13 [⟨R13, "entrypoint:SELFOWN|kind:root"⟩] [] 8 == no R13 1 "[rcic_program_bundle_entry_duplicated]"
end Pins

end Rcic.Scm.ProgramBundle

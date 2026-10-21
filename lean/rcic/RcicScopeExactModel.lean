/-
RCIC 00 §2 — ScopeExact clauses (1)–(3), the pinned Lean model of
`apps/rcic-scope-exact` (`rcic.scope_exact scope_bytes basis_bytes store fuel`).

The carrier decides the DATA half of 00:26-29 as one conjunction: (1) every
declared root is in the source universe; (2) the relevance predicate ref
resolves to nonempty canonical bytes (a frozen specification); (3) under the
basis's selected dependency grade the role-closure of the roots is complete —
every member resolves to nonempty bytes. Clause (4) (no ambient read) is
unbuilt — no extractor exists; nothing here decides it.

PIN (M-002): all 26 rows of `apps/rcic-scope-exact/rcic_scope_exact_corpus.json`
below; the clause-level primed statements `rootsInUniverse'` /
`relevanceFrozen'` / `closureComplete'` agree with the carrier's `ok` flag on
every row (M-002a).

TRANSCRIPTION TABLE (the scm modules → Lean):
  rcic.auth_activation_part_at      → `Rcic.Scm.Embed.partAt` (reused)
  rcic.canon_bytes_ok / part_ok     → `Rcic.BoundObject.canonBytesOk/canonPartOk`
  rcic.store_scan                   → `Rcic.BoundObject.storeScan`
  rcic.outcome_has_key              → `hasKey`
  rcic.cog_bundle_refs_part/list    → `refsPart`/`refsList`
  rcic.residue_rows_member/insert/canon → `listMember`/`listInsert`/`listCanon`
  substrate.events.string_lt        → `· < ·` on String
  rcic.cog_bundle_edge_str          → `edgeStr`
  rcic.cog_bundle_edges_one(_roles) → `edgesOne`/`edgesOneRoles`
  rcic.cog_bundle_regen_edges(_roles) → `regenEdges`/`regenEdgesRoles`
  rcic.cog_bundle_pass/list_eq      → `pass`/`listEq`
  rcic.cog_bundle_fix               → `fix`
  rcic.authority_closure_walk(_roles) → `walk`/`walkRoles`
  rcic.scope_exact_members          → `members`
  rcic.scope_exact_rel_at           → `relAt`
  rcic.scope_exact_profile_at       → `profileAt`
  rcic.scope_exact_grade_ok         → `gradeOk`
  rcic.closure_basis_keys_ok/scope_ok → `keysOk`/`scopeShapeOk`
  rcic.closure_basis_refs_walk      → `refsWalk`
  rcic.genesis_floor_subset         → `subset`
  rcic.scope_exact                  → `evalScopeExact`
-/
import rcic.RcicBoundObject
import rcic.ScmEmbed

namespace Rcic.ScopeExact

open Rcic.BoundObject (StoreEntry storeScan canonBytesOk canonPartOk)
open Rcic.Scm.Embed (partAt)

/-! ## The scm primitives, mirrored -/

/-- `rcic.outcome_has_key`: some `|`-part has the key (first `:`-segment equal). -/
def hasKey (bytes key : String) : Bool :=
  (bytes.splitOn "|").any (fun p => (p.splitOn ":").headD "" = key)

/-- `rcic.cog_bundle_refs_part`: the LAST `refs`-part's value ("" when none). -/
def refsPart (bytes : String) : String :=
  (bytes.splitOn "|").foldl (fun acc p =>
    if (p.splitOn ":").headD "" = "refs" then (p.splitOn ":").getLastD "" else acc) ""

/-- `rcic.cog_bundle_refs_list`: the refs CSV as a member list ([] when the part
    is absent or empty). -/
def refsList (bytes : String) : List String :=
  let rv := refsPart bytes
  if rv = "" then [] else rv.splitOn ","

/-- `rcic.residue_rows_insert`: insert `r` into a sorted list, dedup on equal. -/
def listInsert : List String → String → List String
  | [], r => [r]
  | y :: ys, r =>
    if y = r then y :: ys
    else if r < y then r :: y :: ys
    else y :: listInsert ys r

/-- `rcic.residue_rows_canon`: sorted, deduplicated. -/
def listCanon (xs : List String) : List String := xs.foldl listInsert []

/-- `rcic.residue_rows_member`. -/
def listMember (xs : List String) (r : String) : Bool := xs.contains r

/-- `rcic.cog_bundle_edge_str`: `src>role>tgt`. -/
def edgeStr (src role tgt : String) : String := src ++ ">" ++ role ++ ">" ++ tgt

/-- `rcic.cog_bundle_edges_one`: `d>dep>t` for each `refs:`-CSV member. -/
def edgesOne (e : StoreEntry) (edges : List String) : List String :=
  (refsList e.bytes).foldl (fun acc t => listInsert acc (edgeStr e.digest "dep" t)) edges

/-- `rcic.cog_bundle_edges_one_roles`: for each `k:v` part with `k ∈ roles`,
    `d>k>t` for every CSV member `t` of `v` (an empty `v` emits no edge). -/
def edgesOneRoles (e : StoreEntry) (roles : List String) (edges : List String) : List String :=
  let rc := listCanon roles
  (e.bytes.splitOn "|").foldl (fun acc p =>
    match p.splitOn ":" with
    | [k, v] =>
      if listMember rc k then
        if v = "" then acc
        else (v.splitOn ",").foldl (fun a t => listInsert a (edgeStr e.digest k t)) acc
      else acc
    | _ => acc) edges

/-- `rcic.cog_bundle_regen_edges`. -/
def regenEdges (registry : List StoreEntry) : List String :=
  registry.foldl (fun acc e => edgesOne e acc) []

/-- `rcic.cog_bundle_regen_edges_roles`. -/
def regenEdgesRoles (registry : List StoreEntry) (roles : List String) : List String :=
  registry.foldl (fun acc e => edgesOneRoles e roles acc) []

/-- `rcic.cog_bundle_pass`: follow every edge whose source is already in the table
    (insert order grows the table inside the pass). -/
def pass (edges table : List String) : List String :=
  edges.foldl (fun acc e =>
    let p := e.splitOn ">"
    if listMember acc (p.headD "") then listInsert acc (p.getLastD "") else acc) table

/-- `rcic.cog_bundle_list_eq`. -/
def listEq (a b : List String) : Bool := a == b

/-- `rcic.cog_bundle_fix`'s output `{ok, table}` (ok=0/table=[] on fuel-out). -/
structure FixOut where
  ok : Int
  table : List String
  deriving BEq

/-- `rcic.cog_bundle_fix`: fixpoint of `pass`; empty table when fuel runs out
    while the table is still growing. -/
def fix (edges : List String) (table : List String) (fuel : Int) : FixOut :=
  let next := pass edges table
  if listEq table next then ⟨1, next⟩
  else if h : fuel ≤ 0 then ⟨0, []⟩
  else fix edges next (fuel - 1)
termination_by fuel.toNat
decreasing_by omega

/-- `rcic.authority_closure_walk` (#6306, vendored byte-identical). -/
def walk (store : List StoreEntry) (seeds : List String) (fuel : Int) : List String :=
  (fix (regenEdges store) (listCanon seeds) fuel).table

/-- `rcic.authority_closure_walk_roles`: the ONE role-filtered variant — same
    walk, edges regenerated only from `role:`-keyed parts with `role ∈ roles`.
    At `roles = ["refs"]` the reachable table equals `walk`'s (the walk reads
    only each edge's target). -/
def walkRoles (store : List StoreEntry) (seeds roles : List String) (fuel : Int) : List String :=
  (fix (regenEdgesRoles store roles) (listCanon seeds) fuel).table

/-- `rcic.scope_exact_members`' output `{ok, members}`. -/
structure MOut where
  ok : Int
  members : List String
  deriving BEq

/-- `rcic.scope_exact_members`: a set object resolves, is collision-free,
    canonical, and carries a `refs` part. -/
def members (store : List StoreEntry) (r : String) : MOut :=
  let s := storeScan store r
  if s.found && !s.collision && canonBytesOk s.bytes && hasKey s.bytes "refs"
    then ⟨1, refsList s.bytes⟩
    else ⟨0, []⟩

/-- `rcic.scope_exact_rel_at`'s output `{ok, code}`. -/
structure ROut where
  ok : Int
  code : String
  deriving BEq

/-- `rcic.scope_exact_rel_at`: the relevance predicate ref resolves unanimously
    to nonempty canonical bytes. -/
def relAt (store : List StoreEntry) (r : String) : ROut :=
  let s := storeScan store r
  if !s.found || s.collision then ⟨0, "[rcic_scope_relevance_unresolved]"⟩
  else if s.bytes.length = 0 then ⟨0, "[rcic_scope_relevance_empty]"⟩
  else if canonBytesOk s.bytes then ⟨1, ""⟩
  else ⟨0, "[rcic_scope_relevance_noncanonical]"⟩

/-- `rcic.scope_exact_profile_at`'s output `{ok, grade}`. -/
structure POut where
  ok : Int
  grade : String
  deriving BEq

/-- `rcic.scope_exact_profile_at`: the profile object resolves, is
    collision-free and canonical; its `grade` part is reported verbatim
    ("" when absent). -/
def profileAt (store : List StoreEntry) (r : String) : POut :=
  let s := storeScan store r
  if s.found && !s.collision && canonBytesOk s.bytes
    then ⟨1, partAt s.bytes "grade"⟩
    else ⟨0, ""⟩

/-- `rcic.scope_exact_grade_ok`: the selected grades are `0` (exact) and `1`;
    `2` is `unknown` (09:378) and any other value refuses. -/
def gradeOk (grade : String) : Int := if grade = "0" || grade = "1" then 1 else 0

/-- `rcic.closure_basis_keys_ok`: the `|`-part count equals the key count and
    every key is present. -/
def keysOk (bytes : String) (keys : List String) : Bool :=
  (bytes.splitOn "|").length = keys.length && keys.all (fun k => hasKey bytes k)

/-- `rcic.closure_basis_scope_ok`: canonical bytes with exactly the four scope
    refs. -/
def scopeShapeOk (scope : String) : Bool :=
  canonBytesOk scope &&
    keysOk scope
      ["relevance_predicate_ref", "required_edge_role_set_ref", "root_set_ref",
       "source_universe_ref"]

/-- `rcic.closure_basis_refs_walk`'s output `{ok, fuel_left, code}`. -/
structure WOut where
  ok : Int
  fuelLeft : Int
  code : String
  deriving BEq

/-- `rcic.closure_basis_refs_walk`: every member resolves to nonempty bytes,
    one fuel per member. -/
def refsWalk (fuel : Int) (refs : List String) (store : List StoreEntry) : WOut :=
  refs.foldl (fun acc r =>
    if acc.ok = 1 then
      if acc.fuelLeft > 0 then
        let s := storeScan store r
        if !s.found then ⟨0, acc.fuelLeft, "[rcic_basis_ref_unavailable]"⟩
        else if s.collision then ⟨0, acc.fuelLeft, "[rcic_basis_ref_unavailable]"⟩
        else if s.bytes.length > 0 then ⟨1, acc.fuelLeft - 1, ""⟩
        else ⟨0, acc.fuelLeft, "[rcic_basis_ref_unavailable]"⟩
      else ⟨0, acc.fuelLeft, "[rcic_basis_fuel]"⟩
    else acc) ⟨1, fuel, ""⟩

/-- `rcic.genesis_floor_subset`: every member of `xs` is a member of `ts`. -/
def subset (xs ts : List String) : Int :=
  if xs.all (fun x => listMember ts x) then 1 else 0

/-- `rcic.scope_exact`'s sigma `{ok, r1, r2, r3, roots, universe, roles, grade,
    closure, code}` (`universe` → `univ` here: `universe` is a Lean keyword). -/
structure SOut where
  ok : Int
  r1 : Int
  r2 : Int
  r3 : Int
  roots : List String
  univ : List String
  roles : List String
  grade : String
  closure : List String
  code : String
  deriving BEq

/-- `rcic.scope_exact_refuse`. -/
def refuseOut (code : String) : SOut := ⟨0, 0, 0, 0, [], [], [], "", [], code⟩

/-- `rcic.scope_exact`'s `ok` flag: the (1)∧(2)∧(3) conjunction over the clause
    flags. -/
def okOf (r1 r2 r3 : Int) : Int := if r1 = 1 then (if r2 = 1 then r3 else 0) else 0

/-- `rcic.scope_exact`: the (1)∧(2)∧(3) conjunction with per-clause flags and
    produced objects; `code` names the first failure in check order. -/
def evalScopeExact (scope basis : String) (store : List StoreEntry) (fuel : Int) : SOut :=
  if !scopeShapeOk scope then refuseOut "[rcic_scope_shape]"
  else if !canonBytesOk basis then refuseOut "[rcic_scope_basis_shape]"
  else
    let rr := partAt scope "root_set_ref"
    let ur := partAt scope "source_universe_ref"
    let er := partAt scope "required_edge_role_set_ref"
    let pr := partAt scope "relevance_predicate_ref"
    let dpr := partAt basis "dependency_extraction_profile_ref"
    let rm := members store rr
    let um := members store ur
    let em := members store er
    let roots := rm.members
    let univ := um.members
    let roles := em.members
    let r1 := if rm.ok = 1 then (if um.ok = 1 then subset roots univ else 0) else 0
    let ra := relAt store pr
    let r2 := ra.ok
    let pg := if dpr = "" then ⟨0, ""⟩ else profileAt store dpr
    let gok := if pg.ok = 1 then gradeOk pg.grade else 0
    let cl :=
      if rm.ok = 1 then
        if em.ok = 1 then
          if roles == ["refs"] then walk store roots fuel
          else walkRoles store roots roles fuel
        else []
      else []
    let fuelout :=
      if rm.ok = 1 && em.ok = 1 && roots.length > 0 && cl.length = 0 then 1 else 0
    let rw :=
      if rm.ok = 1 then
        if em.ok = 1 then
          if fuelout = 0 then refsWalk fuel cl store
          else ⟨0, fuel, "[rcic_scope_fuel]"⟩
        else ⟨0, fuel, "[rcic_scope_set_unresolved]"⟩
      else ⟨0, fuel, "[rcic_scope_set_unresolved]"⟩
    let r3 :=
      if fuelout = 0 && rm.ok = 1 && em.ok = 1 then (if gok = 1 then rw.ok else 0) else 0
    { ok := okOf r1 r2 r3
      r1, r2, r3, roots, univ, roles, grade := pg.grade, closure := cl
      code :=
        if fuelout = 1 then "[rcic_scope_fuel]"
        else if rm.ok = 0 || um.ok = 0 || em.ok = 0 then "[rcic_scope_set_unresolved]"
        else if r1 = 0 then "[rcic_scope_roots_not_in_universe]"
        else if ra.ok = 0 then ra.code
        else if pg.ok = 0 then "[rcic_scope_profile_unresolved]"
        else if gok = 0 then "[rcic_scope_grade_unknown]"
        else if rw.ok = 0 then rw.code
        else "" }

/-! ## Clause-level statements over the produced record -/

/-- (1) every declared root is in the source universe (the produced `r1`). -/
def rootsInUniverse' (o : SOut) : Prop := o.r1 = 1

/-- (2) the relevance predicate resolves to nonempty canonical bytes (`r2`). -/
def relevanceFrozen' (o : SOut) : Prop := o.r2 = 1

/-- (3) the role-closure members resolve under a known grade (`r3`). -/
def closureComplete' (o : SOut) : Prop := o.r3 = 1

theorem okOf_eq_one (r1 r2 r3 : Int) :
    okOf r1 r2 r3 = 1 ↔ r1 = 1 ∧ r2 = 1 ∧ r3 = 1 := by
  unfold okOf; by_cases h1 : r1 = 1 <;> by_cases h2 : r2 = 1 <;> by_cases h3 : r3 = 1 <;> simp_all

/-- The produced `ok` flag is exactly the (1)∧(2)∧(3) conjunction — for every
    record whose `ok` is `okOf` of its clause flags, which is how `evalScopeExact`
    builds BOTH branches (`refuseOut` gives `okOf 0 0 0 = 0`; the success record
    gives `okOf r1 r2 r3`). Clause (4) (no ambient read) stays unbuilt: no
    extractor exists, so nothing here concludes it or `NativeRCICClosed`. -/
theorem scopeExact_dataHalf (o : SOut) (h : o.ok = okOf o.r1 o.r2 o.r3) :
    o.ok = 1 ↔ rootsInUniverse' o ∧ relevanceFrozen' o ∧ closureComplete' o := by
  unfold rootsInUniverse' relevanceFrozen' closureComplete'
  rw [h, okOf_eq_one]

/-! ## Corpus pins: all 26 rows of `apps/rcic-scope-exact/rcic_scope_exact_corpus.json`.
    The model is pinned to the carrier's full produced record per row (M-002). -/

-- row 0: ScopeExact (1)-(3) all hold; closure {o1,r1,r2} over refs edges
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨1, 1, 1, 1, ["r1", "r2"], ["r1", "r2", "r3"], ["refs"], "0", ["o1", "r1", "r2"], ""⟩

-- row 1: r1 fails: declared root r2 not in source universe
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨0, 0, 1, 1, ["r1", "r2"], ["r1", "r3"], ["refs"], "0", ["o1", "r1", "r2"], "[rcic_scope_roots_not_in_universe]"⟩

-- row 2: root_set_ref unresolvable: member decode fails (r1,r3 fail)
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨0, 0, 1, 0, [], ["r1", "r2", "r3"], ["refs"], "0", [], "[rcic_scope_set_unresolved]"⟩

-- row 3: source_universe_ref unresolvable: r1 fails, closure still decided
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨0, 0, 1, 1, ["r1", "r2"], [], ["refs"], "0", ["o1", "r1", "r2"], "[rcic_scope_set_unresolved]"⟩

-- row 4: required_edge_role_set_ref unresolvable: r3 fails, r1 still decided
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨0, 1, 1, 0, ["r1", "r2"], ["r1", "r2", "r3"], [], "0", [], "[rcic_scope_set_unresolved]"⟩

-- row 5: relevance_predicate_ref not in store: r2 fails
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨0, 1, 0, 1, ["r1", "r2"], ["r1", "r2", "r3"], ["refs"], "0", ["o1", "r1", "r2"], "[rcic_scope_relevance_unresolved]"⟩

-- row 6: relevance ref collides in store (two byte bodies): r2 fails
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩, ⟨"rp0", "note:other|spec:v2"⟩] 8 == ⟨0, 1, 0, 1, ["r1", "r2"], ["r1", "r2", "r3"], ["refs"], "0", ["o1", "r1", "r2"], "[rcic_scope_relevance_unresolved]"⟩

-- row 7: relevance ref resolves to empty bytes: no frozen spec
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", ""⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨0, 1, 0, 1, ["r1", "r2"], ["r1", "r2", "r3"], ["refs"], "0", ["o1", "r1", "r2"], "[rcic_scope_relevance_empty]"⟩

-- row 8: relevance ref resolves to noncanonical bytes
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "spec:v1|note:frozen"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨0, 1, 0, 1, ["r1", "r2"], ["r1", "r2", "r3"], ["refs"], "0", ["o1", "r1", "r2"], "[rcic_scope_relevance_noncanonical]"⟩

-- row 9: dependency_extraction_profile_ref unresolvable: r3 fails
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"r1", "refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨0, 1, 1, 0, ["r1", "r2"], ["r1", "r2", "r3"], ["refs"], "", ["o1", "r1", "r2"], "[rcic_scope_profile_unresolved]"⟩

-- row 10: profile grade 2 (unknown): not a selected dependency grade
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:2"⟩, ⟨"r1", "refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨0, 1, 1, 0, ["r1", "r2"], ["r1", "r2", "r3"], ["refs"], "2", ["o1", "r1", "r2"], "[rcic_scope_grade_unknown]"⟩

-- row 11: profile object has no grade part: grade unset fails closed
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "note:x"⟩, ⟨"r1", "refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨0, 1, 1, 0, ["r1", "r2"], ["r1", "r2", "r3"], ["refs"], "", ["o1", "r1", "r2"], "[rcic_scope_grade_unknown]"⟩

-- row 12: basis has no dependency_extraction_profile_ref: r3 fails
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨0, 1, 1, 0, ["r1", "r2"], ["r1", "r2", "r3"], ["refs"], "", ["o1", "r1", "r2"], "[rcic_scope_profile_unresolved]"⟩

-- row 13: basis_bytes noncanonical: refused at input shape
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "x" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨0, 0, 0, 0, [], [], [], "", [], "[rcic_scope_basis_shape]"⟩

-- row 14: scope missing source_universe_ref: exact-key shape refuse
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨0, 0, 0, 0, [], [], [], "", [], "[rcic_scope_shape]"⟩

-- row 15: scope_bytes noncanonical key order refused
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|source_universe_ref:su0|root_set_ref:rt0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨0, 0, 0, 0, [], [], [], "", [], "[rcic_scope_shape]"⟩

-- row 16: refs edge reaches a digest absent from the store: r3 fails
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:ghost"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨0, 1, 1, 0, ["r1", "r2"], ["r1", "r2", "r3"], ["refs"], "0", ["ghost", "r1", "r2"], "[rcic_basis_ref_unavailable]"⟩

-- row 17: edge under a non-required role contributes nothing to the closure
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "other:ghost|refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨1, 1, 1, 1, ["r1", "r2"], ["r1", "r2", "r3"], ["refs"], "0", ["o1", "r1", "r2"], ""⟩

-- row 18: roles={other}: variant walk follows only other-edges; ghost reached, o1 not
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:other"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "other:ghost|refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨0, 1, 1, 0, ["r1", "r2"], ["r1", "r2", "r3"], ["other"], "0", ["ghost", "r1", "r2"], "[rcic_basis_ref_unavailable]"⟩

-- row 19: walk fuel=1 on a two-pass graph: refused, not decided
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:a"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩, ⟨"a", "refs:x"⟩, ⟨"x", "name:x"⟩] 1 == ⟨0, 1, 1, 0, ["r1", "r2"], ["r1", "r2", "r3"], ["refs"], "0", [], "[rcic_scope_fuel]"⟩

-- row 20: reachable member resolves digest-only (empty bytes): r3 fails
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:o2"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩, ⟨"o2", ""⟩] 8 == ⟨0, 1, 1, 0, ["r1", "r2"], ["r1", "r2", "r3"], ["refs"], "0", ["o2", "r1", "r2"], "[rcic_basis_ref_unavailable]"⟩

-- row 21: reachable member digest collides in store: r3 fails
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩, ⟨"o1", "data:y"⟩] 8 == ⟨0, 1, 1, 0, ["r1", "r2"], ["r1", "r2", "r3"], ["refs"], "0", ["o1", "r1", "r2"], "[rcic_basis_ref_unavailable]"⟩

-- row 22: declared root r2 absent from store: r1 holds, r3 fails
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:o1"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩] 8 == ⟨0, 1, 1, 0, ["r1", "r2"], ["r1", "r2", "r3"], ["refs"], "0", ["o1", "r1", "r2"], "[rcic_basis_ref_unavailable]"⟩

-- row 23: roles={other,refs}: variant walk unions both edge roles
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:other,refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "other:o2|refs:o1"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩, ⟨"o2", "data:y"⟩] 8 == ⟨1, 1, 1, 1, ["r1", "r2"], ["r1", "r2", "r3"], ["other", "refs"], "0", ["o1", "o2", "r1", "r2"], ""⟩

-- row 24: fuel=3: walk closes, resolve budget one short of the 4-member closure
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:a"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩, ⟨"a", "refs:x"⟩, ⟨"x", "name:x"⟩] 3 == ⟨0, 1, 1, 0, ["r1", "r2"], ["r1", "r2", "r3"], ["refs"], "0", ["a", "r1", "r2", "x"], "[rcic_basis_fuel]"⟩

-- row 25: fuel=4: two-pass walk and four-member resolve both within budget
#guard evalScopeExact "relevance_predicate_ref:rp0|required_edge_role_set_ref:rs0|root_set_ref:rt0|source_universe_ref:su0" "basis_mode:fromGenesis|closure_scope_ref:cs0|dependency_extraction_profile_ref:dx0|master_profile_ref:mp0" [⟨"rt0", "refs:r1,r2"⟩, ⟨"su0", "refs:r1,r2,r3"⟩, ⟨"rs0", "refs:refs"⟩, ⟨"rp0", "note:frozen|spec:v1"⟩, ⟨"dx0", "grade:0"⟩, ⟨"r1", "refs:a"⟩, ⟨"r2", "name:root2"⟩, ⟨"o1", "data:x"⟩, ⟨"r3", "data:extra"⟩, ⟨"a", "refs:x"⟩, ⟨"x", "name:x"⟩] 4 == ⟨1, 1, 1, 1, ["r1", "r2"], ["r1", "r2", "r3"], ["refs"], "0", ["a", "r1", "r2", "x"], ""⟩

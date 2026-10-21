/-
RCIC 00 §11 — the authority-critical set + `publicExact`, the pinned Lean model
of `apps/rcic-authority-critical`
(`rcic.authority_critical closure_bytes genesis_ref store fuel`).

The carrier decides the DATA half of 00:265 ("All authority-critical profiles,
specifications, source artifacts, executable artifacts, proof forests,
activation histories, and recovery histories require `publicExact` …") over a
DECLARED `active_authority_occurrence_ref`: the occurrence→statement→artifact
chain resolves; the `refs`-closure of the artifact, the DERIVED activation
history, and the DERIVED recovery history form one canonical deduplicated
union; every union member resolves to nonempty collision-free bytes. The
histories are scanned from the one store (`rcic.auth_reservation_kind_refs`)
and validated by the `rcic.auth_projection` chain — the AH-020a/AH-013
derivation; no presented set object is read. Deriving WHICH occurrence is
active is the authority layer's lane — unbuilt here; `policySelects` stays
absent. Nothing concludes `NativeRCICClosed`.

PIN (M-002): all 42 rows of
`apps/rcic-authority-critical/rcic_authority_critical_corpus.json` below; the
record-level statements `criticalUnion'` / `publicExactAll'` /
`derivedRecovery'` / `derivedActivation'` agree with the carrier's produced
record on every row (M-002a).

TRANSCRIPTION TABLE (the scm modules → Lean):
  rcic.canon_bytes_ok                → `Rcic.BoundObject.canonBytesOk` (reused)
  rcic.store_scan                    → `Rcic.BoundObject.storeScan` (reused)
  rcic.canonical_at                  → `Rcic.BoundObject.canonicalAt` (reused;
                                       `RcicTypedRef.deriveDigest` inside)
  rcic.auth_activation_part_at       → `Rcic.Scm.Embed.partAt` (reused)
  rcic.closure_basis_keys_ok         → `Rcic.ScopeExact.keysOk` (reused)
  rcic.authority_closure_walk        → `Rcic.ScopeExact.walk` (reused)
  rcic.residue_rows_canon            → `Rcic.ScopeExact.listCanon` (reused)
  rcic.residue_rows_insert           → `Rcic.ScopeExact.listInsert` (reused)
  rcic.residue_rows_member           → `Rcic.ScopeExact.listMember` (reused)
  rcic.closure_basis_refs_walk       → `Rcic.ScopeExact.refsWalk` (reused)
  rcic.auth_reservation_kind_refs    → `kindRefs`
  rcic.value_at_digits_ok            → `digitsOk`
  rcic.genesis_floor_coords_ok       → `coordsOk`
  rcic.auth_activation_ref_bound     → `refBound`
  rcic.auth_activation_seq_ok        → `seqOk`
  rcic.auth_projection_shape         → `projShape`
  rcic.auth_projection_hist_bound    → `histBound`
  rcic.auth_projection_candidates    → `candidates`
  rcic.auth_projection_seq_class     → `seqClass`
  rcic.auth_projection_walk          → `projWalk`/`projWalkAux`
  rcic.auth_projection_leftover      → `leftover`
  rcic.auth_projection_blocked       → `projBlocked`
  rcic.auth_projection               → `projection`
  rcic.authcrit_obj_at               → `objAt`
  rcic.authority_critical_refuse     → `refuseOut`
  rcic.authority_critical            → `evalAuthorityCritical`
-/
import rcic.RcicScopeExactModel

namespace Rcic.AuthorityCritical

open Rcic.BoundObject (StoreEntry storeScan canonBytesOk canonicalAt)
open Rcic.Scm.Embed (partAt)
open Rcic.ScopeExact (keysOk listCanon listInsert listMember walk refsWalk)

/-! ## The scm modules, mirrored -/

/-- `string->int` on the digital domain. In scm a non-digital (or empty)
    string is an eval-time residue, not a value — every site this model
    reaches it through is behind a `digitsOk`/canonical guard, so the
    pinned domain is digital strings; `.getD 0` is unreachable there. -/
def strToInt (s : String) : Int := (s.toNat?).map Int.ofNat |>.getD 0

/-- `rcic.value_at_digits_ok`: nonempty, all chars in `'0'..'9'`. -/
def digitsOk (s : String) : Bool := s.length > 0 && s.toList.all Char.isDigit

/-- `rcic.genesis_floor_coords_ok`: `epoch` and `sequence` parts digital. -/
def coordsOk (bytes : String) : Bool :=
  digitsOk (partAt bytes "epoch") && digitsOk (partAt bytes "sequence")

/-- `rcic.auth_reservation_kind_refs` (vendored from the AH-017a derivation):
    the digest of every store entry whose `kind` part equals `kind`,
    in scan order. The one derivation of a history class — a presented list
    cannot omit or add. -/
def kindRefs (store : List StoreEntry) (kind : String) : List String :=
  store.foldl (fun acc e =>
    if partAt e.bytes "kind" = kind then acc ++ [e.digest] else acc) []

/-- `rcic.auth_activation_ref_bound`'s output `{ok, code, bytes, epoch, sequence}`. -/
structure RBOut where
  ok : Int
  code : String
  bytes : String
  epoch : Int
  sequence : Int
  deriving BEq

/-- `rcic.auth_activation_ref_bound`: resolve `ref`, `canonical_at` it at
    (class, kind), then read its coordinates; `require_earlier ≠ 0` adds the
    strictly-earlier coordinate check. -/
def refBound (fuel cls kind : Int) (ref : String) (store : List StoreEntry)
    (candEpoch candSeq requireEarlier : Int) (missCode : String) : RBOut :=
  let s := storeScan store ref
  if !s.found then ⟨0, missCode, "", 0, 0⟩
  else if s.collision then ⟨0, missCode, "", 0, 0⟩
  else
    let c := canonicalAt fuel cls kind ref s.bytes
    if c.ok = 0 then ⟨0, c.code, "", 0, 0⟩
    else
      let e := strToInt (partAt s.bytes "epoch")
      let q := strToInt (partAt s.bytes "sequence")
      if requireEarlier = 0 then ⟨1, "", s.bytes, e, q⟩
      else if e < candEpoch then ⟨1, "", s.bytes, e, q⟩
      else if e = candEpoch then
        if q < candSeq then ⟨1, "", s.bytes, e, q⟩
        else ⟨0, "[rcic_auth_activation_not_earlier]", "", e, q⟩
      else ⟨0, "[rcic_auth_activation_not_earlier]", "", e, q⟩

/-- `rcic.auth_projection_shape`'s output: `1`/`0` — every found,
    collision-free member of `refs` has digital coordinates (missing and
    colliding entries are the bound pass's problem, not the shape's). -/
def projShape (refs : List String) (store : List StoreEntry) : Int :=
  refs.foldl (fun acc r =>
    if acc = 0 then 0
    else
      let s := storeScan store r
      if !s.found || s.collision then 1
      else if coordsOk s.bytes then 1 else 0) 1

/-- `rcic.auth_projection_hist_bound`'s output `{ok, code}`: fold —
    every ref bound at its derived digest, first failure's code. -/
structure OCOut where
  ok : Int
  code : String
  deriving BEq

def histBound (fuel : Int) (refs : List String) (store : List StoreEntry)
    (missCode : String) : OCOut :=
  refs.foldl (fun acc r =>
    if acc.ok = 0 then acc
    else
      let b := refBound fuel 3 0 r store 0 0 0 missCode
      if b.ok = 0 then ⟨0, b.code⟩ else ⟨1, ""⟩) ⟨1, ""⟩

/-- `rcic.auth_activation_seq_ok`: same-epoch `seq+1` or next-epoch `seq 0`. -/
def seqOk (candEpoch candSeq predEpoch predSeq : Int) : Bool :=
  if candEpoch = predEpoch then candSeq = predSeq + 1
  else if candEpoch = predEpoch + 1 then candSeq = 0
  else false

/-- `rcic.auth_projection_seq_class`: `0` valid step, `1` duplicate,
    `2` back edge, `3` future reference. -/
def seqClass (candEpoch candSeq tipEpoch tipSeq : Int) : Int :=
  if seqOk candEpoch candSeq tipEpoch tipSeq then 0
  else if candEpoch = tipEpoch then
    if candSeq = tipSeq then 1 else if candSeq < tipSeq then 2 else 3
  else if candEpoch < tipEpoch then 2 else 3

/-- `rcic.auth_projection_candidates`' per-entry fold step. -/
private def candStep (store : List StoreEntry) (tip : String)
    (acc : List String) (x : String) : List String :=
  if !(storeScan store x).found || (storeScan store x).collision then acc
  else if partAt (storeScan store x).bytes "predecessor" = tip then
    listInsert acc x else acc

/-- `rcic.auth_projection_candidates`: the scanned activation refs whose
    resolved `predecessor` part equals `tip`, sorted-inserted. -/
def candidates (acts : List String) (tip : String) (store : List StoreEntry) :
    List String :=
  acts.foldl (candStep store tip) []

/-- `rcic.auth_projection_walk`'s output `{ok, code, tip, consumed}`. -/
structure PwOut where
  ok : Int
  code : String
  tip : String
  consumed : List String
  deriving BEq

/-- `rcic.auth_projection_walk`, on a Nat recursion depth — scm's
    `fuel < 0 → [rcic_projection_fuel]` is `depth = 0`; `projWalk` maps the
    Int fuel to `depth = (fuel + 1).toNat`, which is the same boundary
    (scm `fuel = -1` refuses before evaluating candidates; `fuel = 0`
    evaluates one level and lets the recursion refuse). -/
def projWalkAux : Nat → String → List String → List String → List StoreEntry → PwOut
  | 0, _, _, consumed, _ => ⟨0, "[rcic_projection_fuel]", "", consumed⟩
  | depth + 1, tip, acts, consumed, store =>
      let cands := candidates acts tip store
      if cands.length > 1 then ⟨0, "[rcic_projection_fork]", "", consumed⟩
      else if cands.length = 0 then ⟨1, "", tip, consumed⟩
      else
        let c := cands.headD ""
        let csc := storeScan store c
        let tsc := storeScan store tip
        let cls := seqClass (strToInt (partAt csc.bytes "epoch"))
          (strToInt (partAt csc.bytes "sequence"))
          (strToInt (partAt tsc.bytes "epoch"))
          (strToInt (partAt tsc.bytes "sequence"))
        if cls = 0 then projWalkAux depth c acts (listInsert consumed c) store
        else if cls = 1 then ⟨0, "[rcic_projection_duplicate_sequence]", "", consumed⟩
        else if cls = 2 then ⟨0, "[rcic_projection_back_edge]", "", consumed⟩
        else ⟨0, "[rcic_projection_future_ref]", "", consumed⟩

def projWalk (fuel : Int) (tip : String) (acts consumed : List String)
    (store : List StoreEntry) : PwOut :=
  projWalkAux (fuel + 1).toNat tip acts consumed store

/-- `rcic.auth_projection_leftover`: `true` iff some scanned activation was
    not consumed by the walk (an orphan the history cannot silently drop). -/
def leftover (acts consumed : List String) : Bool :=
  acts.any (fun r => !listMember consumed r)

/-- `rcic.auth_projection_blocked`: `true` iff some found challenge targets
    `tip` with `status ≠ "resolved"`. -/
def projBlocked (chs : List String) (tip : String) (store : List StoreEntry) :
    Bool :=
  chs.any (fun r =>
    let s := storeScan store r
    s.found && !s.collision && partAt s.bytes "target" = tip &&
      partAt s.bytes "status" != "resolved")

/-- `rcic.auth_projection`'s output `{ok, tip, code}` —
    `rcic.auth_projection_ok`/`refuse`. -/
structure PrjOut where
  ok : Int
  tip : String
  code : String
  deriving BEq

/-- `rcic.auth_projection`: genesis bound and root-checked, activation shape,
    all three histories bound, the predecessor walk, orphan check, blocking
    challenge, tip integrity residue — each failure's named code passes
    through unchanged. -/
def projection (fuel form : Int) (genesisRef : String)
    (acts chs recs : List String) (hint : String) (ints : List String)
    (store : List StoreEntry) : PrjOut :=
  let go := if form = 0 then true else if form = 1 then hint = "" else false
  if go then
    if fuel < 0 then ⟨0, "", "[rcic_projection_fuel]"⟩
    else
      let gb := refBound (fuel - 1) 3 0 genesisRef store 0 0 0
        "[rcic_projection_genesis_unbound]"
      if gb.ok = 0 then ⟨0, "", gb.code⟩
      else if partAt gb.bytes "kind" != "genesis" then
        ⟨0, "", "[rcic_projection_genesis_not_root]"⟩
      else if partAt gb.bytes "predecessor" != "" then
        ⟨0, "", "[rcic_projection_genesis_not_root]"⟩
      else
        let sh := projShape acts store
        if sh = 0 then ⟨0, "", "[rcic_projection_occurrence_shape]"⟩
        else
          let hb := histBound (fuel - 1) acts store
            "[rcic_projection_activation_unbound]"
          if hb.ok = 0 then ⟨0, "", hb.code⟩
          else
            let cb := histBound (fuel - 1) chs store
              "[rcic_projection_challenge_unbound]"
            if cb.ok = 0 then ⟨0, "", cb.code⟩
            else
              let rb := histBound (fuel - 1) recs store
                "[rcic_projection_recovery_unbound]"
              if rb.ok = 0 then ⟨0, "", rb.code⟩
              else
                let w := projWalk (fuel - 1) genesisRef acts [] store
                if w.ok = 0 then ⟨0, "", w.code⟩
                else if leftover acts w.consumed then
                  ⟨0, "", "[rcic_projection_orphan_activation]"⟩
                else if projBlocked chs w.tip store then
                  ⟨0, "", "[rcic_projection_tip_blocked]"⟩
                else if listMember ints w.tip then
                  ⟨0, "", "[rcic_projection_tip_integrity]"⟩
                else ⟨1, w.tip, ""⟩
  else if form = 1 then ⟨0, "", "[rcic_projection_current_not_writable]"⟩
  else ⟨0, "", "[rcic_projection_unknown_form]"⟩

/-- `rcic.authcrit_obj_at`'s output `{ok, bytes}`: a chain object resolves to
    canonical bytes — store hit, no collision, nonempty, canonical. -/
structure OOut where
  ok : Int
  bytes : String
  deriving BEq

/-- `rcic.authcrit_obj_at`. -/
def objAt (store : List StoreEntry) (r : String) : OOut :=
  let s := storeScan store r
  if s.found && !s.collision && s.bytes.length > 0 && canonBytesOk s.bytes
    then ⟨1, s.bytes⟩
    else ⟨0, ""⟩

/-- `rcic.authority_critical`'s sigma
    `{ok, artifact, closure, activation, recovery, critical, code}`. -/
structure ACOut where
  ok : Int
  artifact : String
  closure : List String
  activation : List String
  recovery : List String
  critical : List String
  code : String
  deriving BEq

/-- `rcic.authority_critical_refuse`. -/
def refuseOut (code : String) : ACOut := ⟨0, "", [], [], [], [], code⟩

/-- `rcic.authority_critical`: early-refuse pipeline — the closure shape, the
    occurrence→statement→artifact chain, the store-derived histories under
    the projection chain, the `refs` closure walk, the deduplicated union,
    and the per-member `publicExact` walk (`rcic.closure_basis_refs_walk`,
    unremapped codes). -/
def evalAuthorityCritical (closureBytes genesisRef : String)
    (store : List StoreEntry) (fuel : Int) : ACOut :=
  if !canonBytesOk closureBytes then refuseOut "[rcic_authcrit_closure_shape]"
  else if !keysOk closureBytes
      ["active_authority_occurrence_ref", "closure_basis_ref"]
    then refuseOut "[rcic_authcrit_closure_shape]"
  else
    let occ := objAt store (partAt closureBytes "active_authority_occurrence_ref")
    if occ.ok = 0 then refuseOut "[rcic_authcrit_occurrence_unresolved]"
    else
      let str := partAt occ.bytes "statement_ref"
      if str = "" then refuseOut "[rcic_authcrit_statement_unresolved]"
      else
        let st := objAt store str
        if st.ok = 0 then refuseOut "[rcic_authcrit_statement_unresolved]"
        else
          let aref := partAt st.bytes "candidate_authority_artifact_ref"
          if aref = "" then refuseOut "[rcic_authcrit_artifact_unresolved]"
          else
            let a := objAt store aref
            if a.ok = 0 then refuseOut "[rcic_authcrit_artifact_unresolved]"
            else
              let acts := kindRefs store "successor"
              let chs := kindRefs store "challenge"
              let recs := kindRefs store "recovery"
              let ints := kindRefs store "integrity"
              let p := projection fuel 0 genesisRef acts chs recs "" ints store
              if p.ok = 0 then refuseOut p.code
              else
                let w := projWalk (fuel - 1) genesisRef acts [] store
                if w.ok = 0 then refuseOut w.code
                else
                  let activation := listInsert w.consumed genesisRef
                  let cl := walk store [aref] fuel
                  if cl.length = 0 then refuseOut "[rcic_authcrit_fuel]"
                  else
                    let critical := listCanon (cl ++ activation ++ recs)
                    let rw := refsWalk fuel critical store
                    ⟨rw.ok, aref, cl, activation, recs, critical, rw.code⟩

/-! ## Record-level statements -/

/-- The produced `critical` is exactly the canonical (sorted, deduplicated)
    union of the produced `closure`, `activation`, and `recovery` member lists.
    `evalAuthorityCritical` maintains this on BOTH branches: the success record
    sets `critical := listCanon (cl ++ activation ++ recs)`, and `refuseOut`
    gives `listCanon ([] ++ [] ++ []) = []`. -/
def criticalUnion' (o : ACOut) : Prop :=
  o.critical = listCanon (o.closure ++ o.activation ++ o.recovery)

theorem criticalUnion_refuse (code : String) : criticalUnion' (refuseOut code) := rfl

theorem criticalUnion_success (ok : Int) (aref : String) (cl am rem : List String)
    (code : String) :
    criticalUnion' ⟨ok, aref, cl, am, rem, listCanon (cl ++ am ++ rem), code⟩ := rfl

/-- The produced `recovery` list IS the store's `kind:recovery` scan — the
    derived history, never a presented set. Stated for any record built the
    way `evalAuthorityCritical` builds it: `refuseOut` satisfies it vacuously
    (`ok = 0`). -/
def derivedRecovery' (o : ACOut) (store : List StoreEntry) : Prop :=
  o.ok = 1 → o.recovery = kindRefs store "recovery"

theorem derivedRecovery_refuse (code : String) (store : List StoreEntry) :
    derivedRecovery' (refuseOut code) store :=
  fun h => absurd h (show ¬(0 : Int) = 1 from by decide)

theorem derivedRecovery_success (ok : Int) (aref : String) (cl act : List String)
    (store : List StoreEntry) (crit : List String) (code : String) :
    derivedRecovery' ⟨ok, aref, cl, act, kindRefs store "recovery", crit, code⟩
      store := fun _ => rfl

/-- The produced `activation` list IS `genesisRef` inserted into the walk's
    consumed successor refs — the projection chain from genesis, not a
    presented list. Vacuous on a refuse record. -/
def derivedActivation' (o : ACOut) (genesisRef : String) (consumed : List String) :
    Prop :=
  o.ok = 1 → o.activation = listInsert consumed genesisRef

theorem derivedActivation_refuse (code : String) (genesisRef : String)
    (consumed : List String) :
    derivedActivation' (refuseOut code) genesisRef consumed :=
  fun h => absurd h (show ¬(0 : Int) = 1 from by decide)

theorem derivedActivation_success (ok : Int) (aref : String) (cl : List String)
    (genesisRef : String) (consumed rec crit : List String) (code : String) :
    derivedActivation'
      ⟨ok, aref, cl, listInsert consumed genesisRef, rec, crit, code⟩
      genesisRef consumed := fun _ => rfl

/-- `publicExact` over the produced `critical`: every member resolves to
    nonempty collision-free bytes — a digest-only commitment is not
    availability. -/
def memberAvailable (store : List StoreEntry) (r : String) : Prop :=
  (storeScan store r).found = true ∧ (storeScan store r).collision = false ∧
    (storeScan store r).bytes.length > 0

/-- Every produced `critical` member is `publicExact`. -/
def publicExactAll' (o : ACOut) (store : List StoreEntry) : Prop :=
  ∀ r ∈ o.critical, memberAvailable store r

/-! ## The derivation lemmas -/

/-- `listInsert` membership: the inserted element or an old member. -/
private theorem listInsert_mem (xs : List String) (c r : String) :
    r ∈ listInsert xs c ↔ r = c ∨ r ∈ xs := by
  induction xs with
  | nil => simp [listInsert]
  | cons y ys ih =>
      simp only [listInsert]
      by_cases hye : y = c
      · rw [if_pos hye]
        subst hye
        rw [List.mem_cons]
        constructor
        · intro h
          rcases h with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (Or.inr h2)
        · intro h
          rcases h with h1 | h2
          · exact Or.inl h1
          · exact h2
      · by_cases hlt : c < y
        · rw [if_neg hye, if_pos hlt, List.mem_cons]
        · rw [if_neg hye, if_neg hlt]
          simp only [List.mem_cons]
          rw [ih]
          exact or_left_comm

/-- `candStep` adds nothing but `x` itself. -/
private theorem candStep_subset (store : List StoreEntry) (tip : String)
    (acc : List String) (x r : String)
    (hr : r ∈ candStep store tip acc x) : r ∈ acc ∨ r = x := by
  unfold candStep at hr
  by_cases h1 : (!(storeScan store x).found ||
      (storeScan store x).collision) = true
  · rw [if_pos h1] at hr; exact Or.inl hr
  · rw [if_neg h1] at hr
    by_cases h2 : partAt (storeScan store x).bytes "predecessor" = tip
    · rw [if_pos h2] at hr
      rcases (listInsert_mem acc x r).mp hr with he | hin
      · exact Or.inr he
      · exact Or.inl hin
    · rw [if_neg h2] at hr; exact Or.inl hr

/-- The `candStep` fold only produces members of the scanned list or the seed
    accumulator. -/
private theorem fold_candStep_subset (store : List StoreEntry) (tip : String) :
    ∀ (xs acc : List String), ∀ r ∈ xs.foldl (candStep store tip) acc,
      r ∈ xs ++ acc := by
  intro xs
  induction xs with
  | nil => intro acc r hr; exact List.mem_append_right _ hr
  | cons a xs ih =>
      intro acc r hr
      rw [List.foldl_cons] at hr
      rcases List.mem_append.mp (ih _ r hr) with hxs | hacc
      · exact List.mem_append_left _ (List.mem_cons_of_mem _ hxs)
      · rcases candStep_subset store tip acc a r hacc with hin | heq
        · exact List.mem_append_right _ hin
        · subst heq; exact List.mem_append_left _ (List.mem_cons_self _ _)

/-- `candidates` only ever inserts members of `acts` — a consumed ref is a
    scanned ref, never an invented one. -/
theorem candidates_subset (acts : List String) (tip : String)
    (store : List StoreEntry) (r : String)
    (hr : r ∈ candidates acts tip store) : r ∈ acts := by
  have := fold_candStep_subset store tip acts [] r hr
  rcases List.mem_append.mp this with h1 | h2
  · exact h1
  · exact absurd h2 (List.not_mem_nil _)

/-- `listInsert` membership, one direction used below. -/
private theorem mem_of_mem_listInsert {xs : List String} {c r : String}
    (h : r ∈ listInsert xs c) : r = c ∨ r ∈ xs := (listInsert_mem xs c r).mp h

/-- `headD` of a nonempty list is a member. -/
private theorem headD_mem (l : List String) (d : String) (h : l ≠ []) :
    l.headD d ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => exact List.mem_cons_self _ _

/-- The walk's `consumed` only grows by refs drawn from `acts`: every consumed
    member was already in the accumulator or is a scanned activation — the
    activation history can never contain a ref outside the store scan. -/
theorem projWalkAux_consumed_subset (depth : Nat) (tip : String)
    (acts consumed : List String) (store : List StoreEntry) :
    ∀ r ∈ (projWalkAux depth tip acts consumed store).consumed,
      r ∈ consumed ++ acts := by
  induction depth generalizing tip consumed with
  | zero =>
      intro r hr
      exact List.mem_append_left _ hr
  | succ depth ih =>
      intro r hr
      simp only [projWalkAux] at hr
      split at hr
      · exact List.mem_append_left _ hr
      · split at hr
        · exact List.mem_append_left _ hr
        · split at hr
          · rename_i hcls hnone hfork
            have hne : candidates acts tip store ≠ [] := by
              intro hnil; rw [hnil] at hnone; exact hnone rfl
            have hca := candidates_subset acts tip store _ (headD_mem _ "" hne)
            have hsub := ih _ _ r hr
            rcases List.mem_append.mp hsub with hin | hact
            · rcases mem_of_mem_listInsert hin with he | hin
              · subst he; exact List.mem_append_right _ hca
              · exact List.mem_append_left _ hin
            · exact List.mem_append_right _ hact
          · split at hr
            · exact List.mem_append_left _ hr
            · split at hr
              · exact List.mem_append_left _ hr
              · exact List.mem_append_left _ hr

/-! ## The availability walk, restated as a proposition -/

private def step (store : List StoreEntry) (acc : ScopeExact.WOut) (r : String) :
    ScopeExact.WOut :=
  if acc.ok = 1 then
    if acc.fuelLeft > 0 then
      let s := storeScan store r
      if !s.found then ⟨0, acc.fuelLeft, "[rcic_basis_ref_unavailable]"⟩
      else if s.collision then ⟨0, acc.fuelLeft, "[rcic_basis_ref_unavailable]"⟩
      else if s.bytes.length > 0 then ⟨1, acc.fuelLeft - 1, ""⟩
      else ⟨0, acc.fuelLeft, "[rcic_basis_ref_unavailable]"⟩
    else ⟨0, acc.fuelLeft, "[rcic_basis_fuel]"⟩
  else acc

private theorem refsWalk_eq_foldl (fuel : Int) (cs : List String) (store : List StoreEntry) :
    refsWalk fuel cs store = List.foldl (step store) ⟨1, fuel, ""⟩ cs := rfl

private theorem fold_stuck (store : List StoreEntry) :
    ∀ (cs : List String) (acc : ScopeExact.WOut), acc.ok ≠ 1 →
      List.foldl (step store) acc cs = acc := by
  intro cs
  induction cs with
  | nil => intro acc _; rfl
  | cons c cs ih =>
      intro acc h
      rw [List.foldl_cons]
      have hstep : step store acc c = acc := by
        unfold step; rw [if_neg h]
      rw [hstep]; exact ih acc h

private theorem fold_ok_iff (store : List StoreEntry) :
    ∀ (cs : List String) (acc : ScopeExact.WOut), acc.ok = 1 →
      ((List.foldl (step store) acc cs).ok = 1 ↔
        (∀ r ∈ cs, memberAvailable store r) ∧ cs.length ≤ acc.fuelLeft.toNat) := by
  intro cs
  induction cs with
  | nil =>
      intro acc hacc
      constructor
      · intro _; exact ⟨fun r hr => absurd hr (List.not_mem_nil r), Nat.zero_le _⟩
      · intro _; exact hacc
  | cons c cs ih =>
      intro acc hacc
      rw [List.foldl_cons]
      cases hfe : decide (0 < acc.fuelLeft) with
      | true =>
          have hf : 0 < acc.fuelLeft := of_decide_eq_true hfe
          cases hf1 : (storeScan store c).found with
          | false =>
              have hnot : ¬ memberAvailable store c := by
                intro h; obtain ⟨hfnd, -, -⟩ := h; simp_all
              have hstep0 : (step store acc c).ok = 0 := by
                unfold step
                rw [if_pos hacc, if_pos hf]
                simp [hf1]
              have h0 : (List.foldl (step store) (step store acc c) cs).ok = 0 := by
                rw [fold_stuck store cs _ (by simp [hstep0]), hstep0]
              rw [h0]
              constructor
              · intro h; exact absurd h (by decide)
              · intro h; obtain ⟨hall, -⟩ := h
                exact absurd (hall c (List.mem_cons_self ..)) hnot
          | true =>
            cases hc1 : (storeScan store c).collision with
            | true =>
                have hnot : ¬ memberAvailable store c := by
                  intro h; obtain ⟨-, hc, -⟩ := h; simp_all
                have hstep0 : (step store acc c).ok = 0 := by
                  unfold step
                  rw [if_pos hacc, if_pos hf]
                  simp [hf1, hc1]
                have h0 : (List.foldl (step store) (step store acc c) cs).ok = 0 := by
                  rw [fold_stuck store cs _ (by simp [hstep0]), hstep0]
                rw [h0]
                constructor
                · intro h; exact absurd h (by decide)
                · intro h; obtain ⟨hall, -⟩ := h
                  exact absurd (hall c (List.mem_cons_self ..)) hnot
            | false =>
              cases hl1 : decide (0 < (storeScan store c).bytes.length) with
              | false =>
                  have hnot : ¬ memberAvailable store c := by
                    intro h; obtain ⟨-, -, hl⟩ := h
                    exact absurd hl (of_decide_eq_false hl1)
                  have hstep0 : (step store acc c).ok = 0 := by
                    unfold step
                    rw [if_pos hacc, if_pos hf]
                    simp [hf1, hc1, of_decide_eq_false hl1]
                  have h0 : (List.foldl (step store) (step store acc c) cs).ok = 0 := by
                    rw [fold_stuck store cs _ (by simp [hstep0]), hstep0]
                  rw [h0]
                  constructor
                  · intro h; exact absurd h (by decide)
                  · intro h; obtain ⟨hall, -⟩ := h
                    exact absurd (hall c (List.mem_cons_self ..)) hnot
              | true =>
                  have hm : memberAvailable store c :=
                    ⟨hf1, hc1, of_decide_eq_true hl1⟩
                  have hstep : step store acc c = ⟨1, acc.fuelLeft - 1, ""⟩ := by
                    unfold step
                    rw [if_pos hacc, if_pos hf]
                    simp [hf1, hc1, of_decide_eq_true hl1]
                  rw [hstep, ih _ rfl]
                  have hfl : (⟨1, acc.fuelLeft - 1, ""⟩ : ScopeExact.WOut).fuelLeft =
                      acc.fuelLeft - 1 := rfl
                  rw [hfl]
                  constructor
                  · intro h
                    obtain ⟨hall, hbudget⟩ := h
                    refine ⟨fun r hr => ?_, ?_⟩
                    · cases List.mem_cons.1 hr with
                      | inl he => rw [he]; exact hm
                      | inr hin => exact hall r hin
                    · simp only [List.length_cons]
                      omega
                  · intro h
                    obtain ⟨hall, hbudget⟩ := h
                    refine ⟨fun r hr => hall r (List.mem_cons_of_mem _ hr), ?_⟩
                    simp only [List.length_cons] at hbudget
                    omega
      | false =>
          have hf : ¬ (0 < acc.fuelLeft) := of_decide_eq_false hfe
          have hstep0 : step store acc c = ⟨0, acc.fuelLeft, "[rcic_basis_fuel]"⟩ := by
            unfold step; rw [if_pos hacc, if_neg hf]
          have h0 : (List.foldl (step store) (step store acc c) cs).ok = 0 := by
            rw [fold_stuck store cs _ (by simp [hstep0]), hstep0]
          rw [h0]
          constructor
          · intro h; exact absurd h (by decide)
          · intro h; obtain ⟨-, hbudget⟩ := h
            simp only [List.length_cons] at hbudget
            omega

/-- `refsWalk`'s `ok = 1` is decided exactly by: the member count fits the
    fuel budget AND every member resolves to nonempty collision-free bytes. -/
theorem refsWalk_ok_iff (cs : List String) (store : List StoreEntry) (fuel : Int) :
    (refsWalk fuel cs store).ok = 1 ↔
      cs.length ≤ fuel.toNat ∧ ∀ r ∈ cs, memberAvailable store r := by
  rw [refsWalk_eq_foldl]
  have := fold_ok_iff store cs ⟨1, fuel, ""⟩ rfl
  simp only [and_comm] at this
  exact this

/-- The produced `ok` flag decides exactly the availability half — for every
    record whose `ok` is the availability walk's verdict on its `critical`
    (which is how `evalAuthorityCritical` builds the success record; the
    earlier stages refuse before a record is produced). -/
theorem authorityCritical_available (o : ACOut) (fuel : Int) (store : List StoreEntry)
    (h : o.ok = (refsWalk fuel o.critical store).ok) :
    o.ok = 1 ↔ o.critical.length ≤ fuel.toNat ∧ publicExactAll' o store := by
  unfold publicExactAll'
  rw [h, refsWalk_ok_iff]

/-! ## Corpus pins: all 42 rows of
    `apps/rcic-authority-critical/rcic_authority_critical_corpus.json`.
    The model is pinned to the carrier's full produced record per row (M-002). -/
-- row 0: (1) chain+closure+derived histories all publicExact; critical = canon union
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"pol0", "data:policy"⟩, ⟨"rc0", "data:receipt"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨1, "art0", ["art0", "d1", "d2"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], ["a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "art0", "d1", "d2", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], ""⟩

-- row 1: closure_bytes keys in wrong order (noncanonical): shape refuse
#guard evalAuthorityCritical "closure_basis_ref:cb0|active_authority_occurrence_ref:occ0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"pol0", "data:policy"⟩, ⟨"rc0", "data:receipt"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_authcrit_closure_shape]"⟩

-- row 2: closure missing active_authority_occurrence_ref: exact-key refuse
#guard evalAuthorityCritical "closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"pol0", "data:policy"⟩, ⟨"rc0", "data:receipt"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_authcrit_closure_shape]"⟩

-- row 3: closure carries an extra key: exact-key refuse
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0|x:1" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"pol0", "data:policy"⟩, ⟨"rc0", "data:receipt"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_authcrit_closure_shape]"⟩

-- row 4: closure has a part without ':': noncanonical refuse
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0|junk" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"pol0", "data:policy"⟩, ⟨"rc0", "data:receipt"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_authcrit_closure_shape]"⟩

-- row 5: occurrence ref absent from store: chain unresolved
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_authcrit_occurrence_unresolved]"⟩

-- row 6: occurrence bytes noncanonical: chain unresolved
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "b|a:1"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_authcrit_occurrence_unresolved]"⟩

-- row 7: occurrence digest collides in store: chain unresolved
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"occ0", "receipt_ref:rc9|statement_ref:st9"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_authcrit_occurrence_unresolved]"⟩

-- row 8: occurrence digest-only (commitment, not data): chain unresolved
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", ""⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_authcrit_occurrence_unresolved]"⟩

-- row 9: occurrence has no statement_ref part: chain unresolved
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_authcrit_statement_unresolved]"⟩

-- row 10: statement ref absent from store: chain unresolved
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_authcrit_statement_unresolved]"⟩

-- row 11: statement bytes noncanonical: chain unresolved
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "z:1|a:2"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_authcrit_statement_unresolved]"⟩

-- row 12: statement has no candidate_authority_artifact_ref: chain unresolved
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_authcrit_artifact_unresolved]"⟩

-- row 13: artifact ref absent from store: chain unresolved
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_authcrit_artifact_unresolved]"⟩

-- row 14: artifact bytes noncanonical: chain unresolved
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "refs:d1|name:a"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_authcrit_artifact_unresolved]"⟩

-- row 15: genesis_ref absent from store: projection genesis unbound
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "ghost" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"pol0", "data:policy"⟩, ⟨"rc0", "data:receipt"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_projection_genesis_unbound]"⟩

-- row 16: genesis_ref names a successor (kind mismatch): genesis_not_root
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"pol0", "data:policy"⟩, ⟨"rc0", "data:receipt"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_projection_genesis_not_root]"⟩

-- row 17: genesis object carries a predecessor part: genesis_not_root
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "0fc8f55165b9d536e198246c25e502f46bd9be2eccf9ac49139f83fe42004069" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"0fc8f55165b9d536e198246c25e502f46bd9be2eccf9ac49139f83fe42004069", "artifact:ag|epoch:0|kind:genesis|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_projection_genesis_not_root]"⟩

-- row 18: successor entry at a non-derived digest: bound digest_mismatch
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"s1", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_bound_object_digest_mismatch]"⟩

-- row 19: successor entry collides at its digest: activation_unbound
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:sX"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_projection_activation_unbound]"⟩

-- row 20: successor entry noncanonical bytes (descending keys) at derived digest: bound noncanonical
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"c5d253b681f442abb5c6a855b7a2e9c09e43bb7fc00e3bbbcbef69e20bbcfaf9", "z:9|sequence:0|kind:successor|epoch:0"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_bound_object_noncanonical_bytes]"⟩

-- row 21: successor entry non-digital sequence: occurrence_shape
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"53972d421c8e00ac3b302e8a61ac857db491ebd5ac5fcbd769ca4f5d91282b68", "artifact:ax|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:one|statement:sx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_projection_occurrence_shape]"⟩

-- row 22: orphan activation (predecessor off-chain): orphan_activation
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"2b275b43daef574cbf319ad36920715f63e8f802793f9e0e68817928b8ffa1e7", "artifact:ao|epoch:0|kind:successor|predecessor:ghost|receipt:ro|sequence:1|statement:so"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_projection_orphan_activation]"⟩

-- row 23: fork at sequence 2 (two successors share a predecessor): projection_fork
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"002031852ab4256e83361480db0f812ba6df76fd06c32aecb6ec1c5adb2fd3fc", "artifact:a2b|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2b|sequence:2|statement:s2b"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_projection_fork]"⟩

-- row 24: open challenge targeting the tip: tip_blocked
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"7641d8c777351f639e766aab56e73620108f1493273d017ea52e1de27ec93171", "epoch:0|kind:challenge|sequence:3|status:open|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_projection_tip_blocked]"⟩

-- row 25: unresolved challenge targeting a non-tip occurrence: passes
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"b337531c4dc3c726b072928799ac29081eaa9b8be381cf84401268326bcaaffb", "epoch:0|kind:challenge|sequence:2|status:open|target:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨1, "art0", ["art0", "d1", "d2"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], ["a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "art0", "d1", "d2", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], ""⟩

-- row 26: challenge entry collides at its digest: challenge_unbound
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:pending|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_projection_challenge_unbound]"⟩

-- row 27: recovery entry collides at its digest: recovery_unbound
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:replay|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_projection_recovery_unbound]"⟩

-- row 28: recovery entry noncanonical bytes (descending keys) at derived digest: bound noncanonical
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"7e34c6c56c6710617db0d2c7c4b221bd938d6bb1581c7afabc2068008d5fbe8f", "z:9|kind:recovery"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_bound_object_noncanonical_bytes]"⟩

-- row 29: a second store recovery object is derived by the total scan (nothing presented can omit it)
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"7c02d3e2796d186543f571682d39157d2858ce9be962569b325901f06ce2efe0", "epoch:0|exercise:replay|kind:recovery|sequence:1|subject:s1"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨1, "art0", ["art0", "d1", "d2"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], ["a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "7c02d3e2796d186543f571682d39157d2858ce9be962569b325901f06ce2efe0"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "7c02d3e2796d186543f571682d39157d2858ce9be962569b325901f06ce2efe0", "a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "art0", "d1", "d2", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], ""⟩

-- row 30: duplicate sequence (candidate at tip coordinates): duplicate_sequence
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"8bda029358cf28c8ec6f8f9735ae279bad455a861687da4f5cd2acb7688487f1", "artifact:ad|epoch:0|kind:successor|predecessor:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87|receipt:rd|sequence:2|statement:sd"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_projection_duplicate_sequence]"⟩

-- row 31: back edge (candidate coordinates below tip): back_edge
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"171c12c3a83a7c91793e4dd7e7304016e973541859354f818c290811f4cb472f", "artifact:ab|epoch:0|kind:successor|predecessor:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87|receipt:rb|sequence:1|statement:sb"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_projection_back_edge]"⟩

-- row 32: future reference (candidate coordinates beyond next step): future_ref
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"d544aa8b57fed93fcab39cd99e21bbb0d15059739e4ff2528c4e65172bfd6768", "artifact:af|epoch:0|kind:successor|predecessor:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87|receipt:rf|sequence:9|statement:sf"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "", [], [], [], [], "[rcic_projection_future_ref]"⟩

-- row 33: reepoch successor (epoch+1, sequence 0) extends the chain
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"f91a1ed22325c299170f6c57b1c22ef565eeb3585916c3af6656261bfa1d7b90", "artifact:ae|epoch:1|kind:successor|predecessor:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87|receipt:re|sequence:0|statement:se"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨1, "art0", ["art0", "d1", "d2"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "f91a1ed22325c299170f6c57b1c22ef565eeb3585916c3af6656261bfa1d7b90"], ["a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "art0", "d1", "d2", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "f91a1ed22325c299170f6c57b1c22ef565eeb3585916c3af6656261bfa1d7b90"], ""⟩

-- row 34: activation member also reachable through artifact refs: dedup union
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨1, "art0", ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "art0", "d1"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], ["a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "art0", "d1", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], ""⟩

-- row 35: closure member digest absent from store: member unavailable
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "art0", ["art0", "d1", "d2"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], ["a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "art0", "d1", "d2", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], "[rcic_basis_ref_unavailable]"⟩

-- row 36: closure member digest-only: member unavailable
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", ""⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "art0", ["art0", "d1", "d2"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], ["a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "art0", "d1", "d2", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], "[rcic_basis_ref_unavailable]"⟩

-- row 37: closure member collides in store: member unavailable
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"d2", "data:other"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 8 == ⟨0, "art0", ["art0", "d1", "d2"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], ["a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "art0", "d1", "d2", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], "[rcic_basis_ref_unavailable]"⟩

-- row 38: projection fuel=2: inner walk refuses
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"pol0", "data:policy"⟩, ⟨"rc0", "data:receipt"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 2 == ⟨0, "", [], [], [], [], "[rcic_projection_fuel]"⟩

-- row 39: projection fits at fuel=3 but the 7-member availability budget does not: basis_fuel
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"pol0", "data:policy"⟩, ⟨"rc0", "data:receipt"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 3 == ⟨0, "art0", ["art0", "d1", "d2"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], ["a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "art0", "d1", "d2", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], "[rcic_basis_fuel]"⟩

-- row 40: refs_walk fuel=6: one short of the 7-member critical set
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"pol0", "data:policy"⟩, ⟨"rc0", "data:receipt"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 6 == ⟨0, "art0", ["art0", "d1", "d2"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], ["a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "art0", "d1", "d2", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], "[rcic_basis_fuel]"⟩

-- row 41: refs_walk fuel=7: availability budget exactly sufficient
#guard evalAuthorityCritical "active_authority_occurrence_ref:occ0|closure_basis_ref:cb0" "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a" [⟨"cb0", "data:basis"⟩, ⟨"occ0", "receipt_ref:rc0|statement_ref:st0"⟩, ⟨"st0", "authority_policy_ref:pol0|candidate_authority_artifact_ref:art0"⟩, ⟨"art0", "name:active-artifact|refs:d1,d2"⟩, ⟨"d1", "data:x"⟩, ⟨"d2", "data:y"⟩, ⟨"pol0", "data:policy"⟩, ⟨"rc0", "data:receipt"⟩, ⟨"f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a", "artifact:ag|epoch:0|kind:genesis|receipt:rgx|sequence:0|statement:sgx"⟩, ⟨"da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "artifact:a1|epoch:0|kind:successor|predecessor:f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a|receipt:r1|sequence:1|statement:s1"⟩, ⟨"12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "artifact:a2|epoch:0|kind:successor|predecessor:da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0|receipt:r2|sequence:2|statement:s2"⟩, ⟨"a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "epoch:0|exercise:debruijn|kind:recovery|sequence:2|subject:s2"⟩, ⟨"505ddd7068a31797619ee5d6cbecbb432bedfa6a5c08592d0ff4908c9d43f30d", "epoch:0|kind:challenge|sequence:2|status:resolved|target:12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87"⟩, ⟨"2148038f3d59857655b4b3658992249f16b8204629b55240c84f42b61c4e5d9c", "epoch:0|kind:integrity|sequence:9|target:occ0"⟩] 7 == ⟨1, "art0", ["art0", "d1", "d2"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], ["a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d"], ["12da37fb86bd9f44e8abf7c4017164899c3fa2dbda2d4ee01de1ee4515f87f87", "a5246fa6ec3693abb6712f61e4a698982cb0279875d1dfc428be41bf8d638d4d", "art0", "d1", "d2", "da86078decce505daabb304b886c1a7a86aca6d55f6e1d3b70c97bb17cbc6db0", "f7e8cbeaf1f5ed48b2f2a0d63643ab29565a7e170d86c86cc52de9b2f4d07a4a"], ""⟩

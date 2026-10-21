/-
RCIC 00 §12 — `openResidues` as the canonical deduplicated union of
STORE-DERIVED sources, minus Annex 26.1/26.15 resolution suppression, the
pinned Lean model of `apps/rcic-open-residues`
(`rcic.open_residues fuel store`).

The carrier decides the DATA half of `openResidues c` over the one content
store: integrity-residue digests by the `kind:integrity` part scan
(`rcic.auth_reservation_kind_refs`), HOLD digests by the
`rcic.hold_scope`-admitted `defect`/`grade` occurrence scan, accepted
challenge digests by the `rcic.challenge_record` scan, accepted
resolutions by the `kind:challenge_resolution` scan judged through
`rcic.challenge_resolution` (the Annex 26.1 carrier, #6406 — model in
`rcic.RcicChallengeResolutionModel`), and accepted permanent residues by
the `kind:permanent_residue` scan judged through `rcic.permanent_residue`
(the Annex 26.15 carrier, #6466 — model in
`rcic.RcicPermanentResidueModel`). The caller presents no set objects and
no status fields: a `resolves:<digest>` part, a `status:resolved` part, or a
bare validated receipt is never a resolution and never suppresses.

Subtraction fails closed: exactly one accepted resolution hit with
`decision = validated` and `disposition ∈ {revalidated, transported}` moves
a challenge to `resolved_challenges`; under Annex 26.15 a `retired` hit
suppresses ONLY when exactly one accepted permanent residue is minted by
that resolution's occurrence; `refuted` and `reopened` hits leave the
challenge open (§10); two or more hits COMPETE and leave it open with the
competing occurrence digests reported. Accepted permanent-residue digests
join the union and are never subtracted. `policySelects` stays absent —
`BlockingResidueProjection` is not decided here and nothing concludes it is
empty. `NativeRCICClosed` has no theorem; `closure_claim` stays 0.

PIN (M-002): all 49 rows of
`apps/rcic-open-residues/rcic_open_residues_corpus.json` below; the
record-level statement `openUnion'` holds on every produced record
(M-002a).

TRANSCRIPTION TABLE (the scm modules → Lean):
  rcic.canon_bytes_ok                 → `Rcic.BoundObject.canonBytesOk` (reused)
  rcic.auth_activation_part_at        → `Rcic.Scm.Embed.partAt` (reused)
  rcic.closure_basis_keys_ok          → `Rcic.ScopeExact.keysOk` (reused)
  rcic.residue_rows_canon             → `Rcic.ScopeExact.listCanon` (reused)
  rcic.residue_rows_member            → `List.contains`
  rcic.challenge_record (form 0)      → `Rcic.ChallengeResolution.challengeAccepted`
  rcic.challenge_resolution           → `Rcic.ChallengeResolution.evalChallengeResolution`
  rcic.challenge_resolution_suppressing → `Rcic.ChallengeResolution.resolSuppressing`
  rcic.value_at_digits_ok             → `valueAtDigitsOk`
  rcic.hold_scope (form 0 → derive)   → `holdScopeAdmit` (the `ok = 1` bit)
  rcic.auth_reservation_kind_refs     → `Rcic.AuthorityCritical.kindRefs`
                                        (`integrityScan` for the integrity arm)
  rcic.open_residues_challenge_scan   → `challengeScan`
  rcic.open_residues_resolution_scan  → `resolutionScan`
  rcic.open_residues_permanent_scan   → `permanentScan`
  rcic.permanent_residue              → `Rcic.PermanentResidue.evalPermanentResidue`
  rcic.permanent_residue_minted_count → `Rcic.PermanentResidue.mintedCount`
  rcic.open_residues_challenge_hits   → `challengeHits`
  rcic.open_residues_subtract         → `subtract`
  rcic.open_residues_hold_scan        → `holdScan`
  rcic.open_residues_refuse           → `refuseOut`
  rcic.open_residues                  → `evalOpenResidues`
-/
import rcic.RcicPermanentResidueModel

namespace Rcic.OpenResidues

open Rcic.BoundObject (StoreEntry)
open Rcic.Scm.Embed (partAt)
open Rcic.ScopeExact (keysOk listCanon)
open Rcic.AuthorityCritical (kindRefs)
open Rcic.ChallengeResolution (challengeAccepted evalChallengeResolution
  resolSuppressing CROut)
open Rcic.PermanentResidue (PROut evalPermanentResidue mintedCount)

/-- Re-export of `Rcic.ChallengeResolution.challengeKeys`: the definition
    moved with Annex 26.1; this name stays for the seal's append-only list. -/
abbrev challengeKeys : List String :=
  Rcic.ChallengeResolution.challengeKeys

/-- Re-export of `Rcic.ChallengeResolution.challengeClasses`. -/
abbrev challengeClasses : List String :=
  Rcic.ChallengeResolution.challengeClasses

/-- Re-export of `Rcic.ChallengeResolution.challengeClassOk`. -/
abbrev challengeClassOk (c : String) : Bool :=
  Rcic.ChallengeResolution.challengeClassOk c

/-- Re-export of `Rcic.ChallengeResolution.challengeLabelHit`. -/
abbrev challengeLabelHit (ev : String) : Bool :=
  Rcic.ChallengeResolution.challengeLabelHit ev

/-- Re-export of `Rcic.ChallengeResolution.challengeAccepted`. -/
abbrev challengeAccepted (fuel : Int) (bytes : String) : Bool :=
  Rcic.ChallengeResolution.challengeAccepted fuel bytes

/-! ## The scm modules, mirrored -/

/-- `rcic.value_at_digits_ok`: nonempty and every char a decimal digit. -/
def valueAtDigitsOk (s : String) : Bool :=
  s.length > 0 && s.all (fun c => decide ('0' ≤ c ∧ c ≤ '9'))

/-- `rcic.hold_scope` form 0 → `hold_scope_derive`, the `ok = 1` bit:
    `defect_class ∈ [0, 4]` and `coverage_grade ∈ [0, 2]` (the shared hold
    table; out-of-table pairs refuse). `fuel` is passed through by the scm
    but is not read by `hold_scope_derive`. -/
def holdScopeAdmit (defect coverage : Int) : Bool :=
  decide (0 ≤ defect ∧ defect ≤ 4 ∧ 0 ≤ coverage ∧ coverage ≤ 2)

/-- `rcic.open_residues_hold_scan`'s per-entry predicate: both `defect:`
    and `grade:` parts present as digit strings, and the pair admitted by
    `hold_scope`. -/
def holdEntryOk (bytes : String) : Bool :=
  let d := partAt bytes "defect"
  let g := partAt bytes "grade"
  d != "" && g != "" && valueAtDigitsOk d && valueAtDigitsOk g &&
    holdScopeAdmit d.toNat! g.toNat!

/-- The shared scan shape of the source derivations: fold the store in
    order, appending each admitted entry's digest. -/
def scanWhere (p : StoreEntry → Bool) (store : List StoreEntry) : List String :=
  store.foldl (fun acc e => if p e then acc ++ [e.digest] else acc) []

/-- `rcic.auth_reservation_kind_refs store "integrity"`. -/
def integrityScan (store : List StoreEntry) : List String :=
  scanWhere (fun e => decide (partAt e.bytes "kind" = "integrity")) store

/-- `rcic.open_residues_challenge_scan`: digests of `challenge_record`-
    accepted entries (the pre-subtraction accepted list). -/
def challengeScan (store : List StoreEntry) (fuel : Int) : List String :=
  scanWhere (fun e => challengeAccepted fuel e.bytes) store

/-- `rcic.open_residues_hold_scan`: digests of `hold_scope`-admitted
    `defect`/`grade` occurrences. -/
def holdScan (store : List StoreEntry) (_fuel : Int) : List String :=
  scanWhere (fun e => holdEntryOk e.bytes) store

/-- `rcic.open_residues_resolution_scan`: every `kind:challenge_resolution`
    store digest judged through `rcic.challenge_resolution`; accepted
    records are kept (malformed/unbound occurrences fall out and never
    reach the subtraction arm). -/
def resolutionScan (store : List StoreEntry) (fuel : Int) : List CROut :=
  (kindRefs store "challenge_resolution").foldl (fun acc d =>
    let r := evalChallengeResolution fuel store d
    if r.ok = 1 then acc ++ [r] else acc) []

/-- `rcic.open_residues_permanent_scan`: every `kind:permanent_residue`
    store digest judged through `rcic.permanent_residue`; accepted
    records are kept (unbound/colliding/malformed residues fall out and
    never reach the union or the suppression arm). -/
def permanentScan (store : List StoreEntry) (fuel : Int) : List PROut :=
  (kindRefs store "permanent_residue").foldl (fun acc d =>
    let r := evalPermanentResidue fuel store d
    if r.ok = 1 then acc ++ [r] else acc) []

/-- `rcic.open_residues_challenge_hits`'s output
    `{n, occs, suppresses}`: accepted resolutions naming `challengeRef`.
    `suppresses` is set by any hit with `decision = validated` and either
    a suppressing disposition or — Annex 26.15 — `disposition = retired`
    with exactly one accepted permanent residue minted by that hit's
    occurrence. -/
structure Hits where
  n : Int
  occs : List String
  suppresses : Bool
  deriving BEq

/-- `rcic.open_residues_challenge_hits`'s fold step: a resolution naming
    the challenge bumps `n`, records its `occ`, and sets `suppresses` when
    it is `validated` with a suppressing disposition or `retired` with
    `mintedCount perms r.occ = 1`. -/
def hitstep (challengeRef : String) (perms : List PROut) (acc : Hits)
    (r : CROut) : Hits :=
  if r.challengeRef = challengeRef then
    ⟨acc.n + 1, acc.occs ++ [r.occ],
     acc.suppresses ||
       (r.decision = "validated" &&
        (resolSuppressing r.disposition ||
         (r.disposition = "retired" && mintedCount perms r.occ = 1)))⟩
  else acc

def challengeHits (challengeRef : String) (resolutions : List CROut)
    (perms : List PROut) : Hits :=
  resolutions.foldl (hitstep challengeRef perms) ⟨0, [], false⟩

/-- `rcic.open_residues_subtract`'s output `{open, resolved, competing}`. -/
structure SubOut where
  openList : List String
  resolved : List String
  competing : List String
  deriving BEq

/-- `rcic.open_residues_subtract`'s fold step: zero hits → open; one hit →
    open unless it is `validated` with a suppressing disposition or
    `retired` with exactly one minted residue (then resolved); two or more
    hits → open, all hit occurrences reported as competing (fail closed). -/
def substep (resolutions : List CROut) (perms : List PROut) (acc : SubOut)
    (c : String) : SubOut :=
  let hits := challengeHits c resolutions perms
  if hits.n = 0 then
    ⟨acc.openList ++ [c], acc.resolved, acc.competing⟩
  else if hits.n = 1 then
    if hits.suppresses then
      ⟨acc.openList, acc.resolved ++ [c], acc.competing⟩
    else ⟨acc.openList ++ [c], acc.resolved, acc.competing⟩
  else
    ⟨acc.openList ++ [c], acc.resolved, acc.competing ++ hits.occs⟩

/-- `rcic.open_residues_subtract`. -/
def subtract (challenges : List String) (resolutions : List CROut)
    (perms : List PROut) : SubOut :=
  challenges.foldl (substep resolutions perms) ⟨[], [], []⟩

/-- `rcic.open_residues`'s sigma `{ok, integrity, open_challenges,
    resolved_challenges, competing_resolutions, resolutions, holds,
    permanent_residues, open_residues, code}`. -/
structure OROut where
  ok : Int
  integrity : List String
  openChallenges : List String
  resolvedChallenges : List String
  competingResolutions : List String
  resolutions : List String
  holds : List String
  permanentResidues : List String
  openResidues : List String
  code : String
  deriving BEq

/-- `rcic.open_residues_refuse`. -/
def refuseOut (code : String) : OROut := ⟨0, [], [], [], [], [], [], [], [], code⟩

/-- `rcic.open_residues`: the fuel gate, then the five store-derived
    sources, the subtraction, and the canonical deduplicated union
    `integrity ++ open ++ holds ++ permanent_residues`. -/
def evalOpenResidues (fuel : Int) (store : List StoreEntry) : OROut :=
  if fuel < 0 then refuseOut "[rcic_openres_fuel]"
  else
    let im := integrityScan store
    let co := challengeScan store fuel
    let hm := holdScan store fuel
    let rs := resolutionScan store fuel
    let pm := permanentScan store fuel
    let sub := subtract co rs pm
    ⟨1, im, sub.openList, listCanon sub.resolved, listCanon sub.competing,
     listCanon (rs.map CROut.occ), hm, listCanon (pm.map PROut.digest),
     listCanon (im ++ sub.openList ++ hm ++ pm.map PROut.digest), ""⟩

/-! ## Record-level statements -/

/-- The produced `open_residues` is exactly the canonical (sorted,
    deduplicated) union of the produced `integrity`, `open_challenges`,
    `holds`, and `permanent_residues` lists. `evalOpenResidues` maintains
    this on BOTH branches: the success record sets it directly, and
    `refuseOut` gives `listCanon ([] ++ [] ++ [] ++ []) = []`. -/
def openUnion' (o : OROut) : Prop :=
  o.openResidues =
    listCanon (o.integrity ++ o.openChallenges ++ o.holds ++ o.permanentResidues)

theorem openUnion_refuse (code : String) : openUnion' (refuseOut code) := rfl

theorem openUnion_success (ok : Int) (im co rs rp res hm pm : List String)
    (code : String) :
    openUnion' ⟨ok, im, co, rs, rp, res, hm, pm,
                  listCanon (im ++ co ++ hm ++ pm), code⟩ := rfl

/-- Negative fuel refuses with the only refusal code. -/
theorem evalOpenResidues_fuel (fuel : Int) (store : List StoreEntry)
    (h : fuel < 0) :
    evalOpenResidues fuel store = refuseOut "[rcic_openres_fuel]" := by
  unfold evalOpenResidues; rw [if_pos h]

/-- Scan membership: a digest produced by the fold is either already in
    the accumulator or witnessed by some store entry carrying it that
    satisfies `p`. -/
theorem mem_scanWhere (p : StoreEntry → Bool) :
    ∀ (store : List StoreEntry) (acc : List String) (d : String),
      d ∈ List.foldl (fun a e => if p e then a ++ [e.digest] else a) acc store →
        d ∈ acc ∨ ∃ e ∈ store, e.digest = d ∧ p e = true := by
  intro store
  induction store with
  | nil => intro acc d h; exact Or.inl h
  | cons e es ih =>
      intro acc d h
      rw [List.foldl_cons] at h
      by_cases hp : p e = true
      · rw [if_pos hp] at h
        obtain h' := ih _ _ h
        cases h' with
        | inl hmem =>
            rw [List.mem_append] at hmem
            cases hmem with
            | inl ha => exact Or.inl ha
            | inr hd =>
                exact Or.inr ⟨e, List.mem_cons_self _ _,
                              (List.mem_singleton.1 hd).symm, hp⟩
        | inr h =>
            obtain ⟨e', he', hd', hp'⟩ := h
            exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hd', hp'⟩
      · rw [if_neg hp] at h
        obtain h' := ih _ _ h
        cases h' with
        | inl hmem => exact Or.inl hmem
        | inr h =>
            obtain ⟨e', he', hd', hp'⟩ := h
            exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hd', hp'⟩

/-- One `substep` keeps `open` inside `acc.openList ∪ {c}` — the step can only
    copy the current challenge in or leave the accumulator alone. -/
theorem substep_open_mem (rs : List CROut) (perms : List PROut) (acc : SubOut)
    (c d : String) :
    d ∈ (substep rs perms acc c).openList → d ∈ acc.openList ∨ d = c := by
  unfold substep
  simp only []
  intro h
  split at h
  · cases List.mem_append.1 h with
    | inl ha => exact Or.inl ha
    | inr hs => exact Or.inr (List.mem_singleton.1 hs)
  · split at h
    · split at h
      · exact Or.inl h
      · cases List.mem_append.1 h with
        | inl ha => exact Or.inl ha
        | inr hs => exact Or.inr (List.mem_singleton.1 hs)
    · cases List.mem_append.1 h with
      | inl ha => exact Or.inl ha
      | inr hs => exact Or.inr (List.mem_singleton.1 hs)

/-- The whole `subtract` fold keeps `openList` inside `acc.openList ∪ challenges`
    — subtraction only removes from the accepted scan, it never invents a
    challenge digest. -/
theorem mem_subtract_open (rs : List CROut) (perms : List PROut) :
    ∀ (cs : List String) (acc : SubOut) (d : String),
      d ∈ (cs.foldl (substep rs perms) acc).openList →
        d ∈ acc.openList ∨ d ∈ cs := by
  intro cs
  induction cs with
  | nil => intro acc d h; exact Or.inl h
  | cons c cs ih =>
      intro acc d h
      rw [List.foldl_cons] at h
      obtain h' := ih _ _ h
      cases h' with
      | inl hs =>
          cases substep_open_mem rs perms acc c d hs with
          | inl ha => exact Or.inl ha
          | inr hc => exact Or.inr (hc ▸ List.mem_cons_self _ _)
      | inr hm => exact Or.inr (List.mem_cons_of_mem _ hm)

/-- A digest in `open_challenges` is a digest of the accepted challenge
    scan — a `challenge_record`-accepted store entry. -/
theorem subtract_open_mem (cs : List String) (rs : List CROut)
    (perms : List PROut) (d : String) :
    d ∈ (subtract cs rs perms).openList → d ∈ cs :=
  fun h =>
    (mem_subtract_open rs perms cs ⟨[], [], []⟩ d h).resolve_left (by simp)

/-- One `substep` keeps `resolved` inside `acc.resolved ∪ {c}` — only a
    single validated suppressing hit can move a challenge there. -/
theorem substep_resolved_mem (rs : List CROut) (perms : List PROut)
    (acc : SubOut) (c d : String) :
    d ∈ (substep rs perms acc c).resolved → d ∈ acc.resolved ∨ d = c := by
  unfold substep
  simp only []
  intro h
  split at h
  · exact Or.inl h
  · split at h
    · split at h
      · cases List.mem_append.1 h with
        | inl ha => exact Or.inl ha
        | inr hs => exact Or.inr (List.mem_singleton.1 hs)
      · exact Or.inl h
    · exact Or.inl h

theorem mem_subtract_resolved (rs : List CROut) (perms : List PROut) :
    ∀ (cs : List String) (acc : SubOut) (d : String),
      d ∈ (cs.foldl (substep rs perms) acc).resolved →
        d ∈ acc.resolved ∨ d ∈ cs := by
  intro cs
  induction cs with
  | nil => intro acc d h; exact Or.inl h
  | cons c cs ih =>
      intro acc d h
      rw [List.foldl_cons] at h
      obtain h' := ih _ _ h
      cases h' with
      | inl hs =>
          cases substep_resolved_mem rs perms acc c d hs with
          | inl ha => exact Or.inl ha
          | inr hc => exact Or.inr (hc ▸ List.mem_cons_self _ _)
      | inr hm => exact Or.inr (List.mem_cons_of_mem _ hm)

/-- A digest in `resolved_challenges` is a digest of the accepted
    challenge scan — resolution never manufactures a new challenge. -/
theorem subtract_resolved_mem (cs : List String) (rs : List CROut)
    (perms : List PROut) (d : String) :
    d ∈ (subtract cs rs perms).resolved → d ∈ cs :=
  fun h =>
    (mem_subtract_resolved rs perms cs ⟨[], [], []⟩ d h).resolve_left (by simp)

/-- One `substep` keeps `competing` inside `acc.competing` plus the hit
    occurrences of the current challenge. -/
theorem substep_competing_mem (rs : List CROut) (perms : List PROut)
    (acc : SubOut) (c d : String) :
    d ∈ (substep rs perms acc c).competing →
      d ∈ acc.competing ∨ d ∈ (challengeHits c rs perms).occs := by
  unfold substep
  simp only []
  intro h
  split at h
  · exact Or.inl h
  · split at h
    · split at h
      · exact Or.inl h
      · exact Or.inl h
    · cases List.mem_append.1 h with
      | inl ha => exact Or.inl ha
      | inr hs => exact Or.inr hs

theorem mem_subtract_competing (rs : List CROut) (perms : List PROut) :
    ∀ (cs : List String) (acc : SubOut) (d : String),
      d ∈ (cs.foldl (substep rs perms) acc).competing →
        d ∈ acc.competing ∨ ∃ c ∈ cs, d ∈ (challengeHits c rs perms).occs := by
  intro cs
  induction cs with
  | nil => intro acc d h; exact Or.inl h
  | cons c cs ih =>
      intro acc d h
      rw [List.foldl_cons] at h
      obtain h' := ih _ _ h
      cases h' with
      | inl hs =>
          cases substep_competing_mem rs perms acc c d hs with
          | inl ha => exact Or.inl ha
          | inr hocc => exact Or.inr ⟨c, List.mem_cons_self _ _, hocc⟩
      | inr hm =>
          obtain ⟨c', hc', hocc⟩ := hm
          exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', hocc⟩

/-- A digest in `competing_resolutions` is an occurrence of some accepted
    challenge's resolution hits — competition reports real occurrences,
    nothing else. -/
theorem subtract_competing_mem (cs : List String) (rs : List CROut)
    (perms : List PROut) (d : String) :
    d ∈ (subtract cs rs perms).competing →
      ∃ c ∈ cs, d ∈ (challengeHits c rs perms).occs :=
  fun h =>
    (mem_subtract_competing rs perms cs ⟨[], [], []⟩ d h).resolve_left (by simp)

/-- One `hitstep` keeps `occs` inside `acc.occs` plus the hit record's
    `occ`. -/
theorem hitstep_occs_mem (c : String) (perms : List PROut) (acc : Hits)
    (r : CROut) (d : String) :
    d ∈ (hitstep c perms acc r).occs →
      d ∈ acc.occs ∨ (r.occ = d ∧ r.challengeRef = c) := by
  unfold hitstep
  intro h
  split at h
  · cases List.mem_append.1 h with
    | inl ha => exact Or.inl ha
    | inr hs =>
        rename_i hcr
        exact Or.inr ⟨(List.mem_singleton.1 hs).symm, hcr⟩
  · exact Or.inl h

theorem mem_challengeHits_occs (c : String) (perms : List PROut) :
    ∀ (rs : List CROut) (acc : Hits) (d : String),
      d ∈ (rs.foldl (hitstep c perms) acc).occs →
        d ∈ acc.occs ∨ ∃ r ∈ rs, r.occ = d ∧ r.challengeRef = c := by
  intro rs
  induction rs with
  | nil => intro acc d h; exact Or.inl h
  | cons r rs ih =>
      intro acc d h
      rw [List.foldl_cons] at h
      obtain h' := ih _ _ h
      cases h' with
      | inl hs =>
          cases hitstep_occs_mem c perms acc r d hs with
          | inl ha => exact Or.inl ha
          | inr hrr => exact Or.inr ⟨r, List.mem_cons_self _ _, hrr.1, hrr.2⟩
      | inr hm =>
          obtain ⟨r', hr', ho, hc⟩ := hm
          exact Or.inr ⟨r', List.mem_cons_of_mem _ hr', ho, hc⟩

/-- Every member of a challenge's hit occurrences is the `occ` field of a
    resolution record in `rs` naming that challenge — hits are witnessed
    resolutions, never presented digests. -/
theorem challengeHits_occs_mem (c : String) (rs : List CROut)
    (perms : List PROut) (d : String) :
    d ∈ (challengeHits c rs perms).occs →
      ∃ r ∈ rs, r.occ = d ∧ r.challengeRef = c :=
  fun h =>
    (mem_challengeHits_occs c perms rs ⟨0, [], false⟩ d h).resolve_left
      (by simp)

/-- Fold-membership for the resolution scan: a record in the produced list
    is either already in the accumulator or witnessed by a scanned digest
    whose judge accepts with exactly that record. -/
theorem mem_resolutionScan (fuel : Int) (store : List StoreEntry) :
    ∀ (ds : List String) (acc : List CROut) (r : CROut),
      r ∈ ds.foldl (fun a d =>
          let v := evalChallengeResolution fuel store d
          if v.ok = 1 then a ++ [v] else a) acc →
        r ∈ acc ∨ ∃ d ∈ ds,
          r.ok = 1 ∧ evalChallengeResolution fuel store d = r := by
  intro ds
  induction ds with
  | nil => intro acc r h; exact Or.inl h
  | cons d ds ih =>
      intro acc r h
      rw [List.foldl_cons] at h
      obtain h' := ih _ _ h
      cases h' with
      | inl hs =>
          dsimp only at hs
          by_cases hv : (evalChallengeResolution fuel store d).ok = 1
          · rw [if_pos hv] at hs
            cases List.mem_append.1 hs with
            | inl ha => exact Or.inl ha
            | inr hr =>
                have he : evalChallengeResolution fuel store d = r :=
                  (List.mem_singleton.1 hr).symm
                exact Or.inr ⟨d, List.mem_cons_self _ _, he ▸ hv, he⟩
          · rw [if_neg hv] at hs; exact Or.inl hs
      | inr hm =>
          obtain ⟨d', hd', hok, he⟩ := hm
          exact Or.inr ⟨d', List.mem_cons_of_mem _ hd', hok, he⟩

/-- A record in `resolutions` is witnessed by a
    `kind:challenge_resolution` store digest the carrier judge accepts —
    resolutions are derived, never presented. -/
theorem resolutionScan_mem (store : List StoreEntry) (fuel : Int) (r : CROut) :
    r ∈ resolutionScan store fuel →
      ∃ d ∈ kindRefs store "challenge_resolution",
        r.ok = 1 ∧ evalChallengeResolution fuel store d = r :=
  fun h => (mem_resolutionScan fuel store _ [] r h).resolve_left (by simp)

/-- Fold-membership for the permanent scan: a record in the produced list
    is either already in the accumulator or witnessed by a scanned digest
    whose judge accepts with exactly that record. -/
theorem mem_permanentScan (fuel : Int) (store : List StoreEntry) :
    ∀ (ds : List String) (acc : List PROut) (p : PROut),
      p ∈ ds.foldl (fun a d =>
          let v := evalPermanentResidue fuel store d
          if v.ok = 1 then a ++ [v] else a) acc →
        p ∈ acc ∨ ∃ d ∈ ds,
          p.ok = 1 ∧ evalPermanentResidue fuel store d = p := by
  intro ds
  induction ds with
  | nil => intro acc p h; exact Or.inl h
  | cons d ds ih =>
      intro acc p h
      rw [List.foldl_cons] at h
      obtain h' := ih _ _ h
      cases h' with
      | inl hs =>
          dsimp only at hs
          by_cases hv : (evalPermanentResidue fuel store d).ok = 1
          · rw [if_pos hv] at hs
            cases List.mem_append.1 hs with
            | inl ha => exact Or.inl ha
            | inr hr =>
                have he : evalPermanentResidue fuel store d = p :=
                  (List.mem_singleton.1 hr).symm
                exact Or.inr ⟨d, List.mem_cons_self _ _, he ▸ hv, he⟩
          · rw [if_neg hv] at hs; exact Or.inl hs
      | inr hm =>
          obtain ⟨d', hd', hok, he⟩ := hm
          exact Or.inr ⟨d', List.mem_cons_of_mem _ hd', hok, he⟩

/-- A record in `permanent_residues` is witnessed by a
    `kind:permanent_residue` store digest the carrier judge accepts —
    residues are derived, never presented. -/
theorem permanentScan_mem (store : List StoreEntry) (fuel : Int) (p : PROut) :
    p ∈ permanentScan store fuel →
      ∃ d ∈ kindRefs store "permanent_residue",
        p.ok = 1 ∧ evalPermanentResidue fuel store d = p :=
  fun h => (mem_permanentScan fuel store _ [] p h).resolve_left (by simp)

/-- A digest in `holds` is witnessed by a `hold_scope`-admitted
    `defect`/`grade` occurrence in the store. -/
theorem holdScan_mem (store : List StoreEntry) (fuel : Int) (d : String) :
    d ∈ holdScan store fuel →
      ∃ e ∈ store, e.digest = d ∧ holdEntryOk e.bytes = true :=
  fun h => (mem_scanWhere _ store [] d h).resolve_left (by simp)

/-- A digest in the accepted challenge scan is witnessed by a
    `challenge_record`-accepted store entry — and every member of
    `open_challenges` is such a digest (subtraction only removes). -/
theorem challengeScan_mem (store : List StoreEntry) (fuel : Int) (d : String) :
    d ∈ challengeScan store fuel →
      ∃ e ∈ store, e.digest = d ∧ challengeAccepted fuel e.bytes = true :=
  fun h => (mem_scanWhere _ store [] d h).resolve_left (by simp)

/-- A digest in `integrity` is witnessed by a `kind:integrity` store
    entry. -/
theorem integrityScan_mem (store : List StoreEntry) (d : String) :
    d ∈ integrityScan store →
      ∃ e ∈ store, e.digest = d ∧ partAt e.bytes "kind" = "integrity" :=
  fun h =>
    let ⟨e, he, hd, hp⟩ := (mem_scanWhere _ store [] d h).resolve_left (by simp)
    ⟨e, he, hd, of_decide_eq_true hp⟩

/-- Presented-evidence fail-closed: an entry whose `|`-part count differs
    from the five challenge keys is never `challenge_record`-accepted — a
    `resolves:<digest>` or `status:resolved` part cannot form a challenge
    record and cannot suppress anything (suppression needs a
    `kind:challenge_resolution` occurrence the carrier accepts). -/
theorem not_accepted_of_part_count (fuel : Int) (bytes : String)
    (h : (bytes.splitOn "|").length ≠
           ChallengeResolution.challengeKeys.length) :
    challengeAccepted fuel bytes = false :=
  ChallengeResolution.not_accepted_of_part_count fuel bytes h

#guard challengeAccepted 100 "resolves:c1" == false

/-! ## Corpus pins: all 49 rows of
    `apps/rcic-open-residues/rcic_open_residues_corpus.json`.
    The model is pinned to the carrier's full produced record per row (M-002). -/

-- row 0: three derived sources union; scan order kept, union canonical
#guard evalOpenResidues (100) [⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b2|evidence_bytes:proof|evidence_class:deterministic_divergence|reproducer_ref:r2|target_ref:t2"⟩, ⟨"h1", "defect:2|epoch:1|grade:1|kind:challenge|sequence:3|status:open|target:t9"⟩, ⟨"i1", "kind:integrity|note:fault"⟩, ⟨"x1", "body:x|kind:exact"⟩] == ⟨1, ["i1"], ["c1", "c2"], [], [], [], ["h1"], [], ["c1", "c2", "h1", "i1"], ""⟩

-- row 1: empty store derives empty
#guard evalOpenResidues (100) [] == ⟨1, [], [], [], [], [], [], [], [], ""⟩

-- row 2: negative fuel refuses
#guard evalOpenResidues (-1) [⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r1|target_ref:t1"⟩] == ⟨0, [], [], [], [], [], [], [], [], "[rcic_openres_fuel]"⟩

-- row 3: label token in evidence_bytes is not an accepted challenge
#guard evalOpenResidues (100) [⟨"c1", "basis_ref:b1|evidence_bytes:label,proof|evidence_class:counterexample_refutation|reproducer_ref:r1|target_ref:t1"⟩] == ⟨1, [], [], [], [], [], [], [], [], ""⟩

-- row 4: unknown evidence_class is not an accepted challenge
#guard evalOpenResidues (100) [⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:nonsense|reproducer_ref:r1|target_ref:t1"⟩] == ⟨1, [], [], [], [], [], [], [], [], ""⟩

-- row 5: missing target_ref is not an accepted challenge
#guard evalOpenResidues (100) [⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r1"⟩] == ⟨1, [], [], [], [], [], [], [], [], ""⟩

-- row 6: status:resolved part makes the record unaccepted (presented flag cannot form)
#guard evalOpenResidues (100) [⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r1|target_ref:t1|status:resolved"⟩] == ⟨1, [], [], [], [], [], [], [], [], ""⟩

-- row 7: duplicate key challenge bytes noncanonical, not accepted
#guard evalOpenResidues (100) [⟨"c1", "basis_ref:b1|basis_ref:b2|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r1|target_ref:t1"⟩] == ⟨1, [], [], [], [], [], [], [], [], ""⟩

-- row 8: digest-only entry (empty bytes) is in no source
#guard evalOpenResidues (100) [⟨"d0", ""⟩] == ⟨1, [], [], [], [], [], [], [], [], ""⟩

-- row 9: kind:integrity counted
#guard evalOpenResidues (100) [⟨"i1", "kind:integrity|note:fault"⟩] == ⟨1, ["i1"], [], [], [], [], [], [], ["i1"], ""⟩

-- row 10: kind:integrity with colonless trailing part still counted
#guard evalOpenResidues (100) [⟨"i9", "kind:integrity|JUNK"⟩] == ⟨1, ["i9"], [], [], [], [], [], [], ["i9"], ""⟩

-- row 11: kind:challenge defect:2 grade:1 is a hold
#guard evalOpenResidues (100) [⟨"h1", "defect:2|epoch:1|grade:1|kind:challenge|sequence:3|status:open|target:t9"⟩] == ⟨1, [], [], [], [], [], ["h1"], [], ["h1"], ""⟩

-- row 12: defect:9 unknown defect is not a hold
#guard evalOpenResidues (100) [⟨"h1", "defect:9|epoch:1|grade:0|kind:challenge|sequence:3|status:open|target:t9"⟩] == ⟨1, [], [], [], [], [], [], [], [], ""⟩

-- row 13: grade:3 unknown grade is not a hold
#guard evalOpenResidues (100) [⟨"h1", "defect:0|epoch:1|grade:3|kind:challenge|sequence:3|status:open|target:t9"⟩] == ⟨1, [], [], [], [], [], [], [], [], ""⟩

-- row 14: grade part absent is not a hold
#guard evalOpenResidues (100) [⟨"h1", "defect:2|epoch:1|kind:challenge|sequence:3|status:open|target:t9"⟩] == ⟨1, [], [], [], [], [], [], [], [], ""⟩

-- row 15: non-digit defect is not a hold
#guard evalOpenResidues (100) [⟨"h1", "defect:ab|epoch:1|grade:0|kind:challenge|sequence:3|status:open|target:t9"⟩] == ⟨1, [], [], [], [], [], [], [], [], ""⟩

-- row 16: defect+grade on kind:genesis counts as a hold (no kind gate)
#guard evalOpenResidues (100) [⟨"g0", "artifact:ag|defect:0|epoch:0|grade:0|kind:genesis|receipt:rg|sequence:0|statement:sg"⟩] == ⟨1, [], [], [], [], [], ["g0"], [], ["g0"], ""⟩

-- row 17: defect+grade without kind counts as a hold
#guard evalOpenResidues (100) [⟨"h1", "defect:1|grade:2|target:t9"⟩] == ⟨1, [], [], [], [], [], ["h1"], [], ["h1"], ""⟩

-- row 18: presented resolves: token does not resolve (BLOCKED-OBJECT)
#guard evalOpenResidues (100) [⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r1|target_ref:t1"⟩, ⟨"r1", "resolves:c1"⟩] == ⟨1, [], ["c1"], [], [], [], [], [], ["c1"], ""⟩

-- row 19: validated receipt is not a resolution occurrence
#guard evalOpenResidues (100) [⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r1|target_ref:t1"⟩, ⟨"rc1", "challenge_ref:c1|decision:validated|validator_occ_ref:v1"⟩, ⟨"v1", "artifact:av1|epoch:1|kind:successor|predecessor:g0|receipt:rv1|sequence:1|statement:sv1"⟩] == ⟨1, [], ["c1"], [], [], [], [], [], ["c1"], ""⟩

-- row 20: resolves token naming an absent challenge changes nothing
#guard evalOpenResidues (100) [⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r1|target_ref:t1"⟩, ⟨"r1", "resolves:cX"⟩] == ⟨1, [], ["c1"], [], [], [], [], [], ["c1"], ""⟩

-- row 21: two accepted challenges sharing one digest
#guard evalOpenResidues (100) [⟨"dup", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r1|target_ref:t1"⟩, ⟨"dup", "basis_ref:b2|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r2|target_ref:t2"⟩] == ⟨1, [], ["dup", "dup"], [], [], [], [], [], ["dup"], ""⟩

-- row 22: colliding digest: one challenge entry, one garbage entry
#guard evalOpenResidues (100) [⟨"cc", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r1|target_ref:t1"⟩, ⟨"cc", "garbage"⟩] == ⟨1, [], ["cc"], [], [], [], [], [], ["cc"], ""⟩

-- row 23: same digest: challenge bytes + hold bytes
#guard evalOpenResidues (100) [⟨"sh", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r1|target_ref:t1"⟩, ⟨"sh", "defect:1|epoch:1|grade:0|kind:challenge|sequence:3|status:open|target:t9"⟩] == ⟨1, [], ["sh"], [], [], [], ["sh"], [], ["sh"], ""⟩

-- row 24: union is canonical, not scan order
#guard evalOpenResidues (100) [⟨"z9", "kind:integrity|note:z"⟩, ⟨"a1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r1|target_ref:ta"⟩, ⟨"m5", "defect:0|epoch:1|grade:0|kind:challenge|sequence:3|status:open|target:t9"⟩] == ⟨1, ["z9"], ["a1"], [], [], [], ["m5"], [], ["a1", "m5", "z9"], ""⟩

-- row 25: source lists keep store scan order
#guard evalOpenResidues (100) [⟨"c9", "basis_ref:b9|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r9|target_ref:t9"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r1|target_ref:t1"⟩, ⟨"h2", "defect:2|epoch:1|grade:0|kind:challenge|sequence:3|status:open|target:t9"⟩, ⟨"h1", "defect:1|epoch:1|grade:1|kind:challenge|sequence:3|status:open|target:t9"⟩] == ⟨1, [], ["c9", "c1"], [], [], [], ["h2", "h1"], [], ["c1", "c9", "h1", "h2"], ""⟩

-- row 26: defect+grade+kind:integrity counts in both holds and integrity
#guard evalOpenResidues (100) [⟨"x1", "defect:1|grade:0|kind:integrity|target:t9"⟩] == ⟨1, ["x1"], [], [], [], [], ["x1"], [], ["x1"], ""⟩

-- row 27: unsorted defect/grade parts still read (as-presented parts)
#guard evalOpenResidues (100) [⟨"h1", "grade:1|defect:2"⟩] == ⟨1, [], [], [], [], [], ["h1"], [], ["h1"], ""⟩

-- row 28: fuel=0 admits
#guard evalOpenResidues (0) [⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r1|target_ref:t1"⟩] == ⟨1, [], ["c1"], [], [], [], [], [], ["c1"], ""⟩

-- row 29: resolves token suppresses only the named challenge
#guard evalOpenResidues (100) [⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r1|target_ref:t1"⟩, ⟨"c2", "basis_ref:b2|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:r2|target_ref:t2"⟩, ⟨"r1", "resolves:c2"⟩] == ⟨1, [], ["c1", "c2"], [], [], [], [], [], ["c1", "c2"], ""⟩

-- row 30: revalidated resolution suppresses its challenge
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] == ⟨1, [], [], ["c1"], [], ["o1"], [], [], [], ""⟩

-- row 31: transported resolution suppresses its challenge
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:transported|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] == ⟨1, [], [], ["c1"], [], ["o1"], [], [], [], ""⟩

-- row 32: retired resolution never suppresses (12:10 permanent residue)
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] == ⟨1, [], ["c1"], [], [], ["o1"], [], [], ["c1"], ""⟩

-- row 33: reopened resolution never suppresses
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:reopened|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] == ⟨1, [], ["c1"], [], [], ["o1"], [], [], ["c1"], ""⟩

-- row 34: refuted resolution never suppresses
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:refuted|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] == ⟨1, [], ["c1"], [], [], ["o1"], [], [], ["c1"], ""⟩

-- row 35: two valid revalidated resolutions compete, challenge stays open
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"s2", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r2", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o2", "epoch:0|kind:challenge_resolution|receipt_ref:r2|sequence:6|statement_ref:s2"⟩] == ⟨1, [], ["c1"], [], ["o1", "o2"], ["o1", "o2"], [], [], ["c1"], ""⟩

-- row 36: refuted plus revalidated resolution still competes (fail closed)
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"s3", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r3", "challenge_ref:c1|decision:refuted|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o3", "epoch:0|kind:challenge_resolution|receipt_ref:r3|sequence:6|statement_ref:s3"⟩] == ⟨1, [], ["c1"], [], ["o1", "o3"], ["o1", "o3"], [], [], ["c1"], ""⟩

-- row 37: resolution naming an absent challenge changes nothing
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:cX|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:cX|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] == ⟨1, [], ["c1"], [], [], [], [], [], ["c1"], ""⟩

-- row 38: resolution with unbound realization_ref changes nothing
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:zX|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] == ⟨1, [], ["c1"], [], [], [], [], [], ["c1"], ""⟩

-- row 39: unknown-disposition resolution changes nothing
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:dissolved|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] == ⟨1, [], ["c1"], [], [], [], [], [], ["c1"], ""⟩

-- row 40: kind:other occurrence is not a resolution
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:other|receipt_ref:r1|sequence:5|statement_ref:s1"⟩] == ⟨1, [], ["c1"], [], [], [], [], [], ["c1"], ""⟩

-- row 41: resolved challenge removed; unrelated hold stays in union
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"h1", "defect:2|grade:1"⟩] == ⟨1, [], [], ["c1"], [], ["o1"], ["h1"], [], ["h1"], ""⟩

-- row 42: one challenge resolves, a second stays open
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:revalidated|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"c2", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t2"⟩] == ⟨1, [], ["c2"], ["c1"], [], ["o1"], [], [], ["c2"], ""⟩

-- row 43: Annex 26.15: retired resolution suppresses when its minted residue is accepted
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩] == ⟨1, [], [], ["c1"], [], ["o1"], [], ["p1"], ["p1"], ""⟩

-- row 44: Annex 26.15: two retired resolutions compete even though one's minted residue is accepted
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"s2", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r2", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o2", "epoch:0|kind:challenge_resolution|receipt_ref:r2|sequence:6|statement_ref:s2"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩] == ⟨1, [], ["c1"], [], ["o1", "o2"], ["o1", "o2"], [], ["p1"], ["c1", "p1"], ""⟩

-- row 45: Annex 26.15: retired, residue back-ref broken stays open
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:z1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩] == ⟨1, [], ["c1"], [], [], ["o1"], [], [], ["c1"], ""⟩

-- row 46: Annex 26.15: retired, two residues claim the minter stays open
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p1|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"p1", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩, ⟨"p9", "kind:permanent_residue|minted_by:o1|obligation_ref:c1"⟩] == ⟨1, [], ["c1"], [], [], ["o1"], [], [], ["c1"], ""⟩

-- row 47: Annex 26.15: retired, residue minted by an irreparable disposition does not suppress
#guard evalOpenResidues (100) [⟨"b1", "basis_object"⟩, ⟨"z1", "realization_object"⟩, ⟨"c1", "basis_ref:b1|evidence_bytes:proof|evidence_class:counterexample_refutation|reproducer_ref:rp1|target_ref:t1"⟩, ⟨"464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02", "artifact:va|epoch:0|kind:successor|receipt:vr|sequence:1|statement:vs"⟩, ⟨"vr", "validator_artifact_ref:vchk"⟩, ⟨"vs", "subject"⟩, ⟨"s1", "basis_ref:b1|challenge_ref:c1|disposition:retired|realization_ref:p2|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"r1", "challenge_ref:c1|decision:validated|validator_occ_ref:464d49a9fff1af19263b253485558faed84433eea2dbc9ae040f9f0e35687c02"⟩, ⟨"o1", "epoch:0|kind:challenge_resolution|receipt_ref:r1|sequence:5|statement_ref:s1"⟩, ⟨"rcpt", "kind:receipt"⟩, ⟨"eff", "effect_kind:secret-leakage|observed_external_receipt_ref:rcpt|originating_execution_occurrence_ref:orig|payload_ref:pay|target_ref:tgt"⟩, ⟨"disp", "constructor:irreparable|effect_ref:eff|permanent_residue_ref:p2"⟩, ⟨"p2", "kind:permanent_residue|minted_by:disp|obligation_ref:eff"⟩] == ⟨1, [], ["c1"], [], [], ["o1"], [], ["p2"], ["c1", "p2"], ""⟩

-- row 48: Annex 26.15: arm-B residue alone joins the union
#guard evalOpenResidues (100) [⟨"rcpt", "kind:receipt"⟩, ⟨"eff", "effect_kind:secret-leakage|observed_external_receipt_ref:rcpt|originating_execution_occurrence_ref:orig|payload_ref:pay|target_ref:tgt"⟩, ⟨"disp", "constructor:irreparable|effect_ref:eff|permanent_residue_ref:p2"⟩, ⟨"p2", "kind:permanent_residue|minted_by:disp|obligation_ref:eff"⟩] == ⟨1, [], [], [], [], [], [], ["p2"], ["p2"], ""⟩

/-! ## Axiom transparency -/

#print axioms Rcic.OpenResidues.openUnion_refuse
#print axioms Rcic.OpenResidues.openUnion_success
#print axioms Rcic.OpenResidues.evalOpenResidues_fuel
#print axioms Rcic.OpenResidues.mem_scanWhere
#print axioms Rcic.OpenResidues.substep_open_mem
#print axioms Rcic.OpenResidues.mem_subtract_open
#print axioms Rcic.OpenResidues.subtract_open_mem
#print axioms Rcic.OpenResidues.substep_resolved_mem
#print axioms Rcic.OpenResidues.mem_subtract_resolved
#print axioms Rcic.OpenResidues.subtract_resolved_mem
#print axioms Rcic.OpenResidues.substep_competing_mem
#print axioms Rcic.OpenResidues.mem_subtract_competing
#print axioms Rcic.OpenResidues.subtract_competing_mem
#print axioms Rcic.OpenResidues.hitstep_occs_mem
#print axioms Rcic.OpenResidues.mem_challengeHits_occs
#print axioms Rcic.OpenResidues.challengeHits_occs_mem
#print axioms Rcic.OpenResidues.mem_resolutionScan
#print axioms Rcic.OpenResidues.resolutionScan_mem
#print axioms Rcic.OpenResidues.mem_permanentScan
#print axioms Rcic.OpenResidues.permanentScan_mem
#print axioms Rcic.OpenResidues.holdScan_mem
#print axioms Rcic.OpenResidues.challengeScan_mem
#print axioms Rcic.OpenResidues.integrityScan_mem
#print axioms Rcic.OpenResidues.not_accepted_of_part_count

/-
R-CIC Foundation (`01` §13, `11` §12–§13, §21, Annex 26.21 & 26.32):
`RF-020` (`security_reservation_has_no_future_reference`) and `SP-011`
(`exact security theorem and budget ledger`).

Formalizes:
1. `SecurityBudgetReservation` (class 3 kind 29), `SuccinctBundle` (class 7 kind 0),
   `JudgmentReceipt` (class 8 kind 0), verification occurrence derivation
   (`occRef recRef = recRef` at class 8 kind 0), and `LedgerEntry` (class 3 kind 34).
2. The `RF-020` no-future-reference discipline (`NoFutureRefOn`, `budgetReservationCheck`):
   a succinct verification receipt never references its own future occurrence
   (`[rcic_succinct_future_occurrence]`) or a `LedgerEntry` containing its own
   future occurrence (`[rcic_succinct_future_ledger]`).
3. The emitting ledger projection (`projectLedgerEntry`, `emitLedgerPosting`,
   `11` §13 `reservation → receipt → occurrence → ledger projection charge`):
   each admitted occurrence under an epoch emits a canonical kind-34 `LedgerEntry`
   charging the reservation's `proof_error_bound`, with duplicate-free occurrence
   posting (`[rcic_ledger_proj_duplicate]`) and reserved-charge integrity
   (`[rcic_ledger_proj_charge_mismatch]`).
4. The `SP-011` conservative union-bound epoch ledger and budget exhaustion theorem
   (`epochTotal`, `budgetEpochCheck`, `SP011_union_bound_additive`,
   `SP011_budgetEpochCheck_iff`, `SP011_exhaustion_verdict`,
   `SP011_positive_charges_count_le_total`):
   epoch totals sum all kind-34 postings in the epoch; exceeding
   `expected_post_charge_bound` refuses with `"[rcic_budget_epoch_exhausted]"`
   (never silently downgrading the security bound), and positive-charge postings
   under bound `B` are bounded in count by `B`.

`closure_claim` remains `0`.
-/
import rcic.RcicTypedRef
namespace Rcic.BudgetLedger

/-! ## 1. Security-Budget Reservation, Receipt, Occurrence, and LedgerEntry Objects -/

/-- `01` §13 / `11` §13 / Annex 26.21 `SecurityBudgetReservation` (class 3, kind 29):
    `authority_epoch_ref`, `verification_statement_ref`, `proof_error_bound`,
    `expected_post_charge_bound`. Represented as a 4-tuple of `Nat`s so binders
    have standard `census_kind` data heads. -/
abbrev ReservationTuple := Nat × Nat × Nat × Nat

def resEpoch (r : ReservationTuple) : Nat := r.1
def resStmt (r : ReservationTuple) : Nat := r.2.1
def resProofErrorBound (r : ReservationTuple) : Nat := r.2.2.1
def resPostChargeBound (r : ReservationTuple) : Nat := r.2.2.2

/-- Succinct `JudgmentEvidenceBundle` (class 7, kind 0, Annex 26.21):
    `(reservation_ref, statement_ref)`. -/
abbrev BundleTuple := Nat × Nat

def bunReservation (b : BundleTuple) : Nat := b.1
def bunStmt (b : BundleTuple) : Nat := b.2

/-- Succinct `JudgmentReceipt` (class 8, kind 0):
    `(statement_ref, evidence_bundle_ref, accepted_flag, cited_refs)`. -/
abbrev ReceiptTuple := Nat × Nat × Nat × List Nat

def recStmt (rc : ReceiptTuple) : Nat := rc.1
def recBundle (rc : ReceiptTuple) : Nat := rc.2.1
def recAccepted (rc : ReceiptTuple) : Nat := rc.2.2.1
def recCitedRefs (rc : ReceiptTuple) : List Nat := rc.2.2.2

/-- Annex 26.32 `LedgerEntry` (class 3, kind 34):
    `(authority_epoch_ref, charge, occurrence_ref)`. -/
abbrev LedgerEntryTuple := Nat × Nat × Nat

def leEpoch (e : LedgerEntryTuple) : Nat := e.1
def leCharge (e : LedgerEntryTuple) : Nat := e.2.1
def leOcc (e : LedgerEntryTuple) : Nat := e.2.2

/-- RF-017 / Annex 26.21 occurrence derivation: the verification occurrence ref of
    a receipt bound at class 8 kind 0 is the receipt's own class-8 digest. -/
def occRefOfReceipt (recRef : Nat) : Nat := recRef

/-- Deterministic content-addressed digest model for emitted kind-34 `LedgerEntry`
    objects (`derive 3 34`). -/
def deriveLedgerRef (e : LedgerEntryTuple) : Nat :=
  34000000 + e.1 * 10000 + e.2.1 * 100 + e.2.2

/-- Key-value lookup in an association list. -/
def assocLookup {α : Type} (xs : List (Nat × α)) (k : Nat) : Option α :=
  match xs with
  | [] => none
  | (k', v) :: rest =>
    match k' == k with
    | true => some v
    | false => assocLookup rest k

/-- Verdict of a budget-reservation, epoch-check, or ledger-projection check:
    `(1, q, "")` on accept, `(0, 0, code)` on refusal. -/
abbrev VerdictTuple := Nat × Nat × String

def verdictOk (q : Nat) : VerdictTuple := (1, q, "")
def verdictRefuse (code : String) : VerdictTuple := (0, 0, code)

private theorem verdictRefuse_ne_ok (code : String) (q : Nat) :
    verdictRefuse code ≠ verdictOk q := by
  intro h
  injection h with h1 _
  cases h1

/-! ## 2. `RF-020`: No Future Reference (`01` §13, `11` §13, Annex 26.21 & 26.32) -/

/-- Scan a single cited reference `v` against `recRef` and the ledger store `ledgers`.
    Fires `"[rcic_succinct_future_occurrence]"` if `v == occRefOfReceipt recRef`,
    and `"[rcic_succinct_future_ledger]"` if `v` resolves in `ledgers` to an entry
    whose `occurrence_ref == occRefOfReceipt recRef`. -/
def budgetRefScan
    (ledgers : List (Nat × LedgerEntryTuple)) (recRef v : Nat) : VerdictTuple :=
  match v == occRefOfReceipt recRef with
  | true => verdictRefuse "[rcic_succinct_future_occurrence]"
  | false =>
    match assocLookup ledgers v with
    | none => verdictOk recRef
    | some le =>
      match leOcc le == occRefOfReceipt recRef with
      | true => verdictRefuse "[rcic_succinct_future_ledger]"
      | false => verdictOk recRef

/-- Fold `budgetRefScan` across a list of cited refs. -/
def budgetRefScanList
    (ledgers : List (Nat × LedgerEntryTuple)) (recRef : Nat) : List Nat → VerdictTuple
  | [] => verdictOk recRef
  | v :: vs =>
    let r := budgetRefScan ledgers recRef v
    match r.1 == 0 with
    | true => r
    | false => budgetRefScanList ledgers recRef vs

/-- Declarative `NoFutureRef` predicate for `RF-020`: no cited ref is `recRef` or
    resolves in `ledgers` to a `LedgerEntry` whose `occurrence_ref` is `recRef`. -/
def NoFutureRefOn
    (ledgers : List (Nat × LedgerEntryTuple)) (recRef : Nat) (refs : List Nat) : Prop :=
  ∀ v ∈ refs,
    v ≠ occRefOfReceipt recRef ∧
    ∀ le, assocLookup ledgers v = some le → leOcc le ≠ occRefOfReceipt recRef

theorem budgetRefScan_ok_iff
    (ledgers : List (Nat × LedgerEntryTuple)) (recRef v : Nat) :
    budgetRefScan ledgers recRef v = verdictOk recRef ↔
      (v ≠ occRefOfReceipt recRef ∧
       ∀ le, assocLookup ledgers v = some le → leOcc le ≠ occRefOfReceipt recRef) := by
  unfold budgetRefScan
  cases hv : (v == occRefOfReceipt recRef) with
  | true =>
    dsimp only []
    have hveq : v = occRefOfReceipt recRef := LawfulBEq.eq_of_beq hv
    constructor
    · intro h
      exact False.elim (verdictRefuse_ne_ok _ _ h)
    · intro ⟨hne, _⟩
      exact False.elim (hne hveq)
  | false =>
    dsimp only []
    have hvne : v ≠ occRefOfReceipt recRef := by
      intro h
      rw [h, beq_self_eq_true] at hv
      cases hv
    cases hlook : assocLookup ledgers v with
    | none =>
      dsimp only []
      constructor
      · intro _
        refine ⟨hvne, fun _ h => by cases h⟩
      · intro _
        rfl
    | some le =>
      dsimp only []
      cases hle : (leOcc le == occRefOfReceipt recRef) with
      | true =>
        dsimp only []
        have hleeq : leOcc le = occRefOfReceipt recRef := LawfulBEq.eq_of_beq hle
        constructor
        · intro h
          exact False.elim (verdictRefuse_ne_ok _ _ h)
        · intro ⟨_, h2⟩
          exact False.elim (h2 le rfl hleeq)
      | false =>
        dsimp only []
        have hlene : leOcc le ≠ occRefOfReceipt recRef := by
          intro h
          rw [h, beq_self_eq_true] at hle
          cases hle
        constructor
        · intro _
          refine ⟨hvne, ?_⟩
          intro le' h'
          injection h' with h'
          subst h'
          exact hlene
        · intro _
          rfl

private theorem budgetRefScan_fst_zero_or_ok
    (ledgers : List (Nat × LedgerEntryTuple)) (recRef v : Nat) :
    ((budgetRefScan ledgers recRef v).1 == 0) = true ∧
      budgetRefScan ledgers recRef v ≠ verdictOk recRef ∨
    ((budgetRefScan ledgers recRef v).1 == 0) = false ∧
      budgetRefScan ledgers recRef v = verdictOk recRef := by
  unfold budgetRefScan
  cases (v == occRefOfReceipt recRef) with
  | true =>
    dsimp only []
    exact Or.inl ⟨rfl, verdictRefuse_ne_ok _ _⟩
  | false =>
    dsimp only []
    cases assocLookup ledgers v with
    | none =>
      dsimp only []
      exact Or.inr ⟨rfl, rfl⟩
    | some le =>
      dsimp only []
      cases (leOcc le == occRefOfReceipt recRef) with
      | true =>
        dsimp only []
        exact Or.inl ⟨rfl, verdictRefuse_ne_ok _ _⟩
      | false =>
        dsimp only []
        exact Or.inr ⟨rfl, rfl⟩

theorem RF020_refScanList_ok_iff
    (ledgers : List (Nat × LedgerEntryTuple)) (recRef : Nat) (refs : List Nat) :
    budgetRefScanList ledgers recRef refs = verdictOk recRef ↔
      NoFutureRefOn ledgers recRef refs := by
  induction refs with
  | nil =>
    constructor
    · intro _ v hv
      cases hv
    · intro _
      rfl
  | cons v vs ih =>
    unfold budgetRefScanList
    dsimp only []
    rcases budgetRefScan_fst_zero_or_ok ledgers recRef v with ⟨hz, hne⟩ | ⟨hfalse, hok⟩
    · rw [hz]
      dsimp only []
      constructor
      · intro h
        exact False.elim (hne h)
      · intro hall
        have hvok := (budgetRefScan_ok_iff ledgers recRef v).mpr (hall v (.head vs))
        exact False.elim (hne hvok)
    · rw [hfalse]
      dsimp only []
      have hvprop := (budgetRefScan_ok_iff ledgers recRef v).mp hok
      constructor
      · intro hvs w hw
        cases hw with
        | head => exact hvprop
        | tail _ hmem => exact (ih.mp hvs) w hmem
      · intro hall
        exact ih.mpr (fun w hw => hall w (.tail v hw))

/-- Full `rcic.budget_reservation` checker over reservation, receipt, bundle, and ledger stores. -/
def budgetReservationCheck
    (reservations : List (Nat × ReservationTuple))
    (bundles : List (Nat × BundleTuple))
    (receipts : List (Nat × ReceiptTuple))
    (ledgers : List (Nat × LedgerEntryTuple))
    (resRef recRef : Nat) : VerdictTuple :=
  match assocLookup reservations resRef, assocLookup receipts recRef with
  | some res, some rc =>
    match recStmt rc == resStmt res with
    | false => verdictRefuse "[rcic_budget_reservation_statement]"
    | true =>
      match assocLookup bundles (recBundle rc) with
      | none => verdictRefuse "[rcic_budget_reservation_unbound]"
      | some bun =>
        match bunReservation bun == resRef with
        | false => verdictRefuse "[rcic_succinct_no_reservation]"
        | true => budgetRefScanList ledgers recRef (recCitedRefs rc)
  | _, _ => verdictRefuse "[rcic_budget_reservation_unbound]"

/-- `RF-020` soundness and completeness: `budgetReservationCheck` accepts `recRef` iff
    the reservation, receipt, and succinct bundle resolve with aligned statement and
    reservation refs and `NoFutureRefOn` holds across all cited refs. -/
theorem RF020_budgetReservation_iff
    (reservations : List (Nat × ReservationTuple))
    (bundles : List (Nat × BundleTuple))
    (receipts : List (Nat × ReceiptTuple))
    (ledgers : List (Nat × LedgerEntryTuple))
    (resRef recRef : Nat) :
    budgetReservationCheck reservations bundles receipts ledgers resRef recRef =
        verdictOk recRef ↔
      ∃ res rc bun,
        assocLookup reservations resRef = some res ∧
        assocLookup receipts recRef = some rc ∧
        recStmt rc = resStmt res ∧
        assocLookup bundles (recBundle rc) = some bun ∧
        bunReservation bun = resRef ∧
        NoFutureRefOn ledgers recRef (recCitedRefs rc) := by
  unfold budgetReservationCheck
  cases hres : assocLookup reservations resRef with
  | none =>
    dsimp only []
    constructor
    · intro h; exact False.elim (verdictRefuse_ne_ok _ _ h)
    · rintro ⟨_, _, _, h1, _⟩; cases h1
  | some res =>
    cases hrc : assocLookup receipts recRef with
    | none =>
      dsimp only []
      constructor
      · intro h; exact False.elim (verdictRefuse_ne_ok _ _ h)
      · rintro ⟨_, _, _, _, h2, _⟩; cases h2
    | some rc =>
      dsimp only []
      cases hst : (recStmt rc == resStmt res) with
      | false =>
        dsimp only []
        constructor
        · intro h; exact False.elim (verdictRefuse_ne_ok _ _ h)
        · rintro ⟨res', rc', _, h1, h2, h3, _⟩
          injection h1 with h1; subst h1
          injection h2 with h2; subst h2
          rw [h3, beq_self_eq_true] at hst
          cases hst
      | true =>
        dsimp only []
        have hsteq : recStmt rc = resStmt res := LawfulBEq.eq_of_beq hst
        cases hbun : assocLookup bundles (recBundle rc) with
        | none =>
          dsimp only []
          constructor
          · intro h; exact False.elim (verdictRefuse_ne_ok _ _ h)
          · rintro ⟨res', rc', bun', h1, h2, _, h4, _⟩
            injection h2 with h2; subst h2
            rw [hbun] at h4; cases h4
        | some bun =>
          dsimp only []
          cases hbr : (bunReservation bun == resRef) with
          | false =>
            dsimp only []
            constructor
            · intro h; exact False.elim (verdictRefuse_ne_ok _ _ h)
            · rintro ⟨res', rc', bun', h1, h2, _, h4, h5, _⟩
              injection h2 with h2; subst h2
              rw [hbun] at h4; injection h4 with h4; subst h4
              rw [h5, beq_self_eq_true] at hbr
              cases hbr
          | true =>
            dsimp only []
            have hbreq : bunReservation bun = resRef := LawfulBEq.eq_of_beq hbr
            constructor
            · intro hscan
              have hnf := (RF020_refScanList_ok_iff ledgers recRef (recCitedRefs rc)).mp hscan
              exact ⟨res, rc, bun, rfl, rfl, hsteq, hbun, hbreq, hnf⟩
            · rintro ⟨res', rc', bun', h1, h2, _, h4, _, h6⟩
              injection h2 with h2; subst h2
              exact (RF020_refScanList_ok_iff ledgers recRef (recCitedRefs rc)).mpr h6

/-- `RF-020` tooth 1: citing the receipt's own future occurrence at the head of
    `cited_refs` produces `"[rcic_succinct_future_occurrence]"`. -/
theorem RF020_future_occurrence_verdict
    (ledgers : List (Nat × LedgerEntryTuple)) (recRef : Nat) (rest : List Nat) :
    budgetRefScanList ledgers recRef (occRefOfReceipt recRef :: rest) =
      verdictRefuse "[rcic_succinct_future_occurrence]" := by
  simp [budgetRefScanList, budgetRefScan, verdictRefuse]

/-- `RF-020` tooth 2: citing a `LedgerEntry` whose `occurrence_ref` is `recRef`
    produces `"[rcic_succinct_future_ledger]"`. -/
theorem RF020_future_ledger_verdict
    (epoch charge recRef ledgerRef : Nat) (rest : List Nat)
    (hne : (ledgerRef == occRefOfReceipt recRef) = false) :
    budgetRefScanList [(ledgerRef, (epoch, charge, occRefOfReceipt recRef))]
        recRef (ledgerRef :: rest) =
      verdictRefuse "[rcic_succinct_future_ledger]" := by
  simp [budgetRefScanList, budgetRefScan, assocLookup, hne, leOcc, verdictRefuse]

/-! ## 3. Ledger Projection Carrier (`01` §13, `11` §13, Annex 26.32) -/

/-- Emit the canonical kind-34 `LedgerEntry` for an admitted occurrence `occRef`
    under reservation `res`: `(authority_epoch_ref, proof_error_bound, occRef)`. -/
def projectLedgerEntry (res : ReservationTuple) (occRef : Nat) : LedgerEntryTuple :=
  (resEpoch res, resProofErrorBound res, occRef)

/-- Emitted `LedgerEntry` paired with its derived class-3 kind-34 digest. -/
def emitLedgerPosting (res : ReservationTuple) (occRef : Nat) : Nat × LedgerEntryTuple :=
  let e := projectLedgerEntry res occRef
  (deriveLedgerRef e, e)

theorem RF020_projectLedgerEntry_fields (res : Nat × Nat × Nat × Nat) (occRef : Nat) :
    leEpoch (projectLedgerEntry res occRef) = resEpoch res ∧
    leCharge (projectLedgerEntry res occRef) = resProofErrorBound res ∧
    leOcc (projectLedgerEntry res occRef) = occRef :=
  ⟨rfl, rfl, rfl⟩

theorem RF020_projectLedgerEntry_injective
    (res : Nat × Nat × Nat × Nat) (occ1 occ2 : Nat)
    (heq : projectLedgerEntry res occ1 = projectLedgerEntry res occ2) :
    occ1 = occ2 := by
  unfold projectLedgerEntry at heq
  injection heq with _ h2
  injection h2 with _ h3

/-! ## 4. Conservative Union Bound and `SP-011` Exact Security Budget Ledger (`11` §12–§13, §21) -/

/-- Filter stored kind-34 ledger postings belonging to `epoch`. -/
def epochEntries
    (ledgers : List (Nat × LedgerEntryTuple)) (epoch : Nat) : List LedgerEntryTuple :=
  (ledgers.filter (fun p => leEpoch p.2 == epoch)).map Prod.snd

/-- Sum of `charge` across a list of `LedgerEntryTuple`s. -/
def sumCharges : List LedgerEntryTuple → Nat
  | [] => 0
  | e :: es => leCharge e + sumCharges es

/-- Conservative union-bound epoch total (`rcic.budget_epoch_total`). -/
def epochTotal (ledgers : List (Nat × LedgerEntryTuple)) (epoch : Nat) : Nat :=
  sumCharges (epochEntries ledgers epoch)

theorem sumCharges_append (xs ys : List LedgerEntryTuple) :
    sumCharges (xs ++ ys) = sumCharges xs + sumCharges ys := by
  induction xs with
  | nil => simp [sumCharges]
  | cons x xs ih =>
    simp [sumCharges, ih, Nat.add_assoc]

/-- `SP-011` additivity of the conservative union bound: appending a posting in
    `epoch` increases `epochTotal` by `leCharge e`. -/
theorem SP011_union_bound_additive
    (ledgers : List (Nat × LedgerEntryTuple)) (d : Nat) (e : Nat × Nat × Nat) :
    epochTotal (ledgers ++ [(d, e)]) (leEpoch e) =
      epochTotal ledgers (leEpoch e) + leCharge e := by
  simp [epochTotal, epochEntries, List.filter_append, sumCharges_append, sumCharges]

/-- Appending a posting in another epoch `eEpoch ≠ epoch` leaves `epochTotal` unchanged. -/
theorem SP011_epochTotal_other_epoch_invariant
    (ledgers : List (Nat × LedgerEntryTuple)) (d epoch : Nat) (e : Nat × Nat × Nat)
    (hother : (leEpoch e == epoch) = false) :
    epochTotal (ledgers ++ [(d, e)]) epoch = epochTotal ledgers epoch := by
  simp [epochTotal, epochEntries, List.filter_append, hother]

/-- Every member of `es` is bounded by `sumCharges es` (union bound dominates each member). -/
theorem SP011_member_le_sumCharges (e : Nat × Nat × Nat) (es : List LedgerEntryTuple)
    (hmem : e ∈ es) :
    leCharge e ≤ sumCharges es := by
  induction es with
  | nil => cases hmem
  | cons x xs ih =>
    cases hmem with
    | head =>
      simp only [sumCharges]
      exact Nat.le_add_right _ _
    | tail _ htail =>
      have h := ih htail
      simp only [sumCharges]
      omega

/-- `rcic.budget_epoch_check`: verifies that `ledgerRef` resolves in `ledgers` to an
    entry `le`, its `occurrence_ref` resolves via `receipts → bundles → reservations`
    to an accepted receipt (`recAccepted rc == 1`) and reservation `res` in the same
    epoch (`resEpoch res == leEpoch le`), and the conservative union bound
    `epochTotal ledgers (leEpoch le) ≤ resPostChargeBound res` holds. -/
def budgetEpochCheck
    (reservations : List (Nat × ReservationTuple))
    (bundles : List (Nat × BundleTuple))
    (receipts : List (Nat × ReceiptTuple))
    (ledgers : List (Nat × LedgerEntryTuple))
    (ledgerRef : Nat) : VerdictTuple :=
  match assocLookup ledgers ledgerRef with
  | none => verdictRefuse "[rcic_budget_ledger_unbound]"
  | some le =>
    match assocLookup receipts (leOcc le) with
    | none => verdictRefuse "[rcic_budget_ledger_occurrence]"
    | some rc =>
      match recAccepted rc == 1 with
      | false => verdictRefuse "[rcic_budget_ledger_occurrence]"
      | true =>
        match assocLookup bundles (recBundle rc) with
        | none => verdictRefuse "[rcic_budget_ledger_occurrence]"
        | some bun =>
          match assocLookup reservations (bunReservation bun) with
          | none => verdictRefuse "[rcic_budget_ledger_occurrence]"
          | some res =>
            match resEpoch res == leEpoch le with
            | false => verdictRefuse "[rcic_budget_ledger_epoch]"
            | true =>
              match decide (resPostChargeBound res < epochTotal ledgers (leEpoch le)) with
              | true => verdictRefuse "[rcic_budget_epoch_exhausted]"
              | false => verdictOk ledgerRef

/-- `SP-011` exact characterization of `budgetEpochCheck`: accepts `ledgerRef` iff
    the entry and its `occurrence → receipt → bundle → reservation` chain resolve in
    the same epoch and `epochTotal ledgers (leEpoch le) ≤ resPostChargeBound res`. -/
theorem SP011_budgetEpochCheck_iff
    (reservations : List (Nat × ReservationTuple))
    (bundles : List (Nat × BundleTuple))
    (receipts : List (Nat × ReceiptTuple))
    (ledgers : List (Nat × LedgerEntryTuple))
    (ledgerRef : Nat) :
    budgetEpochCheck reservations bundles receipts ledgers ledgerRef =
        verdictOk ledgerRef ↔
      ∃ le rc bun res,
        assocLookup ledgers ledgerRef = some le ∧
        assocLookup receipts (leOcc le) = some rc ∧
        recAccepted rc = 1 ∧
        assocLookup bundles (recBundle rc) = some bun ∧
        assocLookup reservations (bunReservation bun) = some res ∧
        resEpoch res = leEpoch le ∧
        epochTotal ledgers (leEpoch le) ≤ resPostChargeBound res := by
  unfold budgetEpochCheck
  cases hle : assocLookup ledgers ledgerRef with
  | none =>
    dsimp only []
    constructor
    · intro h; exact False.elim (verdictRefuse_ne_ok _ _ h)
    · rintro ⟨_, _, _, _, h1, _⟩; cases h1
  | some le =>
    dsimp only []
    cases hrc : assocLookup receipts (leOcc le) with
    | none =>
      dsimp only []
      constructor
      · intro h; exact False.elim (verdictRefuse_ne_ok _ _ h)
      · rintro ⟨le', _, _, _, h1, h2, _⟩
        injection h1 with h1; subst h1
        rw [hrc] at h2; cases h2
    | some rc =>
      dsimp only []
      cases hacc : (recAccepted rc == 1) with
      | false =>
        dsimp only []
        constructor
        · intro h; exact False.elim (verdictRefuse_ne_ok _ _ h)
        · rintro ⟨le', rc', _, _, h1, h2, h3, _⟩
          injection h1 with h1; subst h1
          rw [hrc] at h2; injection h2 with h2; subst h2
          rw [h3] at hacc; cases hacc
      | true =>
        dsimp only []
        have hacceq : recAccepted rc = 1 := LawfulBEq.eq_of_beq hacc
        cases hbun : assocLookup bundles (recBundle rc) with
        | none =>
          dsimp only []
          constructor
          · intro h; exact False.elim (verdictRefuse_ne_ok _ _ h)
          · rintro ⟨le', rc', bun', _, h1, h2, _, h4, _⟩
            injection h1 with h1; subst h1
            rw [hrc] at h2; injection h2 with h2; subst h2
            rw [hbun] at h4; cases h4
        | some bun =>
          dsimp only []
          cases hres : assocLookup reservations (bunReservation bun) with
          | none =>
            dsimp only []
            constructor
            · intro h; exact False.elim (verdictRefuse_ne_ok _ _ h)
            · rintro ⟨le', rc', bun', res', h1, h2, _, h4, h5, _⟩
              injection h1 with h1; subst h1
              rw [hrc] at h2; injection h2 with h2; subst h2
              rw [hbun] at h4; injection h4 with h4; subst h4
              rw [hres] at h5; cases h5
          | some res =>
            dsimp only []
            cases hep : (resEpoch res == leEpoch le) with
            | false =>
              dsimp only []
              constructor
              · intro h; exact False.elim (verdictRefuse_ne_ok _ _ h)
              · rintro ⟨le', rc', bun', res', h1, h2, _, h4, h5, h6, _⟩
                injection h1 with h1; subst h1
                rw [hrc] at h2; injection h2 with h2; subst h2
                rw [hbun] at h4; injection h4 with h4; subst h4
                rw [hres] at h5; injection h5 with h5; subst h5
                rw [h6, beq_self_eq_true] at hep; cases hep
            | true =>
              dsimp only []
              have hepeq : resEpoch res = leEpoch le := LawfulBEq.eq_of_beq hep
              cases hexh : decide (resPostChargeBound res < epochTotal ledgers (leEpoch le)) with
              | true =>
                dsimp only []
                have hlt : resPostChargeBound res < epochTotal ledgers (leEpoch le) :=
                  of_decide_eq_true hexh
                constructor
                · intro h; exact False.elim (verdictRefuse_ne_ok _ _ h)
                · rintro ⟨le', rc', bun', res', h1, h2, _, h4, h5, _, h7⟩
                  injection h1 with h1; subst h1
                  rw [hrc] at h2; injection h2 with h2; subst h2
                  rw [hbun] at h4; injection h4 with h4; subst h4
                  rw [hres] at h5; injection h5 with h5; subst h5
                  exact False.elim (Nat.not_le_of_gt hlt h7)
              | false =>
                dsimp only []
                have hlebound : epochTotal ledgers (leEpoch le) ≤ resPostChargeBound res :=
                  Nat.le_of_not_lt (of_decide_eq_false hexh)
                constructor
                · intro _
                  exact ⟨le, rc, bun, res, rfl, hrc, hacceq, hbun, hres, hepeq, hlebound⟩
                · intro _
                  rfl

/-- `SP-011` budget-exhaustion policy (`11` §13): when `epochTotal` exceeds
    `expected_post_charge_bound`, `budgetEpochCheck` returns
    `verdictRefuse "[rcic_budget_epoch_exhausted]"`, never a silent downgrade. -/
theorem SP011_exhaustion_verdict
    (epoch stmt errBound bound occRef bunRef resRef ledgerRef charge : Nat)
    (hexh : bound < charge) :
    budgetEpochCheck
      [(resRef, (epoch, stmt, errBound, bound))]
      [(bunRef, (resRef, stmt))]
      [(occRef, (stmt, bunRef, 1, []))]
      [(ledgerRef, (epoch, charge, occRef))]
      ledgerRef = verdictRefuse "[rcic_budget_epoch_exhausted]" := by
  unfold budgetEpochCheck
  have hexh' : decide (bound < charge) = true := decide_eq_true hexh
  simp [assocLookup, leOcc, recAccepted, recBundle, bunReservation,
        resEpoch, leEpoch, resPostChargeBound, epochTotal, epochEntries,
        sumCharges, leCharge, hexh']

/-- Executable boolean check that every entry in `es` has positive charge (`1 ≤ leCharge e`). -/
def allPositiveCharges : List LedgerEntryTuple → Bool
  | [] => true
  | e :: es => decide (1 ≤ leCharge e) && allPositiveCharges es

/-- `SP-011` monotone counter bound: when every entry in `es` has positive charge
    (`allPositiveCharges es = true`), the number of posted entries `es.length` is
    bounded by `sumCharges es`. -/
theorem SP011_positive_charges_count_le_total (es : List LedgerEntryTuple)
    (hpos : allPositiveCharges es = true) :
    es.length ≤ sumCharges es := by
  induction es with
  | nil => simp [sumCharges]
  | cons e es ih =>
    simp only [allPositiveCharges, Bool.and_eq_true, decide_eq_true_eq] at hpos
    have hes : es.length ≤ sumCharges es := ih hpos.2
    have he : 1 ≤ leCharge e := hpos.1
    simp only [List.length_cons, sumCharges]
    omega

/-- `11` §13 charge-integrity check (`[rcic_ledger_proj_charge_mismatch]`):
    verifies that a stored `LedgerEntry` `le` for `occRef` under `res` carries
    exact charge `leCharge le = resProofErrorBound res` and `leEpoch le = resEpoch res`. -/
def ledgerChargeIntegrity (res : ReservationTuple) (occRef : Nat) (le : LedgerEntryTuple) : VerdictTuple :=
  match leEpoch le == resEpoch res with
  | false => verdictRefuse "[rcic_budget_ledger_epoch]"
  | true =>
    match leOcc le == occRef with
    | false => verdictRefuse "[rcic_budget_ledger_occurrence]"
    | true =>
      match leCharge le == resProofErrorBound res with
      | false => verdictRefuse "[rcic_ledger_proj_charge_mismatch]"
      | true => verdictOk (deriveLedgerRef le)

theorem RF020_ledgerChargeIntegrity_iff
    (res : Nat × Nat × Nat × Nat) (occRef : Nat) (le : Nat × Nat × Nat) :
    ledgerChargeIntegrity res occRef le = verdictOk (deriveLedgerRef le) ↔
      le = projectLedgerEntry res occRef := by
  rcases res with ⟨ep, st, peb, pcb⟩
  rcases le with ⟨lep, lch, locc⟩
  unfold ledgerChargeIntegrity projectLedgerEntry leEpoch resEpoch leOcc leCharge resProofErrorBound
  dsimp only []
  cases h1 : (lep == ep) with
  | false =>
    dsimp only []
    constructor
    · intro h; exact False.elim (verdictRefuse_ne_ok _ _ h)
    · intro h; injection h with hlep _; subst hlep; rw [beq_self_eq_true] at h1; cases h1
  | true =>
    dsimp only []
    have h1eq : lep = ep := LawfulBEq.eq_of_beq h1
    subst h1eq
    cases h2 : (locc == occRef) with
    | false =>
      dsimp only []
      constructor
      · intro h; exact False.elim (verdictRefuse_ne_ok _ _ h)
      · intro h
        injection h with _ hrest
        injection hrest with _ hlocc
        subst hlocc
        rw [beq_self_eq_true] at h2; cases h2
    | true =>
      dsimp only []
      have h2eq : locc = occRef := LawfulBEq.eq_of_beq h2
      subst h2eq
      cases h3 : (lch == peb) with
      | false =>
        dsimp only []
        constructor
        · intro h; exact False.elim (verdictRefuse_ne_ok _ _ h)
        · intro h
          injection h with _ hrest
          injection hrest with hlch _
          subst hlch
          rw [beq_self_eq_true] at h3; cases h3
      | true =>
        dsimp only []
        have h3eq : lch = peb := LawfulBEq.eq_of_beq h3
        subst h3eq
        exact ⟨fun _ => rfl, fun _ => rfl⟩

/-! ## 5. Sealed SHA-256 Preimage Bridge (`Rcic.TypedRef`), Corpus Pins, and M-005 Witnesses -/

/-- Canonical byte image of an Annex 26.32 kind-34 `LedgerEntry` (`scm/rcic/budget_ledger_proj_entry_of.scm`). -/
def ledgerEntryBytes (epochRef : String) (charge : Nat) (occRef : String) : String :=
  s!"authority_epoch_ref:{epochRef}|charge:{charge}|occurrence_ref:{occRef}"

/-- Exact class-3 kind-34 SHA-256 digest of a `LedgerEntry` (`rcic.derive 3 34` via `Rcic.TypedRef.deriveDigest`). -/
def deriveLedgerDigest (epochRef : String) (charge : Nat) (occRef : String) : String :=
  Rcic.TypedRef.deriveDigest 3 34 (ledgerEntryBytes epochRef charge occRef)

/-- Form-1 typed-ref content-binding adjudication (`Rcic.TypedRef.adjudicate 1 3 34`) for a `LedgerEntry`. -/
def adjudicateLedgerEntry (digest epochRef : String) (charge : Nat) (occRef : String) :
    Rcic.TypedRef.TRVal :=
  Rcic.TypedRef.adjudicate 1 3 34 digest (ledgerEntryBytes epochRef charge occRef)

/-- Every emitted `LedgerEntry` passes the sealed `Rcic.TypedRef.adjudicate 1 3 34` content-binding check. -/
theorem RF020_emitLedgerEntry_adjudicate_ok (epochRef : String) (charge : Nat) (occRef : String) :
    adjudicateLedgerEntry (deriveLedgerDigest epochRef charge occRef) epochRef charge occRef =
      Rcic.TypedRef.TRVal.ok (deriveLedgerDigest epochRef charge occRef) := by
  unfold adjudicateLedgerEntry Rcic.TypedRef.adjudicate Rcic.TypedRef.invalidCode Rcic.TypedRef.classOk
  have heq : deriveLedgerDigest epochRef charge occRef =
      Rcic.TypedRef.deriveDigest 3 34 (ledgerEntryBytes epochRef charge occRef) := rfl
  revert heq
  generalize deriveLedgerDigest epochRef charge occRef = dg1
  generalize Rcic.TypedRef.deriveDigest 3 34 (ledgerEntryBytes epochRef charge occRef) = dg2
  intro heq
  subst heq
  dsimp only []
  match hb : decide (dg1 = dg1) with
  | true => rfl
  | false => exact absurd rfl (of_decide_eq_false hb)
/-- Content-binding soundness (`Rcic.TypedRef.RF005_canonical_object_at_sound` specialized to class 3 kind 34):
    acceptance under `adjudicateLedgerEntry` implies the presented digest equals the exact SHA-256 preimage
    digest `deriveLedgerDigest epochRef charge occRef`. -/
theorem RF020_emitLedgerEntry_digest_sound
    (digest digest' epochRef : String) (charge : Nat) (occRef : String)
    (h : adjudicateLedgerEntry digest epochRef charge occRef = Rcic.TypedRef.TRVal.ok digest') :
    digest = deriveLedgerDigest epochRef charge occRef ∧ digest' = digest := by
  exact Rcic.TypedRef.RF005_canonical_object_at_sound 3 34 digest digest'
    (ledgerEntryBytes epochRef charge occRef) h

/-! ### Compile-enforced pins against `apps/rcic-budget-ledger-emit` corpus digests -/
#eval (if deriveLedgerDigest
    "57365f7d99d9cac23f981ebaf74c6fbd5247653930436806c6f7fd62324f26eb" 7
    "c92cf6ca817013b735810f6817037308e162176f52edd69e87307047c8d60c02" ==
    "957440f3d53b0eacd43077eab888895729ee8b6acbec6b3a480f694a27119c2f"
  then 0 else panic "row 8 kind-34 SHA-256 digest mismatch")

#eval (if deriveLedgerDigest
    "d908ead813bbd8722935062c8319926be2701ebb49f4bd11f28a4cd56721ee60" 99
    "b2bf4721bf02b3524f945ceab96982d97b6fdabb0bc293836f1e37b8a15487ce" ==
    "717fb146adf51d565e3003cf1eff0bd34d9814810b84a4bafa92464626749301"
  then 0 else panic "row 11 kind-34 SHA-256 digest mismatch")

#eval (if budgetReservationCheck [(10, (1, 2, 7, 42))] [(20, (10, 2))] [(30, (2, 20, 1, [40]))] [] 10 30 ==
    verdictOk 30 then 0 else panic "budgetReservationCheck accept pin mismatch")

#eval (if budgetEpochCheck [(10, (1, 2, 7, 42))] [(20, (10, 2))] [(30, (2, 20, 1, []))] [(50, (1, 7, 30))] 50 ==
    verdictOk 50 then 0 else panic "budgetEpochCheck accept pin mismatch")

#eval (if budgetEpochCheck [(10, (1, 2, 7, 5))] [(20, (10, 2))] [(30, (2, 20, 1, []))] [(50, (1, 7, 30))] 50 ==
    verdictRefuse "[rcic_budget_epoch_exhausted]" then 0 else panic "budgetEpochCheck exhaustion pin mismatch")

#eval (if ledgerChargeIntegrity (1, 2, 7, 42) 30 (1, 9, 30) ==
    verdictRefuse "[rcic_ledger_proj_charge_mismatch]" then 0 else panic "ledgerChargeIntegrity mismatch pin")

/-! ### M-005 Quantifier Inhabitation Witnesses -/

theorem RF020_budgetReservation_witness :
    budgetReservationCheck [(10, (1, 2, 7, 42))] [(20, (10, 2))] [(30, (2, 20, 1, [40]))] [] 10 30 =
      verdictOk 30 := rfl

theorem SP011_union_bound_witness :
    epochTotal [(50, (1, 7, 30)), (51, (1, 12, 31))] 1 =
      epochTotal [(50, (1, 7, 30))] 1 + epochTotal [(51, (1, 12, 31))] 1 := rfl

theorem SP011_budgetEpochCheck_witness :
    budgetEpochCheck [(10, (1, 2, 7, 42))] [(20, (10, 2))] [(30, (2, 20, 1, []))] [(50, (1, 7, 30))] 50 =
      verdictOk 50 := rfl

theorem SP011_exhaustion_witness :
    budgetEpochCheck [(10, (1, 2, 7, 5))] [(20, (10, 2))] [(30, (2, 20, 1, []))] [(50, (1, 7, 30))] 50 =
      verdictRefuse "[rcic_budget_epoch_exhausted]" :=
  SP011_exhaustion_verdict 1 2 7 5 30 20 10 50 7 (by decide)

theorem RF020_ledgerChargeIntegrity_witness :
    ledgerChargeIntegrity (1, 2, 7, 42) 30 (1, 7, 30) =
      verdictOk (deriveLedgerRef (1, 7, 30)) :=
  (RF020_ledgerChargeIntegrity_iff (1, 2, 7, 42) 30 (1, 7, 30)).mpr rfl

theorem RF020_emitLedgerEntry_witness :
    adjudicateLedgerEntry
      (deriveLedgerDigest "57365f7d99d9cac23f981ebaf74c6fbd5247653930436806c6f7fd62324f26eb" 7
        "c92cf6ca817013b735810f6817037308e162176f52edd69e87307047c8d60c02")
      "57365f7d99d9cac23f981ebaf74c6fbd5247653930436806c6f7fd62324f26eb" 7
      "c92cf6ca817013b735810f6817037308e162176f52edd69e87307047c8d60c02" =
    Rcic.TypedRef.TRVal.ok
      (deriveLedgerDigest "57365f7d99d9cac23f981ebaf74c6fbd5247653930436806c6f7fd62324f26eb" 7
        "c92cf6ca817013b735810f6817037308e162176f52edd69e87307047c8d60c02") :=
  RF020_emitLedgerEntry_adjudicate_ok _ _ _

#print axioms RF020_refScanList_ok_iff
#print axioms RF020_budgetReservation_iff
#print axioms RF020_future_occurrence_verdict
#print axioms RF020_future_ledger_verdict
#print axioms RF020_projectLedgerEntry_fields
#print axioms RF020_projectLedgerEntry_injective
#print axioms SP011_union_bound_additive
#print axioms SP011_epochTotal_other_epoch_invariant
#print axioms SP011_member_le_sumCharges
#print axioms SP011_budgetEpochCheck_iff
#print axioms SP011_exhaustion_verdict
#print axioms SP011_positive_charges_count_le_total
#print axioms RF020_ledgerChargeIntegrity_iff
#print axioms RF020_emitLedgerEntry_adjudicate_ok
#print axioms RF020_emitLedgerEntry_digest_sound

end Rcic.BudgetLedger

import rcic.RcicSynP2Shared
import rcic.RcicSynE

/-!
# P2 conditional skeleton — `P2Key`, `P2Answer`, `P2IH`, `OpenP2`, `p2_step_conditional`

`research/rcic/sortrow/S8_P2_CONDITIONAL_STEP.md` §3–5. `closure_claim` stays 0;
this is the honest conditional interface — no `AllBelowScoped`, no universal
supplier, and no discharged `sortCoh_at_call` is asserted here.

Measure: `P2Key := Nat × (List Nat × Nat)` = (original prefix length, local key),
ordered by `Prod.Lex (· < ·) LexDM`. `P2IH` answers only strictly lower-ranked
demanded queries — same-rank calls cannot be stated. `OpenP2` is the explicit
conditional payload: a resolved-view supply plus one `P2Case` per tag, covering
all ten dispatch tags.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- The P2 rank key: `(original prefix length, local key)`. -/
abbrev P2Key := Nat × (List Nat × Nat)

/-- The strict order on keys: prefix length first, then `LexDM` on the local
    key. Same-rank calls are therefore out of reach of `P2IH`. -/
abbrev P2LT := Prod.Lex (fun a b : Nat => a < b) LexDM

/-- A conditional answer: a nonempty resolved view plus the computed goal. -/
def P2Answer (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (q : P2Query Eₐ) : Prop :=
  Nonempty (ResolvedView Aw q) ∧ Goal tbl q

/-- The strict-below induction hypothesis: answers demanded queries whose rank
    is strictly under `q`'s. -/
def P2IH (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (q : P2Query Eₐ) : Prop :=
  ∀ q' : P2Query Eₐ, Demand q' →
    P2LT (q'.rank Aw) (q.rank Aw) → P2Answer Aw tbl q'

/-- One dispatched consumer case: from the resolved view and the strict-below
    IH, produce the goal of a query of tag `k`. -/
def P2Case (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) (k : P2Tag) : Prop :=
  ∀ (q : P2Query Eₐ), q.tag = k → Demand q → ResolvedView Aw q →
    P2IH Aw tbl q → Goal tbl q

/-- The conditional payload: supply a `ResolvedView` for every demanded query
    (under strict-below IH), plus a dispatched `P2Case` for every tag —
    explicitly all ten, no wildcard. The hypotheses `hEnv`, `hTbl` name the
    ambient admissibility the whole interface is conditioned on. -/
structure OpenP2 (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (hEnv : EnvWfT Eₐ) (hTbl : TableWF tbl) : Prop where
  /-- the resolved-view supply: computes the working view of any demanded
      query, using only the strict-below IH -/
  resolve : ∀ (q : P2Query Eₐ), Demand q → P2IH Aw tbl q →
    Nonempty (ResolvedView Aw q)
  es : P2Case Aw tbl Eₐ .es
  cl : P2Case Aw tbl Eₐ .cl
  eut : P2Case Aw tbl Eₐ .eut
  cts : P2Case Aw tbl Eₐ .cts
  pb : P2Case Aw tbl Eₐ .pb
  bitCoh : P2Case Aw tbl Eₐ .bitCoh
  mixed : P2Case Aw tbl Eₐ .mixed
  head : P2Case Aw tbl Eₐ .head
  slot : P2Case Aw tbl Eₐ .slot
  observation : P2Case Aw tbl Eₐ .observation

/-- The conditional step itself (S8 §5): given `W : OpenP2`, every demanded
    query admits its conditional answer by explicit tag dispatch. Nothing here
    discharges `W`; it only routes. -/
theorem p2_step_conditional {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (hEnv : EnvWfT Eₐ) (hTbl : TableWF tbl) (W : OpenP2 Aw tbl hEnv hTbl)
    (q : P2Query Eₐ) (hq : Demand q) (ih : P2IH Aw tbl q) :
    P2Answer Aw tbl q := by
  obtain ⟨v⟩ := W.resolve q hq ih
  refine ⟨⟨v⟩, ?_⟩
  cases ht : q.tag with
  | es => exact W.es q ht hq v ih
  | cl => exact W.cl q ht hq v ih
  | eut => exact W.eut q ht hq v ih
  | cts => exact W.cts q ht hq v ih
  | pb => exact W.pb q ht hq v ih
  | bitCoh => exact W.bitCoh q ht hq v ih
  | mixed => exact W.mixed q ht hq v ih
  | head => exact W.head q ht hq v ih
  | slot => exact W.slot q ht hq v ih
  | observation => exact W.observation q ht hq v ih

/-- Conditional completeness at a key: every demanded query ranked strictly
    under `k` has its conditional answer. -/
def P2CompleteAt (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv)
    (k : P2Key) : Prop :=
  ∀ (q : P2Query Eₐ), Demand q → P2LT (q.rank Aw) k → P2Answer Aw tbl q

/-- The bound-step target shape (S8 §5): to complete `(p, B)`, use all keys
    with a strictly smaller prefix, and all same-prefix keys whose local key is
    `LexDM`-smaller — exactly the two reachability legs of `P2LT`. -/
def P2BoundStep {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (p : Nat) (B : List Nat × Nat) : Prop :=
  (∀ p' : Nat, p' < p → ∀ B' : List Nat × Nat, P2CompleteAt Aw tbl Eₐ (p', B')) →
  (∀ B' : List Nat × Nat, LexDM B' B → P2CompleteAt Aw tbl Eₐ (p, B')) →
  P2CompleteAt Aw tbl Eₐ (p, B)

end Rcic.Syn

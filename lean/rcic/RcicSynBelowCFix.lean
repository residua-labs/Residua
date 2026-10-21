import rcic.RcicSynP2Step
import rcic.RcicSynAllBelow
import rcic.RcicSynInlineRefute
import rcic.RcicSynPack
import rcic.RcicSynOrder

/-!
# S15 §6 — the BelowC fixpoint wrapper: `Key`/`KeyLT`/`keyLT_wf`/`solve_of_step`

`research/rcic/sortrow/S15_BELOWC_DISPLAY_FIXPOINT.md` §6. The real
well-founded wrapper over p-auth's landed `P2Query`/`Demand`/`Goal`/
`ResolvedView` interface (`RcicSynP2Shared`). `closure_claim` stays 0.

* `Key` is the S8 rank key `(original prefix length, local key)`; `rank` is
  `P2Query.rank`, computed from the query's original objects — never filled
  by a caller.
* `KeyLT` is `Prod.Lex (· < ·) LexDM`: the first coordinate descends only by
  a strict prefix step; inside one frame the order is `LexDM` on the local
  key. `keyLT_wf` is built exactly the way main builds `lexDM_wf`:
  `Prod.lexAccessible` of the `Nat` well-foundedness and `lexDM_wf` — no new
  DM proof.
* `Before`/`Answer`/`Step`/`At` are the §6 single-step interface, verbatim.
* `solve_of_step` is ONLY the wrapper: `Step` stays a hypothesis — it is
  never claimed, never put inside a definition, and this module asserts no
  `hcoh`, no `AllBelowScoped`, no `sortCoh_at_call`.

`no_legacy_allBelow` is the §3 boundary control: the old scope-free
`AllBelow` is already refuted on main by `below_false_pinBetaP`, so the
fixpoint domain is the adopted `P2Query`/`Demand` interface and never a
same-named `AllBelow` swap. (Supplied on main by `RcicSynBelowBoundary`.)
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- The rank key: `(original prefix length, local key)` — S8's `P2Key`. -/
abbrev Key := Nat × (List Nat × Nat)

/-- The strict key order: strict prefix step first, `LexDM` on the local key
    inside one frame. Same shape as `P2LT`. -/
abbrev KeyLT : Key → Key → Prop := Prod.Lex (fun p' p : Nat => p' < p) LexDM

/-- `KeyLT` is well-founded: `Prod.lexAccessible` of `Nat`'s well-foundedness
    on the first coordinate and `lexDM_wf` on the second — the same
    construction main already uses for `lexDM_wf`. -/
theorem keyLT_wf : WellFounded KeyLT :=
  ⟨fun ⟨p, B⟩ =>
    Prod.lexAccessible (Nat.lt_wfRel.wf.apply p) (fun b => lexDM_wf.apply b) B⟩

/-- `q'` is strictly before `q` when its rank key is `KeyLT`-below `q`'s —
    §6's `Before`, computed from the original objects. -/
abbrev Before (Aw : Nat → Nat) {Eₐ : ResolvedEnv} (q' q : P2Query Eₐ) : Prop :=
  KeyLT (q'.rank Aw) (q.rank Aw)

/-- The conditional answer to `q`: a nonempty resolved view plus the goal the
    query's own objects compute. §6's `Answer`. -/
abbrev Answer (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (q : P2Query Eₐ) : Prop :=
  Nonempty (ResolvedView Aw q) ∧ Goal tbl q

/-- §6's `Step`: at any demanded query, from answers to every strictly
    `Before`-smaller demanded query, produce the answer. `Step` is a
    hypothesis of `solve_of_step`, never discharged here. -/
abbrev Step (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) : Prop :=
  ∀ q : P2Query Eₐ, Demand q →
    (∀ q' : P2Query Eₐ, Demand q' → Before Aw q' q → Answer Aw tbl q') →
    Answer Aw tbl q

/-- `At k`: every demanded query whose rank key is exactly `k` has its answer. -/
abbrev At (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) (k : Key) : Prop :=
  ∀ q : P2Query Eₐ, q.rank Aw = k → Demand q → Answer Aw tbl q

/-- The fixpoint wrapper itself (§6 verbatim): well-founded induction on
    `keyLT_wf` lifts a `Step` to an answer for every demanded query. The only
    recursion entry is an `Answer` at a strictly smaller rank key; nothing
    here discharges `step`. -/
theorem solve_of_step {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (step : Step Aw tbl Eₐ) : ∀ q : P2Query Eₐ, Demand q → Answer Aw tbl q := by
  have allAt : ∀ k : Key, At Aw tbl Eₐ k :=
    keyLT_wf.fix (fun k ih q hkey hq =>
      step q hq (fun q' hq' hlt =>
        ih (q'.rank Aw) (by unfold Before at hlt; rwa [hkey] at hlt) q' rfl hq'))
  intro q hq
  exact allAt (q.rank Aw) q rfl hq

-- §3 boundary control: the old scope-free `AllBelow` cannot be the fixpoint
-- domain — it is already refuted on main by the non-AP let-prefix weakening
-- counterexample `below_false_pinBetaP`. `no_legacy_allBelow` is supplied by
-- `rcic.RcicSynBelowBoundary` on main (identical statement and proof); it is
-- not restated here.

#print axioms Rcic.Syn.solve_of_step

end Rcic.Syn

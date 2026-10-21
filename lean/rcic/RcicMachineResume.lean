/-
RM-004 / RM-008 — run decomposition and exact resumption over the
reference machine's `runRaw` (docs/rcic/03_REFERENCE_MACHINE.md §15,
precision-audit rulings on #6627 via #6676).

The landed carrier `RunResult.suspended` carries no state, so the §15
shape `run(m+n, s) = continue(n, run(m, s))` has no object for
`«continue»` to act on, and `RM008_zero_suspension_exact` only records
`runRaw 0 s = .suspended`.  This module supplies the resumable carrier:

- `RunResumable` — `.done r` wraps the terminal `RunResult`;
  `.suspended s` CARRIES the raw state — the continuation the landed
  `.suspended` ctor drops (RM-008's premise).
- `runRawR` — the `runRaw` recursion over the resumable carrier.
- `«continue» n` — the §15 continue: `n` more budget steps at a carried
  state; terminal results absorb the extra budget.
- `RunResumable.forget` — drops the carried state, recovering `runRaw`
  exactly (`runRawR_forget`).

The laws:

- RM-004 `RM004_run_decompose` — `runRawR (m+n) s = continue n
  (runRawR m s)`, and `RM004_runRaw_decompose` at the landed carrier.
- RM-008 `RM008_suspension_resumes` / `RM008_runRaw_resumes` — a
  suspended run's carried state resumed for `n` more budget equals the
  uninterrupted `m+n` run, at both carriers.

`runRaw_suspended_cases` pins the two ways `runRaw` yields `.suspended`
(fuel-out with a resumable state vs. the state-internal `budget = 0`
`.result .suspended`), so "suspension" is never conflated with the
task-level refusal channel.

`closure_claim = 0`.
-/
import rcic.RcicMachine

namespace Rcic.Machine
open Rcic.Declarative

/-- The resumable run carrier: terminal `RunResult`s wrap as `.done`;
suspension CARRIES the `RawState` — the continuation the landed
`RunResult.suspended` drops (03 §15 RM-008's "a suspended state carries
the continuation"). -/
inductive RunResumable : Type
  | done (r : RunResult) : RunResumable
  | suspended (s : RawState) : RunResumable

/-- The resumable run — `runRaw`'s fuel/`kernelStepRaw` recursion,
suspension retaining the state for `«continue»`. -/
def runRawR : Nat → RawState → RunResumable
  | 0, s => .suspended s
  | k + 1, s =>
    match kernelStepRaw s with
    | .step s' => runRawR k s'
    | .result r => .done r

/-- Forget the carried state — recover the landed `RunResult`. -/
def RunResumable.forget : RunResumable → RunResult
  | .done r => r
  | .suspended _ => .suspended

/-- `«continue»` (03 §15 RM-004's `continue(n, run(m, s))`): `n` more
budget steps at a suspended state; terminal results absorb. -/
def «continue» (n : Nat) : RunResumable → RunResumable
  | .done r => .done r
  | .suspended s => runRawR n s

/-- The resumable run forgets to the landed run — `runRaw` is `runRawR`
with the continuation thrown away. -/
theorem runRawR_forget (k : Nat) (s : RawState) :
    (runRawR k s).forget = runRaw k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    cases hkr : kernelStepRaw s with
    | step s' =>
      simp only [runRawR, runRaw, hkr]
      exact ih s'
    | result r =>
      simp only [runRawR, runRaw, hkr]
      rfl

/-- RM-004 (03 §15): the budget-split law — `run(m+n, s) = continue(n,
run(m, s))`, over the resumable carrier that gives `«continue»` its
object. -/
theorem RM004_run_decompose (m n : Nat) (s : RawState) :
    runRawR (m + n) s = «continue» n (runRawR m s) := by
  induction m generalizing s with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih =>
    rw [Nat.succ_add]
    cases hkr : kernelStepRaw s with
    | step s' =>
      simp only [runRawR, hkr]
      exact ih s'
    | result r =>
      simp only [runRawR, hkr, «continue»]

/-- RM-004 at the landed carrier: the `m+n` `runRaw` result is what
`«continue»` produces at the resumable run, state forgotten. -/
theorem RM004_runRaw_decompose (m n : Nat) (s : RawState) :
    runRaw (m + n) s = («continue» n (runRawR m s)).forget := by
  rw [← RM004_run_decompose m n s, runRawR_forget]

/-- RM-008 (03 §15): suspension resumes exactly — the state carried by
`.suspended` IS the continuation; `«continue»` there reproduces the
uninterrupted `m+n` resumable run. -/
theorem RM008_suspension_resumes (m n : Nat) (s s' : RawState)
    (h : runRawR m s = .suspended s') :
    «continue» n (.suspended s') = runRawR (m + n) s := by
  rw [RM004_run_decompose m n s, h]

/-- RM-008 at the landed carrier: resuming a suspended state for `n`
more budget equals the uninterrupted `runRaw` — `runRaw n s' =
runRaw (m+n) s`. -/
theorem RM008_runRaw_resumes (m n : Nat) (s s' : RawState)
    (h : runRawR m s = .suspended s') :
    runRaw n s' = runRaw (m + n) s := by
  rw [← runRawR_forget n s', ← runRawR_forget (m + n) s,
    RM004_run_decompose m n s, h]
  rfl

/-- A `.done` result agrees with the landed run — the resumable carrier
keeps every terminal result identical. -/
theorem runRaw_of_runRawR_done (m : Nat) (s : RawState) (r : RunResult)
    (h : runRawR m s = .done r) : runRaw m s = r := by
  rw [← runRawR_forget m s, h]
  rfl

/-- A `.suspended` resumable run lands as the landed `.suspended`. -/
theorem runRaw_suspended_of_runRawR (m : Nat) (s s' : RawState)
    (h : runRawR m s = .suspended s') : runRaw m s = .suspended := by
  rw [← runRawR_forget m s, h]
  rfl

/-- The two sources of the landed `.suspended`, pinned: either the run
fuel ran out with the state carried (resumable), or `kernelStepRaw`
decided `.result .suspended` on a state-internal `budget = 0` (terminal
— `«continue»` absorbs it like every `.done`). -/
theorem runRaw_suspended_cases (m : Nat) (s : RawState)
    (h : runRaw m s = .suspended) :
    (∃ s', runRawR m s = .suspended s') ∨
      runRawR m s = .done .suspended := by
  have hf : (runRawR m s).forget = .suspended := by
    rwa [runRawR_forget]
  cases hr : runRawR m s with
  | done r =>
    rw [hr] at hf
    have h2 : r = .suspended := hf
    subst h2
    exact Or.inr rfl
  | suspended s' => exact Or.inl ⟨s', rfl⟩

/-! ## The ruling objects — `run_split_budget_continue` and
`suspension_resume_continuation`, named as the precision-audit rulings
name them (tbl:rulings, `lean_face scope:part` on #6627 via #6676).
Both are premise-free: the carrier makes the continuation part of the
statement, not of a hypothesis. -/

/-- RM-004's ruled object `run_split_budget_continue`: the §15
split-budget law — `run(m+n, s) = «continue»(n, run(m, s))` — stated
over the resumable carrier with no premise. -/
theorem run_split_budget_continue (m n : Nat) (s : RawState) :
    runRawR (m + n) s = «continue» n (runRawR m s) :=
  RM004_run_decompose m n s

/-- The same object at the landed carrier, continuation forgotten. -/
theorem run_split_budget_continue_raw (m n : Nat) (s : RawState) :
    runRaw (m + n) s = («continue» n (runRawR m s)).forget :=
  RM004_runRaw_decompose m n s

/-- RM-008's ruled object `suspension_resume_continuation`: whatever the
`m`-budget run left — a `.suspended` carrying its continuation state, or
a terminal `.done` — `«continue» n` there reproduces the uninterrupted
`m+n` run. Premise-free: the payload IS the continuation, so no
`runRawR m s = .suspended s'` hypothesis is needed. -/
theorem suspension_resume_continuation (m n : Nat) (s : RawState) :
    «continue» n (runRawR m s) = runRawR (m + n) s :=
  (RM004_run_decompose m n s).symm

/-- The same object at the landed carrier: resuming forgets to the
uninterrupted `runRaw` — `runRaw` is `«continue»` with the payload
dropped. -/
theorem suspension_resume_continuation_raw (m n : Nat) (s : RawState) :
    («continue» n (runRawR m s)).forget = runRaw (m + n) s := by
  rw [suspension_resume_continuation m n s, runRawR_forget]

/-! ## The continuation component — the payload is the exact suspended-at
state, and `«continue»` reads it. -/

/-- Fuel-out carries the state verbatim: `runRawR 0` suspends with `s`
itself — not a reset, not an initial state. -/
theorem suspension_carries_exact_state (s : RawState) :
    runRawR 0 s = .suspended s := rfl

/-- Resuming reads the carried payload: `«continue»` at `.suspended s'`
is `runRawR n` from `s'`. -/
theorem continue_reads_payload (n : Nat) (s' : RawState) :
    «continue» n (.suspended s') = runRawR n s' := rfl

/-- Zero extra budget travels the payload untouched. -/
theorem continue_zero_preserves (s : RawState) :
    «continue» 0 (.suspended s) = .suspended s := rfl

/-- Terminal results absorb further budget. -/
theorem continue_done_absorbs (n : Nat) (r : RunResult) :
    «continue» n (.done r) = .done r := rfl

/-- Nested continues compose to the summed budget — resumption is
associative. -/
theorem continue_compose (m n : Nat) (s : RawState) :
    «continue» m («continue» n (.suspended s)) = runRawR (n + m) s := by
  rw [continue_reads_payload n s, suspension_resume_continuation n m s]

/-- A `.suspended` resumable is never a `.done` — the continuation
channel is distinct from the terminal channel. -/
theorem suspended_ne_done (s : RawState) (r : RunResult) :
    (RunResumable.suspended s) ≠ .done r := fun h => nomatch h

/-! ## Fixture teeth — resumption is payload-sensitive, and the landed
carrier's `.suspended` conflates what `«continue»` separates. -/

/-- A `syntaxEqual` fixture that accepts `conversionConfirmed` on one
budget step. -/
def resumeFixtureConfirm : RawState where
  ambient := ⟨emptyEnv, 0, []⟩
  task := .syntaxEqual (.sort .zero) (.sort .zero)
  budget := 1

/-- Same task family, different payload: `syntaxEqual` of two distinct
sorts accepts `conversionMismatch` — the resumption outcome depends on
the carried state, not on `«continue»` alone. -/
def resumeFixtureMismatch : RawState where
  ambient := ⟨emptyEnv, 0, []⟩
  task := .syntaxEqual (.sort .zero) (.sort (.succ .zero))
  budget := 1

/-- TOOTH (RM-004): the split is real — `runRawR 0` suspends carrying
the fixture's state, and one more budget of `«continue»` lands the
accepted payload. -/
theorem pin_split_budget_concrete :
    runRawR 0 resumeFixtureConfirm = .suspended resumeFixtureConfirm ∧
    «continue» 1 (runRawR 0 resumeFixtureConfirm) =
      .done (.accepted .conversionConfirmed) :=
  ⟨rfl, rfl⟩

/-- TOOTH (RM-008, payload-sensitivity): two different suspended
payloads resume to different outcomes — `conversionConfirmed` at the
equal fixture, `conversionMismatch` at the unequal one. A `«continue»`
that dropped the payload (the landed `RunResult.suspended` mutant)
could not produce this split. -/
theorem pin_resume_payload_sensitive :
    «continue» 1 (.suspended resumeFixtureConfirm) =
      .done (.accepted .conversionConfirmed) ∧
    «continue» 1 (.suspended resumeFixtureMismatch) =
      .done (.accepted .conversionMismatch) :=
  ⟨rfl, rfl⟩

/-- TOOTH (the landed-carrier collapse): forgetting the continuation
conflates a resumable fuel-out suspension with a terminal
`.done .suspended` — both land as `.suspended` — while `«continue»`
keeps them apart: at zero budget the resumable payload suspends but
the terminal one stays done. -/
theorem forget_collapses_continue_distinguishes (s : RawState) :
    (RunResumable.suspended s).forget =
      (.done .suspended : RunResumable).forget ∧
    «continue» 0 (.suspended s) ≠ «continue» 0 (.done .suspended) := by
  refine ⟨rfl, fun h => ?_⟩
  rw [continue_zero_preserves, continue_done_absorbs] at h
  exact suspended_ne_done s .suspended h

end Rcic.Machine

/-
RM-004 / RM-008 at the frame-carrying machine — `«continue»`,
split-budget decomposition, and exact resumption over
`Rcic.KernelStepRaw.run` (`RcicKernelStepRaw.lean`), per cc's ruling on
#7178: the law must hold for the framed machine — the `Rcic.Machine`
carrier's `«continue»` is vacuous under `kernelStepRaw_never_step`
(`RcicMachine.lean:562`); here `kernelStepRaw_nonempty_steps`
(`RcicKernelStepRaw.lean:515`) makes the carried state a real mid-run
state.

Mirrors `RcicMachineResume.lean` (batch 64, #7005/#7017). The payload
problem that file solved — the landed `RunResult.suspended` drops the
state — does not exist here: `RunOutcome.suspended st` already carries
`st` (`RcicKernelStepRaw.lean:191`), and there is no `.done`-wrapped
terminal suspension: the framed state has no inner budget field
(budget is `run`'s `Nat` argument, `RcicKernelStepRaw.lean:186-189`),
so `.suspended` is always fuel-out and always resumable — the
`runRaw_suspended_cases` two-source split has no analog.

TRANSCRIPTION TABLE (03 §8, law → data):
  03:217 `run : Nat → State → result`          — `Rcic.KernelStepRaw.run` (landed)
  03:221 `run 0 = suspended(state)`            — `run_zero_is_suspended` (landed, :203)
  03:229 `run(m+n,s) = continue(n,run(m,s))`   — `run_decompose`
  03:238 "suspension resumes from the exact
         continuation"                          — `suspension_resumes`,
                                                 `continue_suspended`
  §8 "final results are stable under
     more budget" — framed analog              — `halted_stable`
                                                 (`RunOutcome` has no
                                                 decision payload;
                                                 `.halted` is the
                                                 terminal arm)

`«continue»` is a NEW name in this namespace (the escaped identifier;
`Rcic.Machine.«continue»` is the frameless one). `closure_claim = 0`.
-/
import rcic.RcicKernelStepRaw

namespace Rcic.KernelStepRaw

open Rcic.StateWf
open Rcic.Frames (FrameKind)
open Rcic.Declarative

/-- `continue` — resume a suspended run inside the same budget; a
    `halted` outcome consumes nothing (03:229's right-hand side, the
    `RunOutcome` arm of the `Rcic.Machine.«continue»` shape). -/
def «continue» (n : Nat) : RunOutcome → RunOutcome
  | .suspended st => run n st
  | .halted st => .halted st

/-- Resuming reads the carried payload: `«continue»` at `.suspended st`
    is `run n` from `st`. -/
theorem continue_suspended (n : Nat) (st : RawKernelState) :
    «continue» n (.suspended st) = run n st := rfl

/-- A `halted` outcome consumes no further budget. -/
theorem continue_halted (n : Nat) (st : RawKernelState) :
    «continue» n (.halted st) = .halted st := rfl

/-- `.suspended` and `.halted` are disjoint outcomes — the continuation
    channel is distinct from the terminal channel. -/
theorem suspended_ne_halted (st st' : RawKernelState) :
    (RunOutcome.suspended st : RunOutcome) ≠ .halted st' :=
  fun h => nomatch h

/-- One step on the state consumes one unit of budget (step arm). -/
theorem run_succ_of_step (k : Nat) (st st' : RawKernelState)
    (h : kernelStepRaw st = .step st') :
    run (k + 1) st = run k st' := by
  simp only [run, h]

/-- The empty-chain STOP is terminal at the current state. -/
theorem run_succ_of_noFrameAction (k : Nat) (st : RawKernelState)
    (h : kernelStepRaw st = .noFrameAction) :
    run (k + 1) st = .halted st := by
  simp only [run, h]

/-- The LookupLocalValue probe is terminal at the current state. -/
theorem run_succ_of_lookedUp (k : Nat) (st : RawKernelState)
    (v : Expr Nat) (h : kernelStepRaw st = .lookedUp v) :
    run (k + 1) st = .halted st := by
  simp only [run, h]

/-- A residue refusal is terminal at the current state. -/
theorem run_succ_of_refused (k : Nat) (st : RawKernelState)
    (r : String) (h : kernelStepRaw st = .refused r) :
    run (k + 1) st = .halted st := by
  simp only [run, h]

/-- RM-004's law at the framed machine (03:229): the budget splits —
    `run (m+n) st = «continue» n (run m st)`. Premise-free: the carrier
    makes the continuation part of the statement, not of a hypothesis. -/
theorem run_decompose (m n : Nat) (st : RawKernelState) :
    run (m + n) st = «continue» n (run m st) := by
  induction m generalizing st with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih =>
      cases hks : kernelStepRaw st with
      | step st' =>
          rw [Nat.succ_add,
            run_succ_of_step (m + n) st st' hks,
            run_succ_of_step m st st' hks]
          exact ih st'
      | noFrameAction =>
          rw [Nat.succ_add,
            run_succ_of_noFrameAction (m + n) st hks,
            run_succ_of_noFrameAction m st hks]
          rfl
      | lookedUp v =>
          rw [Nat.succ_add,
            run_succ_of_lookedUp (m + n) st v hks,
            run_succ_of_lookedUp m st v hks]
          rfl
      | refused c =>
          rw [Nat.succ_add,
            run_succ_of_refused (m + n) st c hks,
            run_succ_of_refused m st c hks]
          rfl

/-- RM-008's law at the framed machine (03:238): a suspended run's
    carried state resumed for `n` more budget equals the uninterrupted
    `m+n` run. -/
theorem suspension_resumes (m n : Nat) (st st' : RawKernelState)
    (h : run m st = .suspended st') :
    run (m + n) st = run n st' := by
  rw [run_decompose m n st, h]; rfl

/-- The framed analog of "stable under more budget": a terminal
    `.halted` outcome absorbs additional budget (the `RunOutcome` arm
    of `RcicScmRefinement.runRawR_done_stable`). -/
theorem halted_stable (m n : Nat) (st st' : RawKernelState)
    (h : run m st = .halted st') :
    run (m + n) st = .halted st' := by
  rw [run_decompose m n st, h]; rfl

/-- Continuations compose: two `«continue»`s equal one `«continue»` of
    the summed budget. -/
theorem continue_compose (m n : Nat) (st : RawKernelState) :
    «continue» m («continue» n (.suspended st)) = run (n + m) st := by
  rw [continue_suspended n st, (run_decompose n m st).symm]

/-! ## Fixture teeth — the carried payload is a real mid-run state,
and a `continue` that ignores it diverges. -/

/-- Concrete resumable fixture: `Infer` of a `Pi` on the empty
    continuation — 03 §10 determines the push
    (`kernelStepRaw_push_pi`). -/
def resumeFixture : RawKernelState := mkTask inferPi []

/-- Non-initial-state suspension pin: the carried payload is NOT the
    input. One step pushes `InferPiDomain` and consumes the task to
    `infer (sort 0)` — the suspended state is the post-push state with
    a nonempty frame chain. -/
theorem pin_suspension_carries_pushed_frame :
    run 1 resumeFixture =
      .suspended (mkTask (.infer (.sort .zero))
        [FrameKind.toNat .inferPiDomain]) := rfl

/-- Second step pops the frame: the carried state has the consumed
    task on the empty chain — still not `resumeFixture` itself. -/
theorem pin_suspension_carries_midrun_state :
    run 2 resumeFixture =
      .suspended (mkTask (.infer (.sort .zero)) []) := rfl

/-- Resuming the mid-run suspension with one more unit halts on the
    empty chain — equal to the uninterrupted `2 + 1` run. -/
theorem pin_continue_resumes_midrun_state :
    run (2 + 1) resumeFixture =
      .halted (mkTask (.infer (.sort .zero)) [])
      ∧ «continue» 1 (run 2 resumeFixture) =
          run (2 + 1) resumeFixture :=
  ⟨rfl, rfl⟩

/-- Mutant (tooth): a `continue`-shaped operation that drops the
    carried payload and restarts `run` from the caller-supplied
    origin — suspension restarts instead of resuming. -/
def continueRestart (n : Nat) (origin : RawKernelState) :
    RunOutcome → RunOutcome
  | .suspended _ => run n origin
  | .halted st => .halted st

/-- The mutant diverges at the fixture: resuming the carried mid-run
    state halts (`noFrameAction` on the empty chain); restarting from
    `resumeFixture` re-pushes the frame and suspends inside it. A
    continuation that ignores the payload cannot produce the split. -/
theorem pin_restart_from_input_mutant :
    «continue» 1 (run 2 resumeFixture) ≠
      continueRestart 1 resumeFixture (run 2 resumeFixture) :=
  fun h => nomatch h

#print axioms Rcic.KernelStepRaw.continue_suspended
#print axioms Rcic.KernelStepRaw.continue_halted
#print axioms Rcic.KernelStepRaw.suspended_ne_halted
#print axioms Rcic.KernelStepRaw.run_succ_of_step
#print axioms Rcic.KernelStepRaw.run_succ_of_noFrameAction
#print axioms Rcic.KernelStepRaw.run_succ_of_lookedUp
#print axioms Rcic.KernelStepRaw.run_succ_of_refused
#print axioms Rcic.KernelStepRaw.run_decompose
#print axioms Rcic.KernelStepRaw.suspension_resumes
#print axioms Rcic.KernelStepRaw.halted_stable
#print axioms Rcic.KernelStepRaw.continue_compose
#print axioms Rcic.KernelStepRaw.pin_suspension_carries_pushed_frame
#print axioms Rcic.KernelStepRaw.pin_suspension_carries_midrun_state
#print axioms Rcic.KernelStepRaw.pin_continue_resumes_midrun_state
#print axioms Rcic.KernelStepRaw.pin_restart_from_input_mutant

end Rcic.KernelStepRaw

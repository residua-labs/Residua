/-
Annex 23 UNIT H-5 — `03` §4 `kernelStepRaw` over the landed
frame-carrying `Rcic.StateWf.RawKernelState`.
Does NOT restate `stateWellFormed` (23.H.5 (b); E-W's predicate).
Does NOT reimplement `Rcic.Machine.kernelStepRaw` (23.H.0 (5)).
Does NOT reclassify any A3 cell. `closure_claim` stays 0.

TRANSCRIPTION TABLE (`03_REFERENCE_MACHINE.md` on this unit's
base, lines re-taken):
  03:94-98 RawKernelState {ambient, control,
           continuation_frames} — consumed from E-W;
           not re-stated. 03:91 is the §4 heading.
  03:113 kernelStepRaw : RawKernelState → RawStepResult
                          — `kernelStepRaw` in this file
  03:119 raw_step_preserves_state_well_formed
                          — `RM003_raw_step_preserves_state_well_formed`
  03:125 kernelStep       — NOT quoted (H-5 states the raw
                            preservation, not the subtype lift)
  03:188 at most one local action
  03:192 "push or pop one frame" — POP (`popLast`) and
                            PUSH (`pushFrame?`) of the three
                            Infer constructors 03 §10 determines
                            (Pi / Lambda / Application)
  03:217 run : Nat → KernelState → …
                          — `run`; budget is this Nat, not a
                            field of RawKernelState
  03:221 run 0 = suspended(raw(state))
                          — `run_zero_is_suspended` (unsealed)
  03:369 RM-003 "raw step preserves StateWellFormed"
                          — the sealed row statement

RELATION TO THE FRAMELESS STEPPER (23.H.5 (a)):
M-001 DEVIATION, not a `continuationFrames = []` fragment.
03:113's `kernelStepRaw` consumes 03:94-98's record (it has
`continuation_frames`). `Rcic.Machine.RawState` has no such
field and carries `budget` (03 §8 places budget on `run`;
03 §2 "The request identity excludes budget").
`Rcic.Machine.kernelStepRaw_never_step` says that stepper
never returns `.step`. This stepper DOES return `.step` on
a nonempty frame chain (`kernelStepRaw_nonempty_steps`).
Empty frames are not a shared fragment: this stepper
returns `.noFrameAction` there (push under-determined);
the frameless stepper returns a `.result` by inspecting
an expression the framed state does not carry.

H-8 PUSH. `Control.task` is the landed `RawTask`. 03 §10
determines the first frame for Infer of three constructors,
quoted, empty continuation only (a nonempty chain's `want`
is not determined by §10 to match the pushed frame's `in`;
03:130 + RM-003). Let, atomic Infer, and every non-Infer
task: WALL, quoted in `pushFrame?`.
Pop of the LAST frame is the unique pop that preserves
03:130's chain together with RM-003. Pop of the HEAD is
refused by measurement (anonymous `example` below).

H-9 LookupLocalValue. `03` §3 names the task
`LookupLocalValue U64`. The framed stepper's
LookupLocal arm, on the empty continuation,
performs `03` §7's "one environment lookup
probe": CALL `lookupValue` (the declarative
reader `Step.zetaLocal` consumes). A let
binder yields `.lookedUp v`; an assumption
or an out-of-range index yields `.refused`
with a named residue. Not a sixth
AcceptedPayload (`03` §6 / Annex 21 D-12);
the carrier extension is this arm. Ambient
gains `ctx` (H-9, named as such).
`closure_claim` stays 0.
-/
import rcic.RcicStateWf

namespace Rcic.KernelStepRaw
open Rcic.StateWf
open Rcic.Frames (FrameKind)
open Rcic.Declarative
open Rcic.Machine (RawTask)

/-- 03:111 `RawStepResult`. 03 names the type and not the
constructors. `.step` is a successor raw state (one local
action). `.noFrameAction` is the empty-chain STOP: pop is
impossible and push is not determined by 03 §10. Not a
KernelRefusal (03 §6): no request is being refused.
H-9: `.lookedUp` / `.refused` are the LookupLocalValue
probe (`03` §7 "one environment lookup probe"), not a
sixth AcceptedPayload. -/
inductive RawStepResult : Type
  | step (st' : RawKernelState)
  | noFrameAction
  | lookedUp (v : Expr Nat)
  | refused (code : String)
  deriving DecidableEq

/-- Carrier residues, byte-equal to
`scm/rcic/lookup_local_value.scm`. -/
def residueLookupAssumption : String :=
  "[rcic_lookup_local_value_assumption]"
def residueLookupUnbound : String :=
  "[rcic_lookup_local_value_unbound]"

/-- Pop the last frame. 03:192 "pop one frame". The last
frame is the unique end whose removal leaves a prefix of
the 03:130 chain. -/
def popLast : List Nat → Option (List Nat)
  | [] => none
  | _k :: t =>
    match t with
    | [] => some []
    | _ :: _ =>
      match popLast t with
      | none => none
      | some pre => some (_k :: pre)

/-- 03:192 "push one frame". 03 §10 determines the first
frame of Infer Pi / Lambda / Application, quoted per arm.
Empty continuation only. WALLED constructors: the sentence
that does not name a frame, quoted, no invention.
  Let — "Check the declared type, check the value, infer
    the body in a local let context, and substitute the
    value into the body type." First action is Check, not
    Infer; no Let frame is in 03 §5's examples; the
    task/result-kind pairing is not determined.
  Sort — "Check the level and return `sort (succ l)`."
  Bound variable — "Lookup the shifted local type through
    the explicit context cursor."
  Constant — "Resolve the exact `MemberRef`..."
  Literal — "Validate profile membership and return the
    profile-declared type."
  Every non-Infer task — 03 §10 is the Inference algorithm. -/
def pushFrame? (st : RawKernelState) : Option RawKernelState :=
  match st.continuationFrames with
  | _ :: _ => none
  | [] =>
    match st.control.task with
    | RawTask.infer e =>
      match e with
      | .pi A _B =>
        some ⟨st.ambient, ⟨RawTask.infer A⟩,
          [FrameKind.toNat .inferPiDomain]⟩
      | .lam A _b =>
        some ⟨st.ambient, ⟨RawTask.infer A⟩,
          [FrameKind.toNat .inferLambdaDomain]⟩
      | .app f _a =>
        some ⟨st.ambient, ⟨RawTask.infer f⟩,
          [FrameKind.toNat .inferAppFunction]⟩
      | .letE _A _v _b => none
      | .bvar _ => none
      | .sort _ => none
      | .const _ _ => none
      | .lit _ => none
    | RawTask.check _ _ => none
    | RawTask.whnfAt _ _ => none
    | RawTask.convType _ _ => none
    | RawTask.convAt _ _ _ => none
    | RawTask.syntaxEqual _ _ => none
    | RawTask.levelEqual _ _ => none
    | RawTask.lookupLocal _ => none
    | RawTask.lookupDeclaration _ _ => none

/-- 03 §7 "one environment lookup probe" for 03 §3
`LookupLocalValue U64`. CALLS `lookupValue` /
`lookupType`; no second reader. -/
def lookupLocalValueStep (ctx : LCtx) (i : Nat) :
    RawStepResult :=
  match lookupValue ctx i with
  | some v => .lookedUp v
  | none =>
    match lookupType ctx i with
    | some _ => .refused residueLookupAssumption
    | none => .refused residueLookupUnbound

/-- 03:111. One local action: push one determined frame,
pop one frame, the LookupLocalValue probe, or the STOP. -/
def kernelStepRaw (st : RawKernelState) : RawStepResult :=
  match pushFrame? st with
  | some st' => .step st'
  | none =>
    match popLast st.continuationFrames with
    | none =>
      match st.control.task with
      | RawTask.lookupLocal i =>
        lookupLocalValueStep st.ambient.ctx i
      | _ => .noFrameAction
    | some pre =>
      .step { st with continuationFrames := pre }

/-- 03:216 / 03:221. Budget is the `Nat` argument, not a
field of `RawKernelState`. Empty frames are not a final
decision 03 names; `run 0` suspends. Unsealed (placement
is the type). -/
inductive RunOutcome : Type
  | suspended (st : RawKernelState)
  | halted (st : RawKernelState)

def run : Nat → RawKernelState → RunOutcome
  | 0, st => .suspended st
  | n + 1, st =>
    match kernelStepRaw st with
    | .step st' => run n st'
    | .noFrameAction => .halted st
    | .lookedUp _ => .halted st
    | .refused _ => .halted st

def run_zero_is_suspended (st : RawKernelState) :
    run 0 st = .suspended st := rfl

/-! ### popLast characterization (unsealed helpers) -/

theorem popLast_none :
    (xs : List Nat) → popLast xs = none → xs = []
  | [], _ => rfl
  | _k :: [], h => nomatch h
  | x :: y :: ys, h =>
    have hunf :
        popLast (x :: y :: ys) =
          match popLast (y :: ys) with
          | none => none
          | some pre => some (x :: pre) := rfl
    match hpop : popLast (y :: ys) with
    | none =>
      nomatch (popLast_none (y :: ys) hpop)
    | some pre =>
      have hsome : popLast (x :: y :: ys) = some (x :: pre) := by
        rw [hunf, hpop]
      nomatch (h.symm.trans hsome)

theorem popLast_snoc :
    (xs : List Nat) → (pre : List Nat) →
    popLast xs = some pre → ∃ k, xs = pre ++ [k]
  | [], _pre, h => nomatch h
  | k :: [], pre, h =>
    have hpre : pre = [] := by
      have : popLast (k :: []) = some [] := rfl
      rw [this] at h
      injection h with hval
      exact hval.symm
    ⟨k, by subst hpre; rfl⟩
  | x :: y :: ys, pre, h =>
    have hunf :
        popLast (x :: y :: ys) =
          match popLast (y :: ys) with
          | none => none
          | some p => some (x :: p) := rfl
    match hpop : popLast (y :: ys) with
    | none =>
      have hnone : popLast (x :: y :: ys) = none := by
        rw [hunf, hpop]
      nomatch (h.symm.trans hnone)
    | some pre' =>
      have hsome : popLast (x :: y :: ys) = some (x :: pre') := by
        rw [hunf, hpop]
      have hpre : pre = x :: pre' := by
        rw [hsome] at h
        injection h with hval
        exact hval.symm
      match popLast_snoc (y :: ys) pre' hpop with
      | ⟨k, hk⟩ =>
        ⟨k, by
          subst hpre
          rw [hk]
          rfl⟩

theorem foldl_snoc
    {α β : Type} (f : β → α → β) (b : β)
    (l : List α) (a : α) :
    List.foldl f b (l ++ [a]) = f (List.foldl f b l) a := by
  induction l generalizing b with
  | nil => rfl
  | cons x xs ih => exact ih (f b x)

/-- Unfolding of `frameChainOk` at a snoc. Calls the landed
fold; does not re-state the predicate. -/
theorem frameChainOk_snoc
    (taskOut : Option Frames.ResultKind) (xs : List Nat) (k : Nat) :
    frameChainOk taskOut (xs ++ [k]) =
      match frameChainOk taskOut xs with
      | ChainStatus.mismatch | ChainStatus.unknownFrame =>
        frameChainOk taskOut xs
      | ChainStatus.ok want =>
        match frameIoNat k with
        | none => ChainStatus.unknownFrame
        | some (inn, out) =>
          if want == some inn then ChainStatus.ok (some out)
          else ChainStatus.mismatch := by
  unfold frameChainOk
  exact foldl_snoc
    (fun (acc : ChainStatus) (fk : Nat) =>
      match acc with
      | ChainStatus.mismatch | ChainStatus.unknownFrame => acc
      | ChainStatus.ok want =>
        match frameIoNat fk with
        | none => ChainStatus.unknownFrame
        | some (inn, out) =>
          if want == some inn then ChainStatus.ok (some out)
          else ChainStatus.mismatch)
    (ChainStatus.ok taskOut) xs k

theorem stateWellFormed_succ (n : Nat) (st : RawKernelState) :
    stateWellFormed (n + 1) st = some residueUnknownForm := rfl

theorem stateWellFormed_zero (st : RawKernelState) :
    stateWellFormed 0 st =
      let taskOut := taskIo (taskTag st.control.task)
      match frameChainOk taskOut st.continuationFrames with
      | ChainStatus.mismatch => some residueMismatch
      | ChainStatus.unknownFrame => some residueUnknownFrame
      | ChainStatus.ok _ =>
        if taskOut.isNone then some residueUnknownTask else none := rfl

theorem stateWellFormed_pop
    (form : Nat) (st : RawKernelState) (pre : List Nat) (k : Nat)
    (hframes : st.continuationFrames = pre ++ [k])
    (hwf : stateWellFormed form st = none) :
    stateWellFormed form { st with continuationFrames := pre }
      = none := by
  cases form with
  | succ n =>
    rw [stateWellFormed_succ] at hwf
    exact nomatch hwf
  | zero =>
    rw [stateWellFormed_zero] at hwf ⊢
    rw [hframes] at hwf
    change
      (match frameChainOk (taskIo (taskTag st.control.task))
            (pre ++ [k]) with
        | ChainStatus.mismatch => some residueMismatch
        | ChainStatus.unknownFrame => some residueUnknownFrame
        | ChainStatus.ok _ =>
          if (taskIo (taskTag st.control.task)).isNone then
            some residueUnknownTask
          else none) = none at hwf
    change
      (match frameChainOk (taskIo (taskTag st.control.task)) pre with
        | ChainStatus.mismatch => some residueMismatch
        | ChainStatus.unknownFrame => some residueUnknownFrame
        | ChainStatus.ok _ =>
          if (taskIo (taskTag st.control.task)).isNone then
            some residueUnknownTask
          else none) = none
    cases hc : frameChainOk (taskIo (taskTag st.control.task))
        (pre ++ [k]) with
    | mismatch =>
      rw [hc] at hwf
      exact nomatch hwf
    | unknownFrame =>
      rw [hc] at hwf
      exact nomatch hwf
    | ok _w =>
      rw [hc] at hwf
      have hsnoc :=
        frameChainOk_snoc (taskIo (taskTag st.control.task)) pre k
      rw [hc] at hsnoc
      cases hp : frameChainOk
          (taskIo (taskTag st.control.task)) pre with
      | mismatch =>
        rw [hp] at hsnoc
        exact nomatch hsnoc
      | unknownFrame =>
        rw [hp] at hsnoc
        exact nomatch hsnoc
      | ok _want =>
        change
          (if (taskIo (taskTag st.control.task)).isNone then
            some residueUnknownTask
          else none) = none at hwf
        change
          (if (taskIo (taskTag st.control.task)).isNone then
            some residueUnknownTask
          else none) = none
        exact hwf

/-- Push of a §10-determined Infer constructor onto the empty
chain preserves well-formedness: the child is still Infer
(tag 2, expr) and the first frame's `in` is expr. -/
theorem stateWellFormed_push
    (form : Nat) (st st' : RawKernelState)
    (hpush : pushFrame? st = some st')
    (hwf : stateWellFormed form st = none) :
    stateWellFormed form st' = none := by
  cases form with
  | succ n =>
    rw [stateWellFormed_succ] at hwf
    exact nomatch hwf
  | zero =>
    unfold pushFrame? at hpush
    cases hfr : st.continuationFrames with
    | cons _ _ =>
      rw [hfr] at hpush
      exact nomatch hpush
    | nil =>
      rw [hfr] at hpush
      cases ht : st.control.task with
      | infer e =>
        rw [ht] at hpush
        cases e with
        | pi A B =>
          have hst' :
              st' = ⟨st.ambient, ⟨RawTask.infer A⟩,
                [FrameKind.toNat .inferPiDomain]⟩ := by
            injection hpush with hval
            exact hval.symm
          subst hst'
          rfl
        | lam A b =>
          have hst' :
              st' = ⟨st.ambient, ⟨RawTask.infer A⟩,
                [FrameKind.toNat .inferLambdaDomain]⟩ := by
            injection hpush with hval
            exact hval.symm
          subst hst'
          rfl
        | app f a =>
          have hst' :
              st' = ⟨st.ambient, ⟨RawTask.infer f⟩,
                [FrameKind.toNat .inferAppFunction]⟩ := by
            injection hpush with hval
            exact hval.symm
          subst hst'
          rfl
        | letE _ _ _ => exact nomatch hpush
        | bvar _ => exact nomatch hpush
        | sort _ => exact nomatch hpush
        | const _ _ => exact nomatch hpush
        | lit _ => exact nomatch hpush
      | check _ _ =>
        rw [ht] at hpush; exact nomatch hpush
      | whnfAt _ _ =>
        rw [ht] at hpush; exact nomatch hpush
      | convType _ _ =>
        rw [ht] at hpush; exact nomatch hpush
      | convAt _ _ _ =>
        rw [ht] at hpush; exact nomatch hpush
      | syntaxEqual _ _ =>
        rw [ht] at hpush; exact nomatch hpush
      | levelEqual _ _ =>
        rw [ht] at hpush; exact nomatch hpush
      | lookupLocal _ =>
        rw [ht] at hpush; exact nomatch hpush
      | lookupDeclaration _ _ =>
        rw [ht] at hpush; exact nomatch hpush

/-! ### Sealed facts -/

/-- 03 §15 RM-003 "raw step preserves StateWellFormed".
Premises: none of the open §19.2 rows. Consumes E-W's
`stateWellFormed`; does not re-state it. -/
theorem RM003_raw_step_preserves_state_well_formed
    (form : Nat) (st st' : RawKernelState)
    (hstep : kernelStepRaw st = .step st')
    (hwf : stateWellFormed form st = none) :
    stateWellFormed form st' = none := by
  unfold kernelStepRaw at hstep
  match hpush : pushFrame? st with
  | some stPush =>
    have hst' : st' = stPush := by
      rw [hpush] at hstep
      injection hstep with hval
      exact hval.symm
    have hwf' : stateWellFormed form stPush = none :=
      stateWellFormed_push form st stPush hpush hwf
    rw [hst']
    exact hwf'
  | none =>
    rw [hpush] at hstep
    cases hpop : popLast st.continuationFrames with
    | none =>
      rw [hpop] at hstep
      revert hstep
      cases st.control.task with
      | lookupLocal i =>
        intro hstep
        dsimp at hstep
        unfold lookupLocalValueStep at hstep
        cases hval : lookupValue st.ambient.ctx i with
        | some _ =>
          rw [hval] at hstep
          exact nomatch hstep
        | none =>
          rw [hval] at hstep
          cases hty : lookupType st.ambient.ctx i with
          | some _ =>
            rw [hty] at hstep
            exact nomatch hstep
          | none =>
            rw [hty] at hstep
            exact nomatch hstep
      | infer _ =>
        intro hstep; exact nomatch hstep
      | check _ _ =>
        intro hstep; exact nomatch hstep
      | whnfAt _ _ =>
        intro hstep; exact nomatch hstep
      | convType _ _ =>
        intro hstep; exact nomatch hstep
      | convAt _ _ _ =>
        intro hstep; exact nomatch hstep
      | syntaxEqual _ _ =>
        intro hstep; exact nomatch hstep
      | levelEqual _ _ =>
        intro hstep; exact nomatch hstep
      | lookupDeclaration _ _ =>
        intro hstep; exact nomatch hstep
    | some pre =>
      rw [hpop] at hstep
      have hst' : st' = { st with continuationFrames := pre } := by
        injection hstep with hval
        exact hval.symm
      subst hst'
      match popLast_snoc st.continuationFrames pre hpop with
      | ⟨k, hk⟩ =>
        exact stateWellFormed_pop form st pre k hk hwf

/-- M-001: this stepper returns `.step` on every nonempty
chain. The frameless `Rcic.Machine.kernelStepRaw` never
does (`kernelStepRaw_never_step`). Not a fragment. -/
theorem kernelStepRaw_nonempty_steps
    (st : RawKernelState)
    (hne : st.continuationFrames ≠ []) :
    ∃ st', kernelStepRaw st = .step st' := by
  have hpush : pushFrame? st = none := by
    unfold pushFrame?
    cases hfr : st.continuationFrames with
    | nil => exact (hne hfr).elim
    | cons _ _ => rfl
  cases hpop : popLast st.continuationFrames with
  | none =>
    exact (hne (popLast_none st.continuationFrames hpop)).elim
  | some pre =>
    refine ⟨{ st with continuationFrames := pre }, ?_⟩
    unfold kernelStepRaw
    rw [hpush, hpop]

/-- M-005 non-trivial instance (degeneracy tooth, H-8): a
PUSH step. Infer of a Pi (03 §10 "Infer the domain as a
sort") on the empty chain steps to Infer of the domain
with InferPiDomainFrame; both well-formed. -/
def inferPi : RawTask :=
  .infer (.pi (.sort .zero) (.sort .zero))

theorem witness_step_framed :
    kernelStepRaw (mkTask inferPi []) =
      .step (mkTask (.infer (.sort .zero))
        [FrameKind.toNat .inferPiDomain])
    ∧ stateWellFormed 0 (mkTask inferPi []) = none
    ∧ stateWellFormed 0
        (mkTask (.infer (.sort .zero))
          [FrameKind.toNat .inferPiDomain]) = none :=
  ⟨rfl, rfl, rfl⟩

/-- 03 §10 Pi: "Infer the domain as a sort". -/
theorem kernelStepRaw_push_pi (A B : Expr Nat) :
    kernelStepRaw (mkTask (.infer (.pi A B)) []) =
      .step (mkTask (.infer A)
        [FrameKind.toNat .inferPiDomain]) := rfl

/-- 03 §10 Lambda: "Infer the domain as a sort". -/
theorem kernelStepRaw_push_lam (A b : Expr Nat) :
    kernelStepRaw (mkTask (.infer (.lam A b)) []) =
      .step (mkTask (.infer A)
        [FrameKind.toNat .inferLambdaDomain]) := rfl

/-- 03 §10 Application: "Infer the function". -/
theorem kernelStepRaw_push_app (f a : Expr Nat) :
    kernelStepRaw (mkTask (.infer (.app f a)) []) =
      .step (mkTask (.infer f)
        [FrameKind.toNat .inferAppFunction]) := rfl

/-- M-005 refusal instance: empty chain, no frame action
(STOP: push under-determined). Corpus row 00. -/
theorem witness_empty_no_frame_action :
    kernelStepRaw (mk 2 []) = .noFrameAction := rfl

/-! ### H-9 LookupLocalValue (03 §3 / 02 §4) -/

/-- 03 §3 `| LookupLocalValue U64` over the framed
LookupLocal arm. 02 §4: "For a local let binding, the
stored value is lifted by the same amount." The arm
CALLS `lookupValue`; a `.lookedUp v` acceptance is
exactly that reader. Empty continuation is a
conclusion (nonempty pops first), not a premise. -/
theorem lookupLocalValueStep_lookedUp
    (ctx : LCtx) (i : Nat) (v : Expr Nat)
    (h : lookupLocalValueStep ctx i = .lookedUp v) :
    lookupValue ctx i = some v := by
  unfold lookupLocalValueStep at h
  cases hlv : lookupValue ctx i with
  | none =>
    rw [hlv] at h
    cases hty : lookupType ctx i with
    | some _ =>
      rw [hty] at h
      exact nomatch h
    | none =>
      rw [hty] at h
      exact nomatch h
  | some v' =>
    rw [hlv] at h
    injection h with hv
    rw [hv]

theorem RM012_lookupLocalValue_accepted
    (st : RawKernelState) (i : Nat) (v : Expr Nat)
    (htask : st.control.task = .lookupLocal i)
    (hacc : kernelStepRaw st = .lookedUp v) :
    lookupValue st.ambient.ctx i = some v := by
  have hpush : pushFrame? st = none := by
    unfold pushFrame?
    cases st.continuationFrames with
    | cons _ _ => rfl
    | nil => simp only [htask]
  unfold kernelStepRaw at hacc
  rw [hpush] at hacc
  cases hpop : popLast st.continuationFrames with
  | some _pre =>
    rw [hpop] at hacc
    exact nomatch hacc
  | none =>
    rw [hpop] at hacc
    revert hacc
    rw [htask]
    intro hacc
    dsimp at hacc
    exact lookupLocalValueStep_lookedUp
      st.ambient.ctx i v hacc

/-- M-005 non-trivial instance (degeneracy tooth,
H-9): a let binder at index 1 behind an assumption.
Both the step and `lookupValue` are closed. -/
def letBehindAssump : LCtx :=
  [.assumption (.sort .zero),
   .letBinding (.sort .zero) (.bvar 0)]

def mkLookup (ctx : LCtx) (i : Nat) : RawKernelState :=
  ⟨{ ctx := ctx }, ⟨.lookupLocal i⟩, []⟩

theorem witness_lookupLocalValue_let :
    kernelStepRaw (mkLookup letBehindAssump 1)
      = .lookedUp (.bvar 2)
    ∧ lookupValue letBehindAssump 1
      = some (.bvar 2) :=
  ⟨rfl, rfl⟩

/-- M-005 refusal instance: looking up the value of
an assumption binder. -/
theorem witness_lookupLocalValue_assumption :
    kernelStepRaw
        (mkLookup [.assumption (.sort .zero)] 0)
      = .refused residueLookupAssumption :=
  rfl

/-- HEAD-pop does not preserve (measurement, not a route).
`mk 2 [3, 15]` is corpus row 15 (wf); dropping the head
leaves `mk 2 [15]`, a mismatch. Anonymous: not sealed. -/
example :
    stateWellFormed 0 (mk 2 [3, 15]) = none
    ∧ stateWellFormed 0 (mk 2 [15])
      = some StateWf.residueMismatch :=
  ⟨rfl, rfl⟩

end Rcic.KernelStepRaw

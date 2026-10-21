/-
Annex 22 UNIT E-W — `03` §4 `StateWellFormed`, quoted, over a
frame-carrying `RawKernelState`.
Pinned to `apps/rcic-state-wellformed/` (`rcic_state_wellformed`)
AND, per 22.E.10 amendment 1, `apps/rcic-kernel-frames/`
(`rcic_kernel_state_ok` — the wrapper that delegates form-0 to C1).
Does NOT reclassify any A3 cell (22.E.3 (i)).
Does NOT mint a second `kernelStepRaw` (already landed on Batch A's
frameless `Rcic.Machine.RawState`).

TRANSCRIPTION TABLE (`03_REFERENCE_MACHINE.md` on this unit's base
`19d7b6d0f`, lines re-taken):
  03:91  RawKernelState {ambient, control, continuation_frames}
                          — this file; ambient CARRIED not validated
                            (C1 APP.md amendment 2)
  03:101 StateWellFormed  — `stateWellFormed`
  03:105 KernelState subtype — `KernelState`
  03:111 kernelStepRaw    — NAMED DEVIATION: already landed at
                            `Rcic.Machine.kernelStepRaw` on the
                            frameless Batch A `RawState`. This unit
                            does not mint a second stepper.
  03:117 raw_step_preserves_state_well_formed — same; the Batch A
                            stepper never steps
                            (`kernelStepRaw_never_step`).
  03:123 kernelStep       — same.
  03:130 chain compatibility — the predicate (sentence lives in §5;
                            C1 quotes it as the characterizing
                            sentence of this belief).
  03:152 resume pairs     — via `Frames.frameIo` numbers + the chain
                            fold (bool→expr 2→0, level→decl 1→3).
No clause of §4 is silently dropped. The three stepper clauses are
named deviations, not omissions.

Annex 23 UNIT H-8 — Control carries `03` §3's `RawTask` (the
landed `Rcic.Machine.RawTask`; no second task type). C1's tag
is the projection `taskTag`. `03` §3 also names `CheckLevel`;
the landed inductive does not. THE TREE WINS: tag 7
(C1 `levelInfer`) is not in the image of `taskTag`. A wire
tag that does not round-trip through `taskTag` is unknown
(H-8 decode round-trip; pin_wd_row01 re-transcribed).

closure_claim stays 0.
-/
import rcic.RcicFrames
import rcic.RcicMachine

namespace Rcic.StateWf
open Rcic.Frames
open Rcic.Declarative
open Rcic.Machine (RawTask)

/-- 03:91 ambient. C1: carried, not validated.
H-9 carrier extension: `ctx` is `03` §2's
`local_context` / `02` §4 `LCtx`, so the
framed LookupLocal arm can CALL `lookupValue`
(no second reader). Default `[]` keeps every
landed `mk` / `mkTask` byte-equal on frames. -/
structure Ambient where
  ctx : LCtx := []
  deriving DecidableEq, Inhabited

/-- 03:91 control. 03 §3: the task IS `RawTask`, not a tag.
C1's tag is recovered by `taskTag`. -/
structure Control where
  task : RawTask
  deriving DecidableEq

/-- 03:91. `continuationFrames` holds kind tags (what `frame_io` reads). -/
structure RawKernelState where
  ambient : Ambient := {}
  control : Control
  continuationFrames : List Nat
  deriving DecidableEq

/-- C1 task table (APP.md "Encoding decisions"): 0 whnfAt,
1 convAt, 2 infer, 3 check, 4 lookupDeclaration, 5 lookupLocal,
6 levelEqual, 8 syntaxEqual. Tag 7 (levelInfer / `03` §3
`CheckLevel`) has no constructor on the landed `RawTask`;
`convType` is not in C1 and is tagged 9 (unknown to `taskIo`). -/
def taskTag : RawTask → Nat
  | .whnfAt _ _ => 0
  | .convAt _ _ _ => 1
  | .infer _ => 2
  | .check _ _ => 3
  | .lookupDeclaration _ _ => 4
  | .lookupLocal _ => 5
  | .levelEqual _ _ => 6
  | .syntaxEqual _ _ => 8
  | .convType _ _ => 9

/-- Dummy payload for a C1 tag. Atomic `sort 0` so `mk 2 []`
stays an Infer that §10 does not push. Tag 7 and every
non-image tag become `convType` (taskTag 9). -/
def dummyExpr : Expr Nat := .sort .zero

def taskOfTag (t : Nat) : RawTask :=
  match t with
  | 0 => .whnfAt dummyExpr dummyExpr
  | 1 => .convAt dummyExpr dummyExpr dummyExpr
  | 2 => .infer dummyExpr
  | 3 => .check dummyExpr dummyExpr
  | 4 => .lookupDeclaration 0 []
  | 5 => .lookupLocal 0
  | 6 => .levelEqual .zero .zero
  | 8 => .syntaxEqual dummyExpr dummyExpr
  | _ => .convType dummyExpr dummyExpr

def mk (task : Nat) (frames : List Nat) : RawKernelState :=
  ⟨{}, ⟨taskOfTag task⟩, frames⟩

def mkTask (task : RawTask) (frames : List Nat) : RawKernelState :=
  ⟨{}, ⟨task⟩, frames⟩

/-- C1 `rcic.task_io`. 0..8 known; else none (= −1). -/
def taskIo (t : Nat) : Option ResultKind :=
  match t with
  | 0 => some .expr   -- whnfAt
  | 1 => some .bool   -- convAt
  | 2 => some .expr   -- infer
  | 3 => some .bool   -- check
  | 4 => some .decl   -- lookupDeclaration
  | 5 => some .expr   -- lookupLocal
  | 6 => some .bool   -- levelEqual
  | 7 => some .level  -- levelInfer
  | 8 => some .bool   -- syntaxEqual
  | _ => none

def frameIoNat (k : Nat) : Option (ResultKind × ResultKind) :=
  (FrameKind.fromNat k).map frameIo

inductive ChainStatus : Type
  | ok (want : Option ResultKind)
  | mismatch
  | unknownFrame
  deriving Repr, DecidableEq

/-- `scm/rcic/frame_chain_ok.scm` fold. -/
def frameChainOk (taskOut : Option ResultKind) (kinds : List Nat) : ChainStatus :=
  kinds.foldl (fun acc k =>
    match acc with
    | .mismatch | .unknownFrame => acc
    | .ok want =>
      match frameIoNat k with
      | none => .unknownFrame
      | some (inn, out) =>
        if want == some inn then .ok (some out) else .mismatch)
    (.ok taskOut)

def residueMismatch : String := "[rcic_state_wellformed_mismatch]"
def residueUnknownFrame : String := "[rcic_state_unknown_frame_kind]"
def residueUnknownTask : String := "[rcic_state_unknown_task]"
def residueUnknownForm : String := "[rcic_state_unknown_form]"
def residueKernelUnknownForm : String := "[rcic_kernel_frames_unknown_form]"

/-- C1 `rcic.state_wellformed`. none = accept.
H-8: the chain still reads a C1 tag; the tag is `taskTag`
of the carried `RawTask` (`03` §3). -/
def stateWellFormed (form : Nat) (st : RawKernelState) : Option String :=
  if form != 0 then some residueUnknownForm
  else
    let taskOut := taskIo (taskTag st.control.task)
    match frameChainOk taskOut st.continuationFrames with
    | .mismatch => some residueMismatch
    | .unknownFrame => some residueUnknownFrame
    | .ok _ =>
      if taskOut.isNone then some residueUnknownTask else none

/-- C2 wrapper. form≠0 refuses the WRAPPER's name, not C1's. -/
def kernelStateOk (form : Nat) (st : RawKernelState) : Option String :=
  if form != 0 then some residueKernelUnknownForm
  else stateWellFormed 0 st

/-- 03:105. The subtype; inhabitant is a pair (state, well-formedness). -/
def KernelState : Type :=
  { st : RawKernelState // stateWellFormed 0 st = none }

/-! ### Sealed facts -/

theorem taskIo_unknown : taskIo 99 = none := rfl

theorem frameIoNat_unknown : frameIoNat 99 = none := rfl

theorem witness_empty_infer :
    stateWellFormed 0 (mk 2 []) = none := rfl

theorem witness_mismatch_bool_expr :
    stateWellFormed 0 (mk 2 [8, 1]) = some residueMismatch := rfl

theorem witness_unknown_frame :
    stateWellFormed 0 (mk 2 [99]) = some residueUnknownFrame := rfl

theorem witness_unknown_task :
    stateWellFormed 0 (mk 99 []) = some residueUnknownTask := rfl

theorem witness_unknown_form :
    stateWellFormed 1 (mk 2 [1]) = some residueUnknownForm := rfl

theorem witness_kernel_unknown_form :
    kernelStateOk 1 (mk 2 []) = some residueKernelUnknownForm := rfl

theorem witness_kernel_delegates :
    kernelStateOk 0 (mk 2 []) = stateWellFormed 0 (mk 2 []) := rfl

/-- C1 0..8 table as a projection of the landed `RawTask`.
Tag 7 is absent (no `CheckLevel` constructor). `convType` is
9, outside the table, so `taskIo` refuses it. -/
theorem taskTag_c1 :
    (∀ A e, taskTag (.whnfAt A e) = 0) ∧
    (∀ A l r, taskTag (.convAt A l r) = 1) ∧
    (∀ e, taskTag (.infer e) = 2) ∧
    (∀ e A, taskTag (.check e A) = 3) ∧
    (∀ r ls, taskTag (.lookupDeclaration r ls) = 4) ∧
    (∀ i, taskTag (.lookupLocal i) = 5) ∧
    (∀ l1 l2, taskTag (.levelEqual l1 l2) = 6) ∧
    (∀ a b, taskTag (.syntaxEqual a b) = 8) ∧
    (∀ A B, taskTag (.convType A B) = 9) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

end Rcic.StateWf

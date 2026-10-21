/-
Annex 23 UNIT H-8b — M-002 pins through the payload.
Each pin: a `#eval` whose input is the row's RawTask payload
decoded (`taskDecode` reuses `exprDecode` / `levelDecode`)
into `Rcic.Machine.RawTask`, then `kernelStepRaw` against
`expected`. Hand-transcribed per §18.3 rule 4.

CARRIER: apps/rcic-state-wellformed/rcic_kernel_step_raw_corpus.json
  (11 rows). before/after (M-009): 11 rows → 11 transcribed
  + 0 excluded. 10 compare `kernelStepRaw` to `expected`.
  1 pins the named WALL: tag 7 (`levelInfer` / `03` §3
  `CheckLevel`) has no `RawTask` constructor (TREE WINS);
  `taskDecode` is `none` (row 03, a POP).
H-9: 3 more #eval pins (11–13) transcribe
  apps/rcic-local-let-value M-005 / H-8c-empty rows
  through `mkLookup` (Ambient.ctx + lookupLocal).
  11 → 14 transcribed + 0 excluded.

PUSH rows 00/01/02 expect `.step` with the pushed frame kind
(InferPiDomain / InferLambdaDomain / InferAppFunction). That
is the degeneracy tooth: a tag-only dummy Infer (`sort 0`)
is `.noFrameAction`, not a push.

TRANSCRIPTION TABLE (fixture ← corpus label, exact strings):
  pin_ksr_row00 ← "PUSH InferPiDomain: 03 §10 Pi — Infer the domain as a sort (empty continuation)"
  pin_ksr_row01 ← "PUSH InferLambdaDomain: 03 §10 Lambda — Infer the domain as a sort (empty continuation)"
  pin_ksr_row02 ← "PUSH InferAppFunction: 03 §10 Application — Infer the function (empty continuation)"
  pin_ksr_row03 ← "POP one frame: 03 §7 — single LevelCursor drops to the empty chain"
  pin_ksr_row04 ← "POP one frame: 03 §7 — pair [3,15] drops its LAST frame (prefix kept)"
  pin_ksr_row05 ← "noFrameAction: Infer of sort — 03 §10 Sort is H-8's quoted WALL (Check, not Infer)"
  pin_ksr_row06 ← "noFrameAction: Infer of letE — H-8's quoted WALL (first action is Check)"
  pin_ksr_row07 ← "noFrameAction: Infer of bvar — H-8's quoted WALL (context cursor lookup)"
  pin_ksr_row08 ← "noFrameAction: check of a pi-typed expr — the tag gate (03 §3: only Infer enters 03 §10; 03 §10 is the Inference algorithm)"
  pin_ksr_row09 ← "noFrameAction: non-Infer task (check) — 03 §10 is the Inference algorithm"
  pin_ksr_row10 ← "push is EMPTY-CONTINUATION only: Infer of pi over [3] pops instead (H-8 pushFrame?)"
  pin_ksr_row11 ← "H-9 M-005 let i=1 behind assump"
  pin_ksr_row12 ← "H-9 M-005 assumption refuses"
  pin_ksr_row13 ← "H-9 H-8c empty ctx unbound"

M-007: this unit does not retire a carrier mutant (the
wrong-frame-kind mutant is the carrier's). Accept and STOP
pins of the stepper are NAMED as not retired. The degeneracy
tooth is pin_ksr_row00 (PUSH InferPiDomain).
-/
import rcic.RcicKernelStepRaw
import rcic.RcicStateWfPins

namespace Rcic.KernelStepRawPins
open Rcic.KernelStepRaw
open Rcic.StateWf
open Rcic.TaskPayloadDecode
open Rcic.Frames (FrameKind)
open Rcic.ExprSubstTask (ExprWire LevelWire)

-- 00 PUSH InferPiDomain (empty continuation)
#eval
  match taskDecode (TaskWire.infer (ExprWire.pi
      (ExprWire.sort LevelWire.zero)
      (ExprWire.sort LevelWire.zero))),
      taskDecode (TaskWire.infer
        (ExprWire.sort LevelWire.zero)) with
  | some t, some t' =>
    if kernelStepRaw (mkTask t [])
        == RawStepResult.step (mkTask t'
          [FrameKind.toNat .inferPiDomain]) then 0
    else panic "pin_ksr_row00"
  | _, _ => panic "pin_ksr_row00"
-- 01 PUSH InferLambdaDomain (empty continuation)
#eval
  match taskDecode (TaskWire.infer (ExprWire.lam
      (ExprWire.sort LevelWire.zero) (ExprWire.bvar 0))),
      taskDecode (TaskWire.infer
        (ExprWire.sort LevelWire.zero)) with
  | some t, some t' =>
    if kernelStepRaw (mkTask t [])
        == RawStepResult.step (mkTask t'
          [FrameKind.toNat .inferLambdaDomain]) then 1
    else panic "pin_ksr_row01"
  | _, _ => panic "pin_ksr_row01"
-- 02 PUSH InferAppFunction (empty continuation)
#eval
  match taskDecode (TaskWire.infer (ExprWire.app
      (ExprWire.bvar 1) (ExprWire.bvar 0))),
      taskDecode (TaskWire.infer (ExprWire.bvar 1)) with
  | some t, some t' =>
    if kernelStepRaw (mkTask t [])
        == RawStepResult.step (mkTask t'
          [FrameKind.toNat .inferAppFunction]) then 2
    else panic "pin_ksr_row02"
  | _, _ => panic "pin_ksr_row02"
-- 03 WALL: CheckLevel / levelInfer has no RawTask constructor
#eval
  match taskDecode (TaskWire.levelInfer LevelWire.zero) with
  | none => 3
  | some _ => panic "pin_ksr_row03"
-- 04 POP pair [3,15] drops LAST frame (prefix kept)
#eval
  match taskDecode (TaskWire.infer
      (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_ksr_row04"
  | some t =>
    if kernelStepRaw (mkTask t [3, 15])
        == RawStepResult.step (mkTask t [3]) then 4
    else panic "pin_ksr_row04"
-- 05 noFrameAction: Infer of sort
#eval
  match taskDecode (TaskWire.infer
      (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_ksr_row05"
  | some t =>
    if kernelStepRaw (mkTask t [])
        == RawStepResult.noFrameAction then 5
    else panic "pin_ksr_row05"
-- 06 noFrameAction: Infer of letE
#eval
  match taskDecode (TaskWire.infer (ExprWire.letE
      (ExprWire.sort LevelWire.zero)
      (ExprWire.bvar 0) (ExprWire.bvar 0))) with
  | none => panic "pin_ksr_row06"
  | some t =>
    if kernelStepRaw (mkTask t [])
        == RawStepResult.noFrameAction then 6
    else panic "pin_ksr_row06"
-- 07 noFrameAction: Infer of bvar
#eval
  match taskDecode (TaskWire.infer (ExprWire.bvar 0)) with
  | none => panic "pin_ksr_row07"
  | some t =>
    if kernelStepRaw (mkTask t [])
        == RawStepResult.noFrameAction then 7
    else panic "pin_ksr_row07"
-- 08 noFrameAction: check of a pi-typed expr (tag gate)
#eval
  match taskDecode (TaskWire.check
      (ExprWire.pi (ExprWire.sort LevelWire.zero)
        (ExprWire.sort LevelWire.zero))
      (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_ksr_row08"
  | some t =>
    if kernelStepRaw (mkTask t [])
        == RawStepResult.noFrameAction then 8
    else panic "pin_ksr_row08"
-- 09 noFrameAction: non-Infer task (check)
#eval
  match taskDecode (TaskWire.check (ExprWire.bvar 0)
      (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_ksr_row09"
  | some t =>
    if kernelStepRaw (mkTask t [])
        == RawStepResult.noFrameAction then 9
    else panic "pin_ksr_row09"
-- 10 push is EMPTY-CONTINUATION only: Infer of pi over [3] pops
#eval
  match taskDecode (TaskWire.infer (ExprWire.pi
      (ExprWire.sort LevelWire.zero)
      (ExprWire.sort LevelWire.zero))) with
  | none => panic "pin_ksr_row10"
  | some t =>
    if kernelStepRaw (mkTask t [3])
        == RawStepResult.step (mkTask t []) then 10
    else panic "pin_ksr_row10"
-- 11 H-9 M-005: let at i=1 behind assumption
-- (corpus "M-005 let at i=1 behind assumption")
#eval
  if kernelStepRaw (mkLookup letBehindAssump 1)
      == RawStepResult.lookedUp (.bvar 2) then 11
  else panic "pin_ksr_row11"
-- 12 H-9 M-005: assumption binder refuses
#eval
  if kernelStepRaw
      (mkLookup [.assumption (.sort .zero)] 0)
      == RawStepResult.refused residueLookupAssumption
    then 12
  else panic "pin_ksr_row12"
-- 13 H-9 H-8c empty ctx unbound
#eval
  if kernelStepRaw (mkLookup [] 0)
      == RawStepResult.refused residueLookupUnbound
    then 13
  else panic "pin_ksr_row13"

end Rcic.KernelStepRawPins

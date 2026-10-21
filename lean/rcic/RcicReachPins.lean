/-
Annex 22 UNIT E-R — M-9 corpus pins for `rcic_reachability`.
Each pin: a `#eval` through `validateReachableState`.
Hand-transcribed per §18.3 rule 4.

CARRIER: apps/rcic-reachability/rcic_reachability_corpus.json (19 rows).
  before/after (M-009): 19 rows → 19 transcribed + 0 excluded.
  (Pinned independently by the other seat before this unit opened.)

TRANSCRIPTION TABLE (fixture ← corpus label, exact strings):
  pin_rs_row00 ← "replay-evidence ACCEPT: request t:8, replay bytes t:8"
  pin_rs_row01 ← "receipt-evidence ACCEPT: receipt payload nonempty"
  pin_rs_row02 ← "EMPTY-evidence refusal: un-evidenced resumption refused"
  pin_rs_row03 ← "wrong-request refusal: request task 2 vs state task 8"
  pin_rs_row04 ← "non-resumable refusal: frames nonempty"
  pin_rs_row05 ← "undecodable request refusal"
  pin_rs_row06 ← "replay mismatch: replay bytes task 2 vs state 8"
  pin_rs_row07 ← "empty receipt payload refused"
  pin_rs_row08 ← "unknown form"
  pin_rs_row09 ← "FIELD form: form 1 over the accept row's exact env"
  pin_rs_row10 ← "FIELD request: t:7 flips to wrong_request"
  pin_rs_row11 ← "FIELD task: task 2 non-terminal flips to not_resumable"
  pin_rs_row12 ← "FIELD frames: task 8 with a frame flips to not_resumable"
  pin_rs_row13 ← "FIELD baseline: receipt accept (pairs with the four flips below)"
  pin_rs_row14 ← "FIELD form flip: same env, form 1"
  pin_rs_row15 ← "FIELD request flip: t:7 same rest"
  pin_rs_row16 ← "FIELD task flip: task 2 same rest"
  pin_rs_row17 ← "FIELD evb flip: empty receipt same rest"
  pin_rs_row18 ← "FIELD frames[0] flip: task 8 with frame 1, rest identical to baseline"

Row 12's *label* says task 8 with a frame; the JSON env is task 2
with a frame. This unit pins the JSON.

M-007 (GM-MACHINE-002-family, second instantiation):
  unknown-evidence 02 → `witness_unknown_evidence`
  not-resumable 04, 11, 12, 16, 18 → `witness_not_resumable`
  wrong-request 03, 05, 10, 15 → `witness_wrong_request`
  evidence-mismatch 06, 07, 17 → `witness_replay_mismatch` / `witness_empty_receipt`
  unknown-form 08, 09, 14 → `witness_unknown_form`
  accept 00, 01, 13 → NAMED as not retired (accepts)
-/
import rcic.RcicReach

namespace Rcic.ReachPins
open Rcic.Reach
open Rcic.StateWf (mk)

def ok8 : Rcic.StateWf.RawKernelState := mk 8 []
def bad2 : Rcic.StateWf.RawKernelState := mk 2 [1]
def task2empty : Rcic.StateWf.RawKernelState := mk 2 []
def task8frame : Rcic.StateWf.RawKernelState := mk 8 [1]

def acceptOk (r : ReachResult) : Bool :=
  match r with
  | .ok ks => ks.val == ok8
  | .refuse _ => false

def isRefuse (r : ReachResult) (c : String) : Bool :=
  match r with
  | .refuse c' => c' == c
  | .ok _ => false

-- 00 replay accept
#eval (if acceptOk (validateReachableState 0 "t:8" ok8 0 "t:8") then 0 else panic "pin_rs_row00")
-- 01 receipt accept
#eval (if acceptOk (validateReachableState 0 "t:8" ok8 1 "rcpt:0x1") then 1 else panic "pin_rs_row01")
-- 02 empty-evidence kind 9
#eval (if isRefuse (validateReachableState 0 "t:8" ok8 9 "") residueUnknownEvidence then 2 else panic "pin_rs_row02")
-- 03 wrong request t:2 vs task 8
#eval (if isRefuse (validateReachableState 0 "t:2" ok8 1 "rcpt") residueWrongRequest then 3 else panic "pin_rs_row03")
-- 04 non-resumable frames nonempty (JSON: task 2 + frame)
#eval (if isRefuse (validateReachableState 0 "t:8" bad2 1 "rcpt") residueNotResumable then 4 else panic "pin_rs_row04")
-- 05 undecodable request t:99
#eval (if isRefuse (validateReachableState 0 "t:99" ok8 1 "rcpt") residueWrongRequest then 5 else panic "pin_rs_row05")
-- 06 replay mismatch t:2
#eval (if isRefuse (validateReachableState 0 "t:8" ok8 0 "t:2") residueEvidenceMismatch then 6 else panic "pin_rs_row06")
-- 07 empty receipt
#eval (if isRefuse (validateReachableState 0 "t:8" ok8 1 "") residueEvidenceMismatch then 7 else panic "pin_rs_row07")
-- 08 unknown form
#eval (if isRefuse (validateReachableState 1 "t:8" ok8 1 "rcpt") residueUnknownForm then 8 else panic "pin_rs_row08")
-- 09 FIELD form
#eval (if isRefuse (validateReachableState 1 "t:8" ok8 1 "rcpt") residueUnknownForm then 9 else panic "pin_rs_row09")
-- 10 FIELD request t:7
#eval (if isRefuse (validateReachableState 0 "t:7" ok8 1 "rcpt") residueWrongRequest then 10 else panic "pin_rs_row10")
-- 11 FIELD task 2 empty frames
#eval (if isRefuse (validateReachableState 0 "t:8" task2empty 1 "rcpt") residueNotResumable then 11 else panic "pin_rs_row11")
-- 12 JSON: task 2 + frame (label says task 8; pin the JSON)
#eval (if isRefuse (validateReachableState 0 "t:8" bad2 1 "rcpt") residueNotResumable then 12 else panic "pin_rs_row12")
-- 13 FIELD baseline receipt accept
#eval (if acceptOk (validateReachableState 0 "t:8" ok8 1 "rcpt") then 13 else panic "pin_rs_row13")
-- 14 FIELD form flip
#eval (if isRefuse (validateReachableState 1 "t:8" ok8 1 "rcpt") residueUnknownForm then 14 else panic "pin_rs_row14")
-- 15 FIELD request flip t:7
#eval (if isRefuse (validateReachableState 0 "t:7" ok8 1 "rcpt") residueWrongRequest then 15 else panic "pin_rs_row15")
-- 16 FIELD task flip
#eval (if isRefuse (validateReachableState 0 "t:8" task2empty 1 "rcpt") residueNotResumable then 16 else panic "pin_rs_row16")
-- 17 FIELD evb flip empty receipt
#eval (if isRefuse (validateReachableState 0 "t:8" ok8 1 "") residueEvidenceMismatch then 17 else panic "pin_rs_row17")
-- 18 FIELD frames[0] task 8 + frame 1
#eval (if isRefuse (validateReachableState 0 "t:8" task8frame 1 "rcpt") residueNotResumable then 18 else panic "pin_rs_row18")

end Rcic.ReachPins

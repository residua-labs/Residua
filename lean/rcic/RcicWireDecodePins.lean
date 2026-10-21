/-
Annex 22 UNIT E-D — M-9 corpus pins for `rcic_wire_decode`.
Each pin: a `#eval` that transcribes a carrier corpus row through
`decodeWireState`. Hand-transcribed per §18.3 rule 4.

CARRIER: apps/rcic-wire-decode/rcic_wire_decode_corpus.json (20 rows).
  before/after (M-009): 20 rows → 20 transcribed + 0 excluded.

TRANSCRIPTION TABLE (fixture ← corpus label, exact strings):
  pin_wd_row00 ← "accept: t:2|f:1"
  pin_wd_row01 ← "accept: t:7|f:15|f:15"
  pin_wd_row02 ← "noncanonical value 't:02' (leading zero — exactness witness)"
  pin_wd_row03 ← "noncanonical value out of bounds 't:2|f:100'"
  pin_wd_row04 ← "bad shape: bare 't' (no colon)"
  pin_wd_row05 ← "bad shape: unknown key 'x:2'"
  pin_wd_row06 ← "bad shape: frame before task"
  pin_wd_row07 ← "bad shape: second task part"
  pin_wd_row08 ← "unknown task 99 (typed reference)"
  pin_wd_row09 ← "unknown frame tag 42 (frame tag syntax)"
  pin_wd_row10 ← "unknown form"
  pin_wd_row11 ← "teeth: task 0 whnfAt accept"
  pin_wd_row12 ← "teeth: task 1 convAt accept"
  pin_wd_row13 ← "teeth: task 3 check accept"
  pin_wd_row14 ← "teeth: task 4 lookupDeclaration accept"
  pin_wd_row15 ← "teeth: task 5 lookupLocal accept"
  pin_wd_row16 ← "teeth: task 6 levelEqual accept"
  pin_wd_row17 ← "teeth: task 8 syntaxEqual accept"
  pin_wd_row18 ← "teeth: ALL 17 frame kinds in one chain (t:2)"
  pin_wd_row19 ← "teeth: bad key MID-chain 't:2|x:1' (the tag check's own witness)"

M-007 (GM-MACHINE-002 minter accepts every form-0 refusal):
  noncanonical 02, 03 → `witness_noncanonical`
  bad-shape 04, 05, 06, 07, 19 → `witness_bad_shape`
  unknown-task 08 → `witness_unknown_task`
  unknown-frame 09 → `witness_unknown_frame`
  unknown-form 10 → `witness_unknown_form` (mutant also refuses this)
  accept rows 00, 01, 11–18 → NAMED as not retired (accepts)
-/
import rcic.RcicWireDecode

namespace Rcic.WireDecodePins
open Rcic.WireDecode
open Rcic.StateWf (mk)

def all17 : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

-- 00 accept: t:2|f:1
#eval (if decodeWireState 0 "t:2|f:1" == .ok (mk 2 [1]) then 0 else panic "pin_wd_row00")
-- 01 re-transcribed through taskTag: C1 tag 7 has no
-- RawTask constructor (03 §3 CheckLevel; landed inductive
-- does not). Round-trip refuses unknown_task.
#eval (if decodeWireState 0 "t:7|f:15|f:15" == .refuse residueUnknownTask then 1 else panic "pin_wd_row01")
-- 02 noncanonical leading zero
#eval (if decodeWireState 0 "t:02|f:1" == .refuse residueNoncanonical then 2 else panic "pin_wd_row02")
-- 03 noncanonical out of bounds
#eval (if decodeWireState 0 "t:2|f:100" == .refuse residueNoncanonical then 3 else panic "pin_wd_row03")
-- 04 bad shape: bare 't'
#eval (if decodeWireState 0 "t|f:1" == .refuse residueBadShape then 4 else panic "pin_wd_row04")
-- 05 bad shape: unknown key
#eval (if decodeWireState 0 "x:2|f:1" == .refuse residueBadShape then 5 else panic "pin_wd_row05")
-- 06 frame before task
#eval (if decodeWireState 0 "f:1|t:2" == .refuse residueBadShape then 6 else panic "pin_wd_row06")
-- 07 second task part
#eval (if decodeWireState 0 "t:2|t:3" == .refuse residueBadShape then 7 else panic "pin_wd_row07")
-- 08 unknown task 99
#eval (if decodeWireState 0 "t:99|f:1" == .refuse residueUnknownTask then 8 else panic "pin_wd_row08")
-- 09 unknown frame tag 42
#eval (if decodeWireState 0 "t:2|f:42" == .refuse residueUnknownFrame then 9 else panic "pin_wd_row09")
-- 10 unknown form
#eval (if decodeWireState 1 "t:2|f:1" == .refuse residueUnknownForm then 10 else panic "pin_wd_row10")
-- 11 teeth: task 0 whnfAt
#eval (if decodeWireState 0 "t:0|f:1" == .ok (mk 0 [1]) then 11 else panic "pin_wd_row11")
-- 12 teeth: task 1 convAt
#eval (if decodeWireState 0 "t:1|f:17" == .ok (mk 1 [17]) then 12 else panic "pin_wd_row12")
-- 13 teeth: task 3 check
#eval (if decodeWireState 0 "t:3|f:17" == .ok (mk 3 [17]) then 13 else panic "pin_wd_row13")
-- 14 teeth: task 4 lookupDeclaration
#eval (if decodeWireState 0 "t:4|f:16" == .ok (mk 4 [16]) then 14 else panic "pin_wd_row14")
-- 15 teeth: task 5 lookupLocal
#eval (if decodeWireState 0 "t:5|f:1" == .ok (mk 5 [1]) then 15 else panic "pin_wd_row15")
-- 16 teeth: task 6 levelEqual
#eval (if decodeWireState 0 "t:6|f:17" == .ok (mk 6 [17]) then 16 else panic "pin_wd_row16")
-- 17 teeth: task 8 syntaxEqual
#eval (if decodeWireState 0 "t:8|f:17" == .ok (mk 8 [17]) then 17 else panic "pin_wd_row17")
-- 18 teeth: ALL 17 frame kinds
#eval (if decodeWireState 0 "t:2|f:1|f:2|f:3|f:4|f:5|f:6|f:7|f:8|f:9|f:10|f:11|f:12|f:13|f:14|f:15|f:16|f:17" == .ok (mk 2 all17) then 18 else panic "pin_wd_row18")
-- 19 teeth: bad key MID-chain
#eval (if decodeWireState 0 "t:2|x:1" == .refuse residueBadShape then 19 else panic "pin_wd_row19")

end Rcic.WireDecodePins


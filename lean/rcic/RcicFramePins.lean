/-
Annex 22 UNIT E-F — M-9 corpus pins for `rcic_frame_kind_ok`.
Each pin: a `#eval` that transcribes a carrier corpus row through
`frameKindOk`. Hand-transcribed per §18.3 rule 4.

CARRIER: apps/rcic-kernel-frames/rcic_frame_kind_ok_corpus.json (38 rows).
  before/after (M-009): 38 rows → 38 transcribed + 0 excluded.

CARRIER: apps/rcic-kernel-frames/rcic_kernel_state_ok_corpus.json (8 rows).
  before/after (M-009): 8 rows → 0 transcribed + 8 EXCLUDED BY LABEL:
  - every form-0 row delegates VERBATIM to C1 `rcic.state_wellformed`
    (APP.md Belief 1). That predicate is UNIT E-W. Pinning it here
    would quote E-W's object. Form≠0 is already pinned as
    `residueUnknownForm` via frame_kind_ok row 25/31.

TRANSCRIPTION TABLE (fixture ← corpus label, exact strings):
  pin_frame_row00 ← "kind 1 once (ctx=parent)"
  pin_frame_row01 ← "kind 2 once (ctx=parent)"
  pin_frame_row02 ← "kind 3 once (ctx=parent)"
  pin_frame_row03 ← "kind 4 once (binder-extended)"
  pin_frame_row04 ← "kind 5 once (binder-extended)"
  pin_frame_row05 ← "kind 6 once (binder-extended)"
  pin_frame_row06 ← "kind 7 once (ctx=parent)"
  pin_frame_row07 ← "kind 8 once (ctx=parent)"
  pin_frame_row08 ← "kind 9 once (ctx=parent)"
  pin_frame_row09 ← "kind 10 once (ctx=parent)"
  pin_frame_row10 ← "kind 11 once (ctx=parent)"
  pin_frame_row11 ← "kind 12 once (ctx=parent)"
  pin_frame_row12 ← "kind 13 once (ctx=parent)"
  pin_frame_row13 ← "kind 14 once (ctx=parent)"
  pin_frame_row14 ← "kind 15 once (ctx=parent)"
  pin_frame_row15 ← "kind 16 once (ctx=parent)"
  pin_frame_row16 ← "kind 17 once (ctx=parent)"
  pin_frame_row17 ← "unknown kind 99"
  pin_frame_row18 ← "extension kind 16 is known (C1 ext)"
  pin_frame_row19 ← "extension kind 17 is known (C1 ext)"
  pin_frame_row20 ← "frame.kind != kind param"
  pin_frame_row21 ← "LEAK: sibling kind 1 inherits binder state"
  pin_frame_row22 ← "LEAK: sibling kind 15 inherits binder state"
  pin_frame_row23 ← "BINDER BREAK: kind 4 ctx not parent+1"
  pin_frame_row24 ← "BINDER BREAK: kind 6 ctx prefix mismatch"
  pin_frame_row25 ← "unknown form"
  pin_frame_row26 ← "LEN witness: kind 4 ctx=[] parent=[] (drop [] 1 = [] passes prefix; len 0≠1 breaks)"
  pin_frame_row27 ← "LEAK length-only killer: kind 1 ctx=[9,2,3] parent=[1,2,3] (equal length, unequal ctx)"
  pin_frame_row28 ← "18th-kind admission killer: kind 18 is UNKNOWN"
  pin_frame_row29 ← "FIELD kind pair (A): kind-param 3 matches frame.kind 3"
  pin_frame_row30 ← "FIELD frame.kind: kind-param 3 vs frame.kind 5 (differs from the A row at frame.kind alone)"
  pin_frame_row31 ← "FIELD form: form 1 over the A row's exact frame (differs at form alone)"
  pin_frame_row32 ← "FIELD ctx[1]: binder 4 ctx=[9,9,2,3] vs [9,1,2,3] at ctx[1] alone"
  pin_frame_row33 ← "FIELD ctx[2]: binder 4 ctx=[9,1,9,3] at ctx[2] alone"
  pin_frame_row34 ← "FIELD parent[0]: sibling 1 ctx=[1,2,3] parent=[9,2,3] at parent_ctx[0] alone"
  pin_frame_row35 ← "FIELD parent[1]: sibling 1 parent=[1,9,3]"
  pin_frame_row36 ← "FIELD parent[2]: sibling 1 parent=[1,2,9]"
  pin_frame_row37 ← "FIELD parent baseline: sibling 1 ctx=[1,2,3] parent=[1,2,3] ok"

M-007 retirement (GM-FRAME-002 deletes the non-binder leak arm;
APP.md: the mutant diverges on the leak rows only):
  leak rows 21, 22, 27, 34, 35, 36
      → retired-to-counterexample by `witness_leak` (row 21 sealed);
        the other five are #eval pins of the same residue.
  unknown-kind rows 17, 28
      → retired by `witness_unknown` (row 17 sealed).
  mismatch rows 20, 30
      → retired by `frameKindOk_mismatch`.
  unknown-form rows 25, 31
      → retired by `frameKindOk_unknown_form`.
  binder-break rows 23, 24, 26, 32, 33
      → retired by `witness_binder_break` (row 26 sealed);
        the other four are #eval pins of the same residue.
  accept rows 00–16, 18, 19, 29, 37
      → NAMED as not retired: they are accept pins, not teeth of
        GM-FRAME-002 (the mutant still accepts them).
  kernel_state_ok 8 rows
      → NAMED as not retired here: EXCLUDED BY LABEL (E-W).
-/
import rcic.RcicFrames

namespace Rcic.FramePins
open Rcic.Frames

-- 00 kind 1 once (ctx=parent)
#eval (if frameKindOk 0 ⟨1, [7, 8], [7, 8]⟩ 1 == none then 0 else panic "pin_frame_row00")
-- 01 kind 2 once (ctx=parent)
#eval (if frameKindOk 0 ⟨2, [7, 8], [7, 8]⟩ 2 == none then 1 else panic "pin_frame_row01")
-- 02 kind 3 once (ctx=parent)
#eval (if frameKindOk 0 ⟨3, [7, 8], [7, 8]⟩ 3 == none then 2 else panic "pin_frame_row02")
-- 03 kind 4 once (binder-extended)
#eval (if frameKindOk 0 ⟨4, [9, 1, 2, 3], [1, 2, 3]⟩ 4 == none then 3 else panic "pin_frame_row03")
-- 04 kind 5 once (binder-extended)
#eval (if frameKindOk 0 ⟨5, [9, 1, 2, 3], [1, 2, 3]⟩ 5 == none then 4 else panic "pin_frame_row04")
-- 05 kind 6 once (binder-extended)
#eval (if frameKindOk 0 ⟨6, [9, 1, 2, 3], [1, 2, 3]⟩ 6 == none then 5 else panic "pin_frame_row05")
-- 06 kind 7 once (ctx=parent)
#eval (if frameKindOk 0 ⟨7, [7, 8], [7, 8]⟩ 7 == none then 6 else panic "pin_frame_row06")
-- 07 kind 8 once (ctx=parent)
#eval (if frameKindOk 0 ⟨8, [7, 8], [7, 8]⟩ 8 == none then 7 else panic "pin_frame_row07")
-- 08 kind 9 once (ctx=parent)
#eval (if frameKindOk 0 ⟨9, [7, 8], [7, 8]⟩ 9 == none then 8 else panic "pin_frame_row08")
-- 09 kind 10 once (ctx=parent)
#eval (if frameKindOk 0 ⟨10, [7, 8], [7, 8]⟩ 10 == none then 9 else panic "pin_frame_row09")
-- 10 kind 11 once (ctx=parent)
#eval (if frameKindOk 0 ⟨11, [7, 8], [7, 8]⟩ 11 == none then 10 else panic "pin_frame_row10")
-- 11 kind 12 once (ctx=parent)
#eval (if frameKindOk 0 ⟨12, [7, 8], [7, 8]⟩ 12 == none then 11 else panic "pin_frame_row11")
-- 12 kind 13 once (ctx=parent)
#eval (if frameKindOk 0 ⟨13, [7, 8], [7, 8]⟩ 13 == none then 12 else panic "pin_frame_row12")
-- 13 kind 14 once (ctx=parent)
#eval (if frameKindOk 0 ⟨14, [7, 8], [7, 8]⟩ 14 == none then 13 else panic "pin_frame_row13")
-- 14 kind 15 once (ctx=parent)
#eval (if frameKindOk 0 ⟨15, [7, 8], [7, 8]⟩ 15 == none then 14 else panic "pin_frame_row14")
-- 15 kind 16 once (ctx=parent)
#eval (if frameKindOk 0 ⟨16, [7, 8], [7, 8]⟩ 16 == none then 15 else panic "pin_frame_row15")
-- 16 kind 17 once (ctx=parent)
#eval (if frameKindOk 0 ⟨17, [7, 8], [7, 8]⟩ 17 == none then 16 else panic "pin_frame_row16")
-- 17 unknown kind 99
#eval (if frameKindOk 0 ⟨99, [1], [1]⟩ 99 == some residueUnknown then 17 else panic "pin_frame_row17")
-- 18 extension kind 16 is known (C1 ext)
#eval (if frameKindOk 0 ⟨16, [1], [1]⟩ 16 == none then 18 else panic "pin_frame_row18")
-- 19 extension kind 17 is known (C1 ext)
#eval (if frameKindOk 0 ⟨17, [2], [2]⟩ 17 == none then 19 else panic "pin_frame_row19")
-- 20 frame.kind != kind param
#eval (if frameKindOk 0 ⟨3, [1], [1]⟩ 5 == some residueMismatch then 20 else panic "pin_frame_row20")
-- 21 LEAK: sibling kind 1 inherits binder state
#eval (if frameKindOk 0 ⟨1, [1, 2, 3, 4], [1, 2, 3]⟩ 1 == some residueBinderLeak then 21 else panic "pin_frame_row21")
-- 22 LEAK: sibling kind 15 inherits binder state
#eval (if frameKindOk 0 ⟨15, [1, 2, 9], [1, 2]⟩ 15 == some residueBinderLeak then 22 else panic "pin_frame_row22")
-- 23 BINDER BREAK: kind 4 ctx not parent+1
#eval (if frameKindOk 0 ⟨4, [1, 2, 3], [1, 2, 3]⟩ 4 == some residueBinderBreak then 23 else panic "pin_frame_row23")
-- 24 BINDER BREAK: kind 6 ctx prefix mismatch
#eval (if frameKindOk 0 ⟨6, [9, 1, 2, 9], [1, 2, 3]⟩ 6 == some residueBinderBreak then 24 else panic "pin_frame_row24")
-- 25 unknown form
#eval (if frameKindOk 1 ⟨1, [1], [1]⟩ 1 == some residueUnknownForm then 25 else panic "pin_frame_row25")
-- 26 LEN witness: kind 4 ctx=[] parent=[]
#eval (if frameKindOk 0 ⟨4, [], []⟩ 4 == some residueBinderBreak then 26 else panic "pin_frame_row26")
-- 27 LEAK length-only killer
#eval (if frameKindOk 0 ⟨1, [9, 2, 3], [1, 2, 3]⟩ 1 == some residueBinderLeak then 27 else panic "pin_frame_row27")
-- 28 18th-kind admission killer
#eval (if frameKindOk 0 ⟨18, [1], [1]⟩ 18 == some residueUnknown then 28 else panic "pin_frame_row28")
-- 29 FIELD kind pair (A)
#eval (if frameKindOk 0 ⟨3, [1], [1]⟩ 3 == none then 29 else panic "pin_frame_row29")
-- 30 FIELD frame.kind
#eval (if frameKindOk 0 ⟨5, [1], [1]⟩ 3 == some residueMismatch then 30 else panic "pin_frame_row30")
-- 31 FIELD form
#eval (if frameKindOk 1 ⟨3, [1], [1]⟩ 3 == some residueUnknownForm then 31 else panic "pin_frame_row31")
-- 32 FIELD ctx[1]
#eval (if frameKindOk 0 ⟨4, [9, 9, 2, 3], [1, 2, 3]⟩ 4 == some residueBinderBreak then 32 else panic "pin_frame_row32")
-- 33 FIELD ctx[2]
#eval (if frameKindOk 0 ⟨4, [9, 1, 9, 3], [1, 2, 3]⟩ 4 == some residueBinderBreak then 33 else panic "pin_frame_row33")
-- 34 FIELD parent[0]
#eval (if frameKindOk 0 ⟨1, [1, 2, 3], [9, 2, 3]⟩ 1 == some residueBinderLeak then 34 else panic "pin_frame_row34")
-- 35 FIELD parent[1]
#eval (if frameKindOk 0 ⟨1, [1, 2, 3], [1, 9, 3]⟩ 1 == some residueBinderLeak then 35 else panic "pin_frame_row35")
-- 36 FIELD parent[2]
#eval (if frameKindOk 0 ⟨1, [1, 2, 3], [1, 2, 9]⟩ 1 == some residueBinderLeak then 36 else panic "pin_frame_row36")
-- 37 FIELD parent baseline
#eval (if frameKindOk 0 ⟨1, [1, 2, 3], [1, 2, 3]⟩ 1 == none then 37 else panic "pin_frame_row37")

end Rcic.FramePins

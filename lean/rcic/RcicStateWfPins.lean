/-
Annex 23 UNIT H-8b — M-002 pins through the payload.
Each pin: a `#eval` whose input is the row's RawTask payload
decoded (`taskDecode` reuses `exprDecode` / `levelDecode`)
into `Rcic.Machine.RawTask`, then `stateWellFormed` against
`expected`. Hand-transcribed per §18.3 rule 4.

CARRIER: apps/rcic-state-wellformed/rcic_state_wellformed_corpus.json
  (36 rows). before/after (M-009): 36 rows → 36 transcribed
  + 0 excluded. 31 compare `stateWellFormed` to `expected`.
  5 pin the named WALL: tag 7 (`levelInfer` / `03` §3
  `CheckLevel`) has no `RawTask` constructor (TREE WINS);
  `taskDecode` is `none` (rows 03, 05, 08, 10, 16).

TRANSCRIPTION TABLE (fixture ← corpus label, exact strings):
  pin_sw_row00 ← "empty chain, infer terminal — wf"
  pin_sw_row01 ← "single InferAppFunction (0,0) on infer"
  pin_sw_row02 ← "single InferPiDomain (0,1) on infer"
  pin_sw_row03 ← "single CheckExpectedSort (1,2) on levelInfer"
  pin_sw_row04 ← "single CheckInferred (0,2) on infer"
  pin_sw_row05 ← "single LevelCursor (1,1) on levelInfer"
  pin_sw_row06 ← "single LookupDeclarationFrame (3,0) on lookupDeclaration"
  pin_sw_row07 ← "single DecisionSinkFrame (2,0) on check"
  pin_sw_row08 ← "compatible pair LevelCursor,LevelCursor on levelInfer"
  pin_sw_row09 ← "INCOMPATIBLE bool->expr: CheckInferred then InferAppFunction"
  pin_sw_row10 ← "INCOMPATIBLE level->decl: LevelCursor then LookupDeclarationFrame"
  pin_sw_row11 ← "INCOMPATIBLE expr->bool: InferAppFunction then DecisionSinkFrame"
  pin_sw_row12 ← "unknown frame kind 99"
  pin_sw_row13 ← "unknown form 1"
  pin_sw_row14 ← "unknown task 99 on the EMPTY chain (the only reachable shape)"
  pin_sw_row15 ← "teeth: InferPiDomain.out observed (LevelCursor resumes it)"
  pin_sw_row16 ← "teeth: CheckExpectedSort.out observed (DecisionSink resumes it)"
  pin_sw_row17 ← "teeth: LookupDeclarationFrame.out observed (InferAppFunction resumes it)"
  pin_sw_row18 ← "teeth: DecisionSinkFrame.out observed (InferAppFunction resumes it)"
  pin_sw_row19 ← "teeth: task whnfAt(0)->expr observed"
  pin_sw_row20 ← "teeth: task convAt(1)->bool observed"
  pin_sw_row21 ← "teeth: task lookupLocal(5)->expr observed"
  pin_sw_row22 ← "teeth: task levelEqual(6)->bool observed"
  pin_sw_row23 ← "teeth: task syntaxEqual(8)->bool observed"
  pin_sw_row24 ← "teeth: InferAppFunction.out observed (another InferAppFunction resumes it)"
  pin_sw_row25 ← "teeth: CheckInferred.out observed (DecisionSink resumes it)"
  pin_sw_row26 ← "widening witness: kind 2 (0,0) accepted, out pinned by InferAppFunction"
  pin_sw_row27 ← "widening witness: kind 4 (0,0)"
  pin_sw_row28 ← "widening witness: kind 6 (0,0)"
  pin_sw_row29 ← "widening witness: kind 9 (0,0)"
  pin_sw_row30 ← "widening witness: kind 10 (0,0)"
  pin_sw_row31 ← "widening witness: kind 11 (0,0)"
  pin_sw_row32 ← "widening witness: kind 12 (0,0)"
  pin_sw_row33 ← "widening witness: kind 13 (0,0)"
  pin_sw_row34 ← "widening witness: kind 14 (0,0)"
  pin_sw_row35 ← "widening witness: kind 5 (0,1) out pinned by LevelCursor"

M-007 (GM-FRAME-001 weakens ONLY the mismatch arm; 3 divergences):
  mismatch rows 09, 11 → retired by `witness_mismatch_bool_expr`
    (row 09 sealed); row 10 is the CheckLevel WALL, not a
    mismatch pin of a representable task.
  unknown-frame 12 → `witness_unknown_frame`.
  unknown-form 13 → `witness_unknown_form`.
  unknown-task 14 → `witness_unknown_task`.
  accept rows 00–02, 04, 06–07, 15, 17–35 → NAMED as not
    retired (accept pins, not teeth of GM-FRAME-001).
  WALL rows 03, 05, 08, 10, 16 → named form, not a mutant tooth.

DECODER ADAPTER (defined once; KernelStepRawPins reuses it).
`exprDecode : ExprWire → Expr String`; `RawTask` consumes
`Expr Nat`. String refs map to `0`. Tag 7 (`levelInfer` /
`03` §3 `CheckLevel`) has no constructor: `taskDecode` is
`none`.
-/
import rcic.RcicStateWf
import rcic.RcicExprSubstTask

namespace Rcic.TaskPayloadDecode
open Rcic.Declarative
open Rcic.ExprSubstTask
open Rcic.Machine (RawTask)

/-- String `const` / lookupDeclaration ref → Nat. Always `0`. -/
def constRefNat (_s : String) : Nat := 0

/-- Reuse `exprDecode`; land the `Expr Nat` `RawTask` consumes. -/
def exprNat : Expr String → Expr Nat
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const _r ls => .const (constRefNat _r) ls
  | .app f x => .app (exprNat f) (exprNat x)
  | .lam a b => .lam (exprNat a) (exprNat b)
  | .pi a b => .pi (exprNat a) (exprNat b)
  | .letE a v b => .letE (exprNat a) (exprNat v) (exprNat b)
  | .lit n => .lit n

def exprDecodeNat (e : ExprWire) : Expr Nat :=
  exprNat (exprDecode e)

/-- Carrier control.task kind-record (APP.md payload table). -/
inductive TaskWire : Type
  | whnfAt (a e : ExprWire)
  | convAt (a l r : ExprWire)
  | infer (e : ExprWire)
  | check (e a : ExprWire)
  | lookupDeclaration (ref : String) (ls : List LevelWire)
  | lookupLocal (i : Int)
  | levelEqual (l1 l2 : LevelWire)
  | levelInfer (l : LevelWire)
  | syntaxEqual (a b : ExprWire)
  | other (tag : Nat)
  deriving DecidableEq

/-- Tag 7 → `none`. Other unknown tags → `convType` (taskTag 9,
outside C1 0..8; `taskIo` refuses). -/
def taskDecode : TaskWire → Option RawTask
  | .whnfAt a e =>
    some (.whnfAt (exprDecodeNat a) (exprDecodeNat e))
  | .convAt a l r =>
    some (.convAt (exprDecodeNat a) (exprDecodeNat l)
      (exprDecodeNat r))
  | .infer e => some (.infer (exprDecodeNat e))
  | .check e a =>
    some (.check (exprDecodeNat e) (exprDecodeNat a))
  | .lookupDeclaration ref ls =>
    some (.lookupDeclaration (constRefNat ref)
      (ls.map levelDecode))
  | .lookupLocal i => some (.lookupLocal i.toNat)
  | .levelEqual l1 l2 =>
    some (.levelEqual (levelDecode l1) (levelDecode l2))
  | .levelInfer _l => none
  | .syntaxEqual a b =>
    some (.syntaxEqual (exprDecodeNat a) (exprDecodeNat b))
  | .other _tag =>
    some (.convType (exprDecodeNat (.sort .zero))
      (exprDecodeNat (.sort .zero)))

end Rcic.TaskPayloadDecode

namespace Rcic.StateWfPins
open Rcic.StateWf
open Rcic.TaskPayloadDecode
open Rcic.ExprSubstTask (ExprWire LevelWire)

-- 00 empty chain, infer terminal — wf
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row00"
  | some t =>
    if stateWellFormed 0 (mkTask t []) == none then 0
    else panic "pin_sw_row00"
-- 01 single InferAppFunction (0,0) on infer
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row01"
  | some t =>
    if stateWellFormed 0 (mkTask t [1]) == none then 1
    else panic "pin_sw_row01"
-- 02 single InferPiDomain (0,1) on infer
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row02"
  | some t =>
    if stateWellFormed 0 (mkTask t [3]) == none then 2
    else panic "pin_sw_row02"
-- 03 WALL: CheckLevel / levelInfer has no RawTask constructor
#eval
  match taskDecode (.levelInfer LevelWire.zero) with
  | none => 3
  | some _ => panic "pin_sw_row03"
-- 04 single CheckInferred (0,2) on infer
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row04"
  | some t =>
    if stateWellFormed 0 (mkTask t [8]) == none then 4
    else panic "pin_sw_row04"
-- 05 WALL: CheckLevel / levelInfer has no RawTask constructor
#eval
  match taskDecode (.levelInfer LevelWire.zero) with
  | none => 5
  | some _ => panic "pin_sw_row05"
-- 06 single LookupDeclarationFrame (3,0) on lookupDeclaration
#eval
  match taskDecode (.lookupDeclaration "Nat.add"
      [LevelWire.zero, LevelWire.param 0]) with
  | none => panic "pin_sw_row06"
  | some t =>
    if stateWellFormed 0 (mkTask t [16]) == none then 6
    else panic "pin_sw_row06"
-- 07 single DecisionSinkFrame (2,0) on check
#eval
  match taskDecode (.check (ExprWire.bvar 0)
      (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row07"
  | some t =>
    if stateWellFormed 0 (mkTask t [17]) == none then 7
    else panic "pin_sw_row07"
-- 08 WALL: CheckLevel / levelInfer has no RawTask constructor
#eval
  match taskDecode (.levelInfer LevelWire.zero) with
  | none => 8
  | some _ => panic "pin_sw_row08"
-- 09 INCOMPATIBLE bool->expr
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row09"
  | some t =>
    if stateWellFormed 0 (mkTask t [8, 1])
        == some residueMismatch then 9
    else panic "pin_sw_row09"
-- 10 WALL: CheckLevel / levelInfer has no RawTask constructor
#eval
  match taskDecode (.levelInfer LevelWire.zero) with
  | none => 10
  | some _ => panic "pin_sw_row10"
-- 11 INCOMPATIBLE expr->bool
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row11"
  | some t =>
    if stateWellFormed 0 (mkTask t [1, 17])
        == some residueMismatch then 11
    else panic "pin_sw_row11"
-- 12 unknown frame kind 99
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row12"
  | some t =>
    if stateWellFormed 0 (mkTask t [99])
        == some residueUnknownFrame then 12
    else panic "pin_sw_row12"
-- 13 unknown form 1
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row13"
  | some t =>
    if stateWellFormed 1 (mkTask t [1])
        == some residueUnknownForm then 13
    else panic "pin_sw_row13"
-- 14 unknown task 99 on the EMPTY chain
#eval
  match taskDecode (.other 99) with
  | none => panic "pin_sw_row14"
  | some t =>
    if stateWellFormed 0 (mkTask t [])
        == some residueUnknownTask then 14
    else panic "pin_sw_row14"
-- 15 teeth: InferPiDomain.out observed
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row15"
  | some t =>
    if stateWellFormed 0 (mkTask t [3, 15]) == none then 15
    else panic "pin_sw_row15"
-- 16 WALL: CheckLevel / levelInfer has no RawTask constructor
#eval
  match taskDecode (.levelInfer LevelWire.zero) with
  | none => 16
  | some _ => panic "pin_sw_row16"
-- 17 teeth: LookupDeclarationFrame.out observed
#eval
  match taskDecode (.lookupDeclaration "Nat.add"
      [LevelWire.zero, LevelWire.param 0]) with
  | none => panic "pin_sw_row17"
  | some t =>
    if stateWellFormed 0 (mkTask t [16, 1]) == none then 17
    else panic "pin_sw_row17"
-- 18 teeth: DecisionSinkFrame.out observed
#eval
  match taskDecode (.check (ExprWire.bvar 0)
      (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row18"
  | some t =>
    if stateWellFormed 0 (mkTask t [17, 1]) == none then 18
    else panic "pin_sw_row18"
-- 19 teeth: task whnfAt(0)->expr
#eval
  match taskDecode (.whnfAt (ExprWire.sort LevelWire.zero)
      (ExprWire.bvar 0)) with
  | none => panic "pin_sw_row19"
  | some t =>
    if stateWellFormed 0 (mkTask t [1]) == none then 19
    else panic "pin_sw_row19"
-- 20 teeth: task convAt(1)->bool
#eval
  match taskDecode (.convAt (ExprWire.sort LevelWire.zero)
      (ExprWire.bvar 0) (ExprWire.bvar 1)) with
  | none => panic "pin_sw_row20"
  | some t =>
    if stateWellFormed 0 (mkTask t [17]) == none then 20
    else panic "pin_sw_row20"
-- 21 teeth: task lookupLocal(5)->expr
#eval
  match taskDecode (.lookupLocal 0) with
  | none => panic "pin_sw_row21"
  | some t =>
    if stateWellFormed 0 (mkTask t [1]) == none then 21
    else panic "pin_sw_row21"
-- 22 teeth: task levelEqual(6)->bool
#eval
  match taskDecode (.levelEqual (LevelWire.succ LevelWire.zero)
      (LevelWire.succ LevelWire.zero)) with
  | none => panic "pin_sw_row22"
  | some t =>
    if stateWellFormed 0 (mkTask t [17]) == none then 22
    else panic "pin_sw_row22"
-- 23 teeth: task syntaxEqual(8)->bool
#eval
  match taskDecode (.syntaxEqual (ExprWire.bvar 0)
      (ExprWire.bvar 0)) with
  | none => panic "pin_sw_row23"
  | some t =>
    if stateWellFormed 0 (mkTask t [17]) == none then 23
    else panic "pin_sw_row23"
-- 24 teeth: InferAppFunction.out observed
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row24"
  | some t =>
    if stateWellFormed 0 (mkTask t [1, 1]) == none then 24
    else panic "pin_sw_row24"
-- 25 teeth: CheckInferred.out observed
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row25"
  | some t =>
    if stateWellFormed 0 (mkTask t [8, 17]) == none then 25
    else panic "pin_sw_row25"
-- 26 widening witness: kind 2 (0,0)
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row26"
  | some t =>
    if stateWellFormed 0 (mkTask t [2, 1]) == none then 26
    else panic "pin_sw_row26"
-- 27 widening witness: kind 4 (0,0)
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row27"
  | some t =>
    if stateWellFormed 0 (mkTask t [4, 1]) == none then 27
    else panic "pin_sw_row27"
-- 28 widening witness: kind 6 (0,0)
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row28"
  | some t =>
    if stateWellFormed 0 (mkTask t [6, 1]) == none then 28
    else panic "pin_sw_row28"
-- 29 widening witness: kind 9 (0,0)
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row29"
  | some t =>
    if stateWellFormed 0 (mkTask t [9, 1]) == none then 29
    else panic "pin_sw_row29"
-- 30 widening witness: kind 10 (0,0)
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row30"
  | some t =>
    if stateWellFormed 0 (mkTask t [10, 1]) == none then 30
    else panic "pin_sw_row30"
-- 31 widening witness: kind 11 (0,0)
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row31"
  | some t =>
    if stateWellFormed 0 (mkTask t [11, 1]) == none then 31
    else panic "pin_sw_row31"
-- 32 widening witness: kind 12 (0,0)
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row32"
  | some t =>
    if stateWellFormed 0 (mkTask t [12, 1]) == none then 32
    else panic "pin_sw_row32"
-- 33 widening witness: kind 13 (0,0)
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row33"
  | some t =>
    if stateWellFormed 0 (mkTask t [13, 1]) == none then 33
    else panic "pin_sw_row33"
-- 34 widening witness: kind 14 (0,0)
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row34"
  | some t =>
    if stateWellFormed 0 (mkTask t [14, 1]) == none then 34
    else panic "pin_sw_row34"
-- 35 widening witness: kind 5 (0,1) out pinned by LevelCursor
#eval
  match taskDecode (.infer (ExprWire.sort LevelWire.zero)) with
  | none => panic "pin_sw_row35"
  | some t =>
    if stateWellFormed 0 (mkTask t [5, 15]) == none then 35
    else panic "pin_sw_row35"

end Rcic.StateWfPins

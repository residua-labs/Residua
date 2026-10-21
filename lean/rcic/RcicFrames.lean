/-
Annex 22 UNIT E-F — `03` §5's frame machine, quoted.
Pinned to `apps/rcic-kernel-frames/` (`rcic_frame_kind_ok`).
Does NOT quote `03` §3 LiftExpr/InstantiateExpr (22.E.4).
Does NOT reclassify any A3 cell (22.E.3 (i)).
`kernel_state_ok` is a WRAPPER over C1 `StateWellFormed` (E-W);
those corpus rows are EXCLUDED BY LABEL in RcicFramePins.lean.

TRANSCRIPTION TABLE (`03_REFERENCE_MACHINE.md` on this unit's base
`17a35b5d0`, lines re-taken):
  03:128 heading          — this file
  03:130 consumes/produces + numeric tags + StateWellFormed
                          chain — `ResultKind`, `frameIo`, comment
                          on `StateWellFormed` (predicate is E-W)
  03:132-150 Examples     — `FrameKind` 1..15; NOT closed
  03:152 Boolean/level    — `resumeOk`
  03:154 binder protocol  — `isBinderKind`, `frameKindOk`
C2 recorded extensions (APP.md; not 03-closed): kinds 16
`LookupDeclarationFrame`, 17 `DecisionSinkFrame`.
No clause of §5 is dropped. No clause is added from §3.

closure_claim stays 0.
-/
namespace Rcic.Frames

/-- 03:130 "Each frame consumes one result kind and produces another."
Numeric tags on the wire; compatibility of the chain is `StateWellFormed`
(E-W). Encoding of the four tags is C1/C2's `rcic.frame_io` (03 does not
tabulate (in,out)): 0 expr / 1 level / 2 bool / 3 decl
(`apps/rcic-state-wellformed/APP.md` "Encoding decisions").
A first drafting of this file swapped the names of tags 1 and 2
against that table and against 03:152's two pairs; the `frameIo`
NUMBERS were already the carrier's. Corrected here. -/
inductive ResultKind : Type
  | expr   -- 0
  | level  -- 1
  | bool   -- 2  (03:152 "Boolean result")
  | decl   -- 3
  deriving DecidableEq, Repr

def ResultKind.toNat : ResultKind → Nat
  | .expr => 0 | .level => 1 | .bool => 2 | .decl => 3

def ResultKind.fromNat : Nat → Option ResultKind
  | 0 => some .expr | 1 => some .level | 2 => some .bool | 3 => some .decl
  | _ => none

/-- 03:132-149 Examples, plus C2's two recorded extensions 16/17.
03:132 says "Examples:" and NOT closed. -/
inductive FrameKind : Type
  | inferAppFunction      -- 1
  | inferAppArgument      -- 2
  | inferPiDomain         -- 3
  | inferPiCodomain       -- 4 binder
  | inferLambdaDomain     -- 5 binder
  | inferLambdaBody       -- 6 binder
  | checkExpectedSort     -- 7
  | checkInferred         -- 8
  | whnfSpine             -- 9
  | convLeftWhnf          -- 10
  | convRightWhnf         -- 11
  | convBinder            -- 12
  | liftCursor            -- 13
  | substitutionCursor    -- 14
  | levelCursor           -- 15
  | lookupDeclaration     -- 16 C2 ext
  | decisionSink          -- 17 C2 ext
  deriving DecidableEq, Repr

def FrameKind.toNat : FrameKind → Nat
  | .inferAppFunction => 1 | .inferAppArgument => 2 | .inferPiDomain => 3
  | .inferPiCodomain => 4 | .inferLambdaDomain => 5 | .inferLambdaBody => 6
  | .checkExpectedSort => 7 | .checkInferred => 8 | .whnfSpine => 9
  | .convLeftWhnf => 10 | .convRightWhnf => 11 | .convBinder => 12
  | .liftCursor => 13 | .substitutionCursor => 14 | .levelCursor => 15
  | .lookupDeclaration => 16 | .decisionSink => 17

def frameKindKnown (k : Nat) : Bool := 1 ≤ k && k ≤ 17

def FrameKind.fromNat : Nat → Option FrameKind
  | 1 => some .inferAppFunction | 2 => some .inferAppArgument
  | 3 => some .inferPiDomain | 4 => some .inferPiCodomain
  | 5 => some .inferLambdaDomain | 6 => some .inferLambdaBody
  | 7 => some .checkExpectedSort | 8 => some .checkInferred
  | 9 => some .whnfSpine | 10 => some .convLeftWhnf
  | 11 => some .convRightWhnf | 12 => some .convBinder
  | 13 => some .liftCursor | 14 => some .substitutionCursor
  | 15 => some .levelCursor | 16 => some .lookupDeclaration
  | 17 => some .decisionSink | _ => none

/-- C1/C2 `rcic.frame_io`. 03 does not tabulate (in,out).
Numbers match `scm/rcic/frame_io.scm` byte-for-byte as tags. -/
def frameIo : FrameKind → ResultKind × ResultKind
  | .inferAppFunction => (.expr, .expr)
  | .inferAppArgument => (.expr, .expr)
  | .inferPiDomain => (.expr, .level)
  | .inferPiCodomain => (.expr, .expr)
  | .inferLambdaDomain => (.expr, .level)
  | .inferLambdaBody => (.expr, .expr)
  | .checkExpectedSort => (.level, .bool)
  | .checkInferred => (.expr, .bool)
  | .whnfSpine => (.expr, .expr)
  | .convLeftWhnf => (.expr, .expr)
  | .convRightWhnf => (.expr, .expr)
  | .convBinder => (.expr, .expr)
  | .liftCursor => (.expr, .expr)
  | .substitutionCursor => (.expr, .expr)
  | .levelCursor => (.level, .level)
  | .lookupDeclaration => (.decl, .expr)
  | .decisionSink => (.bool, .expr)

/-- 03:152 — a Boolean result cannot resume an expression frame;
a level result cannot resume a declaration frame.
Carrier pairs: bool→expr is tag 2→0 (corpus row 09, CheckInferred then
InferAppFunction); level→decl is tag 1→3 (row 10, LevelCursor then
LookupDeclaration). -/
def resumeOk (got : ResultKind) (want : ResultKind) : Bool := got == want

/-- 03:154 binder kinds: InferPiCodomain / InferLambdaDomain / InferLambdaBody.
Carrier encoding: kinds 4/5/6. -/
def isBinderKind (k : Nat) : Bool := k == 4 || k == 5 || k == 6

/-- Carrier frame: newest-first ctx (de Bruijn); binder PREPENDS. -/
structure Frame where
  kind : Nat
  ctx : List Nat
  parentCtx : List Nat
  deriving Repr, DecidableEq

/-- Residues named in `scm/rcic/frame_kind_ok.scm`. -/
def residueUnknownForm : String := "[rcic_kernel_frames_unknown_form]"
def residueMismatch : String := "[rcic_frame_kind_mismatch]"
def residueUnknown : String := "[rcic_frame_kind_unknown]"
def residueBinderBreak : String := "[rcic_frame_kind_binder_break]"
def residueBinderLeak : String := "[rcic_frame_kind_binder_leak]"

/-- `rcic.frame_kind_ok`: none = accept, some code = refuse. -/
def frameKindOk (form : Nat) (frame : Frame) (kind : Nat) : Option String :=
  if form != 0 then some residueUnknownForm
  else if frame.kind != kind then some residueMismatch
  else if !frameKindKnown kind then some residueUnknown
  else if isBinderKind kind then
    if frame.ctx.length == frame.parentCtx.length + 1 &&
       frame.ctx.drop 1 == frame.parentCtx then none
    else some residueBinderBreak
  else if frame.ctx == frame.parentCtx then none
  else some residueBinderLeak

/-! ### Sealed facts (M-005 witnesses below) -/

theorem frameKindKnown_iff (k : Nat) :
    frameKindKnown k = true ↔ 1 ≤ k ∧ k ≤ 17 := by
  simp [frameKindKnown, decide_eq_true_iff]

theorem isBinderKind_iff (k : Nat) :
    isBinderKind k = true ↔ k = 4 ∨ k = 5 ∨ k = 6 := by
  unfold isBinderKind
  constructor
  · intro h; simpa [or_assoc] using h
  · intro h; simpa [or_assoc] using h

theorem frameKindOk_unknown_form (form : Nat) (frame : Frame) (kind : Nat)
    (h : form ≠ 0) :
    frameKindOk form frame kind = some residueUnknownForm := by
  simp [frameKindOk, h]

theorem frameKindOk_mismatch (form : Nat) (frame : Frame) (kind : Nat)
    (hf : form = 0) (hm : frame.kind ≠ kind) :
    frameKindOk form frame kind = some residueMismatch := by
  simp [frameKindOk, hf, hm]

theorem resumeOk_bool_not_expr :
    resumeOk .bool .expr = false := rfl

theorem resumeOk_level_not_decl :
    resumeOk .level .decl = false := rfl

/-- M-005: closed inhabitation, kind 1, ctx = parent. -/
def witness_kind1 : Frame := ⟨1, [7, 8], [7, 8]⟩

theorem witness_kind1_ok :
    frameKindOk 0 witness_kind1 1 = none := rfl

/-- M-005: binder kind 4, ctx = 9 :: parent. -/
def witness_binder4 : Frame := ⟨4, [9, 1, 2, 3], [1, 2, 3]⟩

theorem witness_binder4_ok :
    frameKindOk 0 witness_binder4 4 = none := rfl

/-- M-005: unknown kind refuses. -/
theorem witness_unknown :
    frameKindOk 0 ⟨99, [1], [1]⟩ 99 = some residueUnknown := rfl

/-- M-005: leak refuses. -/
theorem witness_leak :
    frameKindOk 0 ⟨1, [1, 2, 3, 4], [1, 2, 3]⟩ 1 = some residueBinderLeak := rfl

/-- M-005 / M-007: binder-break refuses (corpus row 26, empty ctx). -/
theorem witness_binder_break :
    frameKindOk 0 ⟨4, [], []⟩ 4 = some residueBinderBreak := rfl

end Rcic.Frames

/-
Annex 22 UNIT E-D — `03` §9 `decodeWireState`, quoted.
Pinned to `apps/rcic-wire-decode/` (`rcic_wire_decode`).
22.E.10 amendment 4: quotes `decodeWireState` and `RawKernelState`
(plus `StateDecodeIntegrity`). Does NOT quote `KernelState`.
22.E.3 (vii): raw wire decode DOES NOT MINT well-formed state —
a mismatch chain that E-W refuses is still a successful decode.

TRANSCRIPTION TABLE (`03_REFERENCE_MACHINE.md` on this unit's base
`5f8d7bf6c`, lines re-taken):
  03:246 decodeWireState : Bytes → Result RawKernelState
         StateDecodeIntegrity — `decodeWireState`
  03:250 validates canonical tags, payload shapes, typed
         references, integer bounds, frame tag syntax, and
         exact re-encoding — fold + `wireTagOk` + `wireValueOk`
         + task/frame tables
  03:250 "It does **not** mint `KernelState`" — result is
         `RawKernelState`; `decode_mismatch_is_raw` is the
         STOP (vii) witness (E-W refuses the same chain)
No clause of the §9 decoder block is dropped. `validateReachableState`
is E-R (named, not quoted).

closure_claim stays 0.
-/
import rcic.RcicStateWf

namespace Rcic.WireDecode
open Rcic.StateWf
open Rcic.Frames

inductive DecodeResult : Type
  | ok (st : RawKernelState)
  | refuse (code : String)
  deriving DecidableEq

def residueBadShape : String := "[rcic_wire_bad_shape]"
def residueNoncanonical : String := "[rcic_wire_noncanonical_value]"
def residueUnknownTask : String := "[rcic_wire_unknown_task]"
def residueUnknownFrame : String := "[rcic_wire_unknown_frame_tag]"
def residueUnknownForm : String := "[rcic_wire_unknown_form]"

/-- C3 `rcic.value_at_digits_ok` — over `List Char` so theorems reduce. -/
def digitsOk : List Char → Bool
  | [] => false
  | cs => cs.all fun c => '0' ≤ c && c ≤ '9'

def decCanonical (cs : List Char) : Bool :=
  cs.length ≤ 63 && digitsOk cs && (cs = ['0'] || cs.headD ' ' ≠ '0')

def parseNat (cs : List Char) : Nat :=
  cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- C3 `rcic.wire_value_ok`: canonical decimal in 0..99. -/
def wireValueOk (cs : List Char) : Bool :=
  if !decCanonical cs then false else parseNat cs ≤ 99

/-- C3 `rcic.wire_tag_ok`: `t:` or `f:` and nonempty value. -/
def wireTagOk : List Char → Bool
  | k :: ':' :: rest => (k == 't' || k == 'f') && rest ≠ []
  | _ => false

structure FoldAcc where
  status : Nat      -- 1 ok, 0 bad_shape, 2 noncanonical
  task : Nat
  frames : List Nat
  started : Bool
  deriving Repr

def foldStep (acc : FoldAcc) (p : List Char) : FoldAcc :=
  if acc.status != 1 then acc
  else if !wireTagOk p then ⟨0, 0, [], acc.started⟩
  else
    let k := p.headD ' '
    let v := p.drop 2
    if !wireValueOk v then ⟨2, 0, [], acc.started⟩
    else
      let n := parseNat v
      if k == 't' then
        if !acc.started then ⟨1, n, acc.frames, true⟩
        else ⟨0, 0, [], true⟩
      else
        if acc.started then ⟨1, acc.task, acc.frames ++ [n], true⟩
        else ⟨0, 0, [], true⟩

/-- C3 `rcic.wire_decode_fold` over already-split parts (reduces). -/
def decodeParts (form : Nat) (parts : List (List Char)) : DecodeResult :=
  if form != 0 then .refuse residueUnknownForm
  else
    let acc := parts.foldl foldStep ⟨1, 0, [], false⟩
    if acc.status == 2 then .refuse residueNoncanonical
    else if acc.status != 1 || !acc.started then .refuse residueBadShape
    else
      match taskIo acc.task with
      | none => .refuse residueUnknownTask
      | some tkn =>
        if hrt : taskTag (taskOfTag acc.task) = acc.task then
          match frameChainOk (some tkn) acc.frames with
          | .unknownFrame => .refuse residueUnknownFrame
          | _ => .ok (mk acc.task acc.frames)
        else
          .refuse residueUnknownTask

/-- 03:246. Bytes entry; `|` split is the carrier's part convention.
Theorems pin `decodeParts` (the split is not kernel-reducible). -/
def decodeWireState (form : Nat) (bytes : String) : DecodeResult :=
  decodeParts form ((bytes.splitOn "|").map String.toList)

/-! ### Sealed facts (on the reducible `decodeParts`) -/

theorem witness_accept :
    decodeParts 0 [['t', ':', '2'], ['f', ':', '1']] = .ok (mk 2 [1]) := rfl

theorem witness_noncanonical :
    decodeParts 0 [['t', ':', '0', '2'], ['f', ':', '1']] = .refuse residueNoncanonical := rfl

theorem witness_bad_shape :
    decodeParts 0 [['t'], ['f', ':', '1']] = .refuse residueBadShape := rfl

theorem witness_unknown_task :
    decodeParts 0 [['t', ':', '9', '9'], ['f', ':', '1']] = .refuse residueUnknownTask := rfl

theorem witness_unknown_frame :
    decodeParts 0 [['t', ':', '2'], ['f', ':', '4', '2']] = .refuse residueUnknownFrame := rfl

theorem witness_unknown_form :
    decodeParts 1 [['t', ':', '2'], ['f', ':', '1']] = .refuse residueUnknownForm := rfl

/-- STOP (vii): a chain E-W refuses as mismatch is still a raw decode. -/
theorem decode_mismatch_is_raw :
    decodeParts 0 [['t', ':', '2'], ['f', ':', '8'], ['f', ':', '1']] = .ok (mk 2 [8, 1]) := rfl

theorem decode_mismatch_not_wf :
    stateWellFormed 0 (mk 2 [8, 1]) = some StateWf.residueMismatch := rfl

end Rcic.WireDecode

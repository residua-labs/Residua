/-
WX statement bridge S2 segment 2, Lean pins for slice `control-br`
(Coq side: `coq/wasm_target/Control.v`, relational derivations over
`Wasm.opsem.reduce` under a minimal vacuous local host over Memory_list,
recorded in the table's `trust_base_enlargement`). Rows mirror
`conformance/wasm_target_table/table.json` slice `control-br`: block
entry/exit by falling off the end, `br 0` exiting through the block
label, `br_if` false arm with no branch. The join is the final run
value (`NormSteps ... = .done (.returned <literal> ...)`), matching the
Coq derivation's literal final value. Run-level pins (WX-012 pattern).
NOT `watStep`. `closure_claim = 0`.
-/
import rcic.RcicWasmNormStep

namespace Rcic.WasmNorm.Pins.ControlBr

open Rcic.WasmNorm

/-- Control-row harness: one function, empty stack, no labels, empty
memory (control rows never touch memory). -/
def ctlSt (body : List NormInstr) : NormState where
  module := ⟨[⟨[], [], some .i32Ty, body⟩], 1, [], 0⟩
  funcIdx := 0
  pc := 0
  locals := []
  operandStack := []
  controlStack := []
  callStack := []
  linearMemory := ⟨[]⟩

/-! Row `block` — exit by falling off the block end. -/

theorem pin_norm_control_br_block_block_7 :
    NormSteps 4 (ctlSt [.block, .i32Const 7, .endI])
      = .done (.returned 7 ⟨[]⟩) := by
  decide

/-! Row `br` — exit by branch out of a void block; the value rides below
the block (matches the Coq row: the prefix value is carried through a
top-level label hole around the block). -/

theorem pin_norm_control_br_br_br_9 :
    NormSteps 4 (ctlSt [.i32Const 9, .block, .br 0, .endI])
      = .done (.returned 9 ⟨[]⟩) := by
  decide

/-! Row `br_if` — false arm: no branch, the void block exits by its end;
the value rides below the block. -/

theorem pin_norm_control_br_br_if_br_if_11 :
    NormSteps 6 (ctlSt [.i32Const 11, .block, .i32Const 0, .brIf 0, .endI])
      = .done (.returned 11 ⟨[]⟩) := by
  decide

end Rcic.WasmNorm.Pins.ControlBr

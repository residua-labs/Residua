/-
WX statement bridge S1, pins for slice `i64-divrem-traps`.

Per-row `decide` pins over `NormStep` mirroring the
`conformance/wasm_target_table/table.json` slice `i64-divrem-traps` rows
(the same row bytes are a Coq lemma in `coq/wasm_target/I64DivremTraps.v`;
the join is enforced by `.github/workflows/wasm-target-table.yml`).
#3395 boundary teeth: `div_s(MIN,-1)` traps, `rem_s(_,0)` traps.
NOT `watStep` — that model is retired. `closure_claim = 0`.
-/
import rcic.RcicWasmNormStep

namespace Rcic.WasmNorm.Pins.I64DivremTraps

open Rcic.WasmNorm

/-- Scalar-pin harness: a one-instruction function (index 0) whose body is
the instruction under test; operands with the top of stack at list HEAD. -/
def scalarSt (a b : NormVal) (instr : NormInstr) : NormState where
  module := ⟨[⟨[], [], none, [instr]⟩], 1, [], 0⟩
  funcIdx := 0
  pc := 0
  locals := []
  operandStack := [b, a]
  controlStack := []
  callStack := []
  linearMemory := ⟨[]⟩

/-- Expected state after a scalar step: pc advanced, result pushed. -/
def stepped (st : NormState) (v : NormVal) : NormState :=
  { st with pc := st.pc + 1, operandStack := v :: st.operandStack.drop 2 }

/-! Row `i64.div_s`: `div_s(MIN,-1)` traps (intOverflow), divisor 0 traps. -/

theorem pin_norm_i64_divrem_traps_div_s_min_neg1 :
    NormStep (scalarSt (.i64 9223372036854775808) (.i64 18446744073709551615) .i64DivS)
      = .trap .intOverflow
          (scalarSt (.i64 9223372036854775808) (.i64 18446744073709551615) .i64DivS) := by
  decide

theorem pin_norm_i64_divrem_traps_div_s_zero :
    NormStep (scalarSt (.i64 17) (.i64 0) .i64DivS)
      = .trap .divZero (scalarSt (.i64 17) (.i64 0) .i64DivS) := by
  decide

/-! Row `i64.rem_s`: `rem_s(MIN,-1) = 0` (no overflow), divisor 0 traps. -/

theorem pin_norm_i64_divrem_traps_rem_s_min_neg1 :
    NormStep (scalarSt (.i64 9223372036854775808) (.i64 18446744073709551615) .i64RemS)
      = .step (stepped (scalarSt (.i64 9223372036854775808) (.i64 18446744073709551615)
          .i64RemS) (.i64 0)) := by
  decide

theorem pin_norm_i64_divrem_traps_rem_s_zero :
    NormStep (scalarSt (.i64 17) (.i64 0) .i64RemS)
      = .trap .divZero (scalarSt (.i64 17) (.i64 0) .i64RemS) := by
  decide

/-! ## Shared memory-pin harness (added for the memory slices; the seal is
append-only, so shared harnesses live here with `scalarSt`/`stepped`). -/

/-- Memory-pin harness: one-instruction function, given fixture bytes. -/
def memSt (stack : List NormVal) (instr : NormInstr) (mem : List UInt8) : NormState where
  module := ⟨[⟨[], [], none, [instr]⟩], 1, [], 0⟩
  funcIdx := 0
  pc := 0
  locals := []
  operandStack := stack
  controlStack := []
  callStack := []
  linearMemory := ⟨mem⟩

/-- Expected state after a memory step: pc advanced, both operands popped,
memory replaced. -/
def steppedM (st : NormState) (mem' : List UInt8) : NormState :=
  { st with pc := st.pc + 1, operandStack := st.operandStack.drop 2, linearMemory := ⟨mem'⟩ }

/-- Expected state after a one-operand step (memory.size): pc advanced,
operand stack unchanged. -/
def steppedO (st : NormState) : NormState :=
  { st with pc := st.pc + 1 }

/-- Expected state after a pop-one-push-one step (S2-4: eqz and the
unary conversions): pc advanced, one operand popped, result pushed. -/
def stepped1 (st : NormState) (v : NormVal) : NormState :=
  { st with pc := st.pc + 1, operandStack := v :: st.operandStack.drop 1 }

end Rcic.WasmNorm.Pins.I64DivremTraps

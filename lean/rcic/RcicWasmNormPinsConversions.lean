/-
WX statement bridge S1, Lean pins for slice `conversions`.

Per-row `decide` pins over `NormStep` mirroring the
`conformance/wasm_target_table/table.json` slice `conversions` rows
(Coq side: `coq/wasm_target/Conversions.v`). #3395 teeth:
`wrap_i64` truncation, `extend_i32_s` sign.
Harness reused from the first pins module (the seal is append-only).
NOT `watStep`. `closure_claim = 0`.
-/
import rcic.RcicWasmNormStep
import rcic.RcicWasmNormPinsI64DivremTraps

namespace Rcic.WasmNorm.Pins.Conversions

open Rcic.WasmNorm
open Rcic.WasmNorm.Pins.I64DivremTraps (scalarSt stepped)

private def s32u (v : Int) : UInt32 := Rcic.WasmNorm.sintToU32 v
private def s64u (v : Int) : UInt64 := Rcic.WasmNorm.sintToU64 v

/-- Unary-step expected state: conversions pop ONE operand (the unary fix —
they were transcribed through two-operand `normBinOp` and `.stuck`ed on a
validated unary use; the row fixtures now put the converted value on top). -/
def stepped1 (st : NormState) (v : NormVal) : NormState :=
  { st with pc := st.pc + 1, operandStack := v :: st.operandStack.drop 1 }

/-! Row `i32.wrap_i64` (truncate to the low 32 bits). -/

theorem pin_norm_conversions_wrap_i64_2p32_5 :
    NormStep (scalarSt (.i64 0) (.i64 4294967301) .i32WrapI64)
      = .step (stepped1 (scalarSt (.i64 0) (.i64 4294967301) .i32WrapI64) (.i32 5)) := by
  decide

theorem pin_norm_conversions_wrap_i64_m1 :
    NormStep (scalarSt (.i64 0) (.i64 (s64u (-1))) .i32WrapI64)
      = .step (stepped1 (scalarSt (.i64 0) (.i64 (s64u (-1))) .i32WrapI64) (.i32 (s32u (-1)))) := by
  decide

/-! Row `i64.extend_i32_u` (zero-extend). -/

theorem pin_norm_conversions_extend_i32_u_m1 :
    NormStep (scalarSt (.i32 0) (.i32 (s32u (-1))) .i64ExtendI32U)
      = .step (stepped1 (scalarSt (.i32 0) (.i32 (s32u (-1))) .i64ExtendI32U) (.i64 4294967295)) := by
  decide

/-! Row `i64.extend_i32_s` (sign-extend). -/

theorem pin_norm_conversions_extend_i32_s_m1 :
    NormStep (scalarSt (.i32 0) (.i32 (s32u (-1))) .i64ExtendI32S)
      = .step (stepped1 (scalarSt (.i32 0) (.i32 (s32u (-1))) .i64ExtendI32S) (.i64 (s64u (-1)))) := by
  decide

theorem pin_norm_conversions_extend_i32_s_max32 :
    NormStep (scalarSt (.i32 0) (.i32 2147483647) .i64ExtendI32S)
      = .step (stepped1 (scalarSt (.i32 0) (.i32 2147483647) .i64ExtendI32S) (.i64 2147483647)) := by
  decide

end Rcic.WasmNorm.Pins.Conversions

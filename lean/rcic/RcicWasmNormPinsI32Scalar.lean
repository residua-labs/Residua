/-
WX statement bridge S1, Lean pins for slice `i32-scalar`.

Per-row `decide` pins over `NormStep` mirroring the
`conformance/wasm_target_table/table.json` slice `i32-scalar` rows
(Coq side: `coq/wasm_target/I32Scalar.v`). Includes the
count-mod-width shift tooth (`shl 1 33 = 2`).
Harness reused from the first pins module (the seal is append-only,
so the shared harness stays where it was first sealed).
NOT `watStep`. `closure_claim = 0`.
-/
import rcic.RcicWasmNormStep
import rcic.RcicWasmNormPinsI64DivremTraps

namespace Rcic.WasmNorm.Pins.I32Scalar

open Rcic.WasmNorm
open Rcic.WasmNorm.Pins.I64DivremTraps (scalarSt stepped)

private def s32u (v : Int) : UInt32 := Rcic.WasmNorm.sintToU32 v

theorem pin_norm_i32_scalar_add_max_1 :
    NormStep (scalarSt (.i32 (s32u 2147483647)) (.i32 1) .i32Add)
      = .step (stepped (scalarSt (.i32 (s32u 2147483647)) (.i32 1) .i32Add) (.i32 (s32u (-2147483648)))) := by
  decide

theorem pin_norm_i32_scalar_sub_min_1 :
    NormStep (scalarSt (.i32 (s32u (-2147483648))) (.i32 1) .i32Sub)
      = .step (stepped (scalarSt (.i32 (s32u (-2147483648))) (.i32 1) .i32Sub) (.i32 (s32u 2147483647))) := by
  decide

theorem pin_norm_i32_scalar_mul_65536_65536 :
    NormStep (scalarSt (.i32 65536) (.i32 65536) .i32Mul)
      = .step (stepped (scalarSt (.i32 65536) (.i32 65536) .i32Mul) (.i32 0)) := by
  decide

theorem pin_norm_i32_scalar_eq_3_4 :
    NormStep (scalarSt (.i32 3) (.i32 4) (.i32Cmp .eqOp))
      = .step (stepped (scalarSt (.i32 3) (.i32 4) (.i32Cmp .eqOp)) (.i32 0)) := by
  decide

theorem pin_norm_i32_scalar_ne_3_4 :
    NormStep (scalarSt (.i32 3) (.i32 4) (.i32Cmp .neOp))
      = .step (stepped (scalarSt (.i32 3) (.i32 4) (.i32Cmp .neOp)) (.i32 1)) := by
  decide

theorem pin_norm_i32_scalar_lt_s_m7_3 :
    NormStep (scalarSt (.i32 (s32u (-7))) (.i32 3) (.i32Cmp .ltS))
      = .step (stepped (scalarSt (.i32 (s32u (-7))) (.i32 3) (.i32Cmp .ltS)) (.i32 1)) := by
  decide

theorem pin_norm_i32_scalar_lt_u_1_m1 :
    NormStep (scalarSt (.i32 1) (.i32 (s32u (-1))) (.i32Cmp .ltU))
      = .step (stepped (scalarSt (.i32 1) (.i32 (s32u (-1))) (.i32Cmp .ltU)) (.i32 1)) := by
  decide

theorem pin_norm_i32_scalar_and_12_10 :
    NormStep (scalarSt (.i32 12) (.i32 10) (.i32Bit .andOp))
      = .step (stepped (scalarSt (.i32 12) (.i32 10) (.i32Bit .andOp)) (.i32 8)) := by
  decide

theorem pin_norm_i32_scalar_or_12_10 :
    NormStep (scalarSt (.i32 12) (.i32 10) (.i32Bit .orOp))
      = .step (stepped (scalarSt (.i32 12) (.i32 10) (.i32Bit .orOp)) (.i32 14)) := by
  decide

theorem pin_norm_i32_scalar_xor_12_10 :
    NormStep (scalarSt (.i32 12) (.i32 10) (.i32Bit .xorOp))
      = .step (stepped (scalarSt (.i32 12) (.i32 10) (.i32Bit .xorOp)) (.i32 6)) := by
  decide

theorem pin_norm_i32_scalar_shl_1_4 :
    NormStep (scalarSt (.i32 1) (.i32 4) (.i32Shift .shlOp))
      = .step (stepped (scalarSt (.i32 1) (.i32 4) (.i32Shift .shlOp)) (.i32 16)) := by
  decide

/-- 08 §5 tooth: shift count is modulo the bit width (33 ≡ 1 mod 32). -/
theorem pin_norm_i32_scalar_shl_1_33 :
    NormStep (scalarSt (.i32 1) (.i32 33) (.i32Shift .shlOp))
      = .step (stepped (scalarSt (.i32 1) (.i32 33) (.i32Shift .shlOp)) (.i32 2)) := by
  decide

theorem pin_norm_i32_scalar_shr_s_m8_1 :
    NormStep (scalarSt (.i32 (s32u (-8))) (.i32 1) (.i32Shift .shrS))
      = .step (stepped (scalarSt (.i32 (s32u (-8))) (.i32 1) (.i32Shift .shrS)) (.i32 (s32u (-4)))) := by
  decide

theorem pin_norm_i32_scalar_shr_u_m8_1 :
    NormStep (scalarSt (.i32 (s32u (-8))) (.i32 1) (.i32Shift .shrUOp))
      = .step (stepped (scalarSt (.i32 (s32u (-8))) (.i32 1) (.i32Shift .shrUOp)) (.i32 2147483644)) := by
  decide

end Rcic.WasmNorm.Pins.I32Scalar

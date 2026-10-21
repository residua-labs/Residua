/-
WX bridge S2-4 — machine pins for the four codec-profile ops the #6634
ruling put IN the frozen profile (`scm/rcic/wasm_op_sig.scm` arms
49/60/69/80): `i32.eqz`, `i64.eqz`, `i64.load8_u`, `i64.store8`, plus
the unary-conversion fix teeth. These pin `normStepInstr`'s new arms
directly (`decide`); they are NOT a conformance-table slice — the
table join is later work. Fixture memory: 16 bytes
[11,22,33,44,55,66,77,88,99,170,187,204,221,238,255,128].
Harnesses reused from the first pins module (the seal is append-only).
`closure_claim = 0`.
-/
import rcic.RcicWasmNormStep
import rcic.RcicWasmNormPinsI64DivremTraps

namespace Rcic.WasmNorm.Pins.EqzI64Ldst8

open Rcic.WasmNorm
open Rcic.WasmNorm.Pins.I64DivremTraps (memSt stepped1 steppedM)

private def memFx : List UInt8 :=
  [11,22,33,44,55,66,77,88,99,170,187,204,221,238,255,128]

/-! `i32.eqz` ([i32] → [i32], codec sig s11 op 69): 0 maps to 1,
nonzero to 0; a non-i32 top does not step. -/

theorem pin_norm_eqz_i64ldst8_i32_eqz_zero :
    NormStep (memSt [.i32 0] .i32Eqz memFx)
      = .step (stepped1 (memSt [.i32 0] .i32Eqz memFx) (.i32 1)) := by
  decide

theorem pin_norm_eqz_i64ldst8_i32_eqz_nonzero :
    NormStep (memSt [.i32 7] .i32Eqz memFx)
      = .step (stepped1 (memSt [.i32 7] .i32Eqz memFx) (.i32 0)) := by
  decide

theorem pin_norm_eqz_i64ldst8_i32_eqz_stuck :
    NormStep (memSt [.i64 0] .i32Eqz memFx) = .stuck := by
  decide

/-! `i64.eqz` ([i64] → [i32], codec sig op 80): the result is i32
(`cmpBool32`), matching the codec signature [126]→[127]. -/

theorem pin_norm_eqz_i64ldst8_i64_eqz_zero :
    NormStep (memSt [.i64 0] .i64Eqz memFx)
      = .step (stepped1 (memSt [.i64 0] .i64Eqz memFx) (.i32 1)) := by
  decide

theorem pin_norm_eqz_i64ldst8_i64_eqz_nonzero :
    NormStep (memSt [.i64 9295410792306027107] .i64Eqz memFx)
      = .step (stepped1 (memSt [.i64 9295410792306027107] .i64Eqz memFx) (.i32 0)) := by
  decide

theorem pin_norm_eqz_i64ldst8_i64_eqz_stuck :
    NormStep (memSt [.i32 0] .i64Eqz memFx) = .stuck := by
  decide

/-! `i64.load8_u` ([i32] → [i64], codec sig op 49): one byte,
zero-extended to i64; offset adds to the address; OOB traps. -/

theorem pin_norm_eqz_i64ldst8_i64_load8u_99 :
    NormStep (memSt [.i32 8] (.i64Load8U ⟨0⟩) memFx)
      = .step (stepped1 (memSt [.i32 8] (.i64Load8U ⟨0⟩) memFx) (.i64 99)) := by
  decide

theorem pin_norm_eqz_i64ldst8_i64_load8u_offset :
    NormStep (memSt [.i32 4] (.i64Load8U ⟨4⟩) memFx)
      = .step (stepped1 (memSt [.i32 4] (.i64Load8U ⟨4⟩) memFx) (.i64 99)) := by
  decide

theorem pin_norm_eqz_i64ldst8_i64_load8u_oob :
    NormStep (memSt [.i32 16] (.i64Load8U ⟨0⟩) memFx)
      = .trap .oobMemory (memSt [.i32 16] (.i64Load8U ⟨0⟩) memFx) := by
  decide

/-! `i64.store8` ([i64,i32] → [], codec sig op 60): the value's low
byte is stored at addr+offset; OOB traps; a non-i64 value does not
step. -/

theorem pin_norm_eqz_i64ldst8_i64_store8_low_byte :
    NormStep (memSt [.i64 305419896, .i32 4] (.i64Store8 ⟨0⟩) memFx)
      = .step (steppedM (memSt [.i64 305419896, .i32 4] (.i64Store8 ⟨0⟩) memFx)
          [11,22,33,44,120,66,77,88,99,170,187,204,221,238,255,128]) := by
  decide

theorem pin_norm_eqz_i64ldst8_i64_store8_oob :
    NormStep (memSt [.i64 1, .i32 16] (.i64Store8 ⟨0⟩) memFx)
      = .trap .oobMemory (memSt [.i64 1, .i32 16] (.i64Store8 ⟨0⟩) memFx) := by
  decide

theorem pin_norm_eqz_i64ldst8_i64_store8_stuck :
    NormStep (memSt [.i32 120, .i32 4] (.i64Store8 ⟨0⟩) memFx) = .stuck := by
  decide

end Rcic.WasmNorm.Pins.EqzI64Ldst8

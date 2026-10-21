/-
WX statement bridge S1, Lean pins for slice `memory-ldst`.

Per-row `decide` pins over `NormStep` mirroring the
`conformance/wasm_target_table/table.json` slice `memory-ldst` rows
(Coq side: `coq/wasm_target/MemoryLdst.v`). #3395 teeth: OOB load and
OOB store trap. Fixture: 16 bytes
[11,22,33,44,55,66,77,88,99,170,187,204,221,238,255,128].
Harnesses reused from the first pins module (the seal is append-only).
NOT `watStep`. `closure_claim = 0`.
-/
import rcic.RcicWasmNormStep
import rcic.RcicWasmNormPinsI64DivremTraps

namespace Rcic.WasmNorm.Pins.MemoryLdst

open Rcic.WasmNorm
open Rcic.WasmNorm.Pins.I64DivremTraps (memSt steppedM)

private def memFx : List UInt8 :=
  [11,22,33,44,55,66,77,88,99,170,187,204,221,238,255,128]

private def s32u (v : Int) : UInt32 := Rcic.WasmNorm.sintToU32 v

/-! Row `i32.load` (in-bounds LE reads; OOB traps). -/

theorem pin_norm_memory_ldst_i32_load_4 :
    NormStep (memSt [.i32 4] (.i32Load ⟨0⟩) memFx)
      = .step { (memSt [.i32 4] (.i32Load ⟨0⟩) memFx) with pc := 1, operandStack := [.i32 1481458231] } := by
  decide

theorem pin_norm_memory_ldst_i32_load_12 :
    NormStep (memSt [.i32 12] (.i32Load ⟨0⟩) memFx)
      = .step { (memSt [.i32 12] (.i32Load ⟨0⟩) memFx) with pc := 1, operandStack := [.i32 2164256477] } := by
  decide

theorem pin_norm_memory_ldst_i32_load_oob :
    NormStep (memSt [.i32 13] (.i32Load ⟨0⟩) memFx)
      = .trap .oobMemory (memSt [.i32 13] (.i32Load ⟨0⟩) memFx) := by
  decide

/-! Row `i64.load`. -/

theorem pin_norm_memory_ldst_i64_load_8 :
    NormStep (memSt [.i32 8] (.i64Load ⟨0⟩) memFx)
      = .step { (memSt [.i32 8] (.i64Load ⟨0⟩) memFx) with pc := 1, operandStack := [.i64 9295410792306027107] } := by
  decide

theorem pin_norm_memory_ldst_i64_load_oob :
    NormStep (memSt [.i32 9] (.i64Load ⟨0⟩) memFx)
      = .trap .oobMemory (memSt [.i32 9] (.i64Load ⟨0⟩) memFx) := by
  decide

/-! Row `i32.store` (0x12345678 at ea 4; roundtrip re-read is the row's
result; OOB traps). -/

theorem pin_norm_memory_ldst_i32_store_4 :
    NormStep (memSt [.i32 305419896, .i32 4] (.i32Store ⟨0⟩) memFx)
      = .step (steppedM (memSt [.i32 305419896, .i32 4] (.i32Store ⟨0⟩) memFx)
          [11,22,33,44,120,86,52,18,99,170,187,204,221,238,255,128]) := by
  decide

theorem pin_norm_memory_ldst_i32_store_oob :
    NormStep (memSt [.i32 305419896, .i32 13] (.i32Store ⟨0⟩) memFx)
      = .trap .oobMemory (memSt [.i32 305419896, .i32 13] (.i32Store ⟨0⟩) memFx) := by
  decide

/-! Row `i64.store` (0x0102030405060708 at ea 8). -/

theorem pin_norm_memory_ldst_i64_store_8 :
    NormStep (memSt [.i64 72623859790382856, .i32 8] (.i64Store ⟨0⟩) memFx)
      = .step (steppedM (memSt [.i64 72623859790382856, .i32 8] (.i64Store ⟨0⟩) memFx)
          [11,22,33,44,55,66,77,88,8,7,6,5,4,3,2,1]) := by
  decide

theorem pin_norm_memory_ldst_i64_store_oob :
    NormStep (memSt [.i64 72623859790382856, .i32 9] (.i64Store ⟨0⟩) memFx)
      = .trap .oobMemory (memSt [.i64 72623859790382856, .i32 9] (.i64Store ⟨0⟩) memFx) := by
  decide

end Rcic.WasmNorm.Pins.MemoryLdst

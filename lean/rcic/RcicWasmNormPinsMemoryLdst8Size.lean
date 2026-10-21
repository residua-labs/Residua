/-
WX statement bridge S1, Lean pins for slice `memory-ldst8`; the
`memory-size` slice was an OPEN item here until bridge S2 closed it
with a structural pin (see the `memory.size` section below — kernel
`decide` still never materializes the page spine).

Per-row `decide` pins over `NormStep` mirroring the corresponding
`conformance/wasm_target_table/table.json` rows (Coq side:
`coq/wasm_target/MemoryLdst.v`). #3395 teeth: `load8_u` zero-extension,
`memory.size` fixed pages. Fixture: 16 bytes
[11,22,33,44,55,66,77,88,99,170,187,204,221,238,255,128].
Harnesses reused from the first pins module (the seal is append-only).
NOT `watStep`. `closure_claim = 0`.
-/
import rcic.RcicWasmNormStep
import rcic.RcicWasmNormPinsI64DivremTraps

namespace Rcic.WasmNorm.Pins.MemoryLdst8Size

open Rcic.WasmNorm
open Rcic.WasmNorm.Pins.I64DivremTraps (memSt steppedM)

private def memFx : List UInt8 :=
  [11,22,33,44,55,66,77,88,99,170,187,204,221,238,255,128]

/-! Row `i32.load8_u` (zero-extension; OOB traps). -/

theorem pin_norm_memory_ldst8_i32_load8_u_9 :
    NormStep (memSt [.i32 9] (.i32Load8U ⟨0⟩) memFx)
      = .step { (memSt [.i32 9] (.i32Load8U ⟨0⟩) memFx) with pc := 1, operandStack := [.i32 170] } := by
  decide

theorem pin_norm_memory_ldst8_i32_load8_u_oob :
    NormStep (memSt [.i32 16] (.i32Load8U ⟨0⟩) memFx)
      = .trap .oobMemory (memSt [.i32 16] (.i32Load8U ⟨0⟩) memFx) := by
  decide

/-! Row `i32.store8`. -/

theorem pin_norm_memory_ldst8_i32_store8_15 :
    NormStep (memSt [.i32 7, .i32 15] (.i32Store8 ⟨0⟩) memFx)
      = .step (steppedM (memSt [.i32 7, .i32 15] (.i32Store8 ⟨0⟩) memFx)
          [11,22,33,44,55,66,77,88,99,170,187,204,221,238,255,7]) := by
  decide

theorem pin_norm_memory_ldst8_i32_store8_oob :
    NormStep (memSt [.i32 7, .i32 16] (.i32Store8 ⟨0⟩) memFx)
      = .trap .oobMemory (memSt [.i32 7, .i32 16] (.i32Store8 ⟨0⟩) memFx) := by
  decide

/-! Row `memory.size` — CLOSED by structural pin (bridge S2 segment 1;
the earlier `native_decide` pin was removed per the #6550 review ruling,
and kernel `decide` SIGABRTs on the 65536-byte page spine, so the row is
now pinned symbolically: the spine is never materialized).

- `memOfPages_length_div_page`: the length equation over `List.replicate`
  (`List.length_replicate` reasons about the equation, not the list);
- `normStep_memorySize`: the arm unfolded for any state whose `body[pc]`
  is `.memorySize` (the arm never touches `bytes`);
- `pin_norm_memory_size_size_1page`: the table's row (1 page, expected
  `1`) — the remaining record equality closes by kernel
  constructor-congruence with the `bytes` field syntactically shared.

`lean_open` entry removed from the table in the same patch (ratchet:
examples == pins restored for this slice). The Coq pin (`pin_msize_pages`)
stands and the row stays CI-joined. No `native_decide` (#6550).
`closure_claim = 0`. -/

theorem memOfPages_length_div_page (pages : Nat) :
    (NormMemory.ofPages pages).bytes.length / NormWasmPage = pages := by
  simp only [NormMemory.ofPages, NormWasmPage, List.length_replicate]
  omega

theorem normStep_memorySize (st : NormState) :
    normStepInstr st NormInstr.memorySize = NormStepResult.step { st with
      pc := st.pc + 1,
      operandStack :=
        .i32 (UInt32.ofNat (st.linearMemory.bytes.length / NormWasmPage)) :: st.operandStack } := by
  simp only [normStepInstr]

theorem pin_norm_memory_size_size_1page :
    NormStep (memSt [] NormInstr.memorySize (NormMemory.ofPages 1).bytes)
      = NormStepResult.step { memSt [] NormInstr.memorySize (NormMemory.ofPages 1).bytes with
        pc := 1, operandStack := [.i32 1] } := by
  have hmem : (memSt [] NormInstr.memorySize (NormMemory.ofPages 1).bytes).linearMemory.bytes
      = (NormMemory.ofPages 1).bytes := rfl
  have h := normStep_memorySize (memSt [] NormInstr.memorySize (NormMemory.ofPages 1).bytes)
  rw [
    show NormStep (memSt [] NormInstr.memorySize (NormMemory.ofPages 1).bytes)
        = normStepInstr (memSt [] NormInstr.memorySize (NormMemory.ofPages 1).bytes)
            NormInstr.memorySize from rfl,
    h, hmem, memOfPages_length_div_page]
  rfl

end Rcic.WasmNorm.Pins.MemoryLdst8Size

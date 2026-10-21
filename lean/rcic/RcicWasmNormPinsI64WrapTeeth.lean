/-
WX statement bridge S1, Lean pins for slice `i64-wrap-teeth`.

The two #3395 wrap teeth on the profile grammar: `add(MIN,-1) = MAX` and
`mul(2^32,2^32) = 0` (mod 2^64). A dedicated slice (rather than appended
examples on `i64-scalar-9`, which stays Coq-only: its `div_u`/`rem_u` rows
are outside the Residua-Wasm-0 grammar, so no NormInstr can pin them).
Rows mirror the `i64-wrap-teeth` slice rows
(Coq side: `coq/wasm_target/I64Scalar.v` appended teeth section).
Harness reused from the first pins module (the seal is append-only).
NOT `watStep`. `closure_claim = 0`.
-/
import rcic.RcicWasmNormStep
import rcic.RcicWasmNormPinsI64DivremTraps

namespace Rcic.WasmNorm.Pins.I64WrapTeeth

open Rcic.WasmNorm
open Rcic.WasmNorm.Pins.I64DivremTraps (scalarSt stepped)

private def s64u (v : Int) : UInt64 := Rcic.WasmNorm.sintToU64 v

/-- #3395 tooth: `add(MIN,-1)` wraps to MAX. -/
theorem pin_norm_i64_wrap_teeth_add_min_neg1 :
    NormStep (scalarSt (.i64 (s64u (-9223372036854775808))) (.i64 (s64u (-1))) .i64Add)
      = .step (stepped (scalarSt (.i64 (s64u (-9223372036854775808))) (.i64 (s64u (-1))) .i64Add)
          (.i64 (s64u 9223372036854775807))) := by
  decide

/-- #3395 tooth: `mul(2^32,2^32)` wraps to 0. -/
theorem pin_norm_i64_wrap_teeth_mul_2p32_2p32 :
    NormStep (scalarSt (.i64 4294967296) (.i64 4294967296) .i64Mul)
      = .step (stepped (scalarSt (.i64 4294967296) (.i64 4294967296) .i64Mul) (.i64 0)) := by
  decide

end Rcic.WasmNorm.Pins.I64WrapTeeth

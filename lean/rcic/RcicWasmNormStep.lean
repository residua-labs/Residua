/-
WX statement bridge S1, L1 — the normative embedding (lean transcription).

Transcription of WasmCert-Coq 2.2.0 (`coq-wasm.2.2.0`, tarball sha256
`52396234b60ee7d02fe283b4bef32dbce9c682ab8bc97258fe0e2bb5ec5fc574`) for
the Residua-Wasm-0 profile (08 §3/§4/§5/§14), pinned via
`conformance/wasm_target_table`. NOT `watStep` — that model is retired
(`census.json` `watStep_retired`, #3395 teeth armed). `closure_claim = 0`.

This module is the L1 host only (defs + the three statement lemmas).
The per-row pins live in `RcicWasmNormPins*.lean`; the table crossing
(Coq lemma AND Lean `decide` theorem over the same row bytes) is enforced
by `.github/workflows/wasm-target-table.yml`. L2 agreement with Codex's
`stepWasm0Machine` (S2), L3 `BoundWasm` re-homing (S3), `NormValidate`
and the codec (WX-002) are out of S1's scope.

Grammar (08 §4, exactly; unknown opcodes are UNREPRESENTABLE — validation
refusals, not runtime no-ops), value shapes (08 §5) and the machine state
(08 §14: validated_module_instance, current_function, pc, locals,
operand_stack, control_stack, call_stack, linear_memory) follow the
hand-off in `research/rcic/wx-bootstrap/BRIDGE_S0.md` (S1 section).

Convention: operand/control/call stacks have their TOP at list HEAD.
`NormStep` is total; states that only validation would reject step to
`.stuck` (§5: validation errors prevent construction and are not runtime
traps — `.stuck` is unreachable from validated states).
-/
namespace Rcic.WasmNorm

/-! ## Values, operator parameter types (08 §4 families) -/

inductive NormVal
  | i32 (v : UInt32)
  | i64 (v : UInt64)
  deriving DecidableEq, Repr

/-- Comparison family (both widths; result is i32 0/1, wasm-shaped). -/
inductive NormCmpOp
  | eqOp | neOp | ltS | ltU | gtS | gtU | leS | leU | geS | geU
  deriving DecidableEq, Repr

/-- Bitwise family. -/
inductive NormBitOp
  | andOp | orOp | xorOp
  deriving DecidableEq, Repr

/-- Shift family (count taken modulo the bit width, 08 §5). -/
inductive NormShiftOp
  | shlOp | shrS | shrUOp
  deriving DecidableEq, Repr

/-- Static memory access offset (align omitted: it carries no semantics). -/
structure NormMemArg where
  offset : Nat
  deriving DecidableEq, Repr

/-! ## Closed instruction grammar (08 §4, exactly; S2-4 adds the four
codec-profile ops `i32.eqz`/`i64.eqz`/`i64.load8_u`/`i64.store8` per the
WX-002 grammar-gap measurement — `scm/rcic/wasm_op_sig.scm` arms
49/60/69/80) -/

inductive NormInstr
  | block | loop | ifE | elseE | endI | br (n : Nat) | brIf (n : Nat)
  | call (f : Nat) | return | drop | select
  | localGet (i : Nat) | localSet (i : Nat) | localTee (i : Nat)
  | i32Const (v : UInt32) | i32Eqz | i32Cmp (op : NormCmpOp)
  | i32Add | i32Sub | i32Mul | i32Bit (op : NormBitOp) | i32Shift (op : NormShiftOp)
  | i64Const (v : UInt64) | i64Eqz | i64Cmp (op : NormCmpOp)
  | i64Add | i64Sub | i64Mul | i64DivS | i64RemS
  | i64Bit (op : NormBitOp) | i64Shift (op : NormShiftOp)
  | i32WrapI64 | i64ExtendI32U | i64ExtendI32S
  | i32Load (a : NormMemArg) | i64Load (a : NormMemArg)
  | i32Store (a : NormMemArg) | i64Store (a : NormMemArg)
  | i32Load8U (a : NormMemArg) | i64Load8U (a : NormMemArg)
  | i32Store8 (a : NormMemArg) | i64Store8 (a : NormMemArg)
  | memorySize
  deriving DecidableEq, Repr

/-! ## Memory (08 §3: one fixed-size memory, min = max) -/

def NormWasmPage : Nat := 65536

structure NormMemory where
  bytes : List UInt8
  deriving DecidableEq, Repr

def NormMemory.ofPages (pages : Nat) : NormMemory where
  bytes := List.replicate (pages * NormWasmPage) 0

/-! ## Module shapes (single-value results, 08 §3) -/

inductive NormTy
  | i32Ty | i64Ty
  deriving DecidableEq, Repr

/-- Default value of a type (wasm zero). -/
def NormTy.zero : NormTy → NormVal
  | .i32Ty => .i32 0
  | .i64Ty => .i64 0

structure NormFunc where
  params : List NormTy
  locals : List NormTy
  result : Option NormTy
  body : List NormInstr
  deriving DecidableEq, Repr

structure NormModule where
  funcs : List NormFunc
  memPages : Nat
  datas : List (Nat × List UInt8)
  entry : Nat
  deriving DecidableEq, Repr

/-! ## Machine state (08 §14) -/

/-- Control-stack label kinds. The function frame's implicit outermost
label is NOT stored: `br` at depth = controlStack length is a return. -/
inductive NormLabelKind
  | blockK | loopK | ifK
  deriving DecidableEq, Repr

structure NormLabel where
  kind : NormLabelKind
  height : Nat        -- operand-stack height at label entry
  startPc : Nat       -- pc of the `loop` instruction (loopK resume point)
  endPc : Nat         -- pc AFTER the matching `end` (branch-out point)
  deriving DecidableEq, Repr

structure NormFrame where
  callerIdx : Nat
  retPc : Nat               -- resume pc in the caller body
  savedStack : List NormVal -- caller operand stack below the call
  savedLabels : List NormLabel
  deriving DecidableEq, Repr

structure NormState where
  module : NormModule
  funcIdx : Nat
  pc : Nat
  locals : List NormVal
  operandStack : List NormVal
  controlStack : List NormLabel
  callStack : List NormFrame
  linearMemory : NormMemory
  deriving DecidableEq, Repr

/-! ## Outcomes (08 §5) -/

inductive NormTrapReason
  | divZero | intOverflow | oobMemory | unreach
  deriving DecidableEq, Repr

inductive NormFinal
  | returned (resultI64 : Int) (mem : NormMemory)
  | trapped (reason : NormTrapReason) (state : NormState)
  deriving DecidableEq, Repr

inductive NormRunResult
  | done (f : NormFinal) | suspended (st : NormState)
  deriving DecidableEq, Repr

/-- One step is total: `.stuck` (bare: the machine makes no transition)
marks states validation rejects (§5 — not a runtime trap, unreachable from
validated states). -/
inductive NormStepResult
  | step (st' : NormState)
  | trap (r : NormTrapReason) (st : NormState)
  | ret (v : Int) (mem : NormMemory)
  | stuck
  deriving DecidableEq, Repr

/-! ## Scalar helpers (pure, kernel-reducible) -/

def u64ToSInt (a : UInt64) : Int :=
  if 9223372036854775808 ≤ a.toNat then (Int.ofNat a.toNat) - 18446744073709551616
  else Int.ofNat a.toNat

def u32ToSInt (a : UInt32) : Int :=
  if 2147483648 ≤ a.toNat then (Int.ofNat a.toNat) - 4294967296
  else Int.ofNat a.toNat

/-- Two's-complement bit pattern of an in-range signed value. -/
def sintToU64 (q : Int) : UInt64 :=
  if q ≥ 0 then UInt64.ofNat q.toNat else 0 - UInt64.ofNat (-q).toNat

def sintToU32 (q : Int) : UInt32 :=
  if q ≥ 0 then UInt32.ofNat q.toNat else 0 - UInt32.ofNat (-q).toNat

/-- i64.div_s (08 §5: traps on divisor 0 and MIN,-1; truncates toward 0). -/
def i64DivS (a b : UInt64) : Except NormTrapReason UInt64 :=
  if b == 0 then .error .divZero
  else if a == 9223372036854775808 && b == 18446744073709551615 then .error .intOverflow
  else .ok (sintToU64 (Int.tdiv (u64ToSInt a) (u64ToSInt b)))

/-- i64.rem_s (traps only on divisor 0; truncated remainder). -/
def i64RemS (a b : UInt64) : Except NormTrapReason UInt64 :=
  if b == 0 then .error .divZero
  else .ok (sintToU64 (Int.tmod (u64ToSInt a) (u64ToSInt b)))

def cmpBool32 (b : Bool) : UInt32 := if b then 1 else 0

def cmpU64 (op : NormCmpOp) (a b : UInt64) : UInt32 :=
  match op with
  | .eqOp => cmpBool32 (a == b)
  | .neOp => cmpBool32 (a != b)
  | .ltS => cmpBool32 (u64ToSInt a < u64ToSInt b)
  | .ltU => cmpBool32 (a < b)
  | .gtS => cmpBool32 (u64ToSInt a > u64ToSInt b)
  | .gtU => cmpBool32 (a > b)
  | .leS => cmpBool32 (u64ToSInt a ≤ u64ToSInt b)
  | .leU => cmpBool32 (a ≤ b)
  | .geS => cmpBool32 (u64ToSInt a ≥ u64ToSInt b)
  | .geU => cmpBool32 (a ≥ b)

def cmpU32 (op : NormCmpOp) (a b : UInt32) : UInt32 :=
  match op with
  | .eqOp => cmpBool32 (a == b)
  | .neOp => cmpBool32 (a != b)
  | .ltS => cmpBool32 (u32ToSInt a < u32ToSInt b)
  | .ltU => cmpBool32 (a < b)
  | .gtS => cmpBool32 (u32ToSInt a > u32ToSInt b)
  | .gtU => cmpBool32 (a > b)
  | .leS => cmpBool32 (u32ToSInt a ≤ u32ToSInt b)
  | .leU => cmpBool32 (a ≤ b)
  | .geS => cmpBool32 (u32ToSInt a ≥ u32ToSInt b)
  | .geU => cmpBool32 (a ≥ b)

def bitU64 (op : NormBitOp) (a b : UInt64) : UInt64 :=
  match op with
  | .andOp => a &&& b | .orOp => a ||| b | .xorOp => a ^^^ b

def bitU32 (op : NormBitOp) (a b : UInt32) : UInt32 :=
  match op with
  | .andOp => a &&& b | .orOp => a ||| b | .xorOp => a ^^^ b

def shiftU64 (op : NormShiftOp) (a b : UInt64) : UInt64 :=
  let c := (b.toNat % 64).toUInt64
  match op with
  | .shlOp => a <<< c
  | .shrUOp => a >>> c
  | .shrS => sintToU64 (u64ToSInt a >>> (b.toNat % 64))

def shiftU32 (op : NormShiftOp) (a b : UInt32) : UInt32 :=
  let c := (b.toNat % 32).toUInt32
  match op with
  | .shlOp => a <<< c
  | .shrUOp => a >>> c
  | .shrS => sintToU32 (u32ToSInt a >>> (b.toNat % 32))

/-! ## Memory helpers -/

/-- Little-endian composition (first byte = least significant). -/
def bytesToU32 (bs : List UInt8) : UInt32 :=
  bs.reverse.foldl (fun acc b => (acc <<< 8) ||| b.toUInt32) 0

def bytesToU64 (bs : List UInt8) : UInt64 :=
  bs.reverse.foldl (fun acc b => (acc <<< 8) ||| b.toUInt64) 0

def u32ToBytes (v : UInt32) : List UInt8 :=
  [(v >>> 0).toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]

def u64ToBytes (v : UInt64) : List UInt8 :=
  [(v >>> 0).toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8,
   (v >>> 32).toUInt8, (v >>> 40).toUInt8, (v >>> 48).toUInt8, (v >>> 56).toUInt8]

/-- In-bounds read of `n` bytes at `ea`. -/
def memLoadBytes (m : NormMemory) (ea n : Nat) : Option (List UInt8) :=
  if ea + n ≤ m.bytes.length then some (m.bytes.drop ea |>.take n) else none

/-- In-bounds write of `bs` at `ea`. -/
def memStoreBytes (m : NormMemory) (ea : Nat) (bs : List UInt8) : Option NormMemory :=
  if ea + bs.length ≤ m.bytes.length then
    some ⟨(m.bytes.take ea ++ bs ++ m.bytes.drop (ea + bs.length))⟩
  else none

/-! ## Control map (validator-derived branch targets, 08 §6) -/

/-- Scan `body` from `i`: the first matching `elseE` pc and the matching
`endI` pc of the structured construct opened at `i` (block/loop/ifE).
Fueled by the body length (structural). -/
def normElseEnd (body : List NormInstr) (i : Nat) : Option (Option Nat × Nat) :=
  let rec go (fuel j depth : Nat) (elsePc : Option Nat) : Option (Option Nat × Nat) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match body.get? j with
      | none => none
      | some .block => go fuel (j + 1) (depth + 1) elsePc
      | some .loop => go fuel (j + 1) (depth + 1) elsePc
      | some .ifE => go fuel (j + 1) (depth + 1) elsePc
      | some .endI =>
        if depth = 0 then some (elsePc, j + 1) else go fuel (j + 1) (depth - 1) elsePc
      | some .elseE =>
        if depth = 0 then go fuel (j + 1) depth (elsePc <|> some j)
        else go fuel (j + 1) depth elsePc
      | _ => go fuel (j + 1) depth elsePc
  go (body.length - i) (i + 1) 0 none

/-- Set the i-th local (if in bounds). -/
def normLocalsSet (ls : List NormVal) (i : Nat) (v : NormVal) : Option (List NormVal) :=
  let rec go (fuel : Nat) (ls : List NormVal) (i : Nat) : Option (List NormVal) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match ls, i with
      | [], _ => none
      | _ :: tl, 0 => some (v :: tl)
      | h :: tl, i + 1 => (go fuel tl i).map (h :: ·)
  go ls.length ls i

/-! ## The step relation -/
/-- Function exit (explicit `return`, falling off the body, or `br` at the
function label). Pops one result value when the function has one. -/
def normReturn (st : NormState) : NormStepResult :=
  let arity := ((st.module.funcs.get? st.funcIdx).bind NormFunc.result).isSome
  let res := match arity, st.operandStack with
    | true, v :: _ => some v
    | true, [] => none           -- unvalidated; validation rejects
    | false, _ => none
  match st.callStack with
  | fr :: rest =>
    let st' := { st with funcIdx := fr.callerIdx, pc := fr.retPc, operandStack := fr.savedStack ++ res.toList, controlStack := fr.savedLabels, callStack := rest }
    .step st'
  | [] =>
    match res with
    | some (.i64 v) => .ret (u64ToSInt v) st.linearMemory
    | some (.i32 v) => .ret (u32ToSInt v) st.linearMemory
    | none => if arity then .stuck else .ret 0 st.linearMemory

/-- `br n`: truncate to the target label's entry height; loop labels resume
at the loop body, block/if labels exit past their `end`. Depth = list length
targets the function's implicit label: a return. -/
def normBr (st : NormState) (n : Nat) : NormStepResult :=
  match st.controlStack.drop n with
  | [] => if n = st.controlStack.length then normReturn st else .stuck
  | lab :: outer =>
    let st₁ := { st with operandStack := st.operandStack.take lab.height }
    match lab.kind with
    | .loopK => .step { st₁ with pc := lab.startPc + 1 }
    | .blockK | .ifK => .step { st₁ with pc := lab.endPc, controlStack := outer }

/-- Two-operand scalar step on i64. -/
def normBinOp64 (st : NormState) (f : UInt64 → UInt64 → Option NormVal) : NormStepResult :=
  match st.operandStack with
  | .i64 b :: .i64 a :: rest =>
    match f a b with
    | some v => .step { st with pc := st.pc + 1, operandStack := v :: rest }
    | none => .stuck
  | _ => .stuck

/-- Trap-carrying two-operand step (div_s/rem_s; the reason comes with the
refusal). -/
def normDivRem64 (st : NormState) (f : UInt64 → UInt64 → Except NormTrapReason UInt64) :
    NormStepResult :=
  match st.operandStack with
  | .i64 b :: .i64 a :: rest =>
    match f a b with
    | .ok v => .step { st with pc := st.pc + 1, operandStack := .i64 v :: rest }
    | .error r => .trap r st
  | _ => .stuck

/-- Two-operand scalar step on i32 (result i32). -/
def normBinOp32 (st : NormState) (f : UInt32 → UInt32 → NormVal) : NormStepResult :=
  match st.operandStack with
  | .i32 b :: .i32 a :: rest =>
    .step { st with pc := st.pc + 1, operandStack := f a b :: rest }
  | _ => .stuck

/-- One-operand scalar step on i32 (S2-4: eqz and the i32-source
conversions are unary — the sigs promise one operand, so the binary
helpers would send validated programs to `.stuck`). -/
def normUnOp32 (st : NormState) (f : UInt32 → NormVal) : NormStepResult :=
  match st.operandStack with
  | .i32 a :: rest =>
    .step { st with pc := st.pc + 1, operandStack := f a :: rest }
  | _ => .stuck

/-- One-operand scalar step on i64 (S2-4: eqz and the i64-source
conversions are unary). -/
def normUnOp64 (st : NormState) (f : UInt64 → NormVal) : NormStepResult :=
  match st.operandStack with
  | .i64 a :: rest =>
    .step { st with pc := st.pc + 1, operandStack := f a :: rest }
  | _ => .stuck

def normCmpOp64 (st : NormState) (op : NormCmpOp) : NormStepResult :=
  match st.operandStack with
  | .i64 b :: .i64 a :: rest =>
    .step { st with pc := st.pc + 1, operandStack := .i32 (cmpU64 op a b) :: rest }
  | _ => .stuck

def normCmpOp32 (st : NormState) (op : NormCmpOp) : NormStepResult :=
  match st.operandStack with
  | .i32 b :: .i32 a :: rest =>
    .step { st with pc := st.pc + 1, operandStack := .i32 (cmpU32 op a b) :: rest }
  | _ => .stuck

def normLoad (st : NormState) (a : NormMemArg) (n : Nat)
      (mk : List UInt8 → NormVal) : NormStepResult :=
  match st.operandStack with
  | .i32 addr :: rest =>
    let ea := addr.toNat + a.offset
    match memLoadBytes st.linearMemory ea n with
    | some bs => .step { st with pc := st.pc + 1, operandStack := mk bs :: rest }
    | none => .trap .oobMemory st
  | _ => .stuck

def normStore (st : NormState) (a : NormMemArg) (bsOf : NormVal → Option (List UInt8)) :
    NormStepResult :=
  match st.operandStack with
  | v :: .i32 addr :: rest =>
    match bsOf v with
    | none => .stuck
    | some bs =>
      match memStoreBytes st.linearMemory (addr.toNat + a.offset) bs with
      | some m' => .step { st with pc := st.pc + 1, operandStack := rest, linearMemory := m' }
      | none => .trap .oobMemory st
  | _ => .stuck

def normStepInstr (st : NormState) (instr : NormInstr) : NormStepResult :=
  match instr with
  | .block =>
    match normElseEnd (st.module.funcs.get? st.funcIdx |>.map NormFunc.body |>.getD []) st.pc with
    | some (_, endPc) =>
      .step { st with pc := st.pc + 1, controlStack := ⟨.blockK, st.operandStack.length, st.pc, endPc⟩ :: st.controlStack }
    | none => .stuck
  | .loop =>
    match normElseEnd (st.module.funcs.get? st.funcIdx |>.map NormFunc.body |>.getD []) st.pc with
    | some (_, endPc) =>
      .step { st with pc := st.pc + 1, controlStack := ⟨.loopK, st.operandStack.length, st.pc, endPc⟩ :: st.controlStack }
    | none => .stuck
  | .ifE =>
    match st.operandStack,
          normElseEnd (st.module.funcs.get? st.funcIdx |>.map NormFunc.body |>.getD []) st.pc with
    | .i32 c :: rest, some (elsePc, endPc) =>
      let st₁ := { st with pc := st.pc + 1, operandStack := rest, controlStack := ⟨.ifK, rest.length, st.pc, endPc⟩ :: st.controlStack }
      if c != 0 then .step st₁
      else match elsePc with
        | some e => .step { st₁ with pc := e + 1 }
        | none => .step { st₁ with pc := endPc, controlStack := st.controlStack }
    | _, _ => .stuck
  | .elseE =>
    match st.controlStack with
    | lab :: rest => .step { st with pc := lab.endPc, controlStack := rest }
    | [] => .stuck
  | .endI =>
    match st.controlStack with
    | _ :: rest => .step { st with pc := st.pc + 1, controlStack := rest }
    | [] => .stuck
  | .br n => normBr st n
  | .brIf n =>
    match st.operandStack with
    | .i32 c :: rest =>
      if c != 0 then normBr { st with operandStack := rest } n
      else .step { st with pc := st.pc + 1, operandStack := rest }
    | _ => .stuck
  | .call f =>
    match st.module.funcs.get? f with
    | none => .stuck
    | some callee =>
      let nargs := callee.params.length
      let args := st.operandStack.take nargs
      if args.length != nargs then .stuck
      else
        let rest := st.operandStack.drop nargs
        let locs := (callee.params.zip args.reverse).map (·.2) ++ callee.locals.map NormTy.zero
        .step { st with pc := 0, funcIdx := f, locals := locs, operandStack := [], controlStack := [], callStack := ⟨st.funcIdx, st.pc + 1, rest, st.controlStack⟩ :: st.callStack }
  | .return => normReturn st
  | .drop =>
    match st.operandStack with
    | _ :: rest => .step { st with pc := st.pc + 1, operandStack := rest }
    | [] => .stuck
  | .select =>
    match st.operandStack with
    | .i32 c :: b :: a :: rest =>
      .step { st with pc := st.pc + 1, operandStack := (if c != 0 then a else b) :: rest }
    | _ => .stuck
  | .localGet i =>
    match st.locals.get? i with
    | some v => .step { st with pc := st.pc + 1, operandStack := v :: st.operandStack }
    | none => .stuck
  | .localSet i =>
    match st.operandStack with
    | v :: rest =>
      match normLocalsSet st.locals i v with
      | some ls => .step { st with pc := st.pc + 1, operandStack := rest, locals := ls }
      | none => .stuck
    | [] => .stuck
  | .localTee i =>
    match st.operandStack with
    | v :: rest =>
      match normLocalsSet st.locals i v with
      | some ls => .step { st with pc := st.pc + 1, operandStack := v :: rest, locals := ls }
      | none => .stuck
    | [] => .stuck
  | .i32Const v => .step { st with pc := st.pc + 1, operandStack := .i32 v :: st.operandStack }
  | .i32Eqz => normUnOp32 st (fun a => .i32 (cmpBool32 (a == 0)))
  | .i32Cmp op => normCmpOp32 st op
  | .i32Add => normBinOp32 st (fun a b => .i32 (a + b))
  | .i32Sub => normBinOp32 st (fun a b => .i32 (a - b))
  | .i32Mul => normBinOp32 st (fun a b => .i32 (a * b))
  | .i32Bit op => normBinOp32 st (fun a b => .i32 (bitU32 op a b))
  | .i32Shift op => normBinOp32 st (fun a b => .i32 (shiftU32 op a b))
  | .i64Const v => .step { st with pc := st.pc + 1, operandStack := .i64 v :: st.operandStack }
  | .i64Eqz => normUnOp64 st (fun a => .i32 (cmpBool32 (a == 0)))
  | .i64Cmp op => normCmpOp64 st op
  | .i64Add => normBinOp64 st (fun a b => some (.i64 (a + b)))
  | .i64Sub => normBinOp64 st (fun a b => some (.i64 (a - b)))
  | .i64Mul => normBinOp64 st (fun a b => some (.i64 (a * b)))
  | .i64DivS => normDivRem64 st i64DivS
  | .i64RemS => normDivRem64 st i64RemS
  | .i64Bit op => normBinOp64 st (fun a b => some (.i64 (bitU64 op a b)))
  | .i64Shift op => normBinOp64 st (fun a b => some (.i64 (shiftU64 op a b)))
  | .i32WrapI64 =>
    match st.operandStack with
    | .i64 a :: rest =>
      .step { st with pc := st.pc + 1, operandStack := .i32 (UInt32.ofNat (a.toNat % 4294967296)) :: rest }
    | _ => .stuck
  | .i64ExtendI32U =>
    match st.operandStack with
    | .i32 a :: rest =>
      .step { st with pc := st.pc + 1, operandStack := .i64 (UInt64.ofNat a.toNat) :: rest }
    | _ => .stuck
  | .i64ExtendI32S =>
    match st.operandStack with
    | .i32 a :: rest =>
      .step { st with pc := st.pc + 1, operandStack := .i64 (sintToU64 (u32ToSInt a)) :: rest }
    | _ => .stuck
  | .i32Load a => normLoad st a 4 (fun bs => .i32 (bytesToU32 bs))
  | .i64Load a => normLoad st a 8 (fun bs => .i64 (bytesToU64 bs))
  | .i32Store a =>
    normStore st a (fun v => match v with | .i32 x => some (u32ToBytes x) | _ => none)
  | .i64Store a =>
    normStore st a (fun v => match v with | .i64 x => some (u64ToBytes x) | _ => none)
  | .i32Load8U a => normLoad st a 1 (fun bs => .i32 (match bs with | b :: _ => b.toUInt32 | [] => 0))
  | .i64Load8U a =>
    normLoad st a 1 (fun bs => .i64 (match bs with | b :: _ => b.toUInt64 | [] => 0))
  | .i32Store8 a =>
    normStore st a (fun v => match v with | .i32 x => some [x.toUInt8] | _ => none)
  | .i64Store8 a =>
    normStore st a (fun v => match v with | .i64 x => some [x.toUInt8] | _ => none)
  | .memorySize =>
    .step { st with pc := st.pc + 1, operandStack := .i32 (UInt32.ofNat (st.linearMemory.bytes.length / NormWasmPage)) :: st.operandStack }

/-- `NormStep`: one deterministic step of the normative machine (08 §14).
Falling off the body is the implicit function return. -/
def NormStep (st : NormState) : NormStepResult :=
  match st.module.funcs.get? st.funcIdx with
  | none => .stuck
  | some f =>
    match f.body.get? st.pc with
    | some instr => normStepInstr st instr
    | none => normReturn st

/-! ## Runs (08 §14: deterministic, resumable) -/

/-- Fuel-bounded run: exhaustion yields `.suspended st` (08 §5 Suspension;
distinct from traps and returns). -/
def NormSteps : Nat → NormState → NormRunResult
  | 0, st => .suspended st
  | fuel + 1, st =>
    match NormStep st with
    | .step st' => NormSteps fuel st'
    | .trap r s => .done (.trapped r s)
    | .ret v m => .done (.returned v m)
    | .stuck => .suspended st

theorem normSteps_succ (fuel : Nat) (st : NormState) :
    NormSteps (fuel + 1) st =
      match NormStep st with
      | .step st' => NormSteps fuel st'
      | .trap r s => .done (.trapped r s)
      | .ret v m => .done (.returned v m)
      | .stuck => .suspended st := by rfl

/-- `.stuck` is absorbing under `NormSteps` (an unvalidated state stays
suspended at that state for any remaining fuel). -/
theorem normSteps_stuck_absorbing {s : NormState} (h : NormStep s = .stuck)
    (fuel : Nat) : NormSteps fuel s = .suspended s := by
  induction fuel with
  | zero => rfl
  | succ fuel _ => rw [normSteps_succ, h]

/-- §14 resumability: a suspension at `st'` after `k` steps makes any longer
fuel agree with resuming from `st'`. -/
theorem normRun_suspended_resumable (k n : Nat) (st st' : NormState)
    (h : NormSteps k st = .suspended st') : NormSteps (k + n) st = NormSteps n st' := by
  induction k generalizing st with
  | zero =>
      simp only [NormSteps] at h
      have hst : st = st' := NormRunResult.suspended.inj h
      subst hst
      rw [Nat.zero_add]
  | succ k ih =>
      rw [Nat.add_assoc, Nat.add_comm 1 n, ← Nat.add_assoc, normSteps_succ]
      rw [normSteps_succ] at h
      cases hs : NormStep st with
      | step s =>
          simp only [hs] at h ⊢
          exact ih s h
      | trap r s => rw [hs] at h; exact NormRunResult.noConfusion h
      | ret v m => rw [hs] at h; exact NormRunResult.noConfusion h
      | stuck =>
          simp only [hs] at h ⊢
          have hst : st = st' := NormRunResult.suspended.inj h
          subst hst
          exact (normSteps_stuck_absorbing hs n).symm

/-- `NormStep` is a function: determinism is by construction (the row's
content is carried by the arms, not by a determinism lemma). -/
theorem normStep_deterministic (st : NormState) (r₁ r₂ : NormStepResult)
    (h₁ : NormStep st = r₁) (h₂ : NormStep st = r₂) : r₁ = r₂ := by
  rw [← h₁, ← h₂]

/-- 08 §5 three-way split (here: trap vs return; suspension lives in
`NormRunResult`). -/
theorem normTrap_ne_residue (r : NormTrapReason) (s : NormState) (v : Int) (m : NormMemory) :
    NormFinal.trapped r s ≠ NormFinal.returned v m := by
    intro h; exact NormFinal.noConfusion h

/-! ## Run initialization and entry (08 §14) -/

/-- Host convention: the public input bytes are copied at this byte offset
of linear memory during initialization (§9 pins the region layout; the
formal instantiation row is WX-013, out of S1). -/
def normInputRegionOffset : Nat := 1024

/-- Default fuel for `NormRun` (bounded machine; exhaustion suspends). -/
def normRunDefaultFuel : Nat := 65536

/-- 08 §14 initialization: instantiate (zeroed, fixed-size) memory, apply
data segments at their own offsets, copy exact public input bytes, invoke
the sole export with (input_ptr, input_len). -/
def normInit (m : NormModule) (input : List UInt8) : NormState :=
  let mem₀ := NormMemory.ofPages m.memPages
  let mem₁ := m.datas.foldl (fun acc d =>
    match memStoreBytes acc d.1 d.2 with
    | some m' => m' | none => acc) mem₀
  let mem₂ := (memStoreBytes mem₁ normInputRegionOffset input).getD mem₁
  let entry := m.funcs.get? m.entry |>.getD ⟨[], [], none, []⟩
  { module := m, funcIdx := m.entry, pc := 0,
    locals := [.i32 (UInt32.ofNat normInputRegionOffset), .i32 (UInt32.ofNat input.length)]
      ++ entry.locals.map NormTy.zero,
    operandStack := [], controlStack := [], callStack := [], linearMemory := mem₂ }

/-- 08 §14 run: init then fuel-bounded steps. -/
def NormRun (m : NormModule) (input : List UInt8) : NormRunResult :=
  NormSteps normRunDefaultFuel (normInit m input)

/-! ## The Residua-Wasm-0 profile predicate (08 §3) -/

/-- Structural profile facts expressible over the norm IR: the entry exists
with signature `residua_entry(i32, i32) -> i64`, and the one fixed-size
memory is within the wasm page limit. No imports/tables/globals/reftypes/
exceptions/floats/SIMD/threads, direct calls only and single-value results
are enforced by the CLOSED grammar and the `Option NormTy` result field
(unrepresentable violations); section order and the sole-export shape are
codec-level constraints (WX-001/WX-002 modules, out of S1). -/
def InResiduaWasm0 (m : NormModule) : Prop :=
  ∃ f, m.funcs.get? m.entry = some f ∧ f.params = [.i32Ty, .i32Ty] ∧ f.result = some .i64Ty
    ∧ 1 ≤ m.memPages ∧ m.memPages ≤ 65536

end Rcic.WasmNorm

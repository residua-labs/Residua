/-
WX-002 S1 — the typing layer for validator soundness (08 §5/§6, S0 plan in
research/rcic/wx/S0_WX002.md, #6613; cc added S5: a decidable NormValidate +
agreement pins vs the scm corpus).

This module transcribes the codec carrier's data-half validator
(`scm/rcic/wasm_vstep` + the `wasm_v*`/`wasm_tck_*` family) into a
deterministic check over the norm IR, plus the machine-side invariants
(`NormStateTy`) the S2 progress and S3 preservation lemmas discharge.

Deviations from the scm walk are deliberate and recorded:

- `NormInstr` drops blocktype immediates, so EVERY structured frame has
  `rt = none` — only the implicit function frame carries a result type.
  A norm body has no terminal `end` (the machine falls off the body into
  `normReturn`), so `endI` at the implicit frame is a validation refusal —
  the scm walk instead requires the terminal `end` that pops its tg-5
  frame. This is the norm-grammar-narrower-than-profile site behind
  `[wx002_norm_grammar_narrower_i64_blocktype_if]` (corpus row 2's
  i64-blocktype `if`, pinned in `RcicWasmNormValidate`).
- The machine's `normBr` keeps the TOP `height` stack elements
  (`operandStack.take lab.height`), not the below-frame elements wasm
  unwinding preserves. A validated `br`/`brIf` therefore carries the extra
  check `normVBrEntryOK`: the retained top `base` types must equal the
  target's entry types (vacuous under `un`, like `tck_pop`).
- `normReturn` resumes the caller with `savedStack ++ res` — the result
  lands at the operand-stack TAIL. `normVStep .call` mirrors this: the
  callee result is appended at the type-stack tail, not pushed on top.
- `normVBrk` marks only the INNERMOST frame unreachable (the scm
  `wasm_v_brk` behavior verbatim), which is sufficient because the
  unreachable region ends at that frame's `end`.

`closure_claim = 0`.
-/
import rcic.RcicWasmNormStep

namespace Rcic.WasmNorm

/-- The machine value's type. -/
def NormVal.ty : NormVal → NormTy
  | .i32 _ => .i32Ty
  | .i64 _ => .i64Ty

/-- Validator control tag: the machine's `NormLabelKind` plus the
validator-only else-seen and function frames (rcic.wasm_v* tg 1..5). -/
inductive NormTTag
  | blk | lp | ift | els | fn
  deriving DecidableEq, Repr

/-- A validator frame (rcic.wasm_v*'s `{tg, rt, base, un}`). `entry` is the
operand-type stack at push time — `entry.length` is the scm frame's `base`.
`un` is the unreachable flag set by unconditional br/return. -/
structure NormTFrame where
  tag : NormTTag
  rt : Option NormTy
  entry : List NormTy
  un : Bool
  deriving DecidableEq, Repr

/-- Validator context for one function body: the local types and all
function signatures (the scm walk's ls/tys/fns, resolved against
`NormFunc`). -/
structure NormVCtx where
  locals : List NormTy
  funcs : List (List NormTy × Option NormTy)
  deriving DecidableEq, Repr

/-- Validator state: operand type stack + control frame stack. -/
structure NormVSt where
  os : List NormTy
  cs : List NormTFrame
  deriving DecidableEq, Repr

/-- Bounded pop (rcic.wasm_tck_pop): pops `t` only above the innermost
frame's base; at or below the base the pop succeeds vacuously iff `un`
(unreachable code is stack-polymorphic). -/
def normTckPop (os : List NormTy) (base : Nat) (un : Bool) (t : NormTy) :
    Option (List NormTy) :=
  if base < os.length then
    match os with
    | t' :: rest => if t' = t then some rest else none
    | [] => none
  else if un then some os else none

/-- Bounded any-pop (rcic.wasm_tck_any, used by `drop`/`select`): the popped
type, or `none` for the unknown element available under `un` below the
base. -/
def normTckAny (os : List NormTy) (base : Nat) (un : Bool) :
    Option (Option NormTy × List NormTy) :=
  if base < os.length then
    match os with
    | t' :: rest => some (some t', rest)
    | [] => none
  else if un then some (none, os) else none

/-- Frame-bounded pop (rcic.wasm_v_pop: the innermost frame bounds the
pop). The bottom `fn` frame has base 0, so its pops are ordinary
length-bounded pops. -/
def normVPop (os : List NormTy) (cs : List NormTFrame) (t : NormTy) :
    Option (List NormTy) :=
  match cs with
  | f :: _ => normTckPop os f.entry.length f.un t
  | [] => none

/-- Frame-bounded pops in list order (rcic.wasm_v_pops). -/
def normVPops (os : List NormTy) (cs : List NormTFrame) :
    List NormTy → Option (List NormTy)
  | [] => some os
  | t :: ts =>
    (normVPop os cs t).bind fun os' => normVPops os' cs ts

/-- Sig application (rcic.wasm_v_apply): pop `ps` (pop order), push `rs`
head-first. -/
def normVApply (os : List NormTy) (cs : List NormTFrame)
    (ps rs : List NormTy) : Option (List NormTy) :=
  (normVPops os cs ps).map fun os' => rs ++ os'

/-- Frame end-check (rcic.wasm_v_fchk): the declared result type if any is
popped against the frame's bound, then the operand stack must be exactly
the frame's entry height. -/
def normVFchk (os : List NormTy) (f : NormTFrame) : Option (List NormTy) :=
  (match f.rt with
   | some t => normTckPop os f.entry.length f.un t
   | none => some os).bind fun os' =>
    if os'.length = f.entry.length then some os' else none

/-- The entry-equality the machine's `normBr` needs: `br` truncates the
operand stack to the target label's height keeping the TOP elements, so a
validated branch requires the top `base` types to equal the target's entry
types. Vacuous under `un`, like `tck_pop`; the `fn` target passes trivially
(its entry is `[]`). Structured targets are always `rt = none` in the norm
IR, so the entry types are exactly the continuation's expected types at
`endPc` (and at `startPc+1` for loops). -/
def normVBrEntryOK (s : NormVSt) (tgt : NormTFrame) : Bool :=
  match s.cs with
  | h :: _ =>
    if h.un then true else s.os.take tgt.entry.length == tgt.entry
  | [] => false

/-- (rcic.wasm_v_brk): pop the branch arity (the label's `rt`) against the
INNERMOST frame, truncate the operand types to the innermost base, and mark
the innermost frame unreachable. -/
def normVBrk (s : NormVSt) (lrt : Option NormTy) : Option NormVSt :=
  match s.cs with
  | [] => none
  | h :: rest =>
    (match lrt with
     | some t => normVPop s.os s.cs t
     | none => some s.os).bind fun os' =>
      some ⟨os'.take h.entry.length, ⟨h.tag, h.rt, h.entry, true⟩ :: rest⟩

/-- `br n` (rcic.wasm_v_br op-12 path): the target's `rt` is the branch
arity — none for loops — then `normVBrk`, guarded by `normVBrEntryOK`. -/
def normVBr (s : NormVSt) (n : Nat) : Option NormVSt :=
  match s.cs.drop n with
  | [] => none
  | tgt :: _ =>
    let lrt := if tgt.tag = .lp then none else tgt.rt
    if normVBrEntryOK s tgt then normVBrk s lrt else none

/-- `br_if n` (rcic.wasm_v_br op-13 path): pop the i32 condition, then the
branch arity and push it back — the taken path is additionally guarded by
`normVBrEntryOK`. -/
def normVBrIf (s : NormVSt) (n : Nat) : Option NormVSt :=
  match s.cs.drop n with
  | [] => none
  | tgt :: _ =>
    let lrt := if tgt.tag = .lp then none else tgt.rt
    (normVPop s.os s.cs .i32Ty).bind fun os' =>
      (match lrt with
       | some t => (normVPop os' s.cs t).map fun os'' => t :: os''
       | none => some os').bind fun os'' =>
        if normVBrEntryOK s tgt then some { s with os := os'' } else none

/-- Flat instruction signature (the scalar/conversion/memory rows of
rcic.wasm_op_sig): `ps` in pop order (stack top first), `rs` pushed
head-first. `none` for the ops `normVStep` handles separately. -/
def normInstrSig : NormInstr → Option (List NormTy × List NormTy)
  | .i32Const _ => some ([], [.i32Ty])
  | .i32Eqz => some ([.i32Ty], [.i32Ty])
  | .i32Cmp _ => some ([.i32Ty, .i32Ty], [.i32Ty])
  | .i32Add | .i32Sub | .i32Mul | .i32Bit _ | .i32Shift _ =>
    some ([.i32Ty, .i32Ty], [.i32Ty])
  | .i64Const _ => some ([], [.i64Ty])
  | .i64Eqz => some ([.i64Ty], [.i32Ty])
  | .i64Cmp _ => some ([.i64Ty, .i64Ty], [.i32Ty])
  | .i64Add | .i64Sub | .i64Mul | .i64DivS | .i64RemS | .i64Bit _ | .i64Shift _ =>
    some ([.i64Ty, .i64Ty], [.i64Ty])
  | .i32WrapI64 => some ([.i64Ty], [.i32Ty])
  | .i64ExtendI32U | .i64ExtendI32S => some ([.i32Ty], [.i64Ty])
  | .i32Load _ | .i32Load8U _ => some ([.i32Ty], [.i32Ty])
  | .i64Load _ | .i64Load8U _ => some ([.i32Ty], [.i64Ty])
  | .i32Store _ | .i32Store8 _ => some ([.i32Ty, .i32Ty], [])
  | .i64Store _ | .i64Store8 _ => some ([.i64Ty, .i32Ty], [])
  | .memorySize => some ([], [.i32Ty])
  | _ => none

/-- One validation step (transcription of rcic.wasm_vstep over the norm
grammar, with the `normVBrEntryOK` refinement on branches). -/
def normVStep (C : NormVCtx) (i : NormInstr) (s : NormVSt) : Option NormVSt :=
  match i with
  | .block =>
    some { s with cs := ⟨.blk, none, s.os, false⟩ :: s.cs }
  | .loop =>
    some { s with cs := ⟨.lp, none, s.os, false⟩ :: s.cs }
  | .ifE =>
    (normVPop s.os s.cs .i32Ty).map fun os' =>
      ⟨os', ⟨.ift, none, os', false⟩ :: s.cs⟩
  | .elseE =>
    match s.cs with
    | f :: rest =>
      if f.tag = .ift then
        (normVFchk s.os f).map fun os' =>
          ⟨os', ⟨.els, f.rt, f.entry, f.un⟩ :: rest⟩
      else none
    | [] => none
  | .endI =>
    match s.cs with
    | f :: rest =>
      if f.tag = .fn then none
      else (normVFchk s.os f).map fun os' =>
        ⟨f.rt.toList ++ os', rest⟩
    | [] => none
  | .br n => normVBr s n
  | .brIf n => normVBrIf s n
  | .call f =>
    match C.funcs.get? f with
    | none => none
    | some (ps, rs) =>
      (normVPops s.os s.cs ps.reverse).map fun os' =>
        ⟨os' ++ rs.toList, s.cs⟩
  | .return =>
    normVBrk s ((s.cs.getLast?).bind NormTFrame.rt)
  | .drop =>
    match s.cs with
    | f :: _ =>
      (normTckAny s.os f.entry.length f.un).map fun ⟨_, os'⟩ => ⟨os', s.cs⟩
    | [] => none
  | .select =>
    (normVPop s.os s.cs .i32Ty).bind fun os' =>
      match s.cs with
      | f :: _ =>
        (normTckAny os' f.entry.length f.un).bind fun (t?, os'') =>
          match t? with
          | none => some ⟨os'', s.cs⟩
          | some t =>
            (normVPop os'' s.cs t).map fun os''' => ⟨t :: os''', s.cs⟩
      | [] => none
  | .localGet i =>
    (C.locals.get? i).map fun lt => ⟨lt :: s.os, s.cs⟩
  | .localSet i =>
    (C.locals.get? i).bind fun lt =>
      (normVPop s.os s.cs lt).map fun os' => ⟨os', s.cs⟩
  | .localTee i =>
    (C.locals.get? i).bind fun lt =>
      (normVPop s.os s.cs lt).map fun os' => ⟨lt :: os', s.cs⟩
  | i =>
    (normInstrSig i).bind fun (ps, rs) =>
      (normVApply s.os s.cs ps rs).map fun os' => ⟨os', s.cs⟩

/-- The body walk: `vstep` folded left-to-right (rcic.wasm_vgo). -/
def normVRun (C : NormVCtx) (s : NormVSt) : List NormInstr → Option NormVSt
  | [] => some s
  | i :: is => (normVStep C i s).bind fun s' => normVRun C s' is

/-- The implicit function frame (rcic.wasm_v*'s tg-5 bottom frame): base 0,
result type the function's declared `result`. -/
def normVInit (f : NormFunc) : NormVSt :=
  ⟨[], [⟨.fn, f.result, [], false⟩]⟩

/-- Body acceptance: the walk consumes the body and the function frame's
end-check holds — the result types are produced and nothing else remains.
There is no terminal `end` in the norm IR; exhaustion closes the implicit
frame. -/
def normVAccept (C : NormVCtx) (f : NormFunc) : Bool :=
  match normVRun C (normVInit f) f.body with
  | some ⟨os, [f0]⟩ =>
    (f0.tag == .fn) &&
      (match normVFchk os f0 with | some os' => os'.isEmpty | none => false)
  | _ => false

/-- The body context for `f` inside `m` (the scm walk's ls/tys/fns). -/
def NormVCtx.ofModule (m : NormModule) (f : NormFunc) : NormVCtx :=
  ⟨f.params ++ f.locals, m.funcs.map fun g => (g.params, g.result)⟩

/-- Module validity: the §3 profile predicate, every body accepted by the
validator walk, and every data segment in bounds (the scm `wasm_dat_each`
bound). The codec decides this on presented bytes; this is the Prop its
universal soundness stands behind. -/
def NormValidModule (m : NormModule) : Prop :=
  InResiduaWasm0 m ∧
    (∀ f ∈ m.funcs, normVAccept (NormVCtx.ofModule m f) f = true) ∧
    (∀ d ∈ m.datas, d.1 + d.2.length ≤ m.memPages * NormWasmPage)

/-- The machine control stack corresponds to the validator's frame stack
(minus the implicit function frame): same length, matching kinds (the
validator's else-seen is still the machine's `ifK`), matching heights, and
every label's `endPc` is the computed matching-end position of its opener
(the §6 control map). -/
def NormLabelsCorrespond (body : List NormInstr) (ls : List NormLabel)
    (cs : List NormTFrame) : Prop :=
  cs.length = ls.length + 1 ∧
    (cs.getLast?).map NormTFrame.tag = some .fn ∧
    ∀ i (hi : i < ls.length),
      ∃ (hc : i < cs.length),
        let lab := ls[i]
        let fr := cs[i]
        (match fr.tag with
         | .blk => lab.kind = .blockK
         | .lp => lab.kind = .loopK
         | .ift | .els => lab.kind = .ifK
         | .fn => False) ∧
        lab.height = fr.entry.length ∧
        (∃ elsePc, normElseEnd body lab.startPc = some (elsePc, lab.endPc)) ∧
        (match lab.kind with
         | .blockK => body.get? lab.startPc = some .block
         | .loopK => body.get? lab.startPc = some .loop
         | .ifK => body.get? lab.startPc = some .ifE)

/-- A saved call frame is resumable: the caller body validates to the
resume pc, the saved labels correspond to the validator frames there, and
the operand types are the saved stack's types extended at the TAIL by the
callee's result (the machine resumes with `savedStack ++ res`). -/
def NormFrameOK (m : NormModule) (fr : NormFrame) : Prop :=
  ∃ g, m.funcs.get? fr.callerIdx = some g ∧
    ∃ s, normVRun (NormVCtx.ofModule m g) (normVInit g) (g.body.take fr.retPc) =
        some s ∧
      NormLabelsCorrespond g.body fr.savedLabels s.cs ∧
      ∃ rs, s.os = fr.savedStack.map NormVal.ty ++ rs

/-- Config typing for the norm machine: the current body validates to `pc`,
the operand stack carries exactly the validator's types, the locals carry
the declared types, control/call stacks correspond, and the fixed-size
memory is exactly its page count. Progress and preservation are S2/S3. -/
def NormStateTy (st : NormState) : Prop :=
  ∃ f, st.module.funcs.get? st.funcIdx = some f ∧
    (∃ s, normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s ∧
      s.os = st.operandStack.map NormVal.ty ∧
      NormLabelsCorrespond f.body st.controlStack s.cs) ∧
    st.locals.map NormVal.ty = f.params ++ f.locals ∧
    (∀ fr ∈ st.callStack, NormFrameOK st.module fr) ∧
    st.linearMemory.bytes.length = st.module.memPages * NormWasmPage

/-! ## Basic walk lemmas (the S1 seal set) -/

@[simp] theorem normVRun_nil (C : NormVCtx) (s : NormVSt) :
    normVRun C s [] = some s := rfl

@[simp] theorem normVRun_cons (C : NormVCtx) (s : NormVSt)
    (i : NormInstr) (is : List NormInstr) :
    normVRun C s (i :: is) =
      (normVStep C i s).bind (normVRun C · is) := rfl

/-- Run composition: the prefix walk appends (needed by `NormStateTy` at
`pc` and `pc+1` in S2/S3). -/
theorem normVRun_append (C : NormVCtx) (s : NormVSt)
    (is₁ is₂ : List NormInstr) :
    normVRun C s (is₁ ++ is₂) =
      (normVRun C s is₁).bind (normVRun C · is₂) := by
  induction is₁ generalizing s with
  | nil => rfl
  | cons i is₁ ih =>
    simp only [List.cons_append, normVRun_cons, Option.bind]
    cases normVStep C i s with
    | none => rfl
    | some s' => exact ih s'

/-- A successful step's validator state decomposes. -/
theorem normVRun_cons_inv (C : NormVCtx) (s s' : NormVSt)
    (i : NormInstr) (is : List NormInstr)
    (h : normVRun C s (i :: is) = some s') :
    ∃ s₁, normVStep C i s = some s₁ ∧ normVRun C s₁ is = some s' := by
  rw [normVRun_cons] at h
  cases hs : normVStep C i s with
  | none => rw [hs] at h; exact Option.noConfusion h
  | some s₁ => rw [hs] at h; exact ⟨s₁, rfl, h⟩

/-- `take (n+1)` walks one more instruction (the `pc`/`pc+1` step). -/
theorem normVRun_take_succ (C : NormVCtx) (s : NormVSt)
    (is : List NormInstr) (n : Nat) (i : NormInstr)
    (hi : is.get? n = some i) :
    normVRun C s (is.take (n + 1)) =
      (normVRun C s (is.take n)).bind (normVStep C i) := by
  have ht : is.take (n + 1) = is.take n ++ [i] := by
    induction is generalizing n with
    | nil => simp at hi
    | cons a l ih =>
      cases n with
      | zero =>
        simp only [List.get?_cons_zero, Option.some.injEq] at hi
        subst hi
        simp [List.take_succ_cons]
      | succ n =>
        simp only [List.get?_cons_succ] at hi
        simp only [List.take_succ_cons, ih n hi, List.cons_append]
  rw [ht, normVRun_append]
  congr 1
  funext s'
  rw [normVRun_cons]
  cases normVStep C i s' with
  | none => rfl
  | some s'' => rfl

/-- Bounded pops never grow the operand stack (the `un` branch preserves
it). -/
theorem normTckPop_length (os : List NormTy) (b : Nat) (u : Bool)
    (t : NormTy) (os' : List NormTy)
    (h : normTckPop os b u t = some os') : os'.length ≤ os.length := by
  unfold normTckPop at h
  split at h <;> (try split at h) <;> (try split at h)
  all_goals first
    | exact Option.noConfusion h
    | (simp_all only [Option.some.injEq, List.cons.injEq, List.length_cons];
       omega)

theorem normVPop_length (os : List NormTy) (cs : List NormTFrame)
    (t : NormTy) (os' : List NormTy)
    (h : normVPop os cs t = some os') : os'.length ≤ os.length := by
  unfold normVPop at h
  cases cs with
  | nil => exact Option.noConfusion h
  | cons f _ =>
    exact normTckPop_length os f.entry.length f.un t os' h

theorem normVPops_length (os : List NormTy) (cs : List NormTFrame)
    (ts : List NormTy) (os' : List NormTy)
    (h : normVPops os cs ts = some os') : os'.length ≤ os.length := by
  induction ts generalizing os with
  | nil => unfold normVPops at h; rw [Option.some.inj h]; omega
  | cons t ts ih =>
    unfold normVPops at h
    cases hp : normVPop os cs t with
    | none => rw [hp, Option.bind] at h; exact Option.noConfusion h
    | some o1 =>
      rw [hp, Option.bind] at h
      exact Nat.le_trans (ih o1 h) (normVPop_length os cs t o1 hp)

end Rcic.WasmNorm

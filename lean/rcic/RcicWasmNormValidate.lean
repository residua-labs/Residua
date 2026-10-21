/-
WX-002 S5 — the executable validator + agreement pins (cc's ruling on
#6613, comment-6131955159: "S5 = a decidable `NormValidate` with
`NormValidate m = true → NormValidModule m` (soundness; completeness not
required); plus the shared-fixture agreement pins between `rcic.wasm_v*`'s
corpus and `NormValidate`, in the `ScmExec` M-002 pin pattern.").

`NormValidate` is the Bool face of `NormValidModule`, clause for clause:
the §3 profile predicate, the `normVAccept` walk over every body, and
the data-segment bound. Soundness is the bridge the row needs — the
deployed validator's verdict implies the Lean premise; completeness is
deliberately not claimed (the norm IR's frame discipline is a strictening
of the scm walk at several sites, recorded in `RcicWasmNormTy`'s header).

Agreement pins (`Pins.Validate`): `apps/rcic-wasm-codec`'s 65-row corpus
decides over PRESENTED BYTES; `NormValidate` decides over the decoded
norm IR. A row is shared exactly when its bytes decode to a module every
instruction of which lands in the norm grammar — the fixture is then the
corpus row's own `mod` record transcribed (instructions `{op,x,y}` →
`NormInstr`, blocktype immediates dropped, the body's terminal `end`
dropped, memarg `y` = `NormMemArg.offset`, align dropped). Shareable:

- 8 accept rows (0,1,3,4,5,6,8,9) → `NormValidate m = true` and, via
  soundness, `NormValidModule m`.
- 10 in-domain refusal rows (41,42,43,44,45,52,53,54,55,56): the module
  decodes but the body walk refuses → `NormValidate m = false` and
  `¬ NormValidModule m` (the walk's `normVAccept = false` refutes the
  module-validity conjunct directly).

Boundary rows (the #6634 ruling put the four codec ops in the norm
grammar; these two rows sit on that boundary):

- Row 7 (accept): `loop` + `br_if` + `i32.eqz` — fully in the grammar;
  shared as an accept fixture (`NormValidate = true`).
- Row 2 (corpus accept): stateable since S2-4 but REFUSED by the norm
  walk — OPEN, named divergence
  `[wx002_norm_grammar_narrower_i64_blocktype_if]`: the codec accepts
  the `if`'s i64 blocktype (0x7E) immediate; the norm IR's `NormInstr`
  carries no blocktype immediate, so every structured frame is
  `rt = none`, and the walk's else/end height-check refuses the
  transcribed module. The norm grammar is narrower than the frozen
  profile here — the same class as the four codec-only ops before
  S2-4. Pinned below as corpus-accept/norm-refuse: a divergence
  record, not an agreement (no completeness claim).

Still not shareable, recorded not hidden:

- All remaining refusal rows (10–40, 46–51, 57–64) refuse on the
  decode/section/canonicality surface — head, section order, valtype,
  typeidx, memflag, export shape, align, blocktype, leb minimality,
  unmerged locals, stray data — before any norm module exists. Rows 51
  (align > natural) and 57 (blocktype 0x7B) are additionally
  unrepresentable at the norm IR: `NormMemArg` drops align and
  `NormInstr` drops blocktype immediates.

`closure_claim = 0`.
-/
import rcic.RcicWasmNormTy

namespace Rcic.WasmNorm

/-- Decidable §3 profile predicate — the Bool face of `InResiduaWasm0`:
the entry function exists with signature `(i32,i32) → i64` and the one
memory is within the page limit. -/
def inResiduaWasm0B (m : NormModule) : Bool :=
  match m.funcs.get? m.entry with
  | some f =>
    decide (f.params = [.i32Ty, .i32Ty]) && decide (f.result = some .i64Ty) &&
      decide (1 ≤ m.memPages) && decide (m.memPages ≤ 65536)
  | none => false

/-- The executable validator (WX-002 S5): the profile predicate, every
body accepted by the `normVRun` walk, and every data segment in bounds —
`NormValidModule`'s three conjuncts as one Bool. -/
def NormValidate (m : NormModule) : Bool :=
  inResiduaWasm0B m &&
    m.funcs.all (fun f => normVAccept (NormVCtx.ofModule m f) f) &&
    m.datas.all (fun d => decide (d.1 + d.2.length ≤ m.memPages * NormWasmPage))

/-- Soundness (the S5 bridge): a `true` verdict implies module validity.
Completeness is not claimed — the norm walk's frame discipline can refuse
modules the scm walk accepts (recorded in `RcicWasmNormTy`'s header and
in this file's pin boundary). -/
theorem normValidate_sound (m : NormModule)
    (h : NormValidate m = true) : NormValidModule m := by
  unfold NormValidate at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hp, hv⟩, hd⟩ := h
  refine ⟨?_, fun f hf => (List.all_eq_true.mp hv) f hf, fun d hd' =>
    of_decide_eq_true ((List.all_eq_true.mp hd) d hd')⟩
  unfold inResiduaWasm0B at hp
  cases he : m.funcs.get? m.entry with
  | none => rw [he] at hp; exact Bool.noConfusion hp
  | some f =>
    rw [he] at hp
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hp
    exact ⟨f, he, of_decide_eq_true hp.1.1.1,
      of_decide_eq_true hp.1.1.2, of_decide_eq_true hp.1.2,
      of_decide_eq_true hp.2⟩

/-- A refused body walk refutes module validity: the `normVAccept`
conjunct of `NormValidModule` cannot hold at a func whose walk fails. -/
theorem normValidModule_not_of_accept_false (m : NormModule) (f : NormFunc)
    (hf : f ∈ m.funcs)
    (h : normVAccept (NormVCtx.ofModule m f) f = false) :
    ¬ NormValidModule m := fun ⟨_, hv, _⟩ =>
  absurd (hv f hf) (by rw [h]; exact Bool.noConfusion)

namespace Pins.Validate

/-- Corpus-row shorthand: the (i32,i32) → i64 signature every corpus
function carries. -/
private def sig2 : List NormTy := [.i32Ty, .i32Ty]

/-! Shared accept fixtures (`apps/rcic-wasm-codec` corpus rows 0–9 whose
instructions all land in the norm grammar). Each `modRowN` is that row's
`expected.mod` transcribed: `tys`/`fns` give every func the shared
signature, `code[i].ls` expand to `locals`, `code[i].is` drop blocktype
immediates and the terminal `end`, `mems[0].min` is `memPages`, `dat`
maps `off`/`xs`, the sole export's `i` is `entry`. -/

/-- Row 0 — minimal module: `i64.const 42`. -/
private def modRow0 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.i64Const 42] }], 1, [], 0⟩

/-- Row 1 — locals+arith: `i32.const 3; local.set 2; local.get 0;
local.get 2; i32.add; drop; i64.const 7; i64.const 6; i64.mul`, one
i32 local decl. -/
private def modRow1 : NormModule :=
  ⟨[{ params := sig2, locals := [.i32Ty], result := some .i64Ty,
      body := [.i32Const 3, .localSet 2, .localGet 0, .localGet 2,
        .i32Add, .drop, .i64Const 7, .i64Const 6, .i64Mul] }], 1, [], 0⟩

/-- Row 3 — direct call: f0 calls f1; f1 is
`local.get 0; i64.extend_i32_s; local.get 1; i64.extend_i32_s; i64.add`. -/
private def modRow3 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.localGet 0, .localGet 1, .call 1] },
    { params := sig2, locals := [], result := some .i64Ty,
      body := [.localGet 0, .i64ExtendI32S, .localGet 1, .i64ExtendI32S,
        .i64Add] }], 1, [], 0⟩

/-- Row 4 — memory: `memory.size; local.get 0; i32.store8(0);
local.get 0; i32.load8_u(0); drop; i64.const 0`. -/
private def modRow4 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.memorySize, .localGet 0, .i32Store8 ⟨0⟩, .localGet 0,
        .i32Load8U ⟨0⟩, .drop, .i64Const 0] }], 1, [], 0⟩

/-- Row 5 — row 0's module plus an active data segment `{off 0, [7,8,9]}`. -/
private def modRow5 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.i64Const 42] }], 1, [(0, [7, 8, 9])], 0⟩

/-- Row 6 — `local.get 0; if; i64.const 7; br 1; end; i64.const 9;
return` — the `br 1` targets the function frame. -/
private def modRow6 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.localGet 0, .ifE, .i64Const 7, .br 1, .endI, .i64Const 9,
        .return] }], 1, [], 0⟩

/-- Row 8 — i64 ops: `local.get 0; i64.extend_i32_s; i64.const 6;
i64.div_s; i64.const 3; i64.shr_u; local.get 1; i64.extend_i32_s;
i64.rem_s; i32.wrap_i64; drop; i64.const 0`. -/
private def modRow8 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.localGet 0, .i64ExtendI32S, .i64Const 6, .i64DivS,
        .i64Const 3, .i64Shift .shrUOp, .localGet 1, .i64ExtendI32S,
        .i64RemS, .i32WrapI64, .drop, .i64Const 0] }], 1, [], 0⟩

/-- Row 7 — `loop; local.get 0; i32.eqz; br_if 0; end; i64.const 5` —
shared since S2-4 (`i32.eqz` is in the grammar; the loop's `br_if 0`
targets the `rt = none` loop frame). -/
private def modRow7 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.loop, .localGet 0, .i32Eqz, .brIf 0, .endI,
        .i64Const 5] }], 1, [], 0⟩

/-- Row 9 — merged locals `[(2,i32),(1,i64)]`; body `i64.const 0`. -/
private def modRow9 : NormModule :=
  ⟨[{ params := sig2, locals := [.i32Ty, .i32Ty, .i64Ty],
      result := some .i64Ty, body := [.i64Const 0] }], 1, [], 0⟩

/-! Shared refusal fixtures — rows whose bytes decode to a norm module
the body walk then refuses (the corpus's `wasm_v*`-domain refusals). -/

/-- Row 41 — `br 5` out of range, then `i64.const 1`. -/
private def modRow41 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.br 5, .i64Const 1] }], 1, [], 0⟩

/-- Row 42 — `local.get 9` out of range, `drop`, `i64.const 1`. -/
private def modRow42 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.localGet 9, .drop, .i64Const 1] }], 1, [], 0⟩

/-- Row 43 — `call 3` out of range (one func). -/
private def modRow43 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.call 3] }], 1, [], 0⟩

/-- Row 44 — `i32.add` on an empty operand stack, then `i64.const 1`. -/
private def modRow44 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.i32Add, .i64Const 1] }], 1, [], 0⟩

/-- Row 45 — `i64.const 1; i32.const 2; i32.add`: the second pop meets an
i64, then `drop` and an `i64.const 0` tail. -/
private def modRow45 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.i64Const 1, .i32Const 2, .i32Add, .drop,
        .i64Const 0] }], 1, [], 0⟩

/-- Row 52 — stray `end` at the function frame, then `i64.const 1`. -/
private def modRow52 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.endI, .i64Const 1] }], 1, [], 0⟩

/-- Row 53 — `i64.const 1` then an `end` at the function frame. -/
private def modRow53 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.i64Const 1, .endI] }], 1, [], 0⟩

/-- Row 54 — `block; else; end; i64.const 1`: `else` at a block frame. -/
private def modRow54 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.block, .elseE, .endI, .i64Const 1] }], 1, [], 0⟩

/-- Row 55 — `block; i64.const 1; end`: the block's `rt = none` end-check
cannot consume the i64. -/
private def modRow55 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.block, .i64Const 1, .endI] }], 1, [], 0⟩

/-- Row 56 — `block; i64.const 1` with no `end` at all: the block frame
  is still open at body exhaustion. -/
private def modRow56 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.block, .i64Const 1] }], 1, [], 0⟩

/-! Row 2 — OPEN divergence `[wx002_norm_grammar_narrower_i64_blocktype_if]`
(the norm grammar is narrower than the frozen profile; the same class as
the four codec-only ops before S2-4). The corpus ACCEPTS these bytes
(the codec reads the `if`'s i64 blocktype 0x7E); the transcribed norm
module states every instruction (the `if` blocktype immediate is dropped
per the fixture convention), but the walk's `rt = none` else-check
cannot consume the branch value, so `NormValidate` REFUSES. A
divergence record, not an agreement; no completeness claim. -/

/-- Row 2 — `block; local.get 0; i32.eqz; br_if 0; loop; local.get 1;
i32.eqz; br_if 0; end; local.get 0; if (bt i64); i64.const 1; else;
i64.const 2; end; drop; local.get 0; local.get 1; local.get 0;
select; drop; end; i64.const 0`. -/
private def modRow2 : NormModule :=
  ⟨[{ params := sig2, locals := [], result := some .i64Ty,
      body := [.block, .localGet 0, .i32Eqz, .brIf 0, .loop, .localGet 1,
        .i32Eqz, .brIf 0, .endI, .localGet 0, .ifE, .i64Const 1, .elseE,
        .i64Const 2, .endI, .drop, .localGet 0, .localGet 1, .localGet 0,
        .select, .drop, .endI, .i64Const 0] }], 1, [], 0⟩

/-! ## The agreement pins (verdict per shared corpus row)

Each `pin_wx002_rowN_*` pins the row's corpus verdict over the row's own
decoded `mod`: `= true` where the codec accepted, `= false` where the
body walk refused. Accept rows additionally pin `NormValidModule`
through `normValidate_sound` (the verdict carries the Prop); refusal
rows pin `¬ NormValidModule` (the refused walk refutes the conjunct). -/

theorem pin_wx002_row0_accept : NormValidate modRow0 = true := by decide
theorem pin_wx002_row1_accept : NormValidate modRow1 = true := by decide
theorem pin_wx002_row3_accept : NormValidate modRow3 = true := by decide
theorem pin_wx002_row4_accept : NormValidate modRow4 = true := by decide
theorem pin_wx002_row5_accept : NormValidate modRow5 = true := by decide
theorem pin_wx002_row6_accept : NormValidate modRow6 = true := by decide
theorem pin_wx002_row7_accept : NormValidate modRow7 = true := by decide
theorem pin_wx002_row8_accept : NormValidate modRow8 = true := by decide
theorem pin_wx002_row9_accept : NormValidate modRow9 = true := by decide

theorem pin_wx002_row0_valid : NormValidModule modRow0 :=
  normValidate_sound _ (by decide)
theorem pin_wx002_row1_valid : NormValidModule modRow1 :=
  normValidate_sound _ (by decide)
theorem pin_wx002_row3_valid : NormValidModule modRow3 :=
  normValidate_sound _ (by decide)
theorem pin_wx002_row4_valid : NormValidModule modRow4 :=
  normValidate_sound _ (by decide)
theorem pin_wx002_row5_valid : NormValidModule modRow5 :=
  normValidate_sound _ (by decide)
theorem pin_wx002_row6_valid : NormValidModule modRow6 :=
  normValidate_sound _ (by decide)
theorem pin_wx002_row7_valid : NormValidModule modRow7 :=
  normValidate_sound _ (by decide)
theorem pin_wx002_row8_valid : NormValidModule modRow8 :=
  normValidate_sound _ (by decide)
theorem pin_wx002_row9_valid : NormValidModule modRow9 :=
  normValidate_sound _ (by decide)

theorem pin_wx002_row41_refuse : NormValidate modRow41 = false := by decide
theorem pin_wx002_row42_refuse : NormValidate modRow42 = false := by decide
theorem pin_wx002_row43_refuse : NormValidate modRow43 = false := by decide
theorem pin_wx002_row44_refuse : NormValidate modRow44 = false := by decide
theorem pin_wx002_row45_refuse : NormValidate modRow45 = false := by decide
theorem pin_wx002_row52_refuse : NormValidate modRow52 = false := by decide
theorem pin_wx002_row53_refuse : NormValidate modRow53 = false := by decide
theorem pin_wx002_row54_refuse : NormValidate modRow54 = false := by decide
theorem pin_wx002_row55_refuse : NormValidate modRow55 = false := by decide
theorem pin_wx002_row56_refuse : NormValidate modRow56 = false := by decide

theorem pin_wx002_row41_not_valid : ¬ NormValidModule modRow41 :=
  normValidModule_not_of_accept_false _ _ (List.Mem.head _) (by decide)
theorem pin_wx002_row42_not_valid : ¬ NormValidModule modRow42 :=
  normValidModule_not_of_accept_false _ _ (List.Mem.head _) (by decide)
theorem pin_wx002_row43_not_valid : ¬ NormValidModule modRow43 :=
  normValidModule_not_of_accept_false _ _ (List.Mem.head _) (by decide)
theorem pin_wx002_row44_not_valid : ¬ NormValidModule modRow44 :=
  normValidModule_not_of_accept_false _ _ (List.Mem.head _) (by decide)
theorem pin_wx002_row45_not_valid : ¬ NormValidModule modRow45 :=
  normValidModule_not_of_accept_false _ _ (List.Mem.head _) (by decide)
theorem pin_wx002_row52_not_valid : ¬ NormValidModule modRow52 :=
  normValidModule_not_of_accept_false _ _ (List.Mem.head _) (by decide)
theorem pin_wx002_row53_not_valid : ¬ NormValidModule modRow53 :=
  normValidModule_not_of_accept_false _ _ (List.Mem.head _) (by decide)
theorem pin_wx002_row54_not_valid : ¬ NormValidModule modRow54 :=
  normValidModule_not_of_accept_false _ _ (List.Mem.head _) (by decide)
theorem pin_wx002_row55_not_valid : ¬ NormValidModule modRow55 :=
  normValidModule_not_of_accept_false _ _ (List.Mem.head _) (by decide)
theorem pin_wx002_row56_not_valid : ¬ NormValidModule modRow56 :=
  normValidModule_not_of_accept_false _ _ (List.Mem.head _) (by decide)

/-! Row 2 — the divergence pins for
`[wx002_norm_grammar_narrower_i64_blocktype_if]`: corpus-accept /
norm-refuse (the walk refuses at the `else` of the i64-blocktype `if`;
the codec accepted the same bytes). A named divergence record, not an
agreement; completeness of the norm grammar against the frozen profile
stays open at this residue. -/

theorem pin_wx002_row2_refuse : NormValidate modRow2 = false := by decide

theorem pin_wx002_row2_not_valid : ¬ NormValidModule modRow2 :=
  normValidModule_not_of_accept_false _ _ (List.Mem.head _) (by decide)

end Pins.Validate

end Rcic.WasmNorm


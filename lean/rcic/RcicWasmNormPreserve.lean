/-
WX-002 S3 — PRESERVATION (the subject-reduction segment): every
non-stuck step keeps `NormStateTy` — `NormStep st = .step st'` preserves
`NormStateTy`, mirroring WasmCert's `reduce_preserves_typing`
(subject-reduction file).  S1 (`RcicWasmNormTy`, batch 16 #6626) supplies
`NormStateTy`/`NormValidModule`/`normVRun`; S2 (`RcicWasmNormStep`) is the
machine.

## Measurement findings that shape the statement

`wx002_preservation` as the bare sentence `NormStateTy st →
NormStep st = .step st' → NormStateTy st'` is **false** — the machine's
`normBr`/`brIf`/`ifE`/`elseE`/`normReturn` arms produce `.step` outcomes
the scm-derived validator correspondence (`s.os = operandStack.map ty`)
cannot follow.  The obstructions classify into four classes:

- **(A) Machine keep-vs-validator-live-output.** `normVFchk` is
  length-only (`os'.length = f.entry.length`), so the validator's `os`
  at a label's `end`/`else` is elementwise-free — it records the body's
  *output*, while the machine's branch landings keep a physical prefix
  of the stack.  `brIf`-taken (`rest.take base` vs the live continuation
  `os''`), `ifE`-else (`rest` vs the if-body output `os`), `elseE`
  (the if-body output vs the else-body output `os''`), and `ifE`-no-else
  (`rest` vs `os''`) all diverge.  No premise fixes them — `os''` is
  fixed by the body's own code.  These instructions are excluded by
  `NormStepSafe`.
- **(B) `br`-keep-top-height vs the dead-region os.** `normBr` keeps the
  TOP `lab.height` elements; the validator's `os''` at `endPc` is the
  dead region's walk result, which under `un` truncates to
  `os.take h₀.entry.length` and then freezes only while every
  intermediate frame's `entry.length` bounds the pops above `h₀.base`.
  `br 0` (and any `br` whose h₀..tgt bases are all equal) works; a
  `br n` across unequal bases keeps a middle slice the validator never
  produces.  `NormStepSafe` requires uniform entry heights for non-loop
  targets.
- **(C) `normVStep` at `pc` needn't succeed.**  `NormStateTy` only walks
  to `pc`; `br`/`endI`/`brIf`/`select`/`call`/`localSet`/`localTee` can
  machine-step where the validator refuses (`normVBrEntryOK`,
  `normVFchk`'s length check, arg-type mismatches).  `NormValidModule`
  (whole-body `normVAccept`) discharges `normVStep` at every pc.
- **(D) Dead-region (`un`) divergence.**  At `s.cs.head.un = true`
  positions the validator pops vacuously while the machine pops real
  values (`block(i32,i32); br 0; drop` — `drop` machine-pops, the
  validator keeps `os`).  The `hlive` premise requires the *source*
  state's head frame live.  (The successor may be dead — `NormStateTy`
  doesn't check `un`.)

Two genuine machine bugs surfaced during measurement.  They are class
(E) obstructions — the *machine* is wrong, not the typing — recorded as
residues W-WX002-M1/M2: the repairs change landed machine semantics, so
they are NOT in this lane's diff (the landed `RcicWasmNormStep` /
`RcicWasmNormTy` are additive-only for this lane).  `NormStepSafe`
excludes the buggy arms so the theorem remains true over the landed
machine; dropping the exclusions is gated on the repair item.

- **W-WX002-M1 — `normReturn` does not restore `locals`.**  `call`
  overwrites `st.locals` and `normReturn` resumes the caller leaving the
  callee's locals in place, so the post-return state fails
  `NormStateTy`'s `st.locals.map NormVal.ty = f.params ++ f.locals` for
  every non-coincidental caller.  This arm is reached by `.return`, by
  `br n` to the `.fn` bottom frame (`n + 1 = s.cs.length`), and by falling
  off the body (`f.body.get? st.pc = none`); `NormStepSafe` excludes the
  first two and the theorem is quantified over a fetched instruction.
  The repair (WasmCert's `f_locs`) needs a `NormFrame.savedLocals` field,
  `normReturn` restoring it, and a `NormFrameOK` conjunct
  `fr.savedLocals.map NormVal.ty = g.params ++ g.locals`.
- **W-WX002-M2 — `normBr`'s `loopK` arm keeps the whole
  `controlStack`.**  `br n` to a loop at `n ≥ 1` re-enters at
  `startPc + 1` but leaves the `n` popped labels in place, while the
  validator re-enters with `n` fewer frames (`lab :: outer`), so
  `NormLabelsCorrespond`'s length equation fails.  At `n = 0` the landed
  code coincides with the correct landing, so `NormStepSafe` restricts
  loop targets to `n = 0`.  The repair resumes `lab :: outer` for all `n`.
- **W-WX002-M3 — unary conversions dispatch to binary helpers —
  REPAIRED upstream (batch 23 / #6649).**  `normStepInstr` now matches
  `.i64 a :: rest` (resp. `.i32 a :: rest`) directly for `i32WrapI64` /
  `i64ExtendI32U` / `i64ExtendI32S` and pushes one result, agreeing with
  the unary `normInstrSig` entries; the same merge fixed
  `normLocalsSet`'s fuel (`go ls.length`, previously `ls.length - i`).
  `preserve_i32WrapI64`/`preserve_i64ExtendI32U`/`preserve_i64ExtendI32S`
  below cover the corrected arms.

`closure_claim = 0`.
-/
import rcic.RcicWasmNormTy
import rcic.RcicWasmNormProgress

namespace Rcic.WasmNorm

/-! ## Safe-step predicate -/

/-- The `.step` outcomes the scm-derived validator typing actually
tracks; the complement is class (A) of the header measurement.

- `br n` to a non-loop structured target (`blk`/`ift`/`els`) is safe
  only when every validator frame from the innermost to the target
  shares `entry.length` — then the machine's keep-top-`base` coincides
  with the dead-region `os` at `endPc`.  Loop targets re-enter at
  `startPc+1` (the validator's own `os` there), so no base condition is
  needed; `fn` targets are `normReturn` resumptions (`NormFrameOK`).
- `brIf`-taken and `ifE`-cond-0 land at `endPc`/`elsePc` where the
  validator's `os` is the *live body's* output, not the machine's
  retained prefix — excluded outright (`ifE`-cond-≠0 falls through to
  the if-body, safe).
- `elseE` keeps the if-body's leftover operand types while the
  validator's `os` at `endPc` is the else-branch's — excluded.
- `.return` and `br` to the `.fn` bottom frame delegate to `normReturn`,
  which does not restore `locals` (W-WX002-M1) — excluded.
- `br n` to a `.lp` target at `n ≥ 1` keeps `n` stale labels
  (W-WX002-M2) — only `n = 0` is safe on the landed machine.
- `br n`'s skipped region `[st.pc + 1, lab.endPc)` must not contain
  `.br`, `.return`, or `.call`.  The validator walks that region (dead
  below the innermost frame, then live inside the intermediate ones);
  `.br`/`.return` TOP-take past the suffix `X ++ init` and `.call`
  TAIL-appends `rs` below it — either breaks the `os` the machine's
  `take lab.height` lands on (the `i64.const; br 0` dead-region
  counterexample).  Pushes, bounded pops, `endI`/`elseE` frame-changes
  and `brIf` repushes all preserve the suffix; the excluded ops are the
  only ones that don't. -/
def NormStepSafe (s : NormVSt) (st : NormState) (i : NormInstr) : Prop :=
  (∀ n, i = .br n → n + 1 < s.cs.length → ∀ tgt ∈ (s.cs.drop n).head?.toList,
      (tgt.tag = .lp → n = 0) ∧
      (tgt.tag ≠ .lp → ∀ h ∈ s.cs.head?.toList,
        ∀ fᵢ ∈ s.cs.take (n + 1), fᵢ.entry.length = h.entry.length)) ∧
  (∀ n, i = .br n → n + 1 ≠ s.cs.length) ∧
  (∀ n f lab outer, i = .br n →
      st.module.funcs.get? st.funcIdx = some f →
      st.controlStack.drop n = lab :: outer →
      ∀ k b, st.pc + 1 ≤ k → k < lab.endPc → f.body.get? k = some b →
        b ≠ .return ∧ (∀ m, b ≠ .br m) ∧ (∀ g, b ≠ .call g)) ∧
  (∀ n, i = .brIf n → ∀ c rest, st.operandStack = .i32 c :: rest → c = 0) ∧
  (i = .ifE → ∀ c rest, st.operandStack = .i32 c :: rest → c ≠ 0) ∧
  i ≠ .elseE ∧ i ≠ .return

/-! ## Strict-pop lemmas (live head forces real pops) -/

/-- Under a live (`un = false`) bound, `normTckPop` is a real pop. -/
theorem normTckPop_strict {os : List NormTy} {b : Nat} {t : NormTy}
    {os' : List NormTy}
    (h : normTckPop os b false t = some os') : os = t :: os' := by
  unfold normTckPop at h
  cases os with
  | nil => simp at h
  | cons t' rest =>
    simp only [List.length_cons] at h
    by_cases hb : b < rest.length + 1
    · rw [if_pos hb] at h
      by_cases ht : t' = t
      · rw [if_pos ht] at h
        rw [Option.some.inj h]
        subst ht; rfl
      · rw [if_neg ht] at h; exact Option.noConfusion h
    · rw [if_neg hb] at h; simp at h

/-- Frame-bounded strict pop: `normVPop` on a live innermost frame pops
the real head. -/
theorem normVPop_strict {os : List NormTy} {f : NormTFrame}
    {rest : List NormTFrame} {t : NormTy} {os' : List NormTy}
    (hf : f.un = false)
    (h : normVPop os (f :: rest) t = some os') : os = t :: os' := by
  have h' : normTckPop os f.entry.length f.un t = some os' := h
  rw [hf] at h'
  exact normTckPop_strict h'

/-- `normVPops` under a live head decomposes `os` as `ts ++ os'`. -/
theorem normVPops_strict {os : List NormTy} {cs : List NormTFrame}
    {ts : List NormTy} {os' : List NormTy}
    (hf : (cs.head?).map NormTFrame.un = some false)
    (h : normVPops os cs ts = some os') : os = ts ++ os' := by
  induction ts generalizing os with
  | nil =>
    unfold normVPops at h
    rw [Option.some.inj h]
    simp
  | cons t ts ih =>
    unfold normVPops at h
    cases cs with
    | nil =>
      simp [normVPop] at h
    | cons f rest =>
      have hffalse : f.un = false := by
        simpa using hf
      cases hp : normVPop os (f :: rest) t with
      | none => rw [hp] at h; exact Option.noConfusion h
      | some o1 =>
        rw [hp] at h
        have hos : os = t :: o1 := normVPop_strict hffalse hp
        have h2 : o1 = ts ++ os' := ih (os := o1) h
        rw [hos, h2]
        simp [List.cons_append]

/-- `normTckAny` under a live bound is a real any-pop. -/
theorem normTckAny_strict {os : List NormTy} {b : Nat}
    {t? : Option NormTy} {os' : List NormTy}
    (h : normTckAny os b false = some (t?, os')) :
    ∃ t, os = t :: os' ∧ t? = some t := by
  unfold normTckAny at h
  cases os with
  | nil => simp at h
  | cons t' rest =>
    simp only [List.length_cons] at h
    by_cases hb : b < rest.length + 1
    · rw [if_pos hb] at h
      have h' := Option.some.inj h
      rw [Prod.mk.injEq] at h'
      obtain ⟨h1, h2⟩ := h'
      exact ⟨t', by rw [h2], h1.symm⟩
    · rw [if_neg hb] at h; simp at h

/-- `normVApply` under a live head: `os = ps ++ tail`, result `rs ++ tail`. -/
theorem normVApply_strict {os : List NormTy} {cs : List NormTFrame}
    {ps rs tail : List NormTy}
    (hf : (cs.head?).map NormTFrame.un = some false)
    (h : normVApply os cs ps rs = some tail) :
    ∃ tl, os = ps ++ tl ∧ tail = rs ++ tl := by
  unfold normVApply at h
  cases hp : normVPops os cs ps with
  | none => rw [hp] at h; exact Option.noConfusion h
  | some tl =>
    rw [hp, Option.map_some'] at h
    have hd := normVPops_strict hf hp
    exact ⟨tl, hd, (Option.some.inj h).symm⟩

/-! ## Run decomposition (acceptance reaches every position) -/

/-- Whole-body acceptance makes the run succeed (class C's source). -/
theorem normVAccept_run {C : NormVCtx} {f : NormFunc}
    (h : normVAccept C f = true) :
    ∃ v, normVRun C (normVInit f) f.body = some v := by
  unfold normVAccept at h
  cases hr : normVRun C (normVInit f) f.body with
  | none => rw [hr] at h; exact Bool.noConfusion h
  | some v => exact ⟨v, rfl⟩

/-- Any prefix of a successful run succeeds. -/
theorem normVRun_prefix {C : NormVCtx} {s v : NormVSt} {is : List NormInstr} (n : Nat)
    (h : normVRun C s is = some v) : ∃ s₁, normVRun C s (is.take n) = some s₁ := by
  rw [← List.take_append_drop n is] at h
  rw [normVRun_append] at h
  cases hp : normVRun C s (is.take n) with
  | none => rw [hp] at h; exact Option.noConfusion h
  | some s₁ => exact ⟨s₁, rfl⟩

/-- The instruction at `pc` validates from the reached state (class C:
whole-body acceptance discharges `normVStep` at every position). -/
theorem normVStep_at {C : NormVCtx} {f : NormFunc} {pc : Nat} {i : NormInstr}
    {s : NormVSt}
    (hrun : ∃ v, normVRun C (normVInit f) f.body = some v)
    (hi : f.body.get? pc = some i)
    (h : normVRun C (normVInit f) (f.body.take pc) = some s) :
    ∃ s₁, normVStep C i s = some s₁ := by
  obtain ⟨v, hv⟩ := hrun
  rw [List.get?_eq_getElem?] at hi
  obtain ⟨hlt, hli⟩ := List.getElem?_eq_some_iff.mp hi
  rw [← List.take_append_drop pc f.body, normVRun_append, h,
    Option.some_bind] at hv
  rw [List.drop_eq_getElem_cons hlt, hli, normVRun_cons] at hv
  cases hs1 : normVStep C i s with
  | none => rw [hs1] at hv; exact Option.noConfusion hv
  | some s₁ => exact ⟨s₁, rfl⟩

/-- The state after the successful `vstep` is the `pc + 1` state. -/
theorem normVRun_next {C : NormVCtx} {f : NormFunc} {pc : Nat} {i : NormInstr}
    {s s₁ : NormVSt}
    (hi : f.body.get? pc = some i)
    (h : normVRun C (normVInit f) (f.body.take pc) = some s)
    (hstep : normVStep C i s = some s₁) :
    normVRun C (normVInit f) (f.body.take (pc + 1)) = some s₁ := by
  rw [normVRun_take_succ _ _ _ _ _ hi, h, Option.some_bind, hstep]

/-! ## Value/type and label-correspondence admin -/

theorem NormVal.ty_eq_i32 {v : NormVal} (h : v.ty = .i32Ty) :
    ∃ x, v = .i32 x := by
  cases v with
  | i32 x => exact ⟨x, rfl⟩
  | i64 x => simp [NormVal.ty] at h

theorem NormVal.ty_eq_i64 {v : NormVal} (h : v.ty = .i64Ty) :
    ∃ x, v = .i64 x := by
  cases v with
  | i32 x => simp [NormVal.ty] at h
  | i64 x => exact ⟨x, rfl⟩

@[simp] theorem NormTy.zero_ty (t : NormTy) : (NormTy.zero t).ty = t := by
  cases t <;> rfl

/-- The machine's typed operand head decomposes as the validator's `os`. -/
theorem operandStack_ty_cons {st : NormState} {s : NormVSt} {t : NormTy}
    {tl : List NormTy}
    (h : s.os = st.operandStack.map NormVal.ty)
    (hd : s.os = t :: tl) :
    ∃ v rest, st.operandStack = v :: rest ∧ v.ty = t ∧ rest.map NormVal.ty = tl := by
  cases hst : st.operandStack with
  | nil => rw [hst] at h; simp at h; rw [h] at hd; exact List.noConfusion hd
  | cons v rest =>
    refine ⟨v, rest, rfl, ?_, ?_⟩
    · rw [hst, List.map_cons] at h; rw [h] at hd; exact (List.cons.inj hd).1
    · rw [hst, List.map_cons] at h; rw [h] at hd; exact (List.cons.inj hd).2

/-- Pop direction of `NormLabelsCorrespond`: dropping the innermost pair
keeps the correspondence. -/
theorem normLabelsCorrespond_tail {body : List NormInstr} {ls : List NormLabel}
    {cs : List NormTFrame} {lab : NormLabel} {fr : NormTFrame}
    (h : NormLabelsCorrespond body (lab :: ls) (fr :: cs)) :
    NormLabelsCorrespond body ls cs := by
  obtain ⟨hlen, hlast, hpt⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.length_cons] at hlen ⊢; omega
  · cases cs with
    | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
    | cons c cs' =>
      rw [List.getLast?_cons_cons] at hlast
      exact hlast
  · intro i hi
    obtain ⟨hc, hm, hh, he, hb⟩ := hpt (i + 1) (by simp; omega)
    have hcs : i < cs.length := by
      simp only [List.length_cons] at hc ⊢; omega
    refine ⟨hcs, ?_, ?_, ?_, ?_⟩
    · rw [List.getElem_cons_succ] at hm; exact hm
    · rw [List.getElem_cons_succ] at hh; exact hh
    · rw [List.getElem_cons_succ] at he; exact he
    · rw [List.getElem_cons_succ] at hb; exact hb

/-- Push direction: a new innermost pair extends a correspondence. -/
theorem normLabelsCorrespond_cons {body : List NormInstr} {ls : List NormLabel}
    {cs : List NormTFrame} {lab : NormLabel} {fr : NormTFrame}
    (h : NormLabelsCorrespond body ls cs)
    (hkind : (match fr.tag with
      | .blk => lab.kind = .blockK | .lp => lab.kind = .loopK
      | .ift | .els => lab.kind = .ifK | .fn => False))
    (hh : lab.height = fr.entry.length)
    (he : ∃ elsePc, normElseEnd body lab.startPc = some (elsePc, lab.endPc))
    (hb : (match lab.kind with
      | .blockK => body.get? lab.startPc = some .block
      | .loopK => body.get? lab.startPc = some .loop
      | .ifK => body.get? lab.startPc = some .ifE)) :
    NormLabelsCorrespond body (lab :: ls) (fr :: cs) := by
  obtain ⟨hlen, hlast, hpt⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.length_cons] at hlen ⊢; omega
  · cases cs with
    | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
    | cons c cs' =>
      rw [List.getLast?_cons_cons]
      exact hlast
  · intro i hi
    cases i with
    | zero =>
      exact ⟨Nat.zero_lt_succ _, hkind, hh, he, hb⟩
    | succ i =>
      obtain ⟨hc, hm, hh2, he2, hb2⟩ := hpt i (by simp at hi; omega)
      refine ⟨by simp only [List.length_cons]; omega, ?_, ?_, ?_, ?_⟩
      · rw [List.getElem_cons_succ]; exact hm
      · rw [List.getElem_cons_succ]; exact hh2
      · rw [List.getElem_cons_succ]; exact he2
      · rw [List.getElem_cons_succ]; exact hb2

/-! ## The carried invariant -/

/-- Liveness half of the S3 invariant: every validator control frame the
machine is currently inside is reachable (`un = false`).  Dead frames
arise only from `normVBrk`/`.return`; every machine step that could land
inside a dead region is either excluded by `NormStepSafe` or lands at a
boundary where the enclosing frame was already live — so this conjunct is
preserved.  Carried separately from `NormStateTy` because the latter is
landed and the preservation theorem needs it for the strict-pop lemmas
(`normVApply_strict` needs a live head) and for `endI` (the popped-to
frame must be live). -/
def NormLive (st : NormState) : Prop :=
  ∀ f s, st.module.funcs.get? st.funcIdx = some f →
    normVRun (NormVCtx.ofModule st.module f) (normVInit f)
        (f.body.take st.pc) = some s →
    ∀ fr ∈ s.cs, fr.un = false

/-! ## Control-map scan helpers (`normElseEnd.go`) -/

/-- One `normElseEnd.go` step unfolds (the `Nat.brecOn` encoding
computes). -/
theorem normElseEnd_go_succ (body : List NormInstr) (fuel j depth : Nat)
    (elsePc : Option Nat) :
    normElseEnd.go body (fuel + 1) j depth elsePc =
      (match body.get? j with
      | none => none
      | some .block | some .loop | some .ifE =>
          normElseEnd.go body fuel (j + 1) (depth + 1) elsePc
      | some .endI =>
          if depth = 0 then some (elsePc, j + 1)
          else normElseEnd.go body fuel (j + 1) (depth - 1) elsePc
      | some .elseE =>
          if depth = 0 then normElseEnd.go body fuel (j + 1) depth
            (elsePc.orElse (fun _ => some j))
          else normElseEnd.go body fuel (j + 1) depth elsePc
      | _ => normElseEnd.go body fuel (j + 1) depth elsePc) := rfl

/-- Option-bind inversion. -/
theorem bind_some_inv {α β} {o : Option α} {g : α → Option β} {b : β}
    (h : o.bind g = some b) : ∃ a, o = some a ∧ g a = some b := by
  cases o with
  | none => exact Option.noConfusion h
  | some a => exact ⟨a, rfl, h⟩

/-- Option-map inversion. -/
theorem map_some_inv {α β} {o : Option α} {g : α → β} {b : β}
    (h : o.map g = some b) : ∃ a, o = some a ∧ g a = b := by
  cases o with
  | none => exact Option.noConfusion h
  | some a =>
    simp only [Option.map_some', Option.some.injEq] at h
    exact ⟨a, rfl, h⟩

/-- `drop n` decomposes at a found element. -/
theorem drop_eq_cons_of_get? {α : Type _} {l : List α} {n : Nat} {a : α}
    (h : l.get? n = some a) : l.drop n = a :: l.drop (n + 1) := by
  induction l generalizing n with
  | nil => simp at h
  | cons x xs ih =>
    cases n with
    | zero =>
      simp only [List.get?_cons_zero, Option.some.injEq] at h
      subst h; rfl
    | succ n =>
      simp only [List.get?_cons_succ] at h
      show xs.drop n = a :: xs.drop (n + 1)
      exact ih h

/-- The scan's result position is strictly past its start. -/
theorem go_result_gt {body : List NormInstr} {x : Option Nat} {e j : Nat}
    {fuel d el}
    (h : normElseEnd.go body fuel j d el = some (x, e)) : j < e := by
  induction fuel generalizing j d el x e with
  | zero => exact Option.noConfusion h
  | succ fuel ih =>
    rw [normElseEnd_go_succ] at h
    split at h
    · exact Option.noConfusion h
    · exact Nat.lt_of_succ_lt (ih h)
    · exact Nat.lt_of_succ_lt (ih h)
    · exact Nat.lt_of_succ_lt (ih h)
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
      · exact Nat.lt_of_succ_lt (ih h)
    · split at h <;> exact Nat.lt_of_succ_lt (ih h)
    · exact Nat.lt_of_succ_lt (ih h)

/-- The scan's returned `endI` sits at `e - 1`. -/
theorem go_endI {body : List NormInstr} {x : Option Nat} {e j : Nat}
    {fuel d el}
    (h : normElseEnd.go body fuel j d el = some (x, e)) :
    body.get? (e - 1) = some .endI := by
  induction fuel generalizing j d el x e with
  | zero => exact Option.noConfusion h
  | succ fuel ih =>
    rw [normElseEnd_go_succ] at h
    split at h
    · exact Option.noConfusion h
    · exact ih h
    · exact ih h
    · exact ih h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        rw [Nat.add_sub_cancel]; assumption
      · exact ih h
    · split at h <;> exact ih h
    · exact ih h

/-- Parallel-depth fact: two scans over the same stretch, the deeper
offset by `K > 0`, stay offset — so the shallower scan's depth-0 `endI`
leaves the deeper still positive, and the deeper's own result comes
strictly later.  Used for endPc-nesting (`cons`'s new label ends inside
the enclosing label). -/
theorem go_deeper_aux {body : List NormInstr} {K : Nat} (hK : 0 < K) :
    ∀ {fuel₁ fuel₂ j d₁ el₁ el₂ x₁ x₂ e₁ e₂},
    normElseEnd.go body fuel₁ j d₁ el₁ = some (x₁, e₁) →
    normElseEnd.go body fuel₂ j (K + d₁) el₂ = some (x₂, e₂) →
    e₁ < e₂ := by
  intro fuel₁
  induction fuel₁ with
  | zero =>
    intro fuel₂ j d₁ el₁ el₂ x₁ x₂ e₁ e₂ h₁ h₂
    exact Option.noConfusion h₁
  | succ fuel₁ ih =>
    intro fuel₂ j d₁ el₁ el₂ x₁ x₂ e₁ e₂ h₁ h₂
    rw [normElseEnd_go_succ] at h₁
    cases fuel₂ with
    | zero => exact Option.noConfusion h₂
    | succ fuel₂ =>
      rw [normElseEnd_go_succ] at h₂
      split at h₁
      · exact Option.noConfusion h₁
      · rename_i hget; rw [hget] at h₂; simp only [] at h₂
        exact ih h₁ h₂
      · rename_i hget; rw [hget] at h₂; simp only [] at h₂
        exact ih h₁ h₂
      · rename_i hget; rw [hget] at h₂; simp only [] at h₂
        exact ih h₁ h₂
      · rename_i hget; rw [hget] at h₂; simp only [] at h₂
        split at h₁
        · rename_i hd₁
          subst hd₁
          simp only [Option.some.injEq, Prod.mk.injEq] at h₁
          obtain ⟨-, rfl⟩ := h₁
          split at h₂
          · omega
          · exact go_result_gt h₂
        · rename_i hd₁
          cases d₁ with
          | zero => exact absurd rfl hd₁
          | succ d₁' =>
            split at h₂
            · omega
            · exact ih h₁ h₂
      · rename_i hget; rw [hget] at h₂; simp only [] at h₂
        split at h₁
        · rename_i hd₁
          subst hd₁
          split at h₂
          · omega
          · exact ih h₁ h₂
        · rename_i hd₁
          cases d₁ with
          | zero => exact absurd rfl hd₁
          | succ d₁' =>
            split at h₂
            · omega
            · exact ih h₁ h₂
      · rename_i hget
        split at h₂
        · exact Option.noConfusion h₂
        all_goals first
          | contradiction
          | exact ih h₁ h₂

theorem go_deeper {body : List NormInstr} {j d fuel₁ fuel₂ el₁ el₂
    x₁ x₂ e₁ e₂}
    (h₁ : normElseEnd.go body fuel₁ j 0 el₁ = some (x₁, e₁))
    (h₂ : normElseEnd.go body fuel₂ j (d + 1) el₂ = some (x₂, e₂)) :
    e₁ < e₂ := go_deeper_aux (K := d + 1) (Nat.succ_pos d) h₁ h₂

/-- `normVBrk` mutates the head frame's `un` flag. -/
theorem normVBrk_cs {s : NormVSt} {lrt : Option NormTy} {s' : NormVSt}
    (h : normVBrk s lrt = some s') :
    ∃ f rest, s.cs = f :: rest ∧
      s'.cs = ⟨f.tag, f.rt, f.entry, true⟩ :: rest := by
  simp only [normVBrk] at h
  split at h
  · exact Option.noConfusion h
  · rename_i f rest hcs
    obtain ⟨os', hlrt, hs⟩ := bind_some_inv h
    simp only [Option.some.injEq] at hs; subst hs
    exact ⟨f, rest, hcs, rfl⟩

/-- `normVBrIf` preserves the frame stack. -/
theorem normVBrIf_cs {s : NormVSt} {n : Nat} {s' : NormVSt}
    (h : normVBrIf s n = some s') : s'.cs = s.cs := by
  simp only [normVBrIf] at h
  split at h
  · exact Option.noConfusion h
  · rename_i tgt ts hdrop
    obtain ⟨os', hp, hb⟩ := bind_some_inv h
    obtain ⟨os'', hrt, hb⟩ := bind_some_inv hb
    split at hb
    · simp only [Option.some.injEq] at hb; subst hb; rfl
    · exact Option.noConfusion hb

/-- `normVStep` on a non-opener non-`endI` either preserves `cs` or
mutates its head (frame flags/entry — the `br`/`return`/`elseE` mark and
the `els` retag). -/
theorem normVStep_cs_stable {C : NormVCtx} {i : NormInstr} {s s' : NormVSt}
    (h : normVStep C i s = some s')
    (hn : i ≠ .block ∧ i ≠ .loop ∧ i ≠ .ifE ∧ i ≠ .endI) :
    (∃ f f' rest, s.cs = f :: rest ∧ s'.cs = f' :: rest ∧
      f'.entry = f.entry ∧ f'.rt = f.rt ∧
      (f'.tag = f.tag ∨ f'.tag = .els)) ∨ s'.cs = s.cs := by
  cases i with
  | block => exact absurd rfl hn.1
  | loop => exact absurd rfl hn.2.1
  | ifE => exact absurd rfl hn.2.2.1
  | endI => exact absurd rfl hn.2.2.2
  | elseE =>
    simp only [normVStep] at h; split at h
    · rename_i x f rest hcs; split at h
      · rename_i htag
        obtain ⟨o, ho, hs⟩ := map_some_inv h; subst hs
        exact Or.inl ⟨f, _, rest, hcs, rfl, rfl, rfl, Or.inr rfl⟩
      · exact Option.noConfusion h
    · exact Option.noConfusion h
  | br n =>
    simp only [normVStep, normVBr] at h
    split at h
    · exact Option.noConfusion h
    · rename_i tgt ts hdrop
      split at h
      · rename_i hok
        obtain ⟨f, rest, hcs, hs⟩ := normVBrk_cs h
        exact Or.inl ⟨f, _, rest, hcs, hs, rfl, rfl, Or.inl rfl⟩
      · exact Option.noConfusion h
  | «return» =>
    simp only [normVStep] at h
    obtain ⟨f, rest, hcs, hs⟩ := normVBrk_cs h
    exact Or.inl ⟨f, _, rest, hcs, hs, rfl, rfl, Or.inl rfl⟩
  | brIf n =>
    simp only [normVStep] at h
    exact Or.inr (normVBrIf_cs h)
  | call f =>
    simp only [normVStep] at h; split at h
    · exact Option.noConfusion h
    · rename_i x sig hf
      obtain ⟨o, ho, hs⟩ := map_some_inv h; subst hs
      exact Or.inr rfl
  | drop =>
    simp only [normVStep] at h; split at h
    · rename_i x f rest hcs
      obtain ⟨o, ho, hs⟩ := map_some_inv h; subst hs
      exact Or.inr rfl
    · exact Option.noConfusion h
  | select =>
    simp only [normVStep] at h
    obtain ⟨o1, hp1, hb1⟩ := bind_some_inv h
    split at hb1
    · rename_i x f rest hcs
      obtain ⟨a, ha, hb2⟩ := bind_some_inv hb1
      split at hb2
      · rename_i ht
        simp only [Option.some.injEq] at hb2; subst hb2
        exact Or.inr rfl
      · rename_i ht
        obtain ⟨o3, ho3, hb3⟩ := map_some_inv hb2; subst hb3
        exact Or.inr rfl
    · exact Option.noConfusion hb1
  | localGet i =>
    simp only [normVStep] at h
    obtain ⟨o, ho, hs⟩ := map_some_inv h; subst hs
    exact Or.inr rfl
  | localSet i =>
    simp only [normVStep] at h
    obtain ⟨a, ha, hb'⟩ := bind_some_inv h
    obtain ⟨o, ho, hs⟩ := map_some_inv hb'; subst hs
    exact Or.inr rfl
  | localTee i =>
    simp only [normVStep] at h
    obtain ⟨a, ha, hb'⟩ := bind_some_inv h
    obtain ⟨o, ho, hs⟩ := map_some_inv hb'; subst hs
    exact Or.inr rfl
  | _ =>
    simp only [normVStep] at h
    obtain ⟨sig, hsig, hb'⟩ := bind_some_inv h
    obtain ⟨o, ho, hs⟩ := map_some_inv hb'; subst hs
    exact Or.inr rfl

/-! ## Operand-stack suffix tracking (`X ++ FROZEN`) -/

/-- `normTckPop` preserves a suffix at/below the bound `b ≥ |FROZEN|`:
the real-pop branch only removes an element of `X` (the pop bound is at
or above the frozen tail), the vacuous `un` branch keeps `os`. -/
theorem normTckPop_suffix {os os' : List NormTy} {b : Nat} {t : NormTy}
    {un : Bool} {X FROZEN : List NormTy} {B : Nat}
    (hB : FROZEN.length = B) (hb : B ≤ b) (hos : os = X ++ FROZEN)
    (h : normTckPop os b un t = some os') :
    ∃ X', os' = X' ++ FROZEN := by
  unfold normTckPop at h
  split at h
  · rename_i hlt
    split at h
    · rename_i t' rest
      split at h
      · rename_i htt
        simp only [Option.some.injEq] at h
        have hX : X ≠ [] := by
          intro e; subst e
          rw [List.nil_append] at hos
          have hl := congrArg List.length hos
          simp only [List.length_cons] at hl hlt
          omega
        obtain ⟨x₀, X', hX'⟩ := List.exists_cons_of_ne_nil hX
        rw [hX', List.cons_append] at hos
        injection hos with _ hrest
        exact ⟨X', h ▸ hrest⟩
      · exact Option.noConfusion h
    · exact Option.noConfusion h
  · split at h
    · simp only [Option.some.injEq] at h
      exact ⟨X, h ▸ hos⟩
    · exact Option.noConfusion h

/-- The `any`-pop analogue (`drop`/`select`). -/
theorem normTckAny_suffix {os os' : List NormTy} {b : Nat}
    {t? : Option NormTy} {un : Bool} {X FROZEN : List NormTy} {B : Nat}
    (hB : FROZEN.length = B) (hb : B ≤ b) (hos : os = X ++ FROZEN)
    (h : normTckAny os b un = some (t?, os')) :
    ∃ X', os' = X' ++ FROZEN := by
  unfold normTckAny at h
  split at h
  · rename_i hlt
    split at h
    · rename_i t' rest
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, hos'⟩ := h
      have hX : X ≠ [] := by
        intro e; subst e
        rw [List.nil_append] at hos
        have hl := congrArg List.length hos
        simp only [List.length_cons] at hl hlt
        omega
      obtain ⟨x₀, X', hX'⟩ := List.exists_cons_of_ne_nil hX
      rw [hX', List.cons_append] at hos
      injection hos with _ hrest
      exact ⟨X', hos' ▸ hrest⟩
    · exact Option.noConfusion h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨X, h.2 ▸ hos⟩
    · exact Option.noConfusion h

/-- `normVPop` on a head whose `entry.length ≥ B` preserves the suffix. -/
theorem normVPop_suffix {os os' : List NormTy} {f : NormTFrame}
    {rest : List NormTFrame} {t : NormTy} {X FROZEN : List NormTy} {B : Nat}
    (hB : FROZEN.length = B) (hb : B ≤ f.entry.length)
    (hos : os = X ++ FROZEN)
    (h : normVPop os (f :: rest) t = some os') :
    ∃ X', os' = X' ++ FROZEN :=
  normTckPop_suffix hB hb hos h

/-- `normVPops` (a list of bounded pops) preserves the suffix. -/
theorem normVPops_suffix {f : NormTFrame} {rest : List NormTFrame}
    {FROZEN : List NormTy} {B : Nat}
    (hB : FROZEN.length = B) (hb : B ≤ f.entry.length) :
    ∀ {ts : List NormTy} {os os' : List NormTy} {X : List NormTy},
    os = X ++ FROZEN →
    normVPops os (f :: rest) ts = some os' →
    ∃ X', os' = X' ++ FROZEN := by
  intro ts
  induction ts with
  | nil =>
    intro os os' X hos h
    unfold normVPops at h
    exact ⟨X, (Option.some.inj h).symm.trans hos⟩
  | cons t ts ih =>
    intro os os' X hos h
    unfold normVPops at h
    obtain ⟨os₁, hpop, hrest⟩ := bind_some_inv h
    obtain ⟨X₁, hos₁⟩ := normVPop_suffix hB hb hos hpop
    exact ih hos₁ hrest

/-- `normVApply` = bounded pops then `rs ++` — preserves the suffix. -/
theorem normVApply_suffix {os tail : List NormTy} {f : NormTFrame}
    {rest : List NormTFrame} {ps rs : List NormTy} {X FROZEN : List NormTy}
    {B : Nat}
    (hB : FROZEN.length = B) (hb : B ≤ f.entry.length)
    (hos : os = X ++ FROZEN)
    (h : normVApply os (f :: rest) ps rs = some tail) :
    ∃ X', tail = X' ++ FROZEN := by
  unfold normVApply at h
  obtain ⟨os₁, hpops, hmap⟩ := map_some_inv h
  obtain ⟨X₁, hos₁⟩ := normVPops_suffix hB hb hos hpops
  exact ⟨rs ++ X₁, by rw [← hmap, hos₁, List.append_assoc]⟩

/-- `normVFchk`'s bounded `rt`-pop preserves the suffix. -/
theorem normVFchk_suffix {os os' : List NormTy} {f : NormTFrame}
    {X FROZEN : List NormTy} {B : Nat}
    (hB : FROZEN.length = B) (hb : B ≤ f.entry.length)
    (hos : os = X ++ FROZEN)
    (h : normVFchk os f = some os') :
    ∃ X', os' = X' ++ FROZEN := by
  unfold normVFchk at h
  obtain ⟨os₂, hf, hchk⟩ := bind_some_inv h
  split at hchk
  · simp only [Option.some.injEq] at hchk
    subst hchk
    cases hrt : f.rt with
    | none =>
      rw [hrt] at hf
      obtain rfl := Option.some.inj hf
      exact ⟨X, hos⟩
    | some t =>
      rw [hrt] at hf
      exact normTckPop_suffix hB hb hos hf
  · exact Option.noConfusion hchk

/-- Per-instruction os-suffix preservation: every `normVStep` except
`.br`/`.return` (which `take` a top slice, possibly cutting into
`FROZEN`) and `.call` (which tail-appends `rs`, stranding `FROZEN` in
the middle) keeps `s.os = X ++ FROZEN` — provided the current head
frame's bound is at least `|FROZEN|` (pops then only touch `X`). -/
theorem normVStep_os_suffix {C : NormVCtx} {i : NormInstr} {s s₁ : NormVSt}
    {X FROZEN : List NormTy} {B : Nat}
    (hB : FROZEN.length = B)
    (h : normVStep C i s = some s₁)
    (hex : i ≠ .return ∧ (∀ m, i ≠ .br m) ∧ (∀ g, i ≠ .call g))
    (hhead : ∀ g ∈ s.cs.head?.toList, B ≤ g.entry.length)
    (hos : s.os = X ++ FROZEN) :
    ∃ X', s₁.os = X' ++ FROZEN := by
  have hbound_of : ∀ f₀ rest, s.cs = f₀ :: rest → B ≤ f₀.entry.length := by
    intro f₀ rest hcs
    exact hhead f₀ (by rw [hcs, List.head?_cons, Option.toList_some,
      List.mem_singleton])
  cases i with
  | block =>
    simp only [normVStep, Option.some.injEq] at h
    exact ⟨X, h ▸ hos⟩
  | loop =>
    simp only [normVStep, Option.some.injEq] at h
    exact ⟨X, h ▸ hos⟩
  | ifE =>
    simp only [normVStep] at h
    cases hcs : s.cs with
    | nil => rw [hcs] at h; simp only [normVPop] at h; exact Option.noConfusion h
    | cons f₀ rest =>
      obtain ⟨os₁, hpop, hs₁⟩ := map_some_inv h
      obtain ⟨X₁, hos₁⟩ := normVPop_suffix hB (hbound_of _ _ hcs) hos
        (by rwa [hcs] at hpop)
      exact ⟨X₁, hs₁ ▸ hos₁⟩
  | elseE =>
    simp only [normVStep] at h
    cases hcs : s.cs with
    | nil => rw [hcs] at h; exact Option.noConfusion h
    | cons f₀ rest =>
      simp only [hcs] at h
      split at h
      · obtain ⟨os₁, hfchk, hs₁⟩ := map_some_inv h
        have hs₁' : ⟨os₁, ⟨.els, f₀.rt, f₀.entry, f₀.un⟩ :: rest⟩ = s₁ := hs₁
        obtain ⟨X₁, hos₁⟩ := normVFchk_suffix hB (hbound_of _ _ hcs) hos hfchk
        exact ⟨X₁, hs₁' ▸ hos₁⟩
      · exact Option.noConfusion h
  | endI =>
    simp only [normVStep] at h
    cases hcs : s.cs with
    | nil => rw [hcs] at h; exact Option.noConfusion h
    | cons f₀ rest =>
      simp only [hcs] at h
      split at h
      · exact Option.noConfusion h
      · obtain ⟨os₁, hfchk, hs₁⟩ := map_some_inv h
        have hs₁' : ⟨f₀.rt.toList ++ os₁, rest⟩ = s₁ := hs₁
        obtain ⟨X₁, hos₁⟩ := normVFchk_suffix hB (hbound_of _ _ hcs) hos hfchk
        exact ⟨f₀.rt.toList ++ X₁, by rw [← hs₁']; simp [List.append_assoc,
          hos₁]⟩
  | br n => exact absurd rfl (hex.2.1 n)
  | brIf n =>
    simp only [normVStep, normVBrIf] at h
    cases hcs : s.cs with
    | nil => rw [hcs] at h; simp at h
    | cons f₀ rest =>
      rw [hcs] at h
      split at h
      · exact Option.noConfusion h
      · obtain ⟨os₁, hpop₁, hb₁⟩ := bind_some_inv h
        obtain ⟨X₁, hos₁⟩ := normVPop_suffix hB (hbound_of _ _ hcs) hos hpop₁
        obtain ⟨os₂, hrt, hb₂⟩ := bind_some_inv hb₁
        split at hrt
        · rename_i t _x
          obtain ⟨os₃, hpop₂, hmap⟩ := map_some_inv hrt
          have hmap' : t :: os₃ = os₂ := hmap
          obtain ⟨X₂, hos₂⟩ := normVPop_suffix hB (hbound_of _ _ hcs) hos₁ hpop₂
          try dsimp only at hb₂
          split at hb₂
          · simp only [Option.some.injEq] at hb₂
            exact ⟨t :: X₂, by rw [← hb₂, ← hmap', hos₂]; rfl⟩
          · exact Option.noConfusion hb₂
        · simp only [Option.some.injEq] at hrt
          subst hrt
          split at hb₂
          · simp only [Option.some.injEq] at hb₂
            exact ⟨X₁, by rw [← hb₂]; exact hos₁⟩
          · exact Option.noConfusion hb₂
  | call g => exact absurd rfl (hex.2.2 g)
  | «return» => exact absurd rfl hex.1
  | drop =>
    simp only [normVStep] at h
    cases hcs : s.cs with
    | nil => rw [hcs] at h; exact Option.noConfusion h
    | cons f₀ rest =>
      rw [hcs] at h
      obtain ⟨⟨t?, os₁⟩, hany, hmap⟩ := map_some_inv h
      obtain ⟨X₁, hos₁⟩ := normTckAny_suffix hB (hbound_of _ _ hcs) hos hany
      exact ⟨X₁, by rw [← hmap]; exact hos₁⟩
  | select =>
    simp only [normVStep] at h
    cases hcs : s.cs with
    | nil =>
      rw [hcs] at h
      simp only [normVPop] at h
      exact Option.noConfusion h
    | cons f₀ rest =>
      rw [hcs] at h
      obtain ⟨os₁, hpop, hb₁⟩ := bind_some_inv h
      obtain ⟨X₁, hos₁⟩ := normVPop_suffix hB (hbound_of _ _ hcs) hos hpop
      obtain ⟨⟨t?, os₂⟩, hany, hb₂⟩ := bind_some_inv hb₁
      obtain ⟨X₂, hos₂⟩ := normTckAny_suffix hB (hbound_of _ _ hcs) hos₁ hany
      cases t? with
      | none =>
        simp only [] at hb₂
        obtain rfl := Option.some.inj hb₂
        exact ⟨X₂, hos₂⟩
      | some t =>
        obtain ⟨os₃, hpop₂, hmap⟩ := map_some_inv hb₂
        try dsimp only at hpop₂
        obtain ⟨X₃, hos₃⟩ := normVPop_suffix hB (hbound_of _ _ hcs) hos₂ hpop₂
        exact ⟨t :: X₃, by rw [← hmap]; simp [hos₃]⟩
  | localGet k =>
    simp only [normVStep] at h
    obtain ⟨lt, hlt, hs₁⟩ := map_some_inv h
    exact ⟨lt :: X, by rw [← hs₁]; simp [hos]⟩
  | localSet k =>
    simp only [normVStep] at h
    cases hcs : s.cs with
    | nil =>
      rw [hcs] at h
      obtain ⟨lt, hlt, hb₁⟩ := bind_some_inv h
      simp only [normVPop] at hb₁
      exact Option.noConfusion hb₁
    | cons f₀ rest =>
      rw [hcs] at h
      obtain ⟨lt, hlt, hb₁⟩ := bind_some_inv h
      obtain ⟨os₁, hpop, hmap⟩ := map_some_inv hb₁
      obtain ⟨X₁, hos₁⟩ := normVPop_suffix hB (hbound_of _ _ hcs) hos hpop
      exact ⟨X₁, by rw [← hmap]; exact hos₁⟩
  | localTee k =>
    simp only [normVStep] at h
    cases hcs : s.cs with
    | nil =>
      rw [hcs] at h
      obtain ⟨lt, hlt, hb₁⟩ := bind_some_inv h
      simp only [normVPop] at hb₁
      exact Option.noConfusion hb₁
    | cons f₀ rest =>
      rw [hcs] at h
      obtain ⟨lt, hlt, hb₁⟩ := bind_some_inv h
      obtain ⟨os₁, hpop, hmap⟩ := map_some_inv hb₁
      obtain ⟨X₁, hos₁⟩ := normVPop_suffix hB (hbound_of _ _ hcs) hos hpop
      exact ⟨lt :: X₁, by rw [← hmap]; simp [hos₁]⟩
  | _ =>
    simp only [normVStep] at h
    obtain ⟨⟨ps, rs⟩, _hsig, hb₁⟩ := bind_some_inv h
    obtain ⟨os₁, happ, hmap⟩ := map_some_inv hb₁
    cases hcs : s.cs with
    | nil =>
      rw [hcs] at happ
      cases ps with
      | nil =>
        simp only [normVApply, normVPops, Option.map_some'] at happ
        obtain rfl := Option.some.inj happ
        exact ⟨rs ++ X, by rw [← hmap]; simp [hos, List.append_assoc]⟩
      | cons t ts =>
        simp only [normVApply, normVPops, normVPop] at happ
        exact Option.noConfusion happ
    | cons f₀ rest =>
      rw [hcs] at happ
      obtain ⟨X₁, hos₁⟩ := normVApply_suffix hB (hbound_of _ _ hcs) hos happ
      exact ⟨X₁, by rw [← hmap]; exact hos₁⟩

/-- Fused scan+walk track: while `normElseEnd.go` scans a construct
(enclosing stack `F :: CUR`, inner frames `OPEN` at depth `|OPEN|`), every
scan position before the result `e` has a validator state `OPEN' ++
F' :: CUR` with `|OPEN'|` equal to the scan depth.  Steps touch only
`OPEN'`/`F'`: the `CUR` tail is frozen — the first `CUR`-pop is the
depth-0 `endI` that IS the scan's result.

The two extra conjuncts are the `br` arm's os machinery: a `FROZEN`
operand-suffix `s.os = X ++ FROZEN` (the machine's `take lab.height`
keeps exactly this tail) is preserved by every instruction except the
`hexcl`-excluded `.br`/`.return`/`.call`, and every scanned frame's
`entry.length` stays `≥ |FROZEN|` so bounded pops only touch `X`. -/
theorem seg_track_aux {C : NormVCtx} {body : List NormInstr}
    {CUR : List NormTFrame} {FROZEN : List NormTy} {B : Nat} :
    ∀ {fuel j d el s sf OPEN F x e},
    (body.drop j).length ≤ fuel →
    normVRun C s (body.drop j) = some sf →
    s.cs = OPEN ++ F :: CUR → OPEN.length = d →
    normElseEnd.go body fuel j d el = some (x, e) →
    (∃ X, s.os = X ++ FROZEN) →
    FROZEN.length = B →
    (∀ fr ∈ OPEN ++ [F], B ≤ fr.entry.length) →
    (∀ k b, j ≤ k → k < e → body.get? k = some b →
      b ≠ .return ∧ (∀ m, b ≠ .br m) ∧ (∀ g, b ≠ .call g)) →
    ∀ j',
      j < j' → j' < e →
      ∃ s' OPEN' F' d' el' fuel',
        normElseEnd.go body fuel' j' d' el' = some (x, e) ∧
        normVRun C s ((body.drop j).take (j' - j)) = some s' ∧
        s'.cs = OPEN' ++ F' :: CUR ∧ OPEN'.length = d' ∧
        (∃ X', s'.os = X' ++ FROZEN) ∧
        (∀ fr ∈ OPEN' ++ [F'], B ≤ fr.entry.length) ∧
        (F'.entry = F.entry ∧ F'.rt = F.rt ∧
          (F'.tag = F.tag ∨ F'.tag = .els)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro j d el s sf OPEN F x e hfuel hrun hcs hd hgo hsuf hB hbound hex j' hjj hje
    exact Option.noConfusion hgo
  | succ fuel ih =>
    intro j d el s sf OPEN F x e hfuel hrun hcs hd hgo hsuf hB hbound hex j' hjj hje
    rw [normElseEnd_go_succ] at hgo
    obtain ⟨X, hosX⟩ := hsuf
    have hfuel' : ∀ a, body.get? j = some a →
        (body.drop (j + 1)).length ≤ fuel := by
      intro a ha
      have := hfuel; rw [drop_eq_cons_of_get? ha, List.length_cons] at this
      omega
    have hstep_of : ∀ a, body.get? j = some a →
        ∃ s₁, normVStep C a s = some s₁ ∧
          normVRun C s₁ (body.drop (j + 1)) = some sf := by
      intro a ha
      rw [drop_eq_cons_of_get? ha] at hrun
      simp only [normVRun] at hrun
      exact bind_some_inv hrun
    have htake : ∀ a s₁, body.get? j = some a →
        normVStep C a s = some s₁ →
        normVRun C s ((body.drop j).take (j + 1 - j)) = some s₁ := by
      intro a s₁ ha hstep
      have h1 : j + 1 - j = 1 := by omega
      rw [h1, drop_eq_cons_of_get? ha]
      show normVRun C s [a] = some s₁
      simp only [normVRun]
      rw [hstep]; rfl
    have hchain : ∀ a s₁, body.get? j = some a →
        normVStep C a s = some s₁ → ∀ j',
        j + 1 < j' →
        normVRun C s ((body.drop j).take (j' - j)) =
          normVRun C s₁ ((body.drop (j + 1)).take (j' - (j + 1))) := by
      intro a s₁ ha hstep j' hjj'
      have h1 : j' - j = (j' - (j + 1)) + 1 := by omega
      rw [drop_eq_cons_of_get? ha, h1]
      show normVRun C s (a :: (body.drop (j + 1)).take (j' - (j + 1))) = _
      simp only [normVRun]
      rw [hstep]; rfl
    have hhead : ∀ g ∈ s.cs.head?.toList, B ≤ g.entry.length := by
      intro g hg
      rw [hcs] at hg
      cases OPEN with
      | nil =>
        rw [List.nil_append, List.head?_cons, Option.toList_some,
          List.mem_singleton] at hg
        rw [hg]
        exact hbound F (List.mem_append_right _ (List.mem_singleton_self F))
      | cons f₀ OPEN₁ =>
        rw [List.cons_append, List.head?_cons, Option.toList_some,
          List.mem_singleton] at hg
        rw [hg]
        exact hbound f₀
          (List.mem_append_left _ (List.mem_cons_self f₀ OPEN₁))
    have hsuf_of : ∀ a s₁, body.get? j = some a → a ≠ .return →
        (∀ m, a ≠ .br m) → (∀ g, a ≠ .call g) →
        normVStep C a s = some s₁ → ∃ X₁, s₁.os = X₁ ++ FROZEN := by
      intro a s₁ ha hnr hnbr hncall hstep
      exact normVStep_os_suffix hB hstep ⟨hnr, hnbr, hncall⟩ hhead hosX
    have hex' : ∀ k b, j + 1 ≤ k → k < e → body.get? k = some b →
        b ≠ .return ∧ (∀ m, b ≠ .br m) ∧ (∀ g, b ≠ .call g) :=
      fun k b hk hke hb => hex k b (by omega) hke hb
    split at hgo
    · exact Option.noConfusion hgo
    · -- .block
      rename_i hget
      obtain ⟨s₁, hstep, hrun'⟩ := hstep_of _ hget
      have hs₁ : s₁ = ⟨s.os, ⟨.blk, none, s.os, false⟩ :: s.cs⟩ := by
        simpa [normVStep] using hstep.symm
      have hcs₁ : s₁.cs = (⟨.blk, none, s.os, false⟩ :: OPEN) ++ F :: CUR := by
        have hs : s₁.cs = ⟨.blk, none, s.os, false⟩ :: s.cs := by rw [hs₁]
        simp only [hs, hcs, List.cons_append]
      have hd' : (⟨.blk, none, s.os, false⟩ :: OPEN).length = d + 1 := by
        simp only [List.length_cons]; omega
      have hsuf₁ : ∃ X₁, s₁.os = X₁ ++ FROZEN :=
        ⟨X, by rw [hs₁]; exact hosX⟩
      have hbound₁ : ∀ fr ∈ (⟨.blk, none, s.os, false⟩ :: OPEN) ++ [F],
          B ≤ fr.entry.length := by
        intro fr hm
        rw [List.cons_append, List.mem_cons] at hm
        obtain rfl | hm := hm
        · show B ≤ s.os.length
          rw [hosX, List.length_append, hB]; omega
        · exact hbound fr hm
      obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
      · exact ⟨s₁, _, F, d + 1, el, fuel, hgo,
          htake _ _ hget hstep, hcs₁, hd', hsuf₁, hbound₁,
          rfl, rfl, Or.inl rfl⟩
      · obtain ⟨s', OPEN', F', d'', el', fuel'', hcont'', hrun'', hcs'',
          hd'', hsuf'', hbound'', hF''⟩ := ih (hfuel' _ hget) hrun' hcs₁ hd' hgo
            hsuf₁ hB hbound₁ hex' j' hjj' hje
        exact ⟨s', OPEN', F', d'', el', fuel'', hcont'',
          by rw [hchain _ _ hget hstep j' hjj']; exact hrun'', hcs'', hd'',
          hsuf'', hbound'', hF''⟩
    · -- .loop
      rename_i hget
      obtain ⟨s₁, hstep, hrun'⟩ := hstep_of _ hget
      have hs₁ : s₁ = ⟨s.os, ⟨.lp, none, s.os, false⟩ :: s.cs⟩ := by
        simpa [normVStep] using hstep.symm
      have hcs₁ : s₁.cs = (⟨.lp, none, s.os, false⟩ :: OPEN) ++ F :: CUR := by
        have hs : s₁.cs = ⟨.lp, none, s.os, false⟩ :: s.cs := by rw [hs₁]
        simp only [hs, hcs, List.cons_append]
      have hd' : (⟨.lp, none, s.os, false⟩ :: OPEN).length = d + 1 := by
        simp only [List.length_cons]; omega
      have hsuf₁ : ∃ X₁, s₁.os = X₁ ++ FROZEN :=
        ⟨X, by rw [hs₁]; exact hosX⟩
      have hbound₁ : ∀ fr ∈ (⟨.lp, none, s.os, false⟩ :: OPEN) ++ [F],
          B ≤ fr.entry.length := by
        intro fr hm
        rw [List.cons_append, List.mem_cons] at hm
        obtain rfl | hm := hm
        · show B ≤ s.os.length
          rw [hosX, List.length_append, hB]; omega
        · exact hbound fr hm
      obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
      · exact ⟨s₁, _, F, d + 1, el, fuel, hgo,
          htake _ _ hget hstep, hcs₁, hd', hsuf₁, hbound₁,
          rfl, rfl, Or.inl rfl⟩
      · obtain ⟨s', OPEN', F', d'', el', fuel'', hcont'', hrun'', hcs'',
          hd'', hsuf'', hbound'', hF''⟩ := ih (hfuel' _ hget) hrun' hcs₁ hd' hgo
            hsuf₁ hB hbound₁ hex' j' hjj' hje
        exact ⟨s', OPEN', F', d'', el', fuel'', hcont'',
          by rw [hchain _ _ hget hstep j' hjj']; exact hrun'', hcs'', hd'',
          hsuf'', hbound'', hF''⟩
    · -- .ifE
      rename_i hget
      obtain ⟨s₁, hstep, hrun'⟩ := hstep_of _ hget
      have hstep₂ := hstep
      simp only [normVStep] at hstep₂
      obtain ⟨os₁, hpop, hs₁⟩ := map_some_inv hstep₂
      have hcs₁ : s₁.cs = (⟨.ift, none, os₁, false⟩ :: OPEN) ++ F :: CUR := by
        have hs : s₁.cs = ⟨.ift, none, os₁, false⟩ :: s.cs :=
          congrArg NormVSt.cs hs₁.symm
        simp only [hs, hcs, List.cons_append]
      have hd' : (⟨.ift, none, os₁, false⟩ :: OPEN).length = d + 1 := by
        simp only [List.length_cons]; omega
      obtain ⟨hnr, hnbr, hncall⟩ := hex j .ifE (Nat.le_refl j)
        (by have := go_result_gt hgo; omega) hget
      obtain ⟨X₁, hos₁⟩ := hsuf_of _ _ hget hnr hnbr hncall hstep
      have hs₁os : s₁.os = os₁ := congrArg NormVSt.os hs₁.symm
      have hsuf₁ : ∃ X₁', s₁.os = X₁' ++ FROZEN := ⟨X₁, hos₁⟩
      have hbound₁ : ∀ fr ∈ (⟨.ift, none, os₁, false⟩ :: OPEN) ++ [F],
          B ≤ fr.entry.length := by
        intro fr hm
        rw [List.cons_append, List.mem_cons] at hm
        obtain rfl | hm := hm
        · show B ≤ os₁.length
          rw [hs₁os] at hos₁
          rw [hos₁, List.length_append, hB]; omega
        · exact hbound fr hm
      obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
      · exact ⟨s₁, _, F, d + 1, el, fuel, hgo,
          htake _ _ hget hstep, hcs₁, hd', hsuf₁, hbound₁,
          rfl, rfl, Or.inl rfl⟩
      · obtain ⟨s', OPEN', F', d'', el', fuel'', hcont'', hrun'', hcs'',
          hd'', hsuf'', hbound'', hF''⟩ := ih (hfuel' _ hget) hrun' hcs₁ hd' hgo
            hsuf₁ hB hbound₁ hex' j' hjj' hje
        exact ⟨s', OPEN', F', d'', el', fuel'', hcont'',
          by rw [hchain _ _ hget hstep j' hjj']; exact hrun'', hcs'', hd'',
          hsuf'', hbound'', hF''⟩
    · -- .endI
      rename_i hget
      split at hgo
      · rename_i hd0
        exfalso
        simp only [Option.some.injEq, Prod.mk.injEq] at hgo
        rw [← hgo.2] at hje
        exact absurd hje (Nat.not_lt.mpr (Nat.succ_le_of_lt hjj))
      · rename_i hd0
        obtain ⟨s₁, hstep, hrun'⟩ := hstep_of _ hget
        cases OPEN with
        | nil =>
          simp only [List.length_nil] at hd
          exact absurd hd.symm hd0
        | cons f₀ OPEN' =>
          have hcs' : s.cs = f₀ :: (OPEN' ++ F :: CUR) := by
            simp only [hcs, List.cons_append]
          have hd' : OPEN'.length = d - 1 := by
            simp only [List.length_cons] at hd; omega
          have hcs₁ : s₁.cs = OPEN' ++ F :: CUR := by
            have hstep₂ := hstep
            simp only [normVStep] at hstep₂
            simp only [hcs'] at hstep₂
            split at hstep₂
            · exact Option.noConfusion hstep₂
            · obtain ⟨os₁, hfchk, hs₁⟩ := map_some_inv hstep₂
              exact congrArg NormVSt.cs hs₁.symm
          obtain ⟨hnr, hnbr, hncall⟩ := hex j .endI (Nat.le_refl j)
            (by have := go_result_gt hgo; omega) hget
          obtain ⟨X₁, hos₁⟩ := hsuf_of _ _ hget hnr hnbr hncall hstep
          have hsuf₁ : ∃ X₁', s₁.os = X₁' ++ FROZEN := ⟨X₁, hos₁⟩
          have hbound₁ : ∀ fr ∈ OPEN' ++ [F], B ≤ fr.entry.length := by
            intro fr hm
            exact hbound fr (by
              rw [List.mem_append] at hm ⊢
              cases hm with
              | inl h => exact Or.inl (List.mem_cons_of_mem _ h)
              | inr h => exact Or.inr h)
          obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
          · exact ⟨s₁, OPEN', F, d - 1, el, fuel, hgo,
              htake _ _ hget hstep, hcs₁, hd', hsuf₁, hbound₁,
              rfl, rfl, Or.inl rfl⟩
          · obtain ⟨s', OPEN₁', F', d'', el', fuel'', hcont'', hrun'',
              hcs'', hd'', hsuf'', hbound'', hF''⟩ := ih (hfuel' _ hget) hrun'
                hcs₁ hd' hgo hsuf₁ hB hbound₁ hex' j' hjj' hje
            exact ⟨s', OPEN₁', F', d'', el', fuel'', hcont'',
              by rw [hchain _ _ hget hstep j' hjj']; exact hrun'', hcs'',
              hd'', hsuf'', hbound'', hF''⟩
    · -- .elseE
      rename_i hget
      obtain ⟨s₁, hstep, hrun'⟩ := hstep_of _ hget
      split at hgo
      · rename_i hd0
        subst hd0
        have hO : OPEN = [] := List.length_eq_zero.mp hd
        have hcs' : s.cs = F :: CUR := by
          have h' := hcs; rw [hO] at h'; exact h'
        have hcs₁ : s₁.cs =
            [] ++ (⟨.els, F.rt, F.entry, F.un⟩ : NormTFrame) :: CUR := by
          have hstep₂ := hstep
          simp only [normVStep] at hstep₂
          simp only [hcs'] at hstep₂
          split at hstep₂
          · obtain ⟨os₁, hfchk, hs₁⟩ := map_some_inv hstep₂
            exact congrArg NormVSt.cs hs₁.symm
          · exact Option.noConfusion hstep₂
        obtain ⟨hnr, hnbr, hncall⟩ := hex j .elseE (Nat.le_refl j)
          (by have := go_result_gt hgo; omega) hget
        obtain ⟨X₁, hos₁⟩ := hsuf_of _ _ hget hnr hnbr hncall hstep
        have hsuf₁ : ∃ X₁', s₁.os = X₁' ++ FROZEN := ⟨X₁, hos₁⟩
        have hbound₁ : ∀ fr ∈ [] ++ [(⟨.els, F.rt, F.entry, F.un⟩ : NormTFrame)],
            B ≤ fr.entry.length := by
          intro fr hm
          rw [List.nil_append, List.mem_singleton] at hm
          subst hm
          exact hbound F
            (List.mem_append_right _ (List.mem_singleton_self F))
        obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
        · exact ⟨s₁, [], _, 0, _, fuel, hgo,
            htake _ _ hget hstep, hcs₁, rfl, hsuf₁, hbound₁,
            rfl, rfl, Or.inr rfl⟩
        · obtain ⟨s', OPEN', F', d'', el', fuel'', hcont'', hrun'', hcs'',
            hd'', hsuf'', hbound'', hF''⟩ := ih (hfuel' _ hget) hrun' hcs₁ rfl hgo
              hsuf₁ hB hbound₁ hex' j' hjj' hje
          exact ⟨s', OPEN', F', d'', el', fuel'', hcont'',
            by rw [hchain _ _ hget hstep j' hjj']; exact hrun'', hcs'', hd'',
            hsuf'', hbound'', hF''.1, hF''.2.1,
            Or.inr (hF''.2.2.elim (fun h => h) (fun h => h))⟩
      · rename_i hd0
        cases OPEN with
        | nil =>
          simp only [List.length_nil] at hd
          exact absurd hd.symm hd0
        | cons f₀ OPEN' =>
          have hcs' : s.cs = f₀ :: (OPEN' ++ F :: CUR) := by
            simp only [hcs, List.cons_append]
          have hcs₁ : s₁.cs =
              (⟨.els, f₀.rt, f₀.entry, f₀.un⟩ :: OPEN') ++ F :: CUR := by
            have hstep₂ := hstep
            simp only [normVStep] at hstep₂
            simp only [hcs'] at hstep₂
            split at hstep₂
            · obtain ⟨os₁, hfchk, hs₁⟩ := map_some_inv hstep₂
              exact congrArg NormVSt.cs hs₁.symm
            · exact Option.noConfusion hstep₂
          have hd' : (⟨.els, f₀.rt, f₀.entry, f₀.un⟩ :: OPEN').length = d := by
            simp only [List.length_cons] at hd ⊢; omega
          obtain ⟨hnr, hnbr, hncall⟩ := hex j .elseE (Nat.le_refl j)
            (by have := go_result_gt hgo; omega) hget
          obtain ⟨X₁, hos₁⟩ := hsuf_of _ _ hget hnr hnbr hncall hstep
          have hsuf₁ : ∃ X₁', s₁.os = X₁' ++ FROZEN := ⟨X₁, hos₁⟩
          have hbound₁ : ∀ fr ∈ (⟨.els, f₀.rt, f₀.entry, f₀.un⟩ :: OPEN')
              ++ [F], B ≤ fr.entry.length := by
            intro fr hm
            rw [List.cons_append, List.mem_cons] at hm
            obtain rfl | hm := hm
            · exact hbound f₀
                (List.mem_append_left _ (List.mem_cons_self f₀ OPEN'))
            · exact hbound fr (by
                rw [List.mem_append] at hm ⊢
                cases hm with
                | inl h => exact Or.inl (List.mem_cons_of_mem _ h)
                | inr h => exact Or.inr h)
          obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
          · exact ⟨s₁, _, F, d, el, fuel, hgo,
              htake _ _ hget hstep, hcs₁, hd', hsuf₁, hbound₁,
              rfl, rfl, Or.inl rfl⟩
          · obtain ⟨s', OPEN₁', F', d'', el', fuel'', hcont'', hrun'',
              hcs'', hd'', hsuf'', hbound'', hF''⟩ := ih (hfuel' _ hget) hrun'
                hcs₁ hd' hgo hsuf₁ hB hbound₁ hex' j' hjj' hje
            exact ⟨s', OPEN₁', F', d'', el', fuel'', hcont'',
              by rw [hchain _ _ hget hstep j' hjj']; exact hrun'', hcs'',
              hd'', hsuf'', hbound'', hF''⟩
    · -- wildcard (.br/.return/.call/.brIf/.drop/.select/.local*/flat)
      rename_i hbnone hbblk hblp hbif hbend hbels
      match hj : body.get? j with
      | none => exact absurd hj hbnone
      | some a =>
        obtain ⟨s₁, hstep, hrun'⟩ := hstep_of a hj
        have hstab := normVStep_cs_stable hstep
          ⟨fun h => hbblk (h ▸ hj), fun h => hblp (h ▸ hj),
           fun h => hbif (h ▸ hj), fun h => hbend (h ▸ hj)⟩
        obtain ⟨hnr, hnbr, hncall⟩ := hex j a (Nat.le_refl j)
          (by have := go_result_gt hgo; omega) hj
        obtain ⟨X₁, hos₁⟩ := hsuf_of _ _ hj hnr hnbr hncall hstep
        have hsuf₁ : ∃ X₁', s₁.os = X₁' ++ FROZEN := ⟨X₁, hos₁⟩
        obtain ⟨f, f', rest, hcs_f, hcs₁, hent⟩ | hcs₁ := hstab
        · -- head-mutate (.br/.return/.elseE-shape)
          cases OPEN with
          | nil =>
            simp only [List.nil_append] at hcs
            have h := hcs_f.symm.trans hcs
            injection h with hf hr
            subst hf
            have hcs₁' : s₁.cs = [] ++ f' :: CUR := by
              simp only [hcs₁, hr, List.nil_append]
            have hbound₁ : ∀ fr ∈ [] ++ [f'], B ≤ fr.entry.length := by
              intro fr hm
              rw [List.nil_append, List.mem_singleton] at hm
              subst hm
              rw [hent.1]
              exact hbound f
                (List.mem_append_right _ (List.mem_singleton_self f))
            obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
            · exact ⟨s₁, [], f', d, el, fuel, hgo,
                htake _ _ hj hstep, hcs₁', hd, hsuf₁, hbound₁, hent⟩
            · subst hd
              obtain ⟨s', OPEN', F', d'', el', fuel'', hcont'', hrun'',
                hcs'', hd'', hsuf'', hbound'', hF''⟩ :=
                ih (hfuel' _ hj) hrun' hcs₁' rfl hgo hsuf₁ hB hbound₁ hex'
                  j' hjj' hje
              exact ⟨s', OPEN', F', d'', el', fuel'', hcont'',
                by rw [hchain _ _ hj hstep j' hjj']; exact hrun'', hcs'',
                hd'', hsuf'', hbound'', hF''.1.trans hent.1,
                hF''.2.1.trans hent.2.1,
                hF''.2.2.elim (fun h => hent.2.2.elim
                    (fun g => Or.inl (h.trans g)) (fun g => Or.inr (h.trans g)))
                  (fun h => Or.inr h)⟩
          | cons f₀ OPEN' =>
            have h := hcs_f.symm.trans hcs
            injection h with hf hr
            subst hf
            have hcs₁' : s₁.cs = (f' :: OPEN') ++ F :: CUR := by
              rw [hcs₁, hr]; rfl
            have hd' : (f' :: OPEN').length = d := by
              simp only [List.length_cons] at hd ⊢; omega
            have hbound₁ : ∀ fr ∈ (f' :: OPEN') ++ [F],
                B ≤ fr.entry.length := by
              intro fr hm
              rw [List.cons_append, List.mem_cons] at hm
              obtain rfl | hm := hm
              · rw [hent.1]
                exact hbound f
                  (List.mem_append_left _ (List.mem_cons_self f OPEN'))
              · exact hbound fr (by
                  rw [List.mem_append] at hm ⊢
                  cases hm with
                  | inl hh => exact Or.inl (List.mem_cons_of_mem _ hh)
                  | inr hh => exact Or.inr hh)
            obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
            · exact ⟨s₁, _, F, d, el, fuel, hgo,
                htake _ _ hj hstep, hcs₁', hd', hsuf₁, hbound₁,
                rfl, rfl, Or.inl rfl⟩
            · obtain ⟨s', OPEN₁', F', d'', el', fuel'', hcont'', hrun'',
                hcs'', hd'', hsuf'', hbound'', hF''⟩ :=
                ih (hfuel' _ hj) hrun' hcs₁' hd' hgo hsuf₁ hB hbound₁ hex'
                  j' hjj' hje
              exact ⟨s', OPEN₁', F', d'', el', fuel'', hcont'',
                by rw [hchain _ _ hj hstep j' hjj']; exact hrun'', hcs'',
                hd'', hsuf'', hbound'', hF''⟩
        · -- cs unchanged
          have hcs₁' : s₁.cs = OPEN ++ F :: CUR := by simp only [hcs₁, hcs]
          obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
          · exact ⟨s₁, OPEN, F, d, el, fuel, hgo,
              htake _ _ hj hstep, hcs₁', hd, hsuf₁, hbound,
              rfl, rfl, Or.inl rfl⟩
          · obtain ⟨s', OPEN', F', d'', el', fuel'', hcont'', hrun'', hcs'',
              hd'', hsuf'', hbound'', hF''⟩ := ih (hfuel' _ hj) hrun' hcs₁' hd hgo
                hsuf₁ hB hbound hex' j' hjj' hje
            exact ⟨s', OPEN', F', d'', el', fuel'', hcont'',
              by rw [hchain _ _ hj hstep j' hjj']; exact hrun'', hcs'', hd'',
              hsuf'', hbound'', hF''⟩

/-- A control-stack-only track through a validator run inside one
enclosing frame: at every position `j'` in the open interval `(j, e)` of a
successful `go`-scan, the validator's control stack decomposes as
`OPEN' ++ F' :: CUR` with `|OPEN'|` equal to the scan depth.  This is the
`br` arm's instrument for pinning the scan depth at the branch pc to the
number of frames above the branch target; unlike `seg_track_aux` no
operand-stack suffix is tracked, so no instruction exclusions are needed. -/
theorem seg_track_cs {C : NormVCtx} {body : List NormInstr}
    {CUR : List NormTFrame} :
    ∀ {fuel j d el s sf OPEN F x e},
    (body.drop j).length ≤ fuel →
    normVRun C s (body.drop j) = some sf →
    s.cs = OPEN ++ F :: CUR → OPEN.length = d →
    normElseEnd.go body fuel j d el = some (x, e) →
    ∀ j', j < j' → j' < e →
      ∃ s' OPEN' F' d' el' fuel',
        normElseEnd.go body fuel' j' d' el' = some (x, e) ∧
        normVRun C s ((body.drop j).take (j' - j)) = some s' ∧
        s'.cs = OPEN' ++ F' :: CUR ∧ OPEN'.length = d' := by
  intro fuel
  induction fuel with
  | zero =>
    intro j d el s sf OPEN F x e hfuel hrun hcs hd hgo j' hjj hje
    exact Option.noConfusion hgo
  | succ fuel ih =>
    intro j d el s sf OPEN F x e hfuel hrun hcs hd hgo j' hjj hje
    rw [normElseEnd_go_succ] at hgo
    have hfuel' : ∀ a, body.get? j = some a →
        (body.drop (j + 1)).length ≤ fuel := by
      intro a ha
      have := hfuel; rw [drop_eq_cons_of_get? ha, List.length_cons] at this
      omega
    have hstep_of : ∀ a, body.get? j = some a →
        ∃ s₁, normVStep C a s = some s₁ ∧
          normVRun C s₁ (body.drop (j + 1)) = some sf := by
      intro a ha
      rw [drop_eq_cons_of_get? ha] at hrun
      simp only [normVRun] at hrun
      exact bind_some_inv hrun
    have htake : ∀ a s₁, body.get? j = some a →
        normVStep C a s = some s₁ →
        normVRun C s ((body.drop j).take (j + 1 - j)) = some s₁ := by
      intro a s₁ ha hstep
      have h1 : j + 1 - j = 1 := by omega
      rw [h1, drop_eq_cons_of_get? ha]
      show normVRun C s [a] = some s₁
      simp only [normVRun]
      rw [hstep]; rfl
    have hchain : ∀ a s₁, body.get? j = some a →
        normVStep C a s = some s₁ → ∀ j',
        j + 1 < j' →
        normVRun C s ((body.drop j).take (j' - j)) =
          normVRun C s₁ ((body.drop (j + 1)).take (j' - (j + 1))) := by
      intro a s₁ ha hstep j' hjj'
      have h1 : j' - j = (j' - (j + 1)) + 1 := by omega
      rw [drop_eq_cons_of_get? ha, h1]
      show normVRun C s (a :: (body.drop (j + 1)).take (j' - (j + 1))) = _
      simp only [normVRun]
      rw [hstep]; rfl
    split at hgo
    · exact Option.noConfusion hgo
    · -- .block
      rename_i hget
      obtain ⟨s₁, hstep, hrun'⟩ := hstep_of _ hget
      have hs₁ : s₁ = ⟨s.os, ⟨.blk, none, s.os, false⟩ :: s.cs⟩ := by
        simpa [normVStep] using hstep.symm
      have hcs₁ : s₁.cs = (⟨.blk, none, s.os, false⟩ :: OPEN) ++ F :: CUR := by
        have hs : s₁.cs = ⟨.blk, none, s.os, false⟩ :: s.cs := by rw [hs₁]
        simp only [hs, hcs, List.cons_append]
      have hd' : (⟨.blk, none, s.os, false⟩ :: OPEN).length = d + 1 := by
        simp only [List.length_cons]; omega
      obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
      · exact ⟨s₁, _, F, d + 1, el, fuel, hgo,
          htake _ _ hget hstep, hcs₁, hd'⟩
      · obtain ⟨s', OPEN', F', d'', el', fuel'', hcont'', hrun'', hcs'',
          hd''⟩ := ih (hfuel' _ hget) hrun' hcs₁ hd' hgo j' hjj' hje
        exact ⟨s', OPEN', F', d'', el', fuel'', hcont'',
          by rw [hchain _ _ hget hstep j' hjj']; exact hrun'', hcs'', hd''⟩
    · -- .loop
      rename_i hget
      obtain ⟨s₁, hstep, hrun'⟩ := hstep_of _ hget
      have hs₁ : s₁ = ⟨s.os, ⟨.lp, none, s.os, false⟩ :: s.cs⟩ := by
        simpa [normVStep] using hstep.symm
      have hcs₁ : s₁.cs = (⟨.lp, none, s.os, false⟩ :: OPEN) ++ F :: CUR := by
        have hs : s₁.cs = ⟨.lp, none, s.os, false⟩ :: s.cs := by rw [hs₁]
        simp only [hs, hcs, List.cons_append]
      have hd' : (⟨.lp, none, s.os, false⟩ :: OPEN).length = d + 1 := by
        simp only [List.length_cons]; omega
      obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
      · exact ⟨s₁, _, F, d + 1, el, fuel, hgo,
          htake _ _ hget hstep, hcs₁, hd'⟩
      · obtain ⟨s', OPEN', F', d'', el', fuel'', hcont'', hrun'', hcs'',
          hd''⟩ := ih (hfuel' _ hget) hrun' hcs₁ hd' hgo j' hjj' hje
        exact ⟨s', OPEN', F', d'', el', fuel'', hcont'',
          by rw [hchain _ _ hget hstep j' hjj']; exact hrun'', hcs'', hd''⟩
    · -- .ifE
      rename_i hget
      obtain ⟨s₁, hstep, hrun'⟩ := hstep_of _ hget
      have hstep₂ := hstep
      simp only [normVStep] at hstep₂
      obtain ⟨os₁, hpop, hs₁⟩ := map_some_inv hstep₂
      have hcs₁ : s₁.cs = (⟨.ift, none, os₁, false⟩ :: OPEN) ++ F :: CUR := by
        have hs : s₁.cs = ⟨.ift, none, os₁, false⟩ :: s.cs :=
          congrArg NormVSt.cs hs₁.symm
        simp only [hs, hcs, List.cons_append]
      have hd' : (⟨.ift, none, os₁, false⟩ :: OPEN).length = d + 1 := by
        simp only [List.length_cons]; omega
      obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
      · exact ⟨s₁, _, F, d + 1, el, fuel, hgo,
          htake _ _ hget hstep, hcs₁, hd'⟩
      · obtain ⟨s', OPEN', F', d'', el', fuel'', hcont'', hrun'', hcs'',
          hd''⟩ := ih (hfuel' _ hget) hrun' hcs₁ hd' hgo j' hjj' hje
        exact ⟨s', OPEN', F', d'', el', fuel'', hcont'',
          by rw [hchain _ _ hget hstep j' hjj']; exact hrun'', hcs'', hd''⟩
    · -- .endI
      rename_i hget
      split at hgo
      · rename_i hd0
        exfalso
        simp only [Option.some.injEq, Prod.mk.injEq] at hgo
        rw [← hgo.2] at hje
        exact absurd hje (Nat.not_lt.mpr (Nat.succ_le_of_lt hjj))
      · rename_i hd0
        obtain ⟨s₁, hstep, hrun'⟩ := hstep_of _ hget
        cases OPEN with
        | nil =>
          simp only [List.length_nil] at hd
          exact absurd hd.symm hd0
        | cons f₀ OPEN' =>
          have hcs' : s.cs = f₀ :: (OPEN' ++ F :: CUR) := by
            simp only [hcs, List.cons_append]
          have hd' : OPEN'.length = d - 1 := by
            simp only [List.length_cons] at hd; omega
          have hcs₁ : s₁.cs = OPEN' ++ F :: CUR := by
            have hstep₂ := hstep
            simp only [normVStep] at hstep₂
            simp only [hcs'] at hstep₂
            split at hstep₂
            · exact Option.noConfusion hstep₂
            · obtain ⟨os₁, hfchk, hs₁⟩ := map_some_inv hstep₂
              exact congrArg NormVSt.cs hs₁.symm
          obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
          · exact ⟨s₁, OPEN', F, d - 1, el, fuel, hgo,
              htake _ _ hget hstep, hcs₁, hd'⟩
          · obtain ⟨s', OPEN₁', F', d'', el', fuel'', hcont'', hrun'',
              hcs'', hd''⟩ := ih (hfuel' _ hget) hrun' hcs₁ hd' hgo j' hjj' hje
            exact ⟨s', OPEN₁', F', d'', el', fuel'', hcont'',
              by rw [hchain _ _ hget hstep j' hjj']; exact hrun'', hcs'',
              hd''⟩
    · -- .elseE
      rename_i hget
      obtain ⟨s₁, hstep, hrun'⟩ := hstep_of _ hget
      split at hgo
      · rename_i hd0
        subst hd0
        have hO : OPEN = [] := List.length_eq_zero.mp hd
        have hcs' : s.cs = F :: CUR := by
          have h' := hcs; rw [hO] at h'; exact h'
        have hcs₁ : s₁.cs =
            [] ++ (⟨.els, F.rt, F.entry, F.un⟩ : NormTFrame) :: CUR := by
          have hstep₂ := hstep
          simp only [normVStep] at hstep₂
          simp only [hcs'] at hstep₂
          split at hstep₂
          · obtain ⟨os₁, hfchk, hs₁⟩ := map_some_inv hstep₂
            exact congrArg NormVSt.cs hs₁.symm
          · exact Option.noConfusion hstep₂
        obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
        · exact ⟨s₁, [], _, 0, _, fuel, hgo,
            htake _ _ hget hstep, hcs₁, rfl⟩
        · obtain ⟨s', OPEN', F', d'', el', fuel'', hcont'', hrun'', hcs'',
            hd''⟩ := ih (hfuel' _ hget) hrun' hcs₁ rfl hgo j' hjj' hje
          exact ⟨s', OPEN', F', d'', el', fuel'', hcont'',
            by rw [hchain _ _ hget hstep j' hjj']; exact hrun'', hcs'', hd''⟩
      · rename_i hd0
        cases OPEN with
        | nil =>
          simp only [List.length_nil] at hd
          exact absurd hd.symm hd0
        | cons f₀ OPEN' =>
          have hcs' : s.cs = f₀ :: (OPEN' ++ F :: CUR) := by
            simp only [hcs, List.cons_append]
          have hcs₁ : s₁.cs =
              (⟨.els, f₀.rt, f₀.entry, f₀.un⟩ :: OPEN') ++ F :: CUR := by
            have hstep₂ := hstep
            simp only [normVStep] at hstep₂
            simp only [hcs'] at hstep₂
            split at hstep₂
            · obtain ⟨os₁, hfchk, hs₁⟩ := map_some_inv hstep₂
              exact congrArg NormVSt.cs hs₁.symm
            · exact Option.noConfusion hstep₂
          have hd' : (⟨.els, f₀.rt, f₀.entry, f₀.un⟩ :: OPEN').length = d := by
            simp only [List.length_cons] at hd ⊢; omega
          obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
          · exact ⟨s₁, _, F, d, el, fuel, hgo,
              htake _ _ hget hstep, hcs₁, hd'⟩
          · obtain ⟨s', OPEN₁', F', d'', el', fuel'', hcont'', hrun'',
              hcs'', hd''⟩ := ih (hfuel' _ hget) hrun' hcs₁ hd' hgo j' hjj' hje
            exact ⟨s', OPEN₁', F', d'', el', fuel'', hcont'',
              by rw [hchain _ _ hget hstep j' hjj']; exact hrun'', hcs'',
              hd''⟩
    · -- wildcard (.br/.return/.call/.brIf/.drop/.select/.local*/flat)
      rename_i hbnone hbblk hblp hbif hbend hbels
      match hj : body.get? j with
      | none => exact absurd hj hbnone
      | some a =>
        obtain ⟨s₁, hstep, hrun'⟩ := hstep_of a hj
        have hstab := normVStep_cs_stable hstep
          ⟨fun h => hbblk (h ▸ hj), fun h => hblp (h ▸ hj),
           fun h => hbif (h ▸ hj), fun h => hbend (h ▸ hj)⟩
        obtain ⟨f, f', rest, hcs_f, hcs₁, _hent⟩ | hcs₁ := hstab
        · -- head-mutate (.br/.return/.elseE-shape)
          cases OPEN with
          | nil =>
            simp only [List.nil_append] at hcs
            have h := hcs_f.symm.trans hcs
            injection h with hf hr
            subst hf
            have hcs₁' : s₁.cs = [] ++ f' :: CUR := by
              simp only [hcs₁, hr, List.nil_append]
            obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
            · exact ⟨s₁, [], f', d, el, fuel, hgo,
                htake _ _ hj hstep, hcs₁', hd⟩
            · subst hd
              obtain ⟨s', OPEN', F', d'', el', fuel'', hcont'', hrun'',
                hcs'', hd''⟩ :=
                ih (hfuel' _ hj) hrun' hcs₁' rfl hgo j' hjj' hje
              exact ⟨s', OPEN', F', d'', el', fuel'', hcont'',
                by rw [hchain _ _ hj hstep j' hjj']; exact hrun'', hcs'',
                hd''⟩
          | cons f₀ OPEN' =>
            have h := hcs_f.symm.trans hcs
            injection h with hf hr
            subst hf
            have hcs₁' : s₁.cs = (f' :: OPEN') ++ F :: CUR := by
              rw [hcs₁, hr]; rfl
            have hd' : (f' :: OPEN').length = d := by
              simp only [List.length_cons] at hd ⊢; omega
            obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
            · exact ⟨s₁, _, F, d, el, fuel, hgo,
                htake _ _ hj hstep, hcs₁', hd'⟩
            · obtain ⟨s', OPEN₁', F', d'', el', fuel'', hcont'', hrun'',
                hcs'', hd''⟩ :=
                ih (hfuel' _ hj) hrun' hcs₁' hd' hgo j' hjj' hje
              exact ⟨s', OPEN₁', F', d'', el', fuel'', hcont'',
                by rw [hchain _ _ hj hstep j' hjj']; exact hrun'', hcs'',
                hd''⟩
        · -- cs unchanged
          have hcs₁' : s₁.cs = OPEN ++ F :: CUR := by simp only [hcs₁, hcs]
          obtain rfl | hjj' := Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hjj)
          · exact ⟨s₁, OPEN, F, d, el, fuel, hgo,
              htake _ _ hj hstep, hcs₁', hd⟩
          · obtain ⟨s', OPEN', F', d'', el', fuel'', hcont'', hrun'', hcs'',
              hd''⟩ := ih (hfuel' _ hj) hrun' hcs₁' hd hgo j' hjj' hje
            exact ⟨s', OPEN', F', d'', el', fuel'', hcont'',
              by rw [hchain _ _ hj hstep j' hjj']; exact hrun'', hcs'',
              hd''⟩

/-- The scan visits every position strictly below its result, with some
depth/elsePc state — the continuation at `q` is a tail-call returning the
same result. -/
theorem go_cont {body : List NormInstr} :
    ∀ {fuel j d el x e},
    normElseEnd.go body fuel j d el = some (x, e) →
    ∀ q, j ≤ q → q < e →
    ∃ fuel' d' el', normElseEnd.go body fuel' q d' el' = some (x, e) := by
  intro fuel
  induction fuel with
  | zero =>
    intro j d el x e hgo q hq hqe
    exact Option.noConfusion hgo
  | succ fuel ih =>
    intro j d el x e hgo q hq hqe
    rw [normElseEnd_go_succ] at hgo
    obtain rfl | hq' := Nat.eq_or_lt_of_le hq
    · exact ⟨fuel + 1, d, el, hgo⟩
    · split at hgo
      · exact Option.noConfusion hgo
      · exact ih hgo q (by omega) hqe
      · exact ih hgo q (by omega) hqe
      · exact ih hgo q (by omega) hqe
      · split at hgo
        · simp only [Option.some.injEq, Prod.mk.injEq] at hgo
          rw [← hgo.2] at hqe
          exact absurd hqe (Nat.not_lt.mpr (Nat.succ_le_of_lt hq'))
        · exact ih hgo q (by omega) hqe
      · split at hgo <;> exact ih hgo q (by omega) hqe
      · exact ih hgo q (by omega) hqe

/-- The two scans reaching `e` from the same position carry the same
depth (the depth hitting 0 at `e - 1`'s `endI` is unique). -/
theorem go_depth_unique {body : List NormInstr} {j d₁ d₂ : Nat}
    {fuel₁ fuel₂ el₁ el₂ x₁ x₂ e}
    (h₁ : normElseEnd.go body fuel₁ j d₁ el₁ = some (x₁, e))
    (h₂ : normElseEnd.go body fuel₂ j d₂ el₂ = some (x₂, e))
    (_hlt : j < e) : d₁ = d₂ := by
  rcases Nat.lt_or_ge d₁ d₂ with h | h
  · exfalso
    have hK : 0 < d₂ - d₁ := Nat.sub_pos_of_lt h
    have h₂' : normElseEnd.go body fuel₂ j (d₂ - d₁ + d₁) el₂ =
        some (x₂, e) := by
      rw [Nat.sub_add_cancel (Nat.le_of_lt h)]; exact h₂
    have hlt' := go_deeper_aux (K := d₂ - d₁) hK h₁ h₂'
    omega
  · rcases Nat.lt_or_ge d₂ d₁ with h' | h'
    · exfalso
      have hK : 0 < d₁ - d₂ := Nat.sub_pos_of_lt h'
      have h₁' : normElseEnd.go body fuel₁ j (d₁ - d₂ + d₂) el₁ =
          some (x₁, e) := by
        rw [Nat.sub_add_cancel (Nat.le_of_lt h')]; exact h₁
      have hlt' := go_deeper_aux (K := d₁ - d₂) hK h₂ h₁'
      omega
    · omega

/-- A nested construct ends strictly before the enclosing scan's result:
`body[q]` opens a construct inside the one scanned from `j`. -/
theorem go_nested_ends {body : List NormInstr} {j q : Nat}
    {fuel el x e} {e₀ : Option Nat × Nat}
    (hgo : normElseEnd.go body fuel j 0 el = some (x, e))
    (hq : j ≤ q) (hqe : q < e)
    (hop : body.get? q = some .block ∨ body.get? q = some .loop ∨
      body.get? q = some .ifE)
    (hin : normElseEnd body q = some e₀) : e₀.2 < e := by
  obtain ⟨fuel', d', el', hcont⟩ := go_cont hgo q hq hqe
  cases fuel' with
  | zero => exact Option.noConfusion hcont
  | succ fuel' =>
    rw [normElseEnd_go_succ] at hcont
    obtain ⟨x₀, e₁⟩ := e₀
    show e₁ < e
    unfold normElseEnd at hin
    obtain hb | hb | hb := hop
    · rw [hb] at hcont; simp only [] at hcont; exact go_deeper hin hcont
    · rw [hb] at hcont; simp only [] at hcont; exact go_deeper hin hcont
    · rw [hb] at hcont; simp only [] at hcont; exact go_deeper hin hcont

/-- The label-history content at one validator state: every machine
label's recorded `startPc` precedes `pc`, startPcs are strictly nested,
and the validator's frame stack below label `i` equals the control stack
the walk produced just after stepping that label's opener.  The last
conjunct is the `br` arm's engine: frames below a live label are frozen
while the label is on the stack (LIFO), so the validator state at
`startPc + 1` is recoverable from the current one — that is what a loop
branch resumes into and what the dead-region walk's `MID ++ below` split
is built from. -/
def NormHistInner (C : NormVCtx) (f : NormFunc) (s : NormVSt)
    (pc : Nat) (ls : List NormLabel) : Prop :=
  (∀ i (hi : i < ls.length), ls[i].startPc < pc) ∧
  (∀ i (hi : i + 1 < ls.length), ls[i + 1].startPc < ls[i].startPc) ∧
  (∀ i (hi : i < ls.length), pc < ls[i].endPc) ∧
  (∀ i (hi : i + 1 < ls.length), ls[i].endPc < ls[i + 1].endPc) ∧
  (∀ i (hi : i < ls.length),
      ∃ sᵢ, normVRun C (normVInit f) (f.body.take (ls[i].startPc + 1)) =
          some sᵢ ∧
        s.cs.drop i = sᵢ.cs)

/-- The label-history half of the S3 invariant (the `br` arm needs it;
every other step preserves it trivially). -/
def NormHist (st : NormState) : Prop :=
  ∀ f s, st.module.funcs.get? st.funcIdx = some f →
    normVRun (NormVCtx.ofModule st.module f) (normVInit f)
        (f.body.take st.pc) = some s →
    NormHistInner (NormVCtx.ofModule st.module f) f s st.pc st.controlStack

/-- The invariant `wx002_preservation` carries. -/
def NormInv (st : NormState) : Prop := NormStateTy st ∧ NormLive st ∧ NormHist st

theorem NormInv.components {st : NormState} (h : NormInv st) :
    ∃ f s, st.module.funcs.get? st.funcIdx = some f ∧
      normVRun (NormVCtx.ofModule st.module f) (normVInit f)
          (f.body.take st.pc) = some s ∧
      s.os = st.operandStack.map NormVal.ty ∧
      NormLabelsCorrespond f.body st.controlStack s.cs ∧
      st.locals.map NormVal.ty = f.params ++ f.locals ∧
      (∀ fr ∈ st.callStack, NormFrameOK st.module fr) ∧
      st.linearMemory.bytes.length =
        st.module.memPages * NormWasmPage ∧
      (∀ fr ∈ s.cs, fr.un = false) ∧ s.cs ≠ [] := by
  obtain ⟨f, hget, ⟨s, hvr, hos, hcorr⟩, hloc, hfr, hmem⟩ := h.1
  refine ⟨f, s, hget, hvr, hos, hcorr, hloc, hfr, hmem,
    h.2.1 f s hget hvr, ?_⟩
  obtain ⟨hlen, -, -⟩ := hcorr
  intro e
  rw [e] at hlen
  simp only [List.length_nil] at hlen
  omega

/-- `NormHistInner` survives moving `pc` while `ls`/`s.cs` are fixed
    (the same-frame steps). -/
theorem NormHistInner.mono {C : NormVCtx} {f : NormFunc} {s s₁ : NormVSt}
    {pc pc' : Nat} {ls : List NormLabel}
    (h : NormHistInner C f s pc ls)
    (hpc' : ∀ i (hi : i < ls.length), ls[i].startPc < pc')
    (hend' : ∀ i (hi : i < ls.length), pc' < ls[i].endPc)
    (hcs : s₁.cs = s.cs) :
    NormHistInner C f s₁ pc' ls := by
  obtain ⟨_, hdec, _, hend, hhist⟩ := h
  refine ⟨hpc', hdec, hend', hend, fun i hi => ?_⟩
  obtain ⟨sᵢ, hᵢ, hd⟩ := hhist i hi
  exact ⟨sᵢ, hᵢ, hcs ▸ hd⟩

/-- `NormHistInner` after a push: index 0 is the just-stepped state
    `s₁`, deeper indices shift under the unchanged tail. -/
theorem NormHistInner.cons {C : NormVCtx} {f : NormFunc} {s s₁ : NormVSt}
    {pc : Nat} {ls : List NormLabel} {lab : NormLabel} {fr : NormTFrame}
    (h : NormHistInner C f s pc ls)
    (hvs1 : normVRun C (normVInit f) (f.body.take (pc + 1)) = some s₁)
    (hstart : lab.startPc = pc) (hcs : s₁.cs = fr :: s.cs)
    (hlabend : pc + 1 < lab.endPc)
    (hendold : ∀ i (hi : i < ls.length), pc + 1 < ls[i].endPc)
    (hnest : ∀ l₀ l₁, ls = l₀ :: l₁ → lab.endPc < l₀.endPc) :
    NormHistInner C f s₁ (pc + 1) (lab :: ls) := by
  obtain ⟨hpc, hdec, _, hend, hhist⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    cases i with
    | zero =>
      rw [List.getElem_cons_zero, hstart]; exact Nat.lt_succ_self pc
    | succ i =>
      rw [List.getElem_cons_succ]
      exact Nat.lt_trans (hpc i (Nat.lt_of_succ_lt_succ hi)) (Nat.lt_succ_self pc)
  · intro i hi
    cases i with
    | zero =>
      rw [List.getElem_cons_succ, List.getElem_cons_zero, hstart]
      exact hpc 0 (Nat.lt_of_succ_lt_succ hi)
    | succ i =>
      simp only [List.getElem_cons_succ]
      exact hdec i (Nat.lt_of_succ_lt_succ hi)
  · intro i hi
    cases i with
    | zero => rw [List.getElem_cons_zero]; exact hlabend
    | succ i =>
      rw [List.getElem_cons_succ]
      exact hendold i (Nat.lt_of_succ_lt_succ hi)
  · intro i hi
    cases i with
    | zero =>
      rw [List.getElem_cons_zero, List.getElem_cons_succ]
      cases ls with
      | nil => simp at hi
      | cons l₀ l₁ => exact hnest l₀ l₁ rfl
    | succ i =>
      simp only [List.getElem_cons_succ]
      exact hend i (Nat.lt_of_succ_lt_succ hi)
  · intro i hi
    cases i with
    | zero =>
      exact ⟨s₁, by rw [List.getElem_cons_zero, hstart]; exact hvs1,
        List.drop_zero s₁.cs⟩
    | succ i =>
      obtain ⟨sᵢ, hᵢ, hd⟩ := hhist i (Nat.lt_of_succ_lt_succ hi)
      exact ⟨sᵢ, by rw [List.getElem_cons_succ]; exact hᵢ,
        by rw [hcs, List.drop_succ_cons]; exact hd⟩

/-- `NormHistInner` after the innermost label/frame pair pops. -/
theorem NormHistInner.tail {C : NormVCtx} {f : NormFunc} {s s₁ : NormVSt}
    {pc : Nat} {lab : NormLabel} {ls : List NormLabel} {fr : NormTFrame}
    {rs : List NormTFrame}
    (h : NormHistInner C f s pc (lab :: ls))
    (hcs : s.cs = fr :: rs) (hcs₁ : s₁.cs = rs) :
    NormHistInner C f s₁ (pc + 1) ls := by
  obtain ⟨hpc, hdec, hpe, hend, hhist⟩ := h
  have hlab : ∀ i (hi : i < ls.length), lab.endPc < ls[i].endPc := by
    intro i hi
    induction i with
    | zero =>
      have h0 := hend 0 (by simpa)
      rw [List.getElem_cons_zero, List.getElem_cons_succ] at h0
      exact h0
    | succ k ihk =>
      have hk := hend (k + 1) (by simpa)
      simp only [List.getElem_cons_succ] at hk
      exact Nat.lt_trans (ihk (Nat.lt_of_succ_lt hi)) hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hlt := hpc (i + 1) (by simpa)
    rw [List.getElem_cons_succ] at hlt
    exact Nat.lt_trans hlt (Nat.lt_succ_self _)
  · intro i hi
    have hlt := hdec (i + 1) (by simpa)
    simp only [List.getElem_cons_succ] at hlt
    exact hlt
  · intro i hi
    have hlt := hpe 0 (by simp)
    rw [List.getElem_cons_zero] at hlt
    exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hlt) (hlab i hi)
  · intro i hi
    have hlt := hend (i + 1) (by simpa)
    simp only [List.getElem_cons_succ] at hlt
    exact hlt
  · intro i hi
    obtain ⟨sᵢ, hᵢ, hd⟩ := hhist (i + 1) (by simpa)
    rw [List.getElem_cons_succ] at hᵢ
    refine ⟨sᵢ, hᵢ, ?_⟩
    rw [hcs₁]
    have hdrop : s.cs.drop (i + 1) = rs.drop i := by
      rw [hcs, List.drop_succ_cons]
    rwa [hdrop] at hd

/-- Empty control stack: `NormHistInner` is vacuous (`call`'s fresh
    control stack). -/
theorem NormHistInner.nil {C : NormVCtx} {f : NormFunc} {s : NormVSt}
    {pc : Nat} : NormHistInner C f s pc [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro i hi <;> simp at hi

/-- `pc + 1 < ls[k].endPc` for all labels when the instruction at `pc`
isn't an `endI` (the strict form of `pc < endPc`, for `cons`/`mono`). -/
theorem hpend_succ {body : List NormInstr} {ls : List NormLabel}
    {s : NormVSt} {C : NormVCtx} {f : NormFunc} {pc : Nat} {i : NormInstr}
    (hcorr : NormLabelsCorrespond body ls s.cs)
    (hinner : NormHistInner C f s pc ls)
    (hi : body.get? pc = some i) (hne : i ≠ .endI) :
    ∀ k (hk : k < ls.length), pc + 1 < ls[k].endPc := by
  intro k hk
  have hlt := hinner.2.2.1 k hk
  obtain ⟨hc, htag, hh, hendE, hstart⟩ := hcorr.2.2 k hk
  obtain ⟨elsePc₀, hEE⟩ := hendE
  have hendI := go_endI hEE
  refine Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hlt) ?_
  intro heq
  have hpc_eq : pc = ls[k].endPc - 1 := by omega
  rw [hpc_eq] at hi
  exact hne (Option.some.inj (hi.symm.trans hendI))

/-- An opener at `pc` inside label `ls[0]` ends strictly inside it
(`go_nested_ends` packaging for `cons`'s `hnest` obligation). -/
theorem hnest_opener {body : List NormInstr} {ls : List NormLabel}
    {s : NormVSt} {C : NormVCtx} {f : NormFunc} {pc : Nat} {i : NormInstr}
    {x : Option Nat} {e : Nat}
    (hcorr : NormLabelsCorrespond body ls s.cs)
    (hinner : NormHistInner C f s pc ls)
    (hi : body.get? pc = some i)
    (hop : i = .block ∨ i = .loop ∨ i = .ifE)
    (hEE : normElseEnd body pc = some (x, e)) :
    ∀ l₀ l₁, ls = l₀ :: l₁ → e < l₀.endPc := by
  intro l₀ l₁ hls
  subst hls
  have h0 : 0 < (l₀ :: l₁).length := by simp
  obtain ⟨hc, htag, hh, hendE, hstart₀⟩ := hcorr.2.2 0 h0
  obtain ⟨elsePc₀, hEE₀⟩ := hendE
  simp only [List.getElem_cons_zero] at hEE₀
  have hstart := hinner.1 0 h0
  have hend := hinner.2.2.1 0 h0
  simp only [List.getElem_cons_zero] at hstart hend
  obtain rfl | rfl | rfl := hop
  · exact go_nested_ends hEE₀ (by omega) hend (Or.inl hi) hEE
  · exact go_nested_ends hEE₀ (by omega) hend (Or.inr (Or.inl hi)) hEE
  · exact go_nested_ends hEE₀ (by omega) hend (Or.inr (Or.inr hi)) hEE

/-- A nonempty all-live stack has a live head (the shape
`normVApply_strict` consumes). -/
theorem NormLive.head {s : NormVSt} (hne : s.cs ≠ [])
    (hlive : ∀ fr ∈ s.cs, fr.un = false) :
    (s.cs.head?).map NormTFrame.un = some false := by
  cases hcs : s.cs with
  | nil => exact (hne hcs).elim
  | cons fr frs =>
    rw [List.head?_cons, Option.map_some']
    simpa using hlive fr (hcs.symm ▸ List.mem_cons_self fr frs)

/-- The state reached one instruction later is unique: it is the
`normVStep` outcome. -/
theorem normVRun_next_state {C : NormVCtx} {f : NormFunc} {pc : Nat}
    {i : NormInstr} {s s' s₁ : NormVSt}
    (hi : f.body.get? pc = some i)
    (hvr : normVRun C (normVInit f) (f.body.take pc) = some s)
    (hvs : normVStep C i s = some s₁)
    (hvr' : normVRun C (normVInit f) (f.body.take (pc + 1)) = some s') :
    s' = s₁ := by
  rw [normVRun_take_succ _ _ _ _ _ hi, hvr, Option.some_bind] at hvr'
  exact Option.some.inj (hvr'.symm.trans hvs)

/-! ## Flat signature arms -/

/-- On a `normInstrSig` instruction, `normVStep` is `normVApply`.  The
explicitly-matched arms all have `normInstrSig i = none`, so `hsig`
discharges them. -/
theorem normVStep_flat (C : NormVCtx) (i : NormInstr) (s : NormVSt)
    {ps rs : List NormTy} (hsig : normInstrSig i = some (ps, rs)) :
    normVStep C i s =
      (normVApply s.os s.cs ps rs).map fun os' => ⟨os', s.cs⟩ := by
  cases i <;> simp only [normInstrSig] at hsig <;>
    first
      | exact Option.noConfusion hsig
      | (obtain ⟨rfl, rfl⟩ :=
           (Prod.mk.injEq ..).mp (Option.some.inj hsig); rfl)

/-- Machine-side inversion: a `normBinOp32` step has two i32 operands and
replaces them by `F a b`. -/
theorem normBinOp32_step_inv {st st' : NormState}
    (F : UInt32 → UInt32 → NormVal)
    (h : normBinOp32 st F = .step st') :
    ∃ a b rest, st.operandStack = .i32 b :: .i32 a :: rest ∧
      st' = { st with pc := st.pc + 1, operandStack := F a b :: rest } := by
  unfold normBinOp32 at h
  split at h
  · rename_i b a rest hOS
    exact ⟨a, b, rest, hOS, (NormStepResult.step.inj h).symm⟩
  · exact NormStepResult.noConfusion h

/-- Machine-side inversion: a `normBinOp64` step has two i64 operands and
replaces them by `F a b`'s value. -/
theorem normBinOp64_step_inv {st st' : NormState}
    (F : UInt64 → UInt64 → Option NormVal)
    (h : normBinOp64 st F = .step st') :
    ∃ a b rest v, st.operandStack = .i64 b :: .i64 a :: rest ∧
      F a b = some v ∧
      st' = { st with pc := st.pc + 1, operandStack := v :: rest } := by
  unfold normBinOp64 at h
  split at h
  · rename_i b a rest hOS
    split at h
    · rename_i v hF
      exact ⟨a, b, rest, v, hOS, hF, (NormStepResult.step.inj h).symm⟩
    · exact NormStepResult.noConfusion h
  · exact NormStepResult.noConfusion h

/-- Machine-side inversion for `normCmpOp32`. -/
theorem normCmpOp32_step_inv {st st' : NormState} (op : NormCmpOp)
    (h : normCmpOp32 st op = .step st') :
    ∃ a b rest, st.operandStack = .i32 b :: .i32 a :: rest ∧
      st' = ({ st with pc := st.pc + 1, operandStack := .i32 (cmpU32 op a b) :: rest }) := by
  unfold normCmpOp32 at h
  split at h
  · rename_i b a rest hOS
    exact ⟨a, b, rest, hOS, (NormStepResult.step.inj h).symm⟩
  · exact NormStepResult.noConfusion h

/-- Machine-side inversion for `normCmpOp64`. -/
theorem normCmpOp64_step_inv {st st' : NormState} (op : NormCmpOp)
    (h : normCmpOp64 st op = .step st') :
    ∃ a b rest, st.operandStack = .i64 b :: .i64 a :: rest ∧
      st' = ({ st with pc := st.pc + 1, operandStack := .i32 (cmpU64 op a b) :: rest }) := by
  unfold normCmpOp64 at h
  split at h
  · rename_i b a rest hOS
    exact ⟨a, b, rest, hOS, (NormStepResult.step.inj h).symm⟩
  · exact NormStepResult.noConfusion h

/-- Machine-side inversion for `normDivRem64` (the `.trap` arm is
refuted by the `.step` hypothesis). -/
theorem normDivRem64_step_inv {st st' : NormState}
    (F : UInt64 → UInt64 → Except NormTrapReason UInt64)
    (h : normDivRem64 st F = .step st') :
    ∃ a b rest v, st.operandStack = .i64 b :: .i64 a :: rest ∧
      F a b = .ok v ∧
      st' = ({ st with pc := st.pc + 1, operandStack := .i64 v :: rest }) := by
  unfold normDivRem64 at h
  split at h
  · rename_i b a rest hOS
    split at h
    · rename_i v hF
      exact ⟨a, b, rest, v, hOS, hF, (NormStepResult.step.inj h).symm⟩
    · rename_i r hF
      exact NormStepResult.noConfusion h
  · exact NormStepResult.noConfusion h

/-- Machine-side inversion for `normUnOp32` (the `i32Eqz` arm). -/
theorem normUnOp32_step_inv {st st' : NormState}
    (F : UInt32 → NormVal)
    (h : normUnOp32 st F = .step st') :
    ∃ a rest, st.operandStack = .i32 a :: rest ∧
      st' = { st with pc := st.pc + 1, operandStack := F a :: rest } := by
  unfold normUnOp32 at h
  split at h
  · rename_i a rest hOS
    exact ⟨a, rest, hOS, (NormStepResult.step.inj h).symm⟩
  · exact NormStepResult.noConfusion h

/-- Machine-side inversion for `normUnOp64` (the `i64Eqz` arm — the
result is `i32`, matching `normInstrSig`). -/
theorem normUnOp64_step_inv {st st' : NormState}
    (F : UInt64 → NormVal)
    (h : normUnOp64 st F = .step st') :
    ∃ a rest, st.operandStack = .i64 a :: rest ∧
      st' = { st with pc := st.pc + 1, operandStack := F a :: rest } := by
  unfold normUnOp64 at h
  split at h
  · rename_i a rest hOS
    exact ⟨a, rest, hOS, (NormStepResult.step.inj h).symm⟩
  · exact NormStepResult.noConfusion h

/-- Machine-side inversion for `normLoad`. -/
theorem normLoad_step_inv {st st' : NormState} (a : NormMemArg) (n : Nat)
    (mk : List UInt8 → NormVal)
    (h : normLoad st a n mk = .step st') :
    ∃ addr rest bs, st.operandStack = .i32 addr :: rest ∧
      memLoadBytes st.linearMemory (addr.toNat + a.offset) n = some bs ∧
      st' = ({ st with pc := st.pc + 1, operandStack := mk bs :: rest }) := by
  unfold normLoad at h
  split at h
  · rename_i addr rest hOS
    dsimp only [] at h
    split at h
    · rename_i bs hm
      exact ⟨addr, rest, bs, hOS, hm, (NormStepResult.step.inj h).symm⟩
    · exact NormStepResult.noConfusion h
  · exact NormStepResult.noConfusion h

/-- Machine-side inversion for `normStore`. -/
theorem normStore_step_inv {st st' : NormState} (a : NormMemArg)
    (bsOf : NormVal → Option (List UInt8))
    (h : normStore st a bsOf = .step st') :
    ∃ v addr rest bs m', st.operandStack = v :: .i32 addr :: rest ∧
      bsOf v = some bs ∧
      memStoreBytes st.linearMemory (addr.toNat + a.offset) bs = some m' ∧
      st' = ({ st with pc := st.pc + 1, operandStack := rest, linearMemory := m' }) := by
  unfold normStore at h
  split at h
  · rename_i v addr rest hOS
    split at h
    · exact NormStepResult.noConfusion h
    · rename_i bs hb
      split at h
      · rename_i m' hm
        exact ⟨v, addr, rest, bs, m', hOS, hb, hm,
          (NormStepResult.step.inj h).symm⟩
      · exact NormStepResult.noConfusion h
  · exact NormStepResult.noConfusion h

/-- `memStoreBytes` preserves the memory length (the write is in-bounds). -/
theorem memStoreBytes_length {m m' : NormMemory} {ea : Nat}
    {bs : List UInt8}
    (h : memStoreBytes m ea bs = some m') :
    m'.bytes.length = m.bytes.length := by
  unfold memStoreBytes at h
  split at h
  · rename_i hle
    have h' := Option.some.inj h
    rw [← h']
    show ((m.bytes.take ea ++ bs ++ m.bytes.drop (ea + bs.length))).length
        = m.bytes.length
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  · exact Option.noConfusion h

/-- Tail assembly for all "same-frame" arms: pc+1 with new operand stack
(and optionally locals/memory), control and call stacks untouched, and the
validator keeps `s.cs`. -/
theorem normInv_step' {st : NormState} {f : NormFunc} {s s₁ : NormVSt}
    {i : NormInstr} {newos newloc : List NormVal} {newmem : NormMemory}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some i)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) i s = some s₁)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hos' : s₁.os = newos.map NormVal.ty)
    (hcs' : s₁.cs = s.cs)
    (hloc' : newloc.map NormVal.ty = f.params ++ f.locals)
    (hmem' : newmem.bytes.length = st.module.memPages * NormWasmPage) :
    NormInv ({ st with pc := st.pc + 1, operandStack := newos, locals := newloc, linearMemory := newmem }) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨f, hget, ⟨s₁, ?_, hos', ?_⟩, hloc', hfr, hmem'⟩
    · exact normVRun_next hi hvr hvs
    · show NormLabelsCorrespond f.body st.controlStack s₁.cs
      rw [hcs']; exact hcorr
  · intro f' s' hget' hvr'
    dsimp only [] at hget' hvr'
    have hff : f = f' := Option.some.inj (hget.symm.trans hget')
    subst hff
    rw [normVRun_take_succ _ _ _ _ _ hi, hvr, Option.some_bind] at hvr'
    have hs' : s' = s₁ := Option.some.inj (hvr'.symm.trans hvs)
    intro fr hm
    rw [hs', hcs'] at hm
    exact hlive fr hm
  · intro f' s' hget' hvr'
    dsimp only [] at hget' hvr'
    have hff : f = f' := Option.some.inj (hget.symm.trans hget')
    subst hff
    rw [normVRun_take_succ _ _ _ _ _ hi, hvr, Option.some_bind] at hvr'
    have hs' : s' = s₁ := Option.some.inj (hvr'.symm.trans hvs)
    subst hs'
    have hinner := hhist f s hget hvr
    have hne : i ≠ .endI := by
      intro hc
      subst hc
      have hvs₂ := hvs
      simp only [normVStep] at hvs₂
      cases hs : s.cs with
      | nil =>
        rw [hs] at hvs₂
        simp only [] at hvs₂
        exact Option.noConfusion hvs₂
      | cons f₀ rest =>
        rw [hs] at hvs₂ hcs'
        simp only [] at hvs₂
        split at hvs₂
        · exact Option.noConfusion hvs₂
        · obtain ⟨os', hfchk, hs₁⟩ := map_some_inv hvs₂
          have hlen : s'.cs.length = rest.length :=
            congrArg List.length (congrArg NormVSt.cs hs₁.symm)
          rw [hcs', List.length_cons] at hlen
          exact Nat.ne_of_lt (Nat.lt_succ_self _) hlen.symm
    exact NormHistInner.mono hinner
      (fun i hi => Nat.lt_trans (hinner.1 i hi) (Nat.lt_succ_self _))
      (hpend_succ hcorr hinner hi hne) hcs'

/-- Generic flat-signature preservation over the common record-update
shape: pc+1, operand stack `vals ++ rest` where `pops ++ rest` was the old
stack typed `ps ++ tl`, plus optional locals/memory fields (pass
`st.locals`/`st.linearMemory` for the unchanged cases). -/
theorem preserve_flat {st : NormState} {f : NormFunc} {s s₁ : NormVSt}
    {i : NormInstr} {ps rs : List NormTy}
    {pops vals rest : List NormVal} {newloc : List NormVal}
    {newmem : NormMemory}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some i)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) i s = some s₁)
    (hsig : normInstrSig i = some (ps, rs))
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstack : st.operandStack = pops ++ rest)
    (hpops : pops.map NormVal.ty = ps)
    (hvals : vals.map NormVal.ty = rs)
    (hloc' : newloc.map NormVal.ty = f.params ++ f.locals)
    (hmem' : newmem.bytes.length = st.module.memPages * NormWasmPage) :
    NormInv ({ st with pc := st.pc + 1, operandStack := vals ++ rest, locals := newloc, linearMemory := newmem }) := by
  rw [normVStep_flat _ _ _ hsig, Option.map_eq_some'] at hvs
  obtain ⟨os₁, hvapp, hs₁⟩ := hvs
  have hlen := hcorr.1
  have hne : s.cs ≠ [] := fun e => by
    rw [e, List.length_nil] at hlen; exact Nat.noConfusion hlen
  have hhead := NormLive.head hne hlive
  obtain ⟨tl, hsos, hos₁⟩ := normVApply_strict hhead hvapp
  have htl : rest.map NormVal.ty = tl := by
    have e : st.operandStack.map NormVal.ty = ps ++ tl := by
      rw [← hos]; exact hsos
    rw [hstack, List.map_append, hpops] at e
    exact List.append_inj_right e rfl
  have hvs' : normVStep (NormVCtx.ofModule st.module f) i s =
      some ⟨os₁, s.cs⟩ := by
    rw [normVStep_flat _ _ _ hsig, hvapp, Option.map_some']
  subst hs₁
  exact normInv_step' hget hi hvr hvs' hcorr hfr hlive hhist
    (by show os₁ = (vals ++ rest).map NormVal.ty
        rw [hos₁, List.map_append, hvals, htl]) rfl hloc' hmem'

/-- All `normBinOp32` arms (`i32Add/Sub/Mul/Bit/Shift`): `F`'s result is
always i32. -/
theorem preserve_binOp32 {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt} {i : NormInstr} (F : UInt32 → UInt32 → NormVal)
    (hFty : ∀ a b, (F a b).ty = .i32Ty)
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some i)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) i s = some s₁)
    (hsig : normInstrSig i = some ([.i32Ty, .i32Ty], [.i32Ty]))
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normBinOp32 st F = .step st') :
    NormInv st' := by
  obtain ⟨a, b, rest, hOS, hst⟩ := normBinOp32_step_inv F hstep
  subst hst
  refine preserve_flat (pops := [.i32 b, .i32 a]) (rest := rest)
    (vals := [F a b]) hget hi hvr hvs hsig hos hcorr hfr hlive hhist
    hOS rfl ?_ hloc hmem
  show ([F a b] : List NormVal).map NormVal.ty = [.i32Ty]
  simp [hFty]

/-- All `normBinOp64` arms with i64 result (`i64Add/Sub/Mul/Bit/Shift`). -/
theorem preserve_binOp64 {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt} {i : NormInstr}
    (F : UInt64 → UInt64 → Option NormVal)
    (hFty : ∀ a b v, F a b = some v → v.ty = .i64Ty)
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some i)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) i s = some s₁)
    (hsig : normInstrSig i = some ([.i64Ty, .i64Ty], [.i64Ty]))
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normBinOp64 st F = .step st') :
    NormInv st' := by
  obtain ⟨a, b, rest, v, hOS, hF, hst⟩ := normBinOp64_step_inv F hstep
  subst hst
  refine preserve_flat (pops := [.i64 b, .i64 a]) (rest := rest)
    (vals := [v]) hget hi hvr hvs hsig hos hcorr hfr hlive hhist
    hOS rfl ?_ hloc hmem
  show ([v] : List NormVal).map NormVal.ty = [.i64Ty]
  simp [hFty a b v hF]

/-- All `normCmpOp32` arms (`i32Cmp`). -/
theorem preserve_cmpOp32 {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt} {i : NormInstr} (op : NormCmpOp)
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some i)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) i s = some s₁)
    (hsig : normInstrSig i = some ([.i32Ty, .i32Ty], [.i32Ty]))
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normCmpOp32 st op = .step st') :
    NormInv st' := by
  obtain ⟨a, b, rest, hOS, hst⟩ := normCmpOp32_step_inv op hstep
  subst hst
  exact preserve_flat (pops := [.i32 b, .i32 a]) (rest := rest)
    (vals := [.i32 (cmpU32 op a b)]) hget hi hvr hvs hsig hos hcorr
    hfr hlive hhist hOS rfl rfl hloc hmem

/-- All `normCmpOp64` arms (`i64Cmp`). -/
theorem preserve_cmpOp64 {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt} {i : NormInstr} (op : NormCmpOp)
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some i)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) i s = some s₁)
    (hsig : normInstrSig i = some ([.i64Ty, .i64Ty], [.i32Ty]))
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normCmpOp64 st op = .step st') :
    NormInv st' := by
  obtain ⟨a, b, rest, hOS, hst⟩ := normCmpOp64_step_inv op hstep
  subst hst
  exact preserve_flat (pops := [.i64 b, .i64 a]) (rest := rest)
    (vals := [.i32 (cmpU64 op a b)]) hget hi hvr hvs hsig hos hcorr
    hfr hlive hhist hOS rfl rfl hloc hmem

/-- The `normDivRem64` arms (`i64DivS`/`i64RemS`); `.trap` is excluded by
the `.step` hypothesis, so a stepped division preserves `NormInv`. -/
theorem preserve_divRem64 {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt} {i : NormInstr}
    (F : UInt64 → UInt64 → Except NormTrapReason UInt64)
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some i)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) i s = some s₁)
    (hsig : normInstrSig i = some ([.i64Ty, .i64Ty], [.i64Ty]))
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normDivRem64 st F = .step st') :
    NormInv st' := by
  obtain ⟨a, b, rest, v, hOS, hF, hst⟩ := normDivRem64_step_inv F hstep
  subst hst
  exact preserve_flat (pops := [.i64 b, .i64 a]) (rest := rest)
    (vals := [.i64 v]) hget hi hvr hvs hsig hos hcorr hfr hlive hhist
    hOS rfl rfl hloc hmem

/-- The `normUnOp32` arms (`i32Eqz`): unary i32 pop, `F`'s result typed
`rt` per the sig. -/
theorem preserve_unOp32 {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt} {i : NormInstr} {rt : NormTy} (F : UInt32 → NormVal)
    (hFty : ∀ a, (F a).ty = rt)
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some i)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) i s = some s₁)
    (hsig : normInstrSig i = some ([.i32Ty], [rt]))
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normUnOp32 st F = .step st') :
    NormInv st' := by
  obtain ⟨a, rest, hOS, hst⟩ := normUnOp32_step_inv F hstep
  subst hst
  refine preserve_flat (pops := [.i32 a]) (rest := rest)
    (vals := [F a]) hget hi hvr hvs hsig hos hcorr hfr hlive hhist
    hOS rfl ?_ hloc hmem
  show ([F a] : List NormVal).map NormVal.ty = [rt]
  simp [hFty]

/-- The `normUnOp64` arms (`i64Eqz`): unary i64 pop, result typed `rt`
(`i64Eqz` produces `.i32`). -/
theorem preserve_unOp64 {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt} {i : NormInstr} {rt : NormTy} (F : UInt64 → NormVal)
    (hFty : ∀ a, (F a).ty = rt)
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some i)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) i s = some s₁)
    (hsig : normInstrSig i = some ([.i64Ty], [rt]))
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normUnOp64 st F = .step st') :
    NormInv st' := by
  obtain ⟨a, rest, hOS, hst⟩ := normUnOp64_step_inv F hstep
  subst hst
  refine preserve_flat (pops := [.i64 a]) (rest := rest)
    (vals := [F a]) hget hi hvr hvs hsig hos hcorr hfr hlive hhist
    hOS rfl ?_ hloc hmem
  show ([F a] : List NormVal).map NormVal.ty = [rt]
  simp [hFty]

/-- Constant-push arms (`i32Const`/`i64Const`) and `memorySize`: the
machine pushes one value and nothing else changes. -/
theorem preserve_push {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt} {i : NormInstr} {ps rs : List NormTy}
    (v : NormVal)
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some i)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) i s = some s₁)
    (hsig : normInstrSig i = some (ps, rs))
    (hps : ps = []) (hrs : rs = [v.ty])
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : st' = ({ st with pc := st.pc + 1, operandStack := v :: st.operandStack })) :
    NormInv st' := by
  subst hstep
  refine preserve_flat (pops := []) (rest := st.operandStack)
    (vals := [v]) hget hi hvr hvs hsig hos
    hcorr hfr hlive hhist rfl ?_ ?_ hloc hmem
  · rw [hps]; rfl
  · rw [hrs]; rfl

/-- The `normLoad` arms (`i32Load`/`i64Load`/`i32Load8U`): a stepped load
leaves memory untouched. -/
theorem preserve_load {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt} {i : NormInstr} {rt : NormTy}
    (a : NormMemArg) (n : Nat) (mk : List UInt8 → NormVal)
    (hmkty : ∀ bs, (mk bs).ty = rt)
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some i)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) i s = some s₁)
    (hsig : normInstrSig i = some ([.i32Ty], [rt]))
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normLoad st a n mk = .step st') :
    NormInv st' := by
  obtain ⟨addr, rest, bs, hOS, hm, hst⟩ := normLoad_step_inv a n mk hstep
  subst hst
  refine preserve_flat (pops := [.i32 addr]) (rest := rest)
    (vals := [mk bs]) hget hi hvr hvs hsig hos hcorr hfr hlive hhist
    hOS rfl ?_ hloc hmem
  show ([mk bs] : List NormVal).map NormVal.ty = [rt]
  simp [hmkty]

/-- The `normStore` arms (`i32Store`/`i64Store`/`i32Store8`): the value's
type is fixed by `bsOf` succeeding, and `memStoreBytes` preserves the
memory length. -/
theorem preserve_store {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt} {i : NormInstr} {vt : NormTy}
    (a : NormMemArg) (bsOf : NormVal → Option (List UInt8))
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some i)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) i s = some s₁)
    (hsig : normInstrSig i = some ([vt, .i32Ty], []))
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hvty : ∀ v bs, bsOf v = some bs → v.ty = vt)
    (hstep : normStore st a bsOf = .step st') :
    NormInv st' := by
  obtain ⟨v, addr, rest, bs, m', hOS, hbs, hm, hst⟩ :=
    normStore_step_inv a bsOf hstep
  subst hst
  refine preserve_flat (pops := [v, .i32 addr]) (rest := rest)
    (vals := []) (newmem := m') hget hi hvr hvs hsig hos hcorr
    hfr hlive hhist hOS ?_ rfl hloc ((memStoreBytes_length hm).symm ▸ hmem)
  show v.ty :: NormTy.i32Ty :: [] = [vt, .i32Ty]
  rw [hvty v bs hbs]

/-! ## Locals and stack-shape arms -/

/-- `normLocalsSet` is `List.set` when it succeeds. -/
theorem normLocalsSet_eq_set {v : NormVal} {ls : List NormVal} {i : Nat}
    {ls' : List NormVal} (h : normLocalsSet ls i v = some ls') :
    ls' = ls.set i v := by
  rw [normLocalsSet.eq_def] at h
  generalize hfu : ls.length = fuel at h
  clear hfu
  induction fuel generalizing ls i ls' with
  | zero => exact Option.noConfusion h
  | succ fuel ih =>
    cases ls with
    | nil => exact Option.noConfusion h
    | cons hd tl =>
      cases i with
      | zero =>
        have e := Option.some.inj h
        subst e
        rfl
      | succ j =>
        cases hg : normLocalsSet.go v fuel tl j with
        | none =>
          have e : (normLocalsSet.go v fuel tl j).map (hd :: ·) =
              some ls' := h
          rw [hg] at e
          exact Option.noConfusion e
        | some l'' =>
          have e : (normLocalsSet.go v fuel tl j).map (hd :: ·) =
              some ls' := h
          rw [hg, Option.map_some'] at e
          have e' := Option.some.inj e
          subst e'
          rw [ih hg]
          rfl

/-- Setting a slot to the value it already holds is the identity. -/
theorem set_self_of_get? {α : Type _} {l : List α} {i : Nat} {a : α}
    (h : l.get? i = some a) : l.set i a = l := by
  induction l generalizing i with
  | nil => exact Option.noConfusion h
  | cons hd tl ih =>
    cases i with
    | zero =>
      rw [← Option.some.inj h]
      rfl
    | succ j =>
      have h' : tl.get? j = some a := h
      show hd :: tl.set j a = hd :: tl
      rw [ih h']

/-- `map` commutes with `get?` for machine values. -/
theorem map_ty_get? {ls : List NormVal} {i : Nat} {v : NormVal}
    (hg : ls.get? i = some v) :
    (ls.map NormVal.ty).get? i = some v.ty := by
  rw [List.get?_eq_getElem?] at hg ⊢
  rw [List.getElem?_map, hg]
  rfl

/-- `normLocalsSet` preserves the local type list when the replacement
has the slot's declared type. -/
theorem normLocalsSet_map_ty {ls ls' : List NormVal} {i : Nat} {v : NormVal}
    (h : normLocalsSet ls i v = some ls')
    (hty : (ls.map NormVal.ty).get? i = some v.ty) :
    ls'.map NormVal.ty = ls.map NormVal.ty := by
  rw [normLocalsSet_eq_set h, List.map_set]
  exact set_self_of_get? hty

/-- A nonempty validator control stack with the correspondence invariant
has a live head frame. -/
theorem cs_live_cons {s : NormVSt} {st : NormState} {body : List NormInstr}
    (hcorr : NormLabelsCorrespond body st.controlStack s.cs)
    (hlive : ∀ fr ∈ s.cs, fr.un = false) :
    ∃ fr frs, s.cs = fr :: frs ∧ fr.un = false := by
  cases hcs : s.cs with
  | nil =>
    obtain ⟨hlen, -, -⟩ := hcorr
    rw [hcs, List.length_nil] at hlen
    exact Nat.noConfusion hlen
  | cons fr frs =>
    exact ⟨fr, frs, rfl, hlive fr (hcs.symm ▸ List.mem_cons_self fr frs)⟩

/-- `localGet`: the machine pushes the local's value; the validator pushes
`C.locals[i]`, equal to the value's type by the local-typing invariant. -/
theorem preserve_localGet {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt} {i : Nat}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some (.localGet i))
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (_hvs : normVStep (NormVCtx.ofModule st.module f) (.localGet i) s = some s₁)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normStepInstr st (.localGet i) = .step st') :
    NormInv st' := by
  simp only [normStepInstr] at hstep
  split at hstep
  · rename_i v hv
    have hst : st' = { st with pc := st.pc + 1, operandStack := v :: st.operandStack } :=
      (NormStepResult.step.inj hstep).symm
    subst hst
    have hvs0 := _hvs
    simp only [normVStep] at _hvs
    rw [Option.map_eq_some'] at _hvs
    obtain ⟨lt, hcl, hs₁⟩ := _hvs
    have hclv : (NormVCtx.ofModule st.module f).locals.get? i =
        some v.ty := by
      show (f.params ++ f.locals).get? i = some v.ty
      rw [← hloc]
      exact map_ty_get? hv
    have hlt : lt = v.ty :=
      Option.some.inj (hcl.symm.trans hclv)
    have hs₁' : s₁ = ⟨lt :: s.os, s.cs⟩ := hs₁.symm
    subst hs₁'
    exact normInv_step' hget hi hvr hvs0 hcorr hfr hlive hhist
      (by rw [hlt]; show v.ty :: s.os = (v :: st.operandStack).map NormVal.ty
          rw [List.map_cons, hos]) rfl hloc hmem
  · exact NormStepResult.noConfusion hstep

/-- `localSet`: the value's type equals the slot type (validator pop), and
`normLocalsSet` then preserves the local type list. -/
theorem preserve_localSet {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt} {i : Nat}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some (.localSet i))
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) (.localSet i) s = some s₁)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normStepInstr st (.localSet i) = .step st') :
    NormInv st' := by
  obtain ⟨fr, frs, hcs, hfrun⟩ := cs_live_cons hcorr hlive
  simp only [normStepInstr] at hstep
  split at hstep
  · rename_i v rest hOS
    split at hstep
    · rename_i ls' hls
      have hst : st' = { st with pc := st.pc + 1, operandStack := rest, locals := ls' } :=
        (NormStepResult.step.inj hstep).symm
      subst hst
      have hvs0 := hvs
      simp only [normVStep] at hvs
      rw [Option.bind_eq_some] at hvs
      obtain ⟨lt, hcl, hvs⟩ := hvs
      rw [Option.map_eq_some'] at hvs
      obtain ⟨os', hp, hs₁⟩ := hvs
      rw [hcs] at hp
      have hsos : s.os = lt :: os' := normVPop_strict hfrun hp
      have e : lt :: os' = v.ty :: rest.map NormVal.ty := by
        have e := hsos ▸ hos
        rwa [hOS, List.map_cons] at e
      obtain ⟨hltv, hos'rest⟩ := List.cons.inj e
      have hcl' : (st.locals.map NormVal.ty).get? i = some v.ty := by
        have hcl' : (f.params ++ f.locals).get? i = some lt := hcl
        rw [← hloc, hltv] at hcl'
        exact hcl'
      have hloc' : ls'.map NormVal.ty = f.params ++ f.locals := by
        rw [normLocalsSet_map_ty hls hcl']; exact hloc
      have hs₁' : s₁ = ⟨os', s.cs⟩ := hs₁.symm
      subst hs₁'
      exact normInv_step' hget hi hvr hvs0 hcorr hfr hlive hhist
        hos'rest rfl hloc' hmem
    · exact NormStepResult.noConfusion hstep
  · exact NormStepResult.noConfusion hstep

/-- `localTee`: like `localSet` but the value stays on the stack. -/
theorem preserve_localTee {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt} {i : Nat}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some (.localTee i))
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) (.localTee i) s = some s₁)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normStepInstr st (.localTee i) = .step st') :
    NormInv st' := by
  obtain ⟨fr, frs, hcs, hfrun⟩ := cs_live_cons hcorr hlive
  simp only [normStepInstr] at hstep
  split at hstep
  · rename_i v rest hOS
    split at hstep
    · rename_i ls' hls
      have hst : st' = { st with pc := st.pc + 1, operandStack := v :: rest, locals := ls' } :=
        (NormStepResult.step.inj hstep).symm
      subst hst
      have hvs0 := hvs
      simp only [normVStep] at hvs
      rw [Option.bind_eq_some] at hvs
      obtain ⟨lt, hcl, hvs⟩ := hvs
      rw [Option.map_eq_some'] at hvs
      obtain ⟨os', hp, hs₁⟩ := hvs
      rw [hcs] at hp
      have hsos : s.os = lt :: os' := normVPop_strict hfrun hp
      have e : lt :: os' = v.ty :: rest.map NormVal.ty := by
        have e := hsos ▸ hos
        rwa [hOS, List.map_cons] at e
      obtain ⟨hltv, hos'rest⟩ := List.cons.inj e
      have hcl' : (st.locals.map NormVal.ty).get? i = some v.ty := by
        have hcl' : (f.params ++ f.locals).get? i = some lt := hcl
        rw [← hloc, hltv] at hcl'
        exact hcl'
      have hloc' : ls'.map NormVal.ty = f.params ++ f.locals := by
        rw [normLocalsSet_map_ty hls hcl']; exact hloc
      have hs₁' : s₁ = ⟨lt :: os', s.cs⟩ := hs₁.symm
      subst hs₁'
      exact normInv_step' hget hi hvr hvs0 hcorr hfr hlive hhist
        (by show lt :: os' = (v :: rest).map NormVal.ty
            rw [List.map_cons, hltv, hos'rest]) rfl hloc' hmem
    · exact NormStepResult.noConfusion hstep
  · exact NormStepResult.noConfusion hstep

/-- `drop`: both sides pop one operand. -/
theorem preserve_drop {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some .drop)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) .drop s = some s₁)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normStepInstr st .drop = .step st') :
    NormInv st' := by
  obtain ⟨fr, frs, hcs, hfrun⟩ := cs_live_cons hcorr hlive
  simp only [normStepInstr] at hstep
  split at hstep
  · rename_i v rest hOS
    have hst : st' = { st with pc := st.pc + 1, operandStack := rest } :=
      (NormStepResult.step.inj hstep).symm
    subst hst
    have hvs0 := hvs
    simp only [normVStep] at hvs
    rw [hcs] at hvs
    have hvs2 : (normTckAny s.os fr.entry.length fr.un).map
        (fun x => NormVSt.mk x.snd (fr :: frs)) = some s₁ := hvs
    clear hvs
    rw [hfrun, Option.map_eq_some'] at hvs2
    obtain ⟨⟨t?, os'⟩, hany, hs₁⟩ := hvs2
    obtain ⟨t, hsos, -⟩ := normTckAny_strict hany
    have e : t :: os' = v.ty :: rest.map NormVal.ty := by
      have e := hsos ▸ hos
      rwa [hOS, List.map_cons] at e
    obtain ⟨-, hos'rest⟩ := List.cons.inj e
    have hs₁' : s₁ = ⟨os', fr :: frs⟩ := hs₁.symm
    subst hs₁'
    exact normInv_step' hget hi hvr hvs0 hcorr hfr hlive hhist
      hos'rest hcs.symm hloc hmem
  · exact NormStepResult.noConfusion hstep

/-- `select` (machine keeps `a` iff `c ≠ 0`): the validator's two
any-pops force both candidate types equal. -/
theorem preserve_select {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some .select)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) .select s = some s₁)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normStepInstr st .select = .step st') :
    NormInv st' := by
  obtain ⟨fr, frs, hcs, hfrun⟩ := cs_live_cons hcorr hlive
  simp only [normStepInstr] at hstep
  split at hstep
  · rename_i c b a rest hOS
    have hst : st' = { st with pc := st.pc + 1, operandStack := (if c != 0 then a else b) :: rest } :=
      (NormStepResult.step.inj hstep).symm
    subst hst
    have hvs0 := hvs
    simp only [normVStep] at hvs
    rw [Option.bind_eq_some] at hvs
    obtain ⟨os', hp1, hvs⟩ := hvs
    rw [hcs] at hvs
    have hvs2 : (normTckAny os' fr.entry.length fr.un).bind
        (fun x => match x.fst with
          | none => some (NormVSt.mk x.snd (fr :: frs))
          | some t => (normVPop x.snd (fr :: frs) t).map fun os''' =>
              NormVSt.mk (t :: os''') (fr :: frs)) = some s₁ := hvs
    clear hvs
    rw [hfrun, Option.bind_eq_some] at hvs2
    obtain ⟨⟨t?, os''⟩, hany, hvs2⟩ := hvs2
    obtain ⟨t, hos'T, htsome⟩ := normTckAny_strict hany
    subst htsome
    have hvs3 : (normVPop os'' (fr :: frs) t).map
        (fun os''' => NormVSt.mk (t :: os''') (fr :: frs)) =
        some s₁ := hvs2
    rw [Option.map_eq_some'] at hvs3
    obtain ⟨os''', hp2, hs₁⟩ := hvs3
    rw [hcs] at hp1
    have hs1 : s.os = .i32Ty :: os' := normVPop_strict hfrun hp1
    have hs2 : os'' = t :: os''' := normVPop_strict hfrun hp2
    have e : .i32Ty :: os' = .i32Ty :: b.ty :: a.ty :: rest.map NormVal.ty := by
      have e := hs1 ▸ hos
      rwa [hOS, List.map_cons, List.map_cons, List.map_cons] at e
    obtain ⟨-, e⟩ := List.cons.inj e
    have e' : t :: os'' = b.ty :: a.ty :: rest.map NormVal.ty := by
      rwa [hos'T] at e
    obtain ⟨hbt, e''⟩ := List.cons.inj e'
    have e''' : t :: os''' = a.ty :: rest.map NormVal.ty := by
      rwa [hs2] at e''
    obtain ⟨hat, hos'''⟩ := List.cons.inj e'''
    have hty : (if c != 0 then a else b).ty = t := by
      by_cases hc : (c != 0) = true
      · rw [if_pos hc]; exact hat.symm
      · rw [if_neg hc]; exact hbt.symm
    have hs₁' : s₁ = ⟨t :: os''', fr :: frs⟩ := hs₁.symm
    subst hs₁'
    exact normInv_step' hget hi hvr hvs0 hcorr hfr hlive hhist
      (by show t :: os''' = ((if c != 0 then a else b) :: rest).map NormVal.ty
          rw [List.map_cons, hty, hos''']) hcs.symm hloc hmem
  · exact NormStepResult.noConfusion hstep

/-! ## Unary conversion arms (unary machine since batch 23, W-WX002-M3) -/

/-- `i32WrapI64`: unary pop of `.i64`, push `.i32`. -/
theorem preserve_i32WrapI64 {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some .i32WrapI64)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) .i32WrapI64 s = some s₁)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normStepInstr st .i32WrapI64 = .step st') :
    NormInv st' := by
  simp only [normStepInstr] at hstep
  split at hstep
  · rename_i a rest hOS
    have hst : st' = { st with pc := st.pc + 1, operandStack := .i32 (UInt32.ofNat (a.toNat % 4294967296)) :: rest } :=
      (NormStepResult.step.inj hstep).symm
    subst hst
    exact preserve_flat (pops := [.i64 a]) (rest := rest)
      (vals := [.i32 (UInt32.ofNat (a.toNat % 4294967296))])
      hget hi hvr hvs rfl hos hcorr hfr hlive hhist hOS rfl rfl hloc hmem
  · exact NormStepResult.noConfusion hstep

/-- `i64ExtendI32U`: unary pop of `.i32`, push `.i64`. -/
theorem preserve_i64ExtendI32U {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some .i64ExtendI32U)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) .i64ExtendI32U s =
            some s₁)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normStepInstr st .i64ExtendI32U = .step st') :
    NormInv st' := by
  simp only [normStepInstr] at hstep
  split at hstep
  · rename_i a rest hOS
    have hst : st' = { st with pc := st.pc + 1, operandStack := .i64 (UInt64.ofNat a.toNat) :: rest } :=
      (NormStepResult.step.inj hstep).symm
    subst hst
    exact preserve_flat (pops := [.i32 a]) (rest := rest)
      (vals := [.i64 (UInt64.ofNat a.toNat)])
      hget hi hvr hvs rfl hos hcorr hfr hlive hhist hOS rfl rfl hloc hmem
  · exact NormStepResult.noConfusion hstep

/-- `i64ExtendI32S`: unary pop of `.i32`, push `.i64`. -/
theorem preserve_i64ExtendI32S {st st' : NormState} {f : NormFunc}
    {s s₁ : NormVSt}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some .i64ExtendI32S)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) .i64ExtendI32S s =
            some s₁)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normStepInstr st .i64ExtendI32S = .step st') :
    NormInv st' := by
  simp only [normStepInstr] at hstep
  split at hstep
  · rename_i a rest hOS
    have hst : st' = { st with pc := st.pc + 1, operandStack := .i64 (sintToU64 (u32ToSInt a)) :: rest } :=
      (NormStepResult.step.inj hstep).symm
    subst hst
    exact preserve_flat (pops := [.i32 a]) (rest := rest)
      (vals := [.i64 (sintToU64 (u32ToSInt a))])
      hget hi hvr hvs rfl hos hcorr hfr hlive hhist hOS rfl rfl hloc hmem
  · exact NormStepResult.noConfusion hstep

/-! ## Structured arms -/

/-- Non-`fn` frames keep `rt = none` through one `vstep` (frames are born
with `rt = none`; `elseE` inherits an `ift` frame's — already `none`;
`normVBrk` preserves `rt`; the cs-preserving arms keep it).  Needed by
`endI`/`normVBrk` where the popped frame's `f.rt.toList ++ os'` must
reduce to `os'`. -/
theorem normVStep_rt_none {C : NormVCtx} {i : NormInstr} {s s' : NormVSt}
    (hvs : normVStep C i s = some s')
    (hrt : ∀ fr ∈ s.cs, fr.tag ≠ .fn → fr.rt = none) :
    ∀ fr ∈ s'.cs, fr.tag ≠ .fn → fr.rt = none := by
  intro fr hm hf
  have hbrk : ∀ {lrt : Option NormTy} {s₁ : NormVSt},
      normVBrk s lrt = some s₁ →
      ∀ fr ∈ s₁.cs, fr.tag ≠ .fn → fr.rt = none := by
    intro lrt s₁ hb g hg hgf
    simp only [normVBrk] at hb
    cases hcs : s.cs with
    | nil => rw [hcs] at hb; exact Option.noConfusion hb
    | cons h rest =>
      rw [hcs] at hb
      obtain ⟨os', -, hs⟩ := Option.bind_eq_some.1 hb
      have hs' : s₁ = ⟨os'.take h.entry.length,
          ⟨h.tag, h.rt, h.entry, true⟩ :: rest⟩ := (Option.some.inj hs).symm
      subst hs'
      cases hg with
      | head => exact hrt h (hcs ▸ List.mem_cons_self h rest) hgf
      | tail _ hg => exact hrt _ (hcs ▸ List.mem_cons_of_mem _ hg) hgf
  cases i with
  | block =>
    simp only [normVStep, Option.some.injEq] at hvs
    subst hvs
    cases hm with
    | head => rfl
    | tail _ hm => exact hrt _ hm hf
  | loop =>
    simp only [normVStep, Option.some.injEq] at hvs
    subst hvs
    cases hm with
    | head => rfl
    | tail _ hm => exact hrt _ hm hf
  | ifE =>
    simp only [normVStep, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs
    cases hm with
    | head => rfl
    | tail _ hm => exact hrt _ hm hf
  | elseE =>
    simp only [normVStep] at hvs
    split at hvs
    · rename_i f' rest hcs
      split at hvs
      · rename_i htag
        simp only [Option.map_eq_some'] at hvs
        obtain ⟨os', -, hs⟩ := hvs
        subst hs
        have hfrt : f'.rt = none := hrt f'
          (hcs ▸ List.mem_cons_self _ _)
          (by rw [htag]; exact fun e => NormTTag.noConfusion e)
        cases hm with
        | head => exact hfrt
        | tail _ hm => exact hrt _ (hcs ▸ List.mem_cons_of_mem _ hm) hf
      · exact Option.noConfusion hvs
    · exact Option.noConfusion hvs
  | endI =>
    simp only [normVStep] at hvs
    split at hvs
    · rename_i f' rest hcs
      split at hvs
      · exact Option.noConfusion hvs
      · rename_i htag
        simp only [Option.map_eq_some'] at hvs
        obtain ⟨os', -, hs⟩ := hvs
        subst hs
        exact hrt _ (hcs ▸ List.mem_cons_of_mem _ hm) hf
    · exact Option.noConfusion hvs
  | br n =>
    simp only [normVStep, normVBr] at hvs
    split at hvs
    · exact Option.noConfusion hvs
    · rename_i tgt rest' hdrop
      split at hvs
      · exact hbrk hvs _ hm hf
      · exact Option.noConfusion hvs
  | brIf n =>
    simp only [normVStep, normVBrIf] at hvs
    split at hvs
    · exact Option.noConfusion hvs
    · rename_i tgt rest' hdrop
      obtain ⟨os', hp1, hrest⟩ := Option.bind_eq_some.1 hvs
      obtain ⟨os'', hm2, hb⟩ := Option.bind_eq_some.1 hrest
      split at hb
      · have hs : s' = { s with os := os'' } := (Option.some.inj hb).symm
        subst hs
        exact hrt _ hm hf
      · exact Option.noConfusion hb
  | call g =>
    simp only [normVStep] at hvs
    split at hvs
    · exact Option.noConfusion hvs
    · rename_i pr
      simp only [Option.map_eq_some'] at hvs
      obtain ⟨os', -, hs⟩ := hvs
      subst hs
      exact hrt _ hm hf
  | «return» =>
    simp only [normVStep] at hvs
    exact hbrk hvs _ hm hf
  | drop =>
    simp only [normVStep] at hvs
    split at hvs
    · rename_i f' rest' hcs
      simp only [Option.map_eq_some'] at hvs
      obtain ⟨x, -, hs⟩ := hvs
      subst hs
      exact hrt _ hm hf
    · exact Option.noConfusion hvs
  | select =>
    simp only [normVStep, Option.bind_eq_some] at hvs
    obtain ⟨os', hp1, hrest⟩ := hvs
    split at hrest
    · rename_i f' rest' hcs
      obtain ⟨p, hany, hrest2⟩ := Option.bind_eq_some.1 hrest
      obtain ⟨t?, os''⟩ := p
      cases t? with
      | none =>
        have hs : s' = ⟨os'', s.cs⟩ := (Option.some.inj hrest2).symm
        subst hs; exact hrt _ hm hf
      | some t =>
        simp only [Option.map_eq_some'] at hrest2
        obtain ⟨os''', -, hs⟩ := hrest2
        subst hs; exact hrt _ hm hf
    · exact Option.noConfusion hrest
  | localGet k =>
    simp only [normVStep, Option.map_eq_some'] at hvs
    obtain ⟨lt, -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | localSet k =>
    simp only [normVStep, Option.bind_eq_some] at hvs
    obtain ⟨lt, -, hrest⟩ := hvs
    simp only [Option.map_eq_some'] at hrest
    obtain ⟨os', -, hs⟩ := hrest
    subst hs; exact hrt _ hm hf
  | localTee k =>
    simp only [normVStep, Option.bind_eq_some] at hvs
    obtain ⟨lt, -, hrest⟩ := hvs
    simp only [Option.map_eq_some'] at hrest
    obtain ⟨os', -, hs⟩ := hrest
    subst hs; exact hrt _ hm hf
  | i32Const v =>
    rw [normVStep_flat _ (.i32Const v) _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i32Eqz =>
    rw [normVStep_flat _ .i32Eqz _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i32Cmp op =>
    rw [normVStep_flat _ (.i32Cmp op) _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i32Add =>
    rw [normVStep_flat _ .i32Add _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i32Sub =>
    rw [normVStep_flat _ .i32Sub _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i32Mul =>
    rw [normVStep_flat _ .i32Mul _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i32Bit op =>
    rw [normVStep_flat _ (.i32Bit op) _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i32Shift op =>
    rw [normVStep_flat _ (.i32Shift op) _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i64Const v =>
    rw [normVStep_flat _ (.i64Const v) _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i64Eqz =>
    rw [normVStep_flat _ .i64Eqz _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i64Cmp op =>
    rw [normVStep_flat _ (.i64Cmp op) _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i64Add =>
    rw [normVStep_flat _ .i64Add _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i64Sub =>
    rw [normVStep_flat _ .i64Sub _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i64Mul =>
    rw [normVStep_flat _ .i64Mul _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i64DivS =>
    rw [normVStep_flat _ .i64DivS _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i64RemS =>
    rw [normVStep_flat _ .i64RemS _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i64Bit op =>
    rw [normVStep_flat _ (.i64Bit op) _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i64Shift op =>
    rw [normVStep_flat _ (.i64Shift op) _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i32WrapI64 =>
    rw [normVStep_flat _ .i32WrapI64 _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i64ExtendI32U =>
    rw [normVStep_flat _ .i64ExtendI32U _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i64ExtendI32S =>
    rw [normVStep_flat _ .i64ExtendI32S _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i32Load a =>
    rw [normVStep_flat _ (.i32Load a) _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i32Load8U a =>
    rw [normVStep_flat _ (.i32Load8U a) _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i64Load a =>
    rw [normVStep_flat _ (.i64Load a) _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i64Load8U a =>
    rw [normVStep_flat _ (.i64Load8U a) _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i32Store a =>
    rw [normVStep_flat _ (.i32Store a) _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i32Store8 a =>
    rw [normVStep_flat _ (.i32Store8 a) _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i64Store a =>
    rw [normVStep_flat _ (.i64Store a) _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | i64Store8 a =>
    rw [normVStep_flat _ (.i64Store8 a) _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf
  | memorySize =>
    rw [normVStep_flat _ .memorySize _ rfl, Option.map_eq_some'] at hvs
    obtain ⟨os', -, hs⟩ := hvs
    subst hs; exact hrt _ hm hf

/-- `rt = none` for non-`fn` frames lifts through a whole validator run. -/
theorem normVRun_rt_none {C : NormVCtx} {s s' : NormVSt} {is : List NormInstr}
    (hrt : ∀ fr ∈ s.cs, fr.tag ≠ .fn → fr.rt = none)
    (h : normVRun C s is = some s') :
    ∀ fr ∈ s'.cs, fr.tag ≠ .fn → fr.rt = none := by
  revert s s' hrt h
  induction is with
  | nil =>
    intro s s' hrt h
    rw [normVRun_nil] at h
    have hs : s' = s := (Option.some.inj h).symm
    subst hs; exact hrt
  | cons i is ih =>
    intro s s' hrt h
    rw [normVRun_cons] at h
    obtain ⟨s₁, h1, h2⟩ := Option.bind_eq_some.1 h
    exact ih (normVStep_rt_none h1 hrt) h2

/-- The initial state's frames trivially satisfy the `rt` property. -/
theorem normVInit_rt_none (f : NormFunc) :
    ∀ fr ∈ (normVInit f).cs, fr.tag ≠ .fn → fr.rt = none := by
  intro fr hm hf
  simp only [normVInit, List.mem_singleton] at hm
  subst hm
  exact absurd rfl hf

/-- Assembler for steps that change the control stack at `pc + 1`:
`block`/`loop`/`ifE` push, `endI` pops, `brIf` fallthrough keeps. -/
theorem normInv_step_cs {st : NormState} {f : NormFunc} {s s₁ : NormVSt}
    {i : NormInstr} {newos : List NormVal} {newcs : List NormLabel}
    {newloc : List NormVal} {newmem : NormMemory}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some i)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) i s = some s₁)
    (hcorr' : NormLabelsCorrespond f.body newcs s₁.cs)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hlive' : ∀ fr ∈ s₁.cs, fr.un = false)
    (hhist' : NormHistInner (NormVCtx.ofModule st.module f) f s₁
        (st.pc + 1) newcs)
    (hos' : s₁.os = newos.map NormVal.ty)
    (hloc' : newloc.map NormVal.ty = f.params ++ f.locals)
    (hmem' : newmem.bytes.length = st.module.memPages * NormWasmPage) :
    NormInv ({ st with pc := st.pc + 1, operandStack := newos, controlStack := newcs, locals := newloc, linearMemory := newmem }) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨f, hget, ⟨s₁, normVRun_next hi hvr hvs, hos', hcorr'⟩,
      hloc', hfr, hmem'⟩
  · intro f' s' hget' hvr'
    dsimp only [] at hget' hvr'
    have hff : f = f' := Option.some.inj (hget.symm.trans hget')
    subst hff
    rw [normVRun_take_succ _ _ _ _ _ hi, hvr, Option.some_bind] at hvr'
    have hs' : s' = s₁ := Option.some.inj (hvr'.symm.trans hvs)
    intro fr hm
    rw [hs'] at hm
    exact hlive' fr hm
  · intro f' s' hget' hvr'
    dsimp only [] at hget' hvr'
    have hff : f = f' := Option.some.inj (hget.symm.trans hget')
    subst hff
    rw [normVRun_take_succ _ _ _ _ _ hi, hvr, Option.some_bind] at hvr'
    have hs' : s' = s₁ := Option.some.inj (hvr'.symm.trans hvs)
    subst hs'
    exact hhist'

/-- `block`: machine pushes `.blockK`, validator pushes `.blk`; heights
agree at `st.operandStack.length = s.os.length`. -/
theorem preserve_block {st st' : NormState} {f : NormFunc} {s s₁ : NormVSt}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some .block)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) .block s = some s₁)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normStepInstr st .block = .step st') :
    NormInv st' := by
  simp only [normStepInstr] at hstep
  rw [hget] at hstep
  simp only [Option.map_some', Option.getD_some] at hstep
  cases hEE : normElseEnd f.body st.pc with
  | none =>
    simp only [hEE] at hstep; exact NormStepResult.noConfusion hstep
  | some p =>
    obtain ⟨elsePc, endPc⟩ := p
    simp only [hEE] at hstep
    have hst : st' = { st with pc := st.pc + 1, controlStack := ⟨.blockK, st.operandStack.length, st.pc, endPc⟩ :: st.controlStack } :=
      (NormStepResult.step.inj hstep).symm
    subst hst
    have hs₁ : s₁ = ⟨s.os, ⟨.blk, none, s.os, false⟩ :: s.cs⟩ := by
      simp only [normVStep] at hvs; exact (Option.some.inj hvs).symm
    subst hs₁
    refine normInv_step_cs hget hi hvr hvs ?_ hfr ?_ ?_ ?_ hloc hmem
    · exact normLabelsCorrespond_cons hcorr rfl
        (by rw [hos, List.length_map])
        ⟨elsePc, hEE⟩ hi
    · intro fr hm
      cases hm with
      | head => rfl
      | tail _ hm => exact hlive _ hm
    · exact NormHistInner.cons (hhist f s hget hvr)
        (normVRun_next hi hvr hvs) rfl rfl
        (go_result_gt hEE)
        (hpend_succ hcorr (hhist f s hget hvr) hi (by simp))
        (hnest_opener hcorr (hhist f s hget hvr) hi (Or.inl rfl) hEE)
    · exact hos

/-- `loop`: same push-shape with `.loopK` ↔ `.lp`. -/
theorem preserve_loop {st st' : NormState} {f : NormFunc} {s s₁ : NormVSt}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some .loop)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) .loop s = some s₁)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normStepInstr st .loop = .step st') :
    NormInv st' := by
  simp only [normStepInstr] at hstep
  rw [hget] at hstep
  simp only [Option.map_some', Option.getD_some] at hstep
  cases hEE : normElseEnd f.body st.pc with
  | none =>
    simp only [hEE] at hstep; exact NormStepResult.noConfusion hstep
  | some p =>
    obtain ⟨elsePc, endPc⟩ := p
    simp only [hEE] at hstep
    have hst : st' = { st with pc := st.pc + 1, controlStack := ⟨.loopK, st.operandStack.length, st.pc, endPc⟩ :: st.controlStack } :=
      (NormStepResult.step.inj hstep).symm
    subst hst
    have hs₁ : s₁ = ⟨s.os, ⟨.lp, none, s.os, false⟩ :: s.cs⟩ := by
      simp only [normVStep] at hvs; exact (Option.some.inj hvs).symm
    subst hs₁
    refine normInv_step_cs hget hi hvr hvs ?_ hfr ?_ ?_ ?_ hloc hmem
    · exact normLabelsCorrespond_cons hcorr rfl
        (by rw [hos, List.length_map])
        ⟨elsePc, hEE⟩ hi
    · intro fr hm
      cases hm with
      | head => rfl
      | tail _ hm => exact hlive _ hm
    · exact NormHistInner.cons (hhist f s hget hvr)
        (normVRun_next hi hvr hvs) rfl rfl
        (go_result_gt hEE)
        (hpend_succ hcorr (hhist f s hget hvr) hi (by simp))
        (hnest_opener hcorr (hhist f s hget hvr) hi (Or.inr (Or.inl rfl)) hEE)
    · exact hos

/-- `ifE` with `c ≠ 0` (`NormStepSafe`): pop the i32 condition, push
`.ifK` ↔ `.ift` — heights agree at `rest.length = os'.length`. -/
theorem preserve_ifE {st st' : NormState} {f : NormFunc} {s s₁ : NormVSt}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some .ifE)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) .ifE s = some s₁)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hc0 : ∀ c rest, st.operandStack = .i32 c :: rest → c ≠ 0)
    (hstep : normStepInstr st .ifE = .step st') :
    NormInv st' := by
  simp only [normStepInstr] at hstep
  rw [hget] at hstep
  simp only [Option.map_some', Option.getD_some] at hstep
  cases hOS : st.operandStack with
  | nil =>
    simp only [hOS] at hstep; exact NormStepResult.noConfusion hstep
  | cons v rest =>
    cases v with
    | i64 v =>
      simp only [hOS] at hstep; exact NormStepResult.noConfusion hstep
    | i32 c =>
      simp only [hOS] at hstep
      cases hEE : normElseEnd f.body st.pc with
      | none =>
        simp only [hEE] at hstep; exact NormStepResult.noConfusion hstep
      | some p =>
        obtain ⟨elsePc, endPc⟩ := p
        simp only [hEE] at hstep
        have hc : (c != 0) = true := bne_iff_ne.2 (hc0 c rest hOS)
        rw [if_pos hc] at hstep
        have hst : st' = { st with pc := st.pc + 1, operandStack := rest, controlStack := ⟨.ifK, rest.length, st.pc, endPc⟩ :: st.controlStack } :=
          (NormStepResult.step.inj hstep).symm
        subst hst
        have hvs0 := hvs
        simp only [normVStep, Option.map_eq_some'] at hvs
        obtain ⟨os', hvpop, hs₁⟩ := hvs
        subst hs₁
        obtain ⟨fr, frs, hcs, hfrun⟩ := cs_live_cons hcorr hlive
        have hs1 : s.os = .i32Ty :: os' := by
          rw [hcs] at hvpop; exact normVPop_strict hfrun hvpop
        have hrest : os' = rest.map NormVal.ty := by
          have e := hs1 ▸ hos
          rw [hOS, List.map_cons] at e
          exact (List.cons.inj e).2
        refine normInv_step_cs hget hi hvr hvs0 ?_ hfr ?_ ?_ ?_ hloc hmem
        · exact normLabelsCorrespond_cons hcorr rfl
            (by rw [hrest, List.length_map])
            ⟨elsePc, hEE⟩ hi
        · intro fr hm
          cases hm with
          | head => rfl
          | tail _ hm => exact hlive _ hm
        · exact NormHistInner.cons (hhist f s hget hvr)
            (normVRun_next hi hvr hvs0) rfl rfl
            (go_result_gt hEE)
            (hpend_succ hcorr (hhist f s hget hvr) hi (by simp))
            (hnest_opener hcorr (hhist f s hget hvr) hi
              (Or.inr (Or.inr rfl)) hEE)
        · exact hrest

/-- `endI`: machine pops the innermost label, validator pops the innermost
frame — the popped frame is non-`fn` (its `endI` succeeded) so
`f.rt.toList ++ os' = os' = s.os`, and the tails correspond. -/
theorem preserve_endI {st st' : NormState} {f : NormFunc} {s s₁ : NormVSt}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some .endI)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) .endI s = some s₁)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hstep : normStepInstr st .endI = .step st') :
    NormInv st' := by
  obtain ⟨fr, frs, hcs, hfrun⟩ := cs_live_cons hcorr hlive
  simp only [normStepInstr] at hstep
  cases hLS : st.controlStack with
  | nil =>
    simp only [hLS] at hstep; exact NormStepResult.noConfusion hstep
  | cons lab rest =>
    simp only [hLS] at hstep
    have hst : st' = { st with pc := st.pc + 1, controlStack := rest } :=
      (NormStepResult.step.inj hstep).symm
    subst hst
    have hcorr' : NormLabelsCorrespond f.body rest frs := by
      rw [hLS, hcs] at hcorr
      exact normLabelsCorrespond_tail hcorr
    have hvs0 := hvs
    simp only [normVStep, hcs] at hvs
    split at hvs
    · rename_i htag; exact Option.noConfusion hvs
    · rename_i htag
      simp only [Option.map_eq_some'] at hvs
      obtain ⟨os', hfchk, hs₁⟩ := hvs
      subst hs₁
      have hrt : fr.rt = none := by
        have := normVRun_rt_none (normVInit_rt_none f) hvr
        rw [hcs] at this
        exact this fr (List.mem_cons_self _ _) htag
      have hos' : os' = s.os := by
        simp only [normVFchk, hrt, Option.some_bind] at hfchk
        split at hfchk
        · exact (Option.some.inj hfchk).symm
        · exact Option.noConfusion hfchk
      subst hos'
      refine normInv_step_cs hget hi hvr hvs0 hcorr' hfr ?_ ?_ ?_ hloc hmem
      · intro f' hm
        exact hlive f' (hcs ▸ List.mem_cons_of_mem _ (show f' ∈ frs from hm))
      · exact NormHistInner.tail (hLS ▸ hhist f s hget hvr) hcs rfl
      · show fr.rt.toList ++ s.os = st.operandStack.map NormVal.ty
        rw [hrt]; exact hos

/-- `brIf n` with `c = 0` (`NormStepSafe` forces fallthrough): the machine
advances `pc + 1` with the condition popped; the validator's `normVBrIf`
leaves the frame stack untouched and `os''` reduces to the i32-popped
stack either way. -/
theorem preserve_brIf {st st' : NormState} {f : NormFunc} {s s₁ : NormVSt}
    {n : Nat}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some (.brIf n))
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) (.brIf n) s = some s₁)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hc0 : ∀ c rest, st.operandStack = .i32 c :: rest → c = 0)
    (hstep : normStepInstr st (.brIf n) = .step st') :
    NormInv st' := by
  obtain ⟨fr, frs, hcs, hfrun⟩ := cs_live_cons hcorr hlive
  simp only [normStepInstr] at hstep
  cases hOS : st.operandStack with
  | nil =>
    simp only [hOS] at hstep; exact NormStepResult.noConfusion hstep
  | cons v rest =>
    cases v with
    | i64 v =>
      simp only [hOS] at hstep; exact NormStepResult.noConfusion hstep
    | i32 c =>
      simp only [hOS] at hstep
      have hcf : ¬ (c != 0) = true := fun h => bne_iff_ne.1 h (hc0 c rest hOS)
      rw [if_neg hcf] at hstep
      have hst : st' = { st with pc := st.pc + 1, operandStack := rest } :=
        (NormStepResult.step.inj hstep).symm
      subst hst
      have hvs0 := hvs
      simp only [normVStep, normVBrIf] at hvs
      split at hvs
      · exact Option.noConfusion hvs
      · rename_i tgt rest' hdrop
        obtain ⟨os', hp1, hrest⟩ := Option.bind_eq_some.1 hvs
        obtain ⟨os'', hm2, hb⟩ := Option.bind_eq_some.1 hrest
        split at hb
        · rename_i hok
          have hs : s₁ = { s with os := os'' } := (Option.some.inj hb).symm
          subst hs
          have hos'' : os'' = os' := by
            split at hm2
            · rename_i t hlrt
              rw [Option.map_eq_some'] at hm2
              obtain ⟨os''', hp3, h4⟩ := hm2
              rw [hcs] at hp3
              have h5 : os' = t :: os''' := normVPop_strict hfrun hp3
              exact h4.symm.trans h5.symm
            · exact (Option.some.inj hm2).symm
          subst os''
          have hs1 : s.os = .i32Ty :: os' := by
            rw [hcs] at hp1; exact normVPop_strict hfrun hp1
          have hrest : os' = rest.map NormVal.ty := by
            have e := hs1 ▸ hos
            rw [hOS, List.map_cons] at e
            exact (List.cons.inj e).2
          exact normInv_step' hget hi hvr hvs0 hcorr hfr hlive hhist
            (by show os' = rest.map NormVal.ty; exact hrest) rfl hloc hmem
        · exact Option.noConfusion hb

/-- Fresh control stack at a call site: `[]` corresponds to the singleton
implicit `fn` frame. -/
theorem normLabelsCorrespond_fn (body : List NormInstr) (fr : NormTFrame)
    (hf : fr.tag = .fn) : NormLabelsCorrespond body [] [fr] := by
  refine ⟨rfl, ?_, ?_⟩
  · cases fr with
    | mk tag rt entry un => cases tag <;> simp_all
  · intro i hi; exact absurd hi (by simp)

/-- `call g`: the machine installs a fresh frame — callee `pc := 0`, empty
operand/control stacks, `NormFrame` saving the caller's resume state. The
validator applies the callee signature: `os' ++ rs.toList` with cs kept,
which is exactly the `NormFrameOK` shape for the new head frame. -/
theorem preserve_call {st st' : NormState} {f : NormFunc} {s s₁ : NormVSt}
    {g : Nat}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some (.call g))
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) (.call g) s = some s₁)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (_hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (_hhist : NormHist st)
    (hstep : normStepInstr st (.call g) = .step st') :
    NormInv st' := by
  simp only [normStepInstr] at hstep
  cases hcallee : st.module.funcs.get? g with
  | none =>
    rw [hcallee] at hstep; exact NormStepResult.noConfusion hstep
  | some callee =>
    have hvs0 := hvs
    have hcallee' := hcallee
    rw [List.get?_eq_getElem?] at hcallee'
    have hgetC : (NormVCtx.ofModule st.module f).funcs.get? g =
        some (callee.params, callee.result) := by
      simp only [NormVCtx.ofModule, List.get?_eq_getElem?,
        List.getElem?_map, hcallee', Option.map_some']
    simp only [normVStep, hgetC] at hvs
    simp only [Option.map_eq_some'] at hvs
    obtain ⟨os', hpops, hs₁⟩ := hvs
    have hlen := hcorr.1
    have hne : s.cs ≠ [] := fun e => by
      rw [e, List.length_nil] at hlen; exact Nat.noConfusion hlen
    have hhead := NormLive.head hne hlive
    have hsos : s.os = callee.params.reverse ++ os' :=
      normVPops_strict hhead hpops
    have harglen : (st.operandStack.take callee.params.length).length =
        callee.params.length := by
      rw [List.length_take]
      exact Nat.min_eq_left (by
        have e : st.operandStack.length = s.os.length := by
          rw [hos, List.length_map]
        rw [e, hsos, List.length_append, List.length_reverse]; omega)
    simp only [hcallee] at hstep
    rw [if_neg (fun h => (bne_iff_ne.1 h) harglen)] at hstep
    have hst := (NormStepResult.step.inj hstep).symm
    subst hst hs₁
    have hargs : ((st.operandStack.take callee.params.length).map
        NormVal.ty) = callee.params.reverse := by
      rw [List.map_take, ← hos, hsos, ← List.length_reverse callee.params,
          List.take_left]
    have hrest : ((st.operandStack.drop callee.params.length).map
        NormVal.ty) = os' := by
      rw [List.map_drop, ← hos, hsos, ← List.length_reverse callee.params,
          List.drop_left]
    have hzip : ((callee.params.zip
          (st.operandStack.take callee.params.length).reverse).map (·.2)) =
        (st.operandStack.take callee.params.length).reverse :=
      List.map_snd_zip _ _ (by
        rw [List.length_reverse]; omega)
    refine ⟨⟨callee, hcallee, ⟨normVInit callee, ?_, rfl, ?_⟩, ?_, ?_,
        hmem⟩, ?_, ?_⟩
    · show normVRun (NormVCtx.ofModule st.module callee)
          (normVInit callee) (callee.body.take 0) =
            some (normVInit callee)
      rw [List.take_zero, normVRun_nil]
    · exact normLabelsCorrespond_fn _ _ rfl
    · show (((callee.params.zip
            (st.operandStack.take callee.params.length).reverse).map (·.2))
          ++ callee.locals.map NormTy.zero).map NormVal.ty =
          callee.params ++ callee.locals
      rw [List.map_append, hzip, List.map_map]
      show ((st.operandStack.take callee.params.length).reverse.map
          NormVal.ty) ++
          callee.locals.map (NormVal.ty ∘ NormTy.zero) = _
      rw [List.map_reverse, hargs, List.reverse_reverse]
      have hz2 : callee.locals.map (NormVal.ty ∘ NormTy.zero) =
          callee.locals :=
        List.map_id'' (fun t => NormTy.zero_ty t) _
      rw [hz2]
    · intro fr hm
      cases hm with
      | head =>
        refine ⟨f, hget, _, normVRun_next hi hvr hvs0, ?_, ?_⟩
        · show NormLabelsCorrespond f.body st.controlStack s.cs
          exact hcorr
        · exact ⟨callee.result.toList, by rw [← hrest]⟩
      | tail _ hm => exact hfr _ hm
    · intro f₂ s₂ hget₂ hvr₂
      dsimp only [] at hget₂ hvr₂
      have hff : callee = f₂ :=
        Option.some.inj (hcallee.symm.trans hget₂)
      subst hff
      rw [List.take_zero, normVRun_nil] at hvr₂
      have hs₂ : s₂ = normVInit callee := (Option.some.inj hvr₂).symm
      subst hs₂
      intro fr hm
      simp only [normVInit, List.mem_singleton] at hm
      subst hm; rfl
    · intro f₂ s₂ hget₂ hvr₂
      exact NormHistInner.nil

/-! ## `br` arm: scan-stop lemmas and the validator branch inversion -/

theorem go_zero (body : List NormInstr) (j d : Nat) (el : Option Nat) :
    normElseEnd.go body 0 j d el = none := rfl

/-- A scan that stops at `e = j + 1` from `j` is the depth-0 `endI`
return: the depth at `j` was 0 (every continuing arm recurses from
`j + 1`, and `go_result_gt` then contradicts `e = j + 1`). -/
theorem go_stop_depth0 {body : List NormInstr} {fuel j d : Nat}
    {el x e}
    (h : normElseEnd.go body fuel j d el = some (x, e)) (hj : e = j + 1) :
    d = 0 := by
  cases fuel with
  | zero => rw [go_zero] at h; exact absurd h (by simp)
  | succ fuel =>
    rw [normElseEnd_go_succ] at h
    split at h
    · exact Option.noConfusion h
    · have := go_result_gt h; omega
    · have := go_result_gt h; omega
    · have := go_result_gt h; omega
    · split at h
      · rename_i hd0
        exact hd0
      · have := go_result_gt h; omega
    · split at h <;>
        · have := go_result_gt h; omega
    · have := go_result_gt h; omega

/-- A depth-0 `endI` at `q` ends the scan at `q + 1`. -/
theorem go_endI_depth0_stop {body : List NormInstr} {fuel q : Nat}
    {el x e}
    (h : normElseEnd.go body fuel q 0 el = some (x, e))
    (hi : body.get? q = some .endI) : e = q + 1 := by
  cases fuel with
  | zero => rw [go_zero] at h; exact absurd h (by simp)
  | succ fuel =>
    rw [normElseEnd_go_succ, hi] at h
    simp only [Nat.zero_eq, if_true, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.symm

/-- Contrapositive: a scan still running past an `endI` at `q` with
`q + 1 < e` sits at positive depth there. -/
theorem go_endI_pos_depth {body : List NormInstr} {fuel q d : Nat}
    {el x e}
    (h : normElseEnd.go body fuel q d el = some (x, e))
    (hi : body.get? q = some .endI) (hq : q + 1 < e) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have := go_endI_depth0_stop h hi
    omega
  · exact hd

/-- A successful scan from `j` needed at least `e - j` fuel — every
recursed step consumed one. -/
theorem go_fuel_bound {body : List NormInstr} (fuel : Nat) :
    ∀ (j d : Nat) (el : Option Nat) (x : Option Nat) (e : Nat),
    normElseEnd.go body fuel j d el = some (x, e) → e - j ≤ fuel := by
  induction fuel with
  | zero =>
    intro j d el x e h
    rw [go_zero] at h
    exact absurd h (by simp)
  | succ fuel ih =>
    intro j d el x e h
    rw [normElseEnd_go_succ] at h
    split at h
    · exact Option.noConfusion h
    · have := ih (j + 1) (d + 1) el x e h
      have := go_result_gt h
      omega
    · have := ih (j + 1) (d + 1) el x e h
      have := go_result_gt h
      omega
    · have := ih (j + 1) (d + 1) el x e h
      have := go_result_gt h
      omega
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        omega
      · have := ih (j + 1) (d - 1) el x e h
        have := go_result_gt h
        omega
    · split at h <;>
        · have := ih (j + 1) d _ x e h
          have := go_result_gt h
          omega
    · have := ih (j + 1) d el x e h
      have := go_result_gt h
      omega

/-- Unused fuel is irrelevant: a successful scan succeeds with any larger
fuel (the fuel only truncates long scans; the step structure is
fuel-independent). -/
theorem go_fuel_mono {body : List NormInstr} :
    ∀ (fuel j d : Nat) (el : Option Nat) (x : Option Nat) (e : Nat),
    normElseEnd.go body fuel j d el = some (x, e) →
    ∀ fuel₂, fuel ≤ fuel₂ →
      normElseEnd.go body fuel₂ j d el = some (x, e) := by
  intro fuel
  induction fuel with
  | zero =>
    intro j d el x e h fuel₂ _
    rw [go_zero] at h
    exact absurd h (by simp)
  | succ fuel ih =>
    intro j d el x e h fuel₂ hle
    cases fuel₂ with
    | zero => omega
    | succ fuel₂ =>
      rw [normElseEnd_go_succ] at h
      split at h
      · exact absurd h (by simp)
      · rename_i hbody
        simp only [normElseEnd_go_succ, hbody]
        exact ih (j + 1) (d + 1) el x e h fuel₂ (by omega)
      · rename_i hbody
        simp only [normElseEnd_go_succ, hbody]
        exact ih (j + 1) (d + 1) el x e h fuel₂ (by omega)
      · rename_i hbody
        simp only [normElseEnd_go_succ, hbody]
        exact ih (j + 1) (d + 1) el x e h fuel₂ (by omega)
      · split at h
        · rename_i hbody hd0
          simp only [normElseEnd_go_succ, hbody, if_pos hd0]
          exact h
        · rename_i hbody hd0
          simp only [normElseEnd_go_succ, hbody, if_neg hd0]
          exact ih (j + 1) (d - 1) el x e h fuel₂ (by omega)
      · split at h
        · rename_i hbody hd0
          simp only [normElseEnd_go_succ, hbody, if_pos hd0]
          exact ih (j + 1) d _ x e h fuel₂ (by omega)
        · rename_i hbody hd0
          simp only [normElseEnd_go_succ, hbody, if_neg hd0]
          exact ih (j + 1) d el x e h fuel₂ (by omega)
      · rename_i hbody
        simp only [normElseEnd_go_succ, hbody]
        exact ih (j + 1) d el x e h fuel₂ (by omega)

theorem mem_of_drop_head? {α : Type _} {l : List α} {n : Nat} {a : α}
    (h : (l.drop n).head? = some a) : a ∈ l := by
  induction n generalizing l with
  | zero =>
    simp only [List.drop_zero] at h
    cases l with
    | nil => simp at h
    | cons b bs =>
      have hb : (b :: bs).head? = some b := rfl
      rw [hb, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
  | succ n ih =>
    cases l with
    | nil => simp at h
    | cons b bs =>
      have h' : (bs.drop n).head? = some a := h
      exact List.mem_cons_of_mem _ (ih h')

/-- The validator `br n` step, inverted: the target is a structured
(non-`fn`) frame, the guard `normVBrEntryOK` passed (with a live head
this is the landing-slice equality `os.take tgt.entry.length = tgt.entry`),
the branch arity is `none` (loop targets by construction, block/if
targets by the rt-none walk property), and the successor truncates the
operand types to the INNERMOST base, marking the innermost frame
unreachable. -/
theorem normVBr_step_inv {C : NormVCtx} {n : Nat} {s s' : NormVSt}
    (h : normVStep C (.br n) s = some s')
    (hrt : ∀ fr ∈ s.cs, fr.tag ≠ .fn → fr.rt = none)
    (hnf : ∀ tgt, (s.cs.drop n).head? = some tgt → tgt.tag ≠ .fn) :
    ∃ h₀ rest tgt, s.cs = h₀ :: rest ∧
      (s.cs.drop n).head? = some tgt ∧
      (h₀.un = true ∨ s.os.take tgt.entry.length = tgt.entry) ∧
      s' = ⟨s.os.take h₀.entry.length,
             ⟨h₀.tag, h₀.rt, h₀.entry, true⟩ :: rest⟩ := by
  simp only [normVStep, normVBr] at h
  split at h
  · exact Option.noConfusion h
  · rename_i tgt ts hdrop
    have hcsne : s.cs ≠ [] := by
      intro e
      rw [e] at hdrop
      exact absurd hdrop (by simp)
    obtain ⟨h₀, rest, hcs⟩ : ∃ h₀ rest, s.cs = h₀ :: rest := by
      revert hdrop hcsne
      cases s.cs with
      | nil => intro hdrop _; simp at hdrop
      | cons h₀ rest => intro _ _; exact ⟨h₀, rest, rfl⟩
    have hhead : (s.cs.drop n).head? = some tgt := by rw [hdrop]; rfl
    have hlrtnone : (if tgt.tag = .lp then none else tgt.rt) = none := by
      by_cases hlp : tgt.tag = .lp
      · simp [hlp]
      · have hnone := hrt tgt (mem_of_drop_head? hhead) (hnf tgt hhead)
        simp [hlp, hnone]
    rw [hlrtnone] at h
    split at h
    · rename_i hguard
      simp only [normVBrEntryOK, hcs] at hguard
      split at hguard
      · rename_i hun
        refine ⟨h₀, rest, tgt, hcs, hhead, Or.inl hun, ?_⟩
        simp only [normVBrk, hcs, Option.bind_some] at h
        exact (Option.some.inj h).symm
      · have hslice : s.os.take tgt.entry.length = tgt.entry := by
          simpa using hguard
        refine ⟨h₀, rest, tgt, hcs, hhead, Or.inr hslice, ?_⟩
        simp only [normVBrk, hcs, Option.bind_some] at h
        exact (Option.some.inj h).symm
    · exact Option.noConfusion h

/-! ## `br` arm: tail-drop correspondence and label monotonicity -/

/-- `map` commutes with `take` (stdlib name drift shim). -/
theorem take_map {α β : Type _} (f : α → β) :
    ∀ (l : List α) (n : Nat), (l.take n).map f = (l.map f).take n := by
  intro l
  induction l with
  | nil => intro n; cases n <;> rfl
  | cons a l ih =>
    intro n
    cases n with
    | zero => rfl
    | succ n => simp only [List.take_succ_cons, List.map_cons, ih]

/-- Membership in a dropped tail is membership in the whole. -/
theorem mem_of_mem_drop {α : Type _} {l : List α} {n : Nat} {a : α}
    (h : a ∈ l.drop n) : a ∈ l := by
  have hs : l = l.take n ++ l.drop n := (List.take_append_drop n l).symm
  rw [hs]
  exact List.mem_append.2 (Or.inr h)

/-- Dropping a common prefix of corresponding machine/validator stacks
keeps the label correspondence (the `.fn` sentinel stays at the bottom of
both tails). -/
theorem normLabelsCorrespond_drop {body : List NormInstr}
    {ls : List NormLabel} {cs : List NormTFrame}
    (h : NormLabelsCorrespond body ls cs) (k : Nat) (hk : k ≤ ls.length) :
    NormLabelsCorrespond body (ls.drop k) (cs.drop k) := by
  obtain ⟨hlen, hbot, hall⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_drop, List.length_drop, hlen]; omega
  · rw [Option.map_eq_some'] at hbot ⊢
    obtain ⟨fr, hfr, hft⟩ := hbot
    rw [List.getLast?_eq_some_iff] at hfr
    obtain ⟨init, rfl⟩ := hfr
    have hilen : init.length = ls.length := by
      rw [List.length_append, List.length_singleton] at hlen; omega
    have hk2 : k ≤ init.length := by omega
    refine ⟨fr, ?_, hft⟩
    rw [List.getLast?_eq_some_iff]
    exact ⟨init.drop k, by
      rw [List.drop_append_eq_append_drop, Nat.sub_eq_zero_of_le hk2,
        List.drop_zero]⟩
  · intro i hi
    rw [List.length_drop] at hi
    obtain ⟨hncc, hk2, hh, hend, hstart⟩ := hall (k + i) (by omega)
    refine ⟨by rw [List.length_drop]; omega, ?_⟩
    simp only [List.getElem_drop]
    exact ⟨hk2, hh, hend, hstart⟩

/-- The label `startPc`s strictly decrease inward; hence `ls[j].startPc`
of an outer (`j ≥ i`) label is at most `ls[i].startPc`. -/
theorem startPc_mono {ls : List NormLabel}
    (hdec : ∀ i (hi : i + 1 < ls.length), ls[i + 1].startPc < ls[i].startPc) :
    ∀ i j (hi : i < ls.length) (hj : j < ls.length), i ≤ j →
      ls[j].startPc ≤ ls[i].startPc := by
  intro i j hi hj hij
  induction j generalizing i hi with
  | zero =>
    have : i = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | h'
    · exact Nat.le_refl _
    · have hi' : i < ls.length :=
        Nat.lt_of_le_of_lt (Nat.le_of_lt_succ h') (Nat.lt_of_succ_lt hj)
      exact Nat.le_trans (Nat.le_of_lt (hdec j hj))
        (ih i hi' (Nat.lt_of_succ_lt hj) (Nat.le_of_lt_succ h'))

/-- The label `endPc`s strictly increase outward: `i < j` gives
`ls[i].endPc < ls[j].endPc`. -/
theorem endPc_mono {ls : List NormLabel}
    (hnest : ∀ i (hi : i + 1 < ls.length), ls[i].endPc < ls[i + 1].endPc) :
    ∀ i j (hi : i < ls.length) (hj : j < ls.length), i < j →
      ls[i].endPc < ls[j].endPc := by
  intro i j hi hj hij
  induction j generalizing i hi with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hij) with rfl | h'
    · exact hnest _ hj
    · have hi' : i < ls.length := Nat.lt_trans h' (Nat.lt_of_succ_lt hj)
      exact Nat.lt_trans (ih i hi' (Nat.lt_of_succ_lt hj) h')
        (hnest j hj)

/-- `NormHistInner` restricted to a tail of the label stack at a moved
`pc`: the three structural conjuncts index-shift by `k`, and the history
states ride along because `s'.cs = s.cs.drop k`. -/
theorem NormHistInner.drop {C : NormVCtx} {f : NormFunc} {s s' : NormVSt}
    {pc pc' : Nat} {ls : List NormLabel} {k : Nat}
    (h : NormHistInner C f s pc ls)
    (hcs : s'.cs = s.cs.drop k)
    (hpc1 : ∀ i (hi : i < (ls.drop k).length), (ls.drop k)[i].startPc < pc')
    (hpc2 : ∀ i (hi : i < (ls.drop k).length), pc' < (ls.drop k)[i].endPc) :
    NormHistInner C f s' pc' (ls.drop k) := by
  obtain ⟨_, hdec, _, hnest, hhist⟩ := h
  refine ⟨hpc1, ?_, hpc2, ?_, ?_⟩
  · intro i hi
    rw [List.length_drop] at hi
    have h := hdec (k + i) (by omega)
    simpa [List.getElem_drop] using h
  · intro i hi
    rw [List.length_drop] at hi
    have h := hnest (k + i) (by omega)
    simpa [List.getElem_drop] using h
  · intro i hi
    rw [List.length_drop] at hi
    obtain ⟨sᵢ, hᵢ, hd⟩ := hhist (k + i) (by omega)
    refine ⟨sᵢ, ?_, ?_⟩
    · rwa [List.getElem_drop]
    · rw [hcs, List.drop_drop]; exact hd

/-! ## `br` arm: loop landing and block/if dead-walk -/

/-- `take (i + j)` splits at `i` (stdlib name-drift shim). -/
theorem take_add {α : Type _} (l : List α) (i j : Nat) :
    l.take (i + j) = l.take i ++ (l.drop i).take j := by
  induction i generalizing l with
  | zero => simp
  | succ i ih =>
    cases l with
    | nil => simp
    | cons a as =>
      rw [show i + 1 + j = (i + j) + 1 from by omega,
          List.take_succ_cons, List.drop_succ_cons, List.take_succ_cons,
          List.cons_append, ih]

/-- `l.drop n = a :: tl` pins `l.get? n` to `a`. -/
theorem drop_cons_get? {α : Type _} :
    ∀ {l : List α} {n : Nat} {a : α} {tl : List α},
      l.drop n = a :: tl → l.get? n = some a := by
  intro l n
  induction n generalizing l with
  | zero =>
    intro a tl h
    rw [List.drop_zero] at h; rw [h]; rfl
  | succ n ih =>
    intro a tl h
    cases l with
    | nil => simp at h
    | cons b bs =>
      rw [List.drop_succ_cons] at h
      rw [List.get?_cons_succ]
      exact ih h

/-- `a ∈ l.take k` unfolds to an in-bounds index of `l`. -/
theorem mem_take_get? {α : Type _} {l : List α} {n : Nat} {a : α}
    (h : a ∈ l.take n) : ∃ i, i < n ∧ l.get? i = some a := by
  induction l generalizing n with
  | nil => simp at h
  | cons b bs ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      rw [List.take_succ_cons, List.mem_cons] at h
      cases h with
      | inl h => exact ⟨0, Nat.zero_lt_succ n, by rw [h]; rfl⟩
      | inr h =>
        obtain ⟨i, hi, hgi⟩ := ih h
        exact ⟨i + 1, Nat.succ_lt_succ hi, by
          rw [List.get?_cons_succ]; exact hgi⟩

/-- `l.get? i = some a` with `i < k` lands `a` in `l.take k`. -/
theorem get?_mem_take {α : Type _} {l : List α} {i k : Nat} {a : α}
    (hg : l.get? i = some a) (hik : i < k) : a ∈ l.take k := by
  induction l generalizing i k with
  | nil => simp at hg
  | cons b bs ih =>
    cases k with
    | zero => exact absurd hik (Nat.not_lt_zero i)
    | succ k =>
      rw [List.take_succ_cons, List.mem_cons]
      cases i with
      | zero =>
        simp only [List.get?_cons_zero, Option.some.injEq] at hg
        exact Or.inl hg.symm
      | succ i =>
        simp only [List.get?_cons_succ] at hg
        exact Or.inr (ih hg (Nat.lt_of_succ_lt_succ hik))

/-- `br n` to a `.loopK` target (`NormStepSafe` restricts loop targets to
`n = 0`): the machine truncates the operand stack to the loop's entry
height and resumes at `startPc + 1` with the control stack unchanged.
The landing types are the branch guard's own slice equality (with the
head frame live, `normVBrEntryOK` holds only because the top `base`
types ARE the entry), and `NormHistInner`'s fifth conjunct pins the walk
state at `startPc + 1`: same frames, and `os` = the entry the loop
opener recorded (the loop validator step never touches `os`). -/
theorem preserve_br_loop {st st' : NormState} {f : NormFunc} {s s₁ : NormVSt}
    {n : Nat} {lab : NormLabel} {outer : List NormLabel}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (_hi : f.body.get? st.pc = some (.br n))
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) (.br n) s = some s₁)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hsafe : NormStepSafe s st (.br n))
    (hdrop : st.controlStack.drop n = lab :: outer)
    (hkind : lab.kind = .loopK)
    (hst' : st' = { st with pc := lab.startPc + 1, operandStack := st.operandStack.take lab.height }) :
    NormInv st' := by
  subst hst'
  have hrt : ∀ fr ∈ s.cs, fr.tag ≠ .fn → fr.rt = none :=
    normVRun_rt_none (normVInit_rt_none f) hvr
  have hnlt : n < st.controlStack.length := by
    rcases Nat.lt_or_ge n st.controlStack.length with h | hge
    · exact h
    · exfalso
      rw [List.drop_eq_nil_iff.mpr hge] at hdrop
      exact List.noConfusion hdrop
  have hcslen : n + 1 < s.cs.length := by
    have hlen := hcorr.1; omega
  obtain ⟨tgt, lab₂, ts, tls₂, hcsdrop, hlsdrop, hkindm, hheightm, _⟩ :=
    cs_cons_of_labels hcorr hnlt
  obtain ⟨rfl, rfl⟩ := List.cons.inj (hdrop.symm.trans hlsdrop)
  have htaglp : tgt.tag = .lp := by
    cases htg : tgt.tag <;> simp_all
  -- `NormStepSafe`'s loop clause forces `n = 0`
  obtain ⟨hcl1, _, _, _, _, _, _⟩ := hsafe
  have htgtm : tgt ∈ (s.cs.drop n).head?.toList := by
    rw [hcsdrop]; show tgt ∈ [tgt]; simp
  have hn0 : n = 0 := (hcl1 n rfl hcslen tgt htgtm).1 htaglp
  subst hn0
  rw [List.drop_zero] at hcsdrop hdrop
  -- validator inversion: with a live head the guard is the slice eq
  have hnf : ∀ t, (s.cs.drop 0).head? = some t → t.tag ≠ .fn := by
    intro t hh
    rw [List.drop_zero, hcsdrop] at hh
    have hh' := Option.some.inj hh
    rw [← hh', htaglp]
    exact fun c => NormTTag.noConfusion c
  obtain ⟨h₀, rest, tgtV, hcscons, hheadT, hguard, _⟩ :=
    normVBr_step_inv hvs hrt hnf
  have htgtV : tgt = tgtV := by
    rw [List.drop_zero, hcsdrop] at hheadT
    exact Option.some.inj hheadT
  subst htgtV
  have h₀live : h₀.un = false :=
    hlive h₀ (hcscons ▸ List.mem_cons_self h₀ rest)
  have hslice : s.os.take tgt.entry.length = tgt.entry := by
    cases hguard with
    | inl hun => rw [hun] at h₀live; exact absurd h₀live (by simp)
    | inr hslice => exact hslice
  -- history engine: the validator state at `lab.startPc + 1`
  have hlen0 : 0 < st.controlStack.length := by
    have e := congrArg List.length hdrop
    rw [List.length_cons] at e; omega
  have hstartPc : st.controlStack[0]'hlen0 = lab := by
    have hd1 := List.drop_eq_getElem_cons hlen0
    rw [List.drop_zero] at hd1
    exact (List.cons.inj (hd1.symm.trans hdrop)).1
  have hist := hhist f s hget hvr
  obtain ⟨s₀, h₀walk, hs₀cs⟩ := hist.2.2.2.2 0 hlen0
  rw [hstartPc] at h₀walk
  have hs₀cs' : s₀.cs = s.cs := by
    have h := hs₀cs
    rw [List.drop_zero] at h
    exact h.symm
  -- the opener at lab.startPc is `.loop`, so `s₀` is the post-push state
  obtain ⟨_, _, _, _, hopener⟩ := hcorr.2.2 0 hlen0
  rw [hstartPc] at hopener
  simp only [hkind] at hopener
  obtain ⟨prev, hstep₀⟩ : ∃ prev,
      normVStep (NormVCtx.ofModule st.module f) .loop prev = some s₀ := by
    rw [normVRun_take_succ _ _ _ _ _ hopener] at h₀walk
    obtain ⟨prev, _, hstep₀⟩ := bind_some_inv h₀walk
    exact ⟨prev, hstep₀⟩
  simp only [normVStep] at hstep₀
  have hs₀shape : s₀ = ⟨prev.os, ⟨.lp, none, prev.os, false⟩ :: prev.cs⟩ :=
    (Option.some.inj hstep₀).symm
  have htgt_eq : tgt = ⟨.lp, none, prev.os, false⟩ := by
    have e : s₀.cs = ⟨.lp, none, prev.os, false⟩ :: prev.cs := by
      rw [hs₀shape]
    rw [hs₀cs', hcsdrop] at e
    exact (List.cons.inj e).1
  have htgtE : tgt.entry = prev.os := by rw [htgt_eq]
  have hs₀os : s₀.os = prev.os := by rw [hs₀shape]
  refine ⟨⟨f, hget, ⟨s₀, h₀walk, ?_, ?_⟩, hloc, hfr, hmem⟩, ?_, ?_⟩
  · show s₀.os = (st.operandStack.take lab.height).map NormVal.ty
    rw [take_map, ← hos, hheightm, hslice, htgtE]
    exact hs₀os
  · show NormLabelsCorrespond f.body st.controlStack s₀.cs
    rw [hs₀cs']
    exact hcorr
  · intro f' s' hget' hvr'
    dsimp only [] at hget' hvr'
    have hff : f' = f := Option.some.inj (hget'.symm.trans hget)
    subst hff
    have hs' : s' = s₀ := Option.some.inj (hvr'.symm.trans h₀walk)
    subst hs'
    intro fr hm
    rw [hs₀cs'] at hm
    exact hlive fr hm
  · intro f' s' hget' hvr'
    dsimp only [] at hget' hvr'
    have hff : f' = f := Option.some.inj (hget'.symm.trans hget)
    subst hff
    have hs' : s' = s₀ := Option.some.inj (hvr'.symm.trans h₀walk)
    subst hs'
    refine NormHistInner.mono hist ?_ ?_ hs₀cs'
    · intro i hi
      show (st.controlStack[i]'hi).startPc < lab.startPc + 1
      have htop := startPc_mono hist.2.1 0 i hlen0 hi (Nat.zero_le i)
      rw [hstartPc] at htop
      omega
    · intro i hi
      show lab.startPc + 1 < (st.controlStack[i]'hi).endPc
      have hpend := hist.2.2.1 i hi
      have hbot := hist.1 0 hlen0
      rw [hstartPc] at hbot
      omega

/-- `br n` to a `.blockK`/`.ifK` target: the machine truncates to the
label's height, drops `n` labels plus the target, and lands at
`lab.endPc` — one position past the target's `endI`.  On the validator
side `normVBr` marks the innermost frame `un` and truncates `os` to the
innermost base; the run then dead-walks the region `[st.pc + 1,
lab.endPc - 1)` (excluded `br`/`return`/`call` by `NormStepSafe` keeps
the `os`-suffix and frame entries intact — `seg_track_aux`), lands on
the `endI` at `lab.endPc - 1` at scan depth 0 — i.e. exactly the frames
above the target popped — and `endI` pops the marked frame, landing in
`outer`/`ts` with `os` = the innermost base.  `take`-height arithmetic
then turns the bottom-`base` slice into the machine's top-`height`
truncation (uniform entry heights across the popped frames), and
`NormHistInner.drop` carries history to the `n+1`-tail. -/
theorem preserve_br_blk {st st' : NormState} {f : NormFunc} {s s₁ : NormVSt}
    {n : Nat} {lab : NormLabel} {outer : List NormLabel}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some (.br n))
    (hfull : ∃ v, normVRun (NormVCtx.ofModule st.module f) (normVInit f)
        f.body = some v)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) (.br n) s = some s₁)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hsafe : NormStepSafe s st (.br n))
    (hdrop : st.controlStack.drop n = lab :: outer)
    (hkindl : lab.kind = .blockK ∨ lab.kind = .ifK)
    (hst' : st' = { st with pc := lab.endPc, operandStack := st.operandStack.take lab.height, controlStack := outer }) :
    NormInv st' := by
  subst hst'
  have hrt := normVRun_rt_none (normVInit_rt_none f) hvr
  have hnlt : n < st.controlStack.length := by
    rcases Nat.lt_or_ge n st.controlStack.length with h | hge
    · exact h
    · exfalso
      rw [List.drop_eq_nil_iff.mpr hge] at hdrop
      exact List.noConfusion hdrop
  have hcslen : n + 1 < s.cs.length := by
    have hlen := hcorr.1; omega
  obtain ⟨tgt, lab₂, ts, tls₂, hcsdrop, hlsdrop, hkindm, hheightm, hendm⟩ :=
    cs_cons_of_labels hcorr hnlt
  obtain ⟨rfl, rfl⟩ := List.cons.inj (hdrop.symm.trans hlsdrop)
  have htgne : tgt.tag ≠ .fn ∧ tgt.tag ≠ .lp := by
    cases htg : tgt.tag <;> simp_all
  -- validator inversion
  have hnf : ∀ t, (s.cs.drop n).head? = some t → t.tag ≠ .fn := by
    intro t hh
    rw [hcsdrop] at hh
    have hh' := Option.some.inj hh
    rw [← hh']; exact htgne.1
  obtain ⟨h₀, rest, tgtV, hcscons, hheadT, hguard, hs₁shape⟩ :=
    normVBr_step_inv hvs hrt hnf
  have htgtV : tgt = tgtV := by
    rw [hcsdrop] at hheadT
    exact Option.some.inj hheadT
  subst htgtV
  have h₀live : h₀.un = false := hlive h₀ (hcscons ▸ List.mem_cons_self h₀ rest)
  have hslice : s.os.take tgt.entry.length = tgt.entry := by
    cases hguard with
    | inl hun => rw [hun] at h₀live; exact absurd h₀live (by simp)
    | inr hslice => exact hslice
  have hs₁os : s₁.os = s.os.take h₀.entry.length :=
    congrArg NormVSt.os hs₁shape
  have hs₁cs : s₁.cs = ⟨h₀.tag, h₀.rt, h₀.entry, true⟩ :: rest :=
    congrArg NormVSt.cs hs₁shape
  -- uniform-base clause: every frame at-or-above the target has the
  -- innermost base
  obtain ⟨hcl1, _, hcl3, -, -, -, -⟩ := hsafe
  have h₀mem : h₀ ∈ s.cs.head?.toList := by
    rw [hcscons]; show h₀ ∈ [h₀]; simp
  have huni0 := (hcl1 n rfl hcslen tgt
    (by rw [hcsdrop]; show tgt ∈ [tgt]; simp)).2 htgne.2
  have hgetn : s.cs.get? n = some tgt := drop_cons_get? hcsdrop
  have htgtmem : tgt ∈ s.cs.take (n + 1) :=
    get?_mem_take hgetn (Nat.lt_succ_self n)
  have htgtE : tgt.entry.length = h₀.entry.length :=
    huni0 h₀ h₀mem tgt htgtmem
  -- the post-branch stack's frame at drop n: the marked head at n = 0,
  -- else the target itself
  obtain ⟨F₀, hF₀drop, hF₀ent, hF₀rt, hF₀tag⟩ :
      ∃ F₀, s₁.cs.drop n = F₀ :: ts ∧
        F₀.entry = tgt.entry ∧ F₀.rt = tgt.rt ∧
        (F₀.tag = tgt.tag ∨ F₀.tag = .els) := by
    cases n with
    | zero =>
      rw [List.drop_zero] at hcsdrop
      obtain ⟨rfl, rfl⟩ := List.cons.inj (hcscons.symm.trans hcsdrop)
      refine ⟨⟨h₀.tag, h₀.rt, h₀.entry, true⟩, ?_, rfl, rfl, Or.inl rfl⟩
      rw [List.drop_zero]; exact hs₁cs
    | succ m =>
      refine ⟨tgt, ?_, rfl, rfl, Or.inl rfl⟩
      rw [hs₁cs, List.drop_succ_cons]
      have e : s.cs.drop (m + 1) = rest.drop m := by
        rw [hcscons, List.drop_succ_cons]
      rw [← e]; exact hcsdrop
  -- every frame in the post-branch prefix has base ≥ the innermost base
  have hbound : ∀ fr ∈ s₁.cs.take n ++ [F₀],
      h₀.entry.length ≤ fr.entry.length := by
    intro fr hm
    rw [List.mem_append] at hm
    cases hm with
    | inl hm =>
      obtain ⟨i, hi, hgi⟩ := mem_take_get? hm
      cases i with
      | zero =>
        rw [hs₁cs, List.get?_cons_zero, Option.some.injEq] at hgi
        rw [← hgi]
        exact Nat.le_refl _
      | succ i =>
        rw [hs₁cs, List.get?_cons_succ] at hgi
        have hgi' : s.cs.get? (i + 1) = some fr := by
          rw [hcscons, List.get?_cons_succ]; exact hgi
        exact Nat.le_of_eq (huni0 h₀ h₀mem fr
          (get?_mem_take hgi' (by omega))).symm
    | inr hm =>
      rw [List.mem_singleton] at hm; subst hm
      exact Nat.le_of_eq
        (htgtE.symm.trans (congrArg List.length hF₀ent).symm)
  have hB : (s.os.take h₀.entry.length).length = h₀.entry.length := by
    have e := congrArg List.length hslice
    rw [List.length_take] at e ⊢
    rw [htgtE] at e
    omega
  -- the whole-body acceptance run reaches s₁'s continuation
  obtain ⟨v, hfull⟩ := hfull
  have hrun_dead : normVRun (NormVCtx.ofModule st.module f) s₁ (f.body.drop (st.pc + 1)) = some v := by
    have e : f.body = f.body.take st.pc ++
        (.br n :: f.body.drop (st.pc + 1)) := by
      rw [← drop_eq_cons_of_get? hi, List.take_append_drop]
    rw [e, normVRun_append, hvr, Option.some_bind, normVRun_cons, hvs,
        Option.some_bind] at hfull
    exact hfull
  -- label-side history at the target index
  have hist := hhist f s hget hvr
  obtain ⟨hlabidx, houter⟩ : st.controlStack[n]'hnlt = lab ∧
      st.controlStack.drop (n + 1) = outer := by
    have hd1 := List.drop_eq_getElem_cons hnlt
    exact List.cons.inj (hd1.symm.trans hdrop)
  have hstartpc : lab.startPc < st.pc := by
    have h := hist.1 n hnlt
    rwa [hlabidx] at h
  have hpcend : st.pc < lab.endPc := by
    have h := hist.2.2.1 n hnlt
    rwa [hlabidx] at h
  obtain ⟨sᵢ, hvrᵢ, hdsᵢ⟩ := hist.2.2.2.2 n hnlt
  rw [hlabidx] at hvrᵢ
  have hsᵢcs : sᵢ.cs = tgt :: ts := hdsᵢ ▸ hcsdrop
  obtain ⟨elsePc, hend⟩ := hendm
  unfold normElseEnd at hend
  have hendI : f.body.get? (lab.endPc - 1) = some .endI := go_endI hend
  have hpc_lt1 : st.pc + 1 ≤ lab.endPc - 1 := by
    have hne : st.pc ≠ lab.endPc - 1 := by
      intro h
      have e := hi
      rw [h] at e
      exact NormInstr.noConfusion (Option.some.inj (e.symm.trans hendI))
    omega
  -- pin the scan depth at st.pc + 1 to n
  obtain ⟨FD, elD, hgoD⟩ : ∃ FD elD,
      normElseEnd.go f.body FD (st.pc + 1) n elD =
        some (elsePc, lab.endPc) := by
    rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hstartpc) with hsp | hsp
    · obtain ⟨s₂, OPEN', F', d', el', fuel', hgo_st, hrun_st, hcs_st,
          hlen_st⟩ :=
        seg_track_cs (body := f.body) (fuel := f.body.length - lab.startPc)
          (j := lab.startPc + 1) (d := 0) (el := none) (x := elsePc)
          (e := lab.endPc) (s := sᵢ) (sf := v) (OPEN := []) (F := tgt)
          (CUR := ts)
          (by rw [List.length_drop]; omega)
          (by
            rw [← List.take_append_drop (lab.startPc + 1) f.body,
                normVRun_append, hvrᵢ, Option.some_bind] at hfull
            exact hfull)
          (by rw [List.nil_append]; exact hsᵢcs)
          rfl hend st.pc hsp hpcend
      have hseg0 : f.body.take st.pc = f.body.take (lab.startPc + 1) ++
          (f.body.drop (lab.startPc + 1)).take
            (st.pc - (lab.startPc + 1)) := by
        rw [← take_add,
            show lab.startPc + 1 + (st.pc - (lab.startPc + 1)) = st.pc
              from by omega]
      have hvrseg : normVRun (NormVCtx.ofModule st.module f) sᵢ
          ((f.body.drop (lab.startPc + 1)).take
            (st.pc - (lab.startPc + 1))) = some s := by
        rw [hseg0, normVRun_append, hvrᵢ, Option.some_bind] at hvr
        exact hvr
      have hs2 : s₂ = s := Option.some.inj (hrun_st.symm.trans hvrseg)
      subst hs2
      have hlen' : OPEN'.length = n := by
        have e1 := congrArg List.length hcs_st
        have e2 := congrArg List.length hcsdrop
        rw [List.length_append, List.length_cons] at e1
        rw [List.length_drop, List.length_cons] at e2
        omega
      have hd' : d' = n := hlen_st ▸ hlen'
      rw [hd'] at hgo_st
      cases fuel' with
      | zero => rw [go_zero] at hgo_st; exact absurd hgo_st (by simp)
      | succ F =>
        rw [normElseEnd_go_succ, hi] at hgo_st
        exact ⟨F, el', hgo_st⟩
    · -- the branch sits at the scan's start position: sᵢ = s and n = 0
      have hsp' : lab.startPc + 1 = st.pc := hsp
      have hseq : s = sᵢ := by
        rw [hsp'] at hvrᵢ
        exact Option.some.inj (hvr.symm.trans hvrᵢ)
      have hn0 : n = 0 := by
        have e0 : s.cs = tgt :: ts := hseq.symm ▸ hsᵢcs
        have e2 := congrArg List.length hcsdrop
        have e3 := congrArg List.length e0
        rw [List.length_drop, List.length_cons] at e2
        rw [List.length_cons] at e3
        omega
      rw [hn0]
      rw [hsp'] at hend
      revert hend
      cases hF : f.body.length - lab.startPc with
      | zero =>
        intro hend; rw [go_zero] at hend; exact absurd hend (by simp)
      | succ F =>
        intro hend
        rw [normElseEnd_go_succ, hi] at hend
        exact ⟨F, none, hend⟩
  -- the dead-region walk to the `endI` at lab.endPc - 1
  have hex : ∀ k b, st.pc + 1 ≤ k → k < lab.endPc →
      f.body.get? k = some b →
      b ≠ .return ∧ (∀ m, b ≠ .br m) ∧ (∀ g, b ≠ .call g) :=
    hcl3 n f lab outer rfl hget hdrop
  have hcs1 : s₁.cs = s₁.cs.take n ++ F₀ :: ts := by
    have e := (List.take_append_drop n s₁.cs).symm
    rw [hF₀drop] at e
    exact e
  have hd0 : (s₁.cs.take n).length = n := by
    rw [List.length_take]
    have e : s₁.cs.length = s.cs.length := by
      rw [hs₁cs, hcscons, List.length_cons, List.length_cons]
    omega
  have hsuf : ∃ X, s₁.os = X ++ s.os.take h₀.entry.length := ⟨[], hs₁os⟩
  obtain ⟨s_pre, F₂, el₂, fuel₂, hrun_seg, hcs_pre, hos_pre, hF₂, hgo_pre⟩ :
      ∃ s_pre F₂ el₂ fuel₂,
        normVRun (NormVCtx.ofModule st.module f) s₁ ((f.body.drop (st.pc + 1)).take
            (lab.endPc - 1 - (st.pc + 1))) = some s_pre ∧
        s_pre.cs = F₂ :: ts ∧
        (∃ X', s_pre.os = X' ++ s.os.take h₀.entry.length) ∧
        (F₂.entry = tgt.entry ∧ F₂.rt = tgt.rt ∧
          (F₂.tag = tgt.tag ∨ F₂.tag = .els)) ∧
        normElseEnd.go f.body fuel₂ (lab.endPc - 1) 0 el₂ =
          some (elsePc, lab.endPc) := by
    rcases Nat.lt_or_eq_of_le hpc_lt1 with hlt1 | heq1
    · have hgoD' : normElseEnd.go f.body
          (max FD (f.body.drop (st.pc + 1)).length) (st.pc + 1) n elD =
          some (elsePc, lab.endPc) :=
        go_fuel_mono _ _ _ _ _ _ hgoD _ (Nat.le_max_left _ _)
      obtain ⟨s₂, OPEN₂, F₂, d₂, el₂, fuel₂, hgo_pre, hrun_seg, hcs_pre,
          hlen₂, hos_pre, _, hF₂⟩ :=
        seg_track_aux (Nat.le_max_right _ _) hrun_dead hcs1 hd0 hgoD'
          hsuf hB hbound hex (lab.endPc - 1) hlt1 (by omega)
      have hd2 : d₂ = 0 := go_stop_depth0 hgo_pre (by omega)
      subst hd2
      have hOPEN2 : OPEN₂ = [] := by
        cases OPEN₂ with
        | nil => rfl
        | cons a l =>
          rw [List.length_cons] at hlen₂
          exact absurd hlen₂ (by omega)
      refine ⟨s₂, F₂, el₂, fuel₂, hrun_seg, ?_, hos_pre, ?_, hgo_pre⟩
      · rw [hOPEN2, List.nil_append] at hcs_pre; exact hcs_pre
      · exact ⟨hF₂.1.trans hF₀ent, hF₂.2.1.trans hF₀rt,
          hF₂.2.2.elim
            (fun h => hF₀tag.elim (fun h2 => Or.inl (h.trans h2))
              (fun h2 => Or.inr (h.trans h2)))
            (fun h => Or.inr h)⟩
    · -- the `endI` is the very next instruction: the walk is empty
      have hn0 : n = 0 := go_stop_depth0 hgoD (by omega)
      subst hn0
      have hcs₁' : s₁.cs = F₀ :: ts := by
        have e := hF₀drop
        rw [List.drop_zero] at e; exact e
      rw [heq1] at hgoD
      refine ⟨s₁, F₀, elD, FD, ?_, hcs₁', hsuf, ⟨hF₀ent, hF₀rt, hF₀tag⟩,
        hgoD⟩
      rw [show lab.endPc - 1 - (st.pc + 1) = 0 from by omega,
          List.take_zero]
      exact normVRun_nil _ _
  -- the `.endI` step lands the run at `⟨s_pre.os, ts⟩`
  have hsegA : f.body.drop (st.pc + 1) =
      (f.body.drop (st.pc + 1)).take (lab.endPc - 1 - (st.pc + 1)) ++
        (.endI :: f.body.drop (lab.endPc - 1 + 1)) := by
    have e2 : (f.body.drop (st.pc + 1)).drop (lab.endPc - 1 - (st.pc + 1)) =
        .endI :: f.body.drop (lab.endPc - 1 + 1) := by
      rw [List.drop_drop,
          show st.pc + 1 + (lab.endPc - 1 - (st.pc + 1)) = lab.endPc - 1
            from by omega]
      exact drop_eq_cons_of_get? hendI
    rw [← e2, List.take_append_drop]
  rw [hsegA, normVRun_append, hrun_seg, Option.some_bind,
      normVRun_cons] at hrun_dead
  obtain ⟨s_land, hstep_land, -⟩ := bind_some_inv hrun_dead
  have hF₂nfn : F₂.tag ≠ .fn := by
    cases hF₂.2.2 with
    | inl h => rw [h]; exact htgne.1
    | inr h => rw [h]; exact fun c => NormTTag.noConfusion c
  have hF₂rt : F₂.rt = none := by
    rw [hF₂.2.1]
    exact hrt tgt (mem_of_drop_head? hheadT) htgne.1
  have hs_land : ∃ os₂, s_land = ⟨F₂.rt.toList ++ os₂, ts⟩ ∧
      os₂ = s_pre.os ∧ s_pre.os.length = F₂.entry.length := by
    simp only [normVStep, hcs_pre] at hstep_land
    split at hstep_land
    · rename_i hfn; exact absurd hfn hF₂nfn
    · simp only [Option.map_eq_some'] at hstep_land
      obtain ⟨os', hfchk, hsland⟩ := hstep_land
      simp only [normVFchk, hF₂rt, Option.some_bind] at hfchk
      split at hfchk
      · rename_i hlenok
        exact ⟨os', hsland.symm, (Option.some.inj hfchk).symm, hlenok⟩
      · exact Option.noConfusion hfchk
  obtain ⟨os₂, hsland_eq, hos₂, hlenok⟩ := hs_land
  -- the suffix bound forces s_pre.os = the innermost base slice
  obtain ⟨X', hosX'⟩ := hos_pre
  have hX' : X' = [] := by
    have e := congrArg List.length hosX'
    rw [List.length_append, hlenok, hF₂.1, htgtE, hB] at e
    cases X' with
    | nil => rfl
    | cons a l => rw [List.length_cons] at e; exact absurd e (by omega)
  have hsp_os : s_pre.os = s.os.take h₀.entry.length := by
    rw [hX', List.nil_append] at hosX'; exact hosX'
  have hsland_os : s_land.os = s.os.take h₀.entry.length := by
    rw [hsland_eq, hF₂rt, hos₂, hsp_os]
    rfl
  -- take lab.endPc = run-to-(endPc-1) then the endI step
  have hvr1 : normVRun (NormVCtx.ofModule st.module f) (normVInit f) (f.body.take (lab.endPc - 1)) =
      some s_pre := by
    have hseg : f.body.take (lab.endPc - 1) =
        f.body.take st.pc ++ (.br n ::
          (f.body.drop (st.pc + 1)).take
            (lab.endPc - 1 - (st.pc + 1))) := by
      have e1 : f.body.take (lab.endPc - 1) =
          f.body.take st.pc ++
            (f.body.drop st.pc).take (lab.endPc - 1 - st.pc) := by
        rw [← take_add,
            show st.pc + (lab.endPc - 1 - st.pc) = lab.endPc - 1
              from by omega]
      rw [e1]; congr 1
      rw [drop_eq_cons_of_get? hi,
          show lab.endPc - 1 - st.pc =
            (lab.endPc - 1 - (st.pc + 1)) + 1 from by omega,
          List.take_succ_cons]
    rw [hseg, normVRun_append, hvr, Option.some_bind, normVRun_cons, hvs,
        Option.some_bind]
    exact hrun_seg
  have hvr_land : normVRun (NormVCtx.ofModule st.module f) (normVInit f) (f.body.take lab.endPc) =
      some s_land := by
    rw [show lab.endPc = lab.endPc - 1 + 1 from by omega,
        normVRun_take_succ _ _ _ _ _ hendI, hvr1, Option.some_bind,
        hstep_land]
  have hos' : s_land.os =
      (st.operandStack.take lab.height).map NormVal.ty := by
    rw [take_map, ← hos, hheightm, htgtE]
    exact hsland_os
  have hts_eq : ts = s.cs.drop (n + 1) := by
    have e := List.drop_eq_getElem_cons (Nat.lt_of_succ_lt hcslen)
    exact (List.cons.inj (e.symm.trans hcsdrop)).2.symm
  have hcorr' : NormLabelsCorrespond f.body outer s_land.cs := by
    have e := normLabelsCorrespond_drop hcorr (n + 1) (by omega)
    rw [houter, hts_eq.symm] at e
    have ecs : s_land.cs = ts := congrArg NormVSt.cs hsland_eq
    rwa [ecs]
  refine ⟨⟨f, hget, ⟨s_land, hvr_land, hos', hcorr'⟩, hloc, hfr, hmem⟩,
    ?_, ?_⟩
  · intro f' s' hget' hvr'
    dsimp only [] at hget' hvr'
    have hff : f = f' := Option.some.inj (hget.symm.trans hget')
    subst hff
    have hs' : s' = s_land := Option.some.inj (hvr'.symm.trans hvr_land)
    subst hs'
    intro fr hm
    have e : s'.cs = ts := congrArg NormVSt.cs hsland_eq
    rw [e, hts_eq] at hm
    exact hlive fr (mem_of_mem_drop hm)
  · intro f' s' hget' hvr'
    dsimp only [] at hget' hvr'
    have hff : f = f' := Option.some.inj (hget.symm.trans hget')
    subst hff
    have hs' : s' = s_land := Option.some.inj (hvr'.symm.trans hvr_land)
    subst hs'
    have hcs' : s'.cs = s.cs.drop (n + 1) := by
      have e : s'.cs = ts := congrArg NormVSt.cs hsland_eq
      rw [e]; exact hts_eq
    have hdrop' : NormHistInner (NormVCtx.ofModule st.module f) f s' lab.endPc
        (st.controlStack.drop (n + 1)) := by
      refine NormHistInner.drop hist hcs' ?_ ?_
      · intro i hi2
        rw [List.length_drop] at hi2
        rw [List.getElem_drop]
        have h1 : st.controlStack[n + 1 + i].startPc < st.pc :=
          hist.1 _ (by omega)
        exact Nat.lt_trans h1 hpcend
      · intro i hi2
        rw [List.length_drop] at hi2
        rw [List.getElem_drop]
        have h2 : st.controlStack[n].endPc < st.controlStack[n+1+i].endPc :=
          endPc_mono hist.2.2.2.1 n (n + 1 + i) hnlt (by omega) (by omega)
        rwa [hlabidx] at h2
    rwa [houter] at hdrop'

/-- `br n` dispatch: no-target means `n = controlStack.length` (the
function-label `return`), excluded by `NormStepSafe`; otherwise the
target kind routes to the loop rewind or the block/if dead-walk. -/
theorem preserve_br {st st' : NormState} {f : NormFunc} {s s₁ : NormVSt}
    {n : Nat}
    (hget : st.module.funcs.get? st.funcIdx = some f)
    (hi : f.body.get? st.pc = some (.br n))
    (hfull : ∃ v, normVRun (NormVCtx.ofModule st.module f) (normVInit f)
        f.body = some v)
    (hvr : normVRun (NormVCtx.ofModule st.module f) (normVInit f)
            (f.body.take st.pc) = some s)
    (hvs : normVStep (NormVCtx.ofModule st.module f) (.br n) s = some s₁)
    (hos : s.os = st.operandStack.map NormVal.ty)
    (hcorr : NormLabelsCorrespond f.body st.controlStack s.cs)
    (hloc : st.locals.map NormVal.ty = f.params ++ f.locals)
    (hfr : ∀ fr ∈ st.callStack, NormFrameOK st.module fr)
    (hmem : st.linearMemory.bytes.length =
              st.module.memPages * NormWasmPage)
    (hlive : ∀ fr ∈ s.cs, fr.un = false)
    (hhist : NormHist st)
    (hsafe : NormStepSafe s st (.br n))
    (hstep : normStepInstr st (.br n) = .step st') :
    NormInv st' := by
  simp only [normStepInstr] at hstep
  unfold normBr at hstep
  split at hstep
  · rename_i hdn
    split at hstep
    · rename_i hret
      obtain ⟨-, hne, -, -, -, -, -⟩ := hsafe
      exact absurd
        (by rw [hret, hcorr.1] : n + 1 = s.cs.length) (hne n rfl)
    · exact NormStepResult.noConfusion hstep
  · rename_i lab outer hdrop
    cases hkl : lab.kind with
    | blockK =>
      rw [hkl] at hstep
      simp only [] at hstep
      exact preserve_br_blk hget hi hfull hvr hvs hos hcorr hloc hfr hmem
        hlive hhist hsafe hdrop (Or.inl hkl)
        (NormStepResult.step.inj hstep).symm
    | loopK =>
      rw [hkl] at hstep
      simp only [] at hstep
      exact preserve_br_loop hget hi hvr hvs hos hcorr hloc hfr hmem
        hlive hhist hsafe hdrop hkl
        (NormStepResult.step.inj hstep).symm
    | ifK =>
      rw [hkl] at hstep
      simp only [] at hstep
      exact preserve_br_blk hget hi hfull hvr hvs hos hcorr hloc hfr hmem
        hlive hhist hsafe hdrop (Or.inr hkl)
        (NormStepResult.step.inj hstep).symm

/-! ## The assembled preservation theorem -/

/-- Step-admissibility gate: at a `NormStepOK` state the pc fetches an
instruction and that instruction satisfies `NormStepSafe`.  The `∃ i`
conjunct also excludes the implicit `normReturn` boundary
(`f.body.get? st.pc = none`), where W-WX002-M1 makes the bare statement
false — `preserve`/`preserveLive` in `Wx002Preservation` are stated over
this gate. -/
def NormStepOK (st : NormState) : Prop :=
  ∀ f s, st.module.funcs.get? st.funcIdx = some f →
    normVRun (NormVCtx.ofModule st.module f) (normVInit f)
        (f.body.take st.pc) = some s →
    ∃ i, f.body.get? st.pc = some i ∧ NormStepSafe s st i

/-- `wx002_preservation` — S3's deliverable.  S0's bare
`NormStateTy st → NormStep st = .step st' → NormStateTy st'` is honestly
extended three ways, all documented in the header:

- the carried invariant is `NormInv` (`NormStateTy` + `NormLive` +
  `NormHist`): the live-frames and label-history halves are what the
  structured-control and `br` arms consume and re-establish;
- `hvalid` supplies whole-body validation (`normVAccept`), which the
  `br` arm needs for the dead-region walk and every arm needs for the
  `normVStep` witness at `pc + 1`;
- `hsafe : NormStepOK st` gates the documented exclusions —
  W-WX002-M1 (`.return`, `br` to the `.fn` bottom, and the none-pc
  `normReturn` boundary), W-WX002-M2 (`br` to `.lp` at `n ≥ 1`),
  machine-reached `.elseE`, `brIf`-taken and `ifE`-cond-0, and
  `br`/`return`/`call` inside a branch's skipped region. -/
theorem wx002_preservation {st st' : NormState}
    (hvalid : NormValidModule st.module) (hinv : NormInv st)
    (hsafe : NormStepOK st) (hstep : NormStep st = .step st') :
    NormInv st' := by
  obtain ⟨hT, hliveF, hhist⟩ := hinv
  obtain ⟨f, hget, ⟨s, hvr, hos, hcorr⟩, hloc, hfr, hmem⟩ := hT
  have hlive := hliveF f s hget hvr
  obtain ⟨i, hi, hsaf⟩ := hsafe f s hget hvr
  have hstep' : normStepInstr st i = .step st' := by
    unfold NormStep at hstep
    simp only [hget, hi] at hstep
    exact hstep
  have hfull : ∃ v, normVRun (NormVCtx.ofModule st.module f) (normVInit f)
      f.body = some v := by
    have hacc := hvalid.2.1 f (List.get?_mem hget)
    unfold normVAccept at hacc
    split at hacc
    · rename_i os₀ f0 hrun
      exact ⟨_, hrun⟩
    · exact Bool.noConfusion hacc
  obtain ⟨v₀, hrun⟩ := hfull
  have hfull : ∃ v, normVRun (NormVCtx.ofModule st.module f) (normVInit f)
      f.body = some v := ⟨v₀, hrun⟩
  have hbd : f.body =
      f.body.take st.pc ++ i :: f.body.drop (st.pc + 1) := by
    rw [← drop_eq_cons_of_get? hi]
    exact (List.take_append_drop st.pc f.body).symm
  rw [hbd, normVRun_append, hvr] at hrun
  simp only [Option.some_bind] at hrun
  rw [normVRun_cons] at hrun
  obtain ⟨s₁, hvs, -⟩ := bind_some_inv hrun
  cases i with
    | block =>
      exact preserve_block hget hi hvr hvs hos hcorr hloc hfr hmem
        hlive hhist hstep'
    | loop =>
      exact preserve_loop hget hi hvr hvs hos hcorr hloc hfr hmem
        hlive hhist hstep'
    | ifE =>
      obtain ⟨-, -, -, -, hc0, -, -⟩ := hsaf
      exact preserve_ifE hget hi hvr hvs hos hcorr hloc hfr hmem
        hlive hhist (hc0 rfl) hstep'
    | elseE =>
      obtain ⟨-, -, -, -, -, hne, -⟩ := hsaf
      exact absurd rfl hne
    | endI =>
      exact preserve_endI hget hi hvr hvs hos hcorr hloc hfr hmem
        hlive hhist hstep'
    | br n =>
      exact preserve_br hget hi hfull hvr hvs hos hcorr hloc hfr hmem
        hlive hhist hsaf hstep'
    | brIf n =>
      obtain ⟨-, -, -, hc0, -, -, -⟩ := hsaf
      exact preserve_brIf hget hi hvr hvs hos hcorr hloc hfr hmem
        hlive hhist (hc0 n rfl) hstep'
    | call g =>
      exact preserve_call hget hi hvr hvs hos hcorr hloc hfr hmem
        hlive hhist hstep'
    | «return» =>
      obtain ⟨-, -, -, -, -, -, hne⟩ := hsaf
      exact absurd rfl hne
    | drop =>
      exact preserve_drop hget hi hvr hvs hos hcorr hloc hfr hmem
        hlive hhist hstep'
    | select =>
      exact preserve_select hget hi hvr hvs hos hcorr hloc hfr hmem
        hlive hhist hstep'
    | localGet j =>
      exact preserve_localGet hget hi hvr hvs hos hcorr hloc hfr hmem
        hlive hhist hstep'
    | localSet j =>
      exact preserve_localSet hget hi hvr hvs hos hcorr hloc hfr hmem
        hlive hhist hstep'
    | localTee j =>
      exact preserve_localTee hget hi hvr hvs hos hcorr hloc hfr hmem
        hlive hhist hstep'
    | i32Const v =>
      simp only [normStepInstr] at hstep'
      exact preserve_push (.i32 v) hget hi hvr hvs rfl rfl rfl
        hos hcorr hloc hfr hmem hlive hhist
        (NormStepResult.step.inj hstep').symm
    | i32Eqz =>
      simp only [normStepInstr] at hstep'
      exact preserve_unOp32 (fun a => .i32 (cmpBool32 (a == 0)))
        (fun _ => rfl) hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist hstep'
    | i32Cmp op =>
      simp only [normStepInstr] at hstep'
      exact preserve_cmpOp32 op hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist hstep'
    | i32Add =>
      simp only [normStepInstr] at hstep'
      exact preserve_binOp32 (fun a b => .i32 (a + b)) (fun _ _ => rfl) hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist hstep'
    | i32Sub =>
      simp only [normStepInstr] at hstep'
      exact preserve_binOp32 (fun a b => .i32 (a - b)) (fun _ _ => rfl) hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist hstep'
    | i32Mul =>
      simp only [normStepInstr] at hstep'
      exact preserve_binOp32 (fun a b => .i32 (a * b)) (fun _ _ => rfl) hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist hstep'
    | i32Bit op =>
      simp only [normStepInstr] at hstep'
      exact preserve_binOp32 (fun a b => .i32 (bitU32 op a b)) (fun _ _ => rfl) hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist hstep'
    | i32Shift op =>
      simp only [normStepInstr] at hstep'
      exact preserve_binOp32 (fun a b => .i32 (shiftU32 op a b)) (fun _ _ => rfl) hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist hstep'
    | i64Const v =>
      simp only [normStepInstr] at hstep'
      exact preserve_push (.i64 v) hget hi hvr hvs rfl rfl rfl
        hos hcorr hloc hfr hmem hlive hhist
        (NormStepResult.step.inj hstep').symm
    | i64Eqz =>
      simp only [normStepInstr] at hstep'
      exact preserve_unOp64 (fun a => .i32 (cmpBool32 (a == 0)))
        (fun _ => rfl) hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist hstep'
    | i64Cmp op =>
      simp only [normStepInstr] at hstep'
      exact preserve_cmpOp64 op hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist hstep'
    | i64Add =>
      simp only [normStepInstr] at hstep'
      exact preserve_binOp64 (fun a b => some (.i64 (a + b)))
        (fun _ _ _ h => congrArg NormVal.ty (Option.some.inj h).symm)
        hget hi hvr hvs rfl hos hcorr hloc hfr hmem hlive hhist hstep'
    | i64Sub =>
      simp only [normStepInstr] at hstep'
      exact preserve_binOp64 (fun a b => some (.i64 (a - b)))
        (fun _ _ _ h => congrArg NormVal.ty (Option.some.inj h).symm)
        hget hi hvr hvs rfl hos hcorr hloc hfr hmem hlive hhist hstep'
    | i64Mul =>
      simp only [normStepInstr] at hstep'
      exact preserve_binOp64 (fun a b => some (.i64 (a * b)))
        (fun _ _ _ h => congrArg NormVal.ty (Option.some.inj h).symm)
        hget hi hvr hvs rfl hos hcorr hloc hfr hmem hlive hhist hstep'
    | i64DivS =>
      simp only [normStepInstr] at hstep'
      exact preserve_divRem64 i64DivS hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist hstep'
    | i64RemS =>
      simp only [normStepInstr] at hstep'
      exact preserve_divRem64 i64RemS hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist hstep'
    | i64Bit op =>
      simp only [normStepInstr] at hstep'
      exact preserve_binOp64 (fun a b => some (.i64 (bitU64 op a b)))
        (fun _ _ _ h => congrArg NormVal.ty (Option.some.inj h).symm)
        hget hi hvr hvs rfl hos hcorr hloc hfr hmem hlive hhist hstep'
    | i64Shift op =>
      simp only [normStepInstr] at hstep'
      exact preserve_binOp64 (fun a b => some (.i64 (shiftU64 op a b)))
        (fun _ _ _ h => congrArg NormVal.ty (Option.some.inj h).symm)
        hget hi hvr hvs rfl hos hcorr hloc hfr hmem hlive hhist hstep'
    | i32WrapI64 =>
      exact preserve_i32WrapI64 hget hi hvr hvs hos hcorr hloc hfr hmem
        hlive hhist hstep'
    | i64ExtendI32U =>
      exact preserve_i64ExtendI32U hget hi hvr hvs hos hcorr hloc hfr hmem
        hlive hhist hstep'
    | i64ExtendI32S =>
      exact preserve_i64ExtendI32S hget hi hvr hvs hos hcorr hloc hfr hmem
        hlive hhist hstep'
    | i32Load a =>
      simp only [normStepInstr] at hstep'
      exact preserve_load (rt := .i32Ty) a 4
        (fun bs => .i32 (bytesToU32 bs)) (fun _ => rfl)
        hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist hstep'
    | i64Load a =>
      simp only [normStepInstr] at hstep'
      exact preserve_load (rt := .i64Ty) a 8
        (fun bs => .i64 (bytesToU64 bs)) (fun _ => rfl)
        hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist hstep'
    | i32Store a =>
      simp only [normStepInstr] at hstep'
      exact preserve_store (vt := .i32Ty) a
        (fun v => match v with | .i32 x => some (u32ToBytes x) | _ => none)
        hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist
        (by intro v _ h; cases v with
            | i32 _ => rfl
            | i64 _ => exact Option.noConfusion h) hstep'
    | i64Store a =>
      simp only [normStepInstr] at hstep'
      exact preserve_store (vt := .i64Ty) a
        (fun v => match v with | .i64 x => some (u64ToBytes x) | _ => none)
        hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist
        (by intro v _ h; cases v with
            | i32 _ => exact Option.noConfusion h
            | i64 _ => rfl) hstep'
    | i32Load8U a =>
      simp only [normStepInstr] at hstep'
      exact preserve_load (rt := .i32Ty) a 1
        (fun bs => .i32 (match bs with | b :: _ => b.toUInt32 | [] => 0))
        (fun _ => rfl)
        hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist hstep'
    | i64Load8U a =>
      simp only [normStepInstr] at hstep'
      exact preserve_load (rt := .i64Ty) a 1
        (fun bs => .i64 (match bs with | b :: _ => b.toUInt64 | [] => 0))
        (fun _ => rfl)
        hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist hstep'
    | i32Store8 a =>
      simp only [normStepInstr] at hstep'
      exact preserve_store (vt := .i32Ty) a
        (fun v => match v with | .i32 x => some [x.toUInt8] | _ => none)
        hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist
        (by intro v _ h; cases v with
            | i32 _ => rfl
            | i64 _ => exact Option.noConfusion h) hstep'
    | i64Store8 a =>
      simp only [normStepInstr] at hstep'
      exact preserve_store (vt := .i64Ty) a
        (fun v => match v with | .i64 x => some [x.toUInt8] | _ => none)
        hget hi hvr hvs rfl
        hos hcorr hloc hfr hmem hlive hhist
        (by intro v _ h; cases v with
            | i32 _ => exact Option.noConfusion h
            | i64 _ => rfl) hstep'
    | memorySize =>
      simp only [normStepInstr] at hstep'
      exact preserve_push
        (.i32 (UInt32.ofNat
          (st.linearMemory.bytes.length / NormWasmPage)))
        hget hi hvr hvs rfl rfl rfl
        hos hcorr hloc hfr hmem hlive hhist
        (NormStepResult.step.inj hstep').symm

end Rcic.WasmNorm

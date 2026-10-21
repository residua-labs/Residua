/-
WX-002 S4 — RUN-LEVEL SOUNDNESS: a validated module's fuel-bounded run
never suspends at a `.stuck` state (`wx002_validated_run_never_stuck`).
S2's `wx002_progress` (landed, batch 23 / #6649) supplies the per-state
discharge; S3's `wx002_preservation` is composed as the explicit,
named hypothesis structure `Wx002Preservation` — the statement fixed
in `research/rcic/wx/S0_WX002.md`:

    wx002_preservation (st st' : NormState)
        (hwt : NormStateTy st) (hs : NormStep st = .step st') :
        NormStateTy st'

plus the `Wx002Live` half the landed `wx002_progress.hlive` premise
needs (the live-frames conjunct `NormStateTy` does not carry — f05b's
in-flight `RcicWasmNormPreserve` on `devin/wx002-s3-preserve` develops
the same conjunct as `NormLive` inside `NormInv`; it is inlined here
under an S4-local name so this module stays independent of the S3
branch and both can land in either order without a name clash).

Instantiation, now landed with S3, is a single structure literal:

    ⟨wx002_preservation⟩

S3's deliverable is the joint `NormInv` statement — the bare S0
`NormStateTy → step → NormStateTy` field turned out unprovable on the
landed machine (`normReturn` does not restore `locals`, W-WX002-M1; the
`br`-to-`.lp` `n ≥ 1` label retention, W-WX002-M2), so `preserve` carries
the joint invariant plus the `NormStepOK` step-admissibility gate — the
pre-repair scaffold for residues W-WX002-M1/M2 plus the `.elseE`/taken-
`brIf`/cond-0-`ifE` os-mismatches and the `br` dead-region exclusions
documented in `RcicWasmNormPreserve`'s header; dropping the exclusions
is gated on the machine repair item, per that file.  The gate surfaces
in `wx002_validated_run_never_stuck` as a per-visited-state premise —
the honest shape of S3's coverage, not a hidden hole.

`closure_claim = 0`.
-/
import rcic.RcicWasmNormPreserve

namespace Rcic.WasmNorm

/-! ## The S3 hypothesis package -/

/-- The liveness half of the run invariant (f05b's `NormLive`, inlined
under an S4-local name so this module does not depend on the in-flight
S3 file): at the current pc the validator's control frames are all live
— a machine-reached state never sits inside a dead region.  Neither
`NormStateTy` nor `NormLabelsCorrespond` carries this (they check
tags/heights/kinds only), but `wx002_progress` consumes it as `hlive`,
so the run must thread it. -/
def Wx002Live (st : NormState) : Prop :=
  ∀ f s, st.module.funcs.get? st.funcIdx = some f →
    normVRun (NormVCtx.ofModule st.module f) (normVInit f)
        (f.body.take st.pc) = some s →
    ∀ fr ∈ s.cs, fr.un = false

/-- The S3 hypothesis S4 composes, named so the eventual instantiation
is one line once `RcicWasmNormPreserve` lands.

- `preserve` is verbatim the statement fixed for `wx002_preservation`
  in `research/rcic/wx/S0_WX002.md`: successful steps preserve config
  typing (`NormStateTy`).
- `preserveLive` is the same sentence at the `NormLive` carrier — the
  second half of S3's `NormInv = NormStateTy ∧ NormLive` invariant —
  given the source typing (which `preserve` already threads).

Everything else S4 needs beyond these two fields is machine-level
bookkeeping this file proves outright: `st.module` is step-invariant
(`normStep_preserves_module`), so `NormValidModule` at the suspended
state is the *given* `NormValidModule m`, not a hypothesis field. -/
structure Wx002Preservation where
  /-- `wx002_preservation`, honestly extended past S0's bare
  `NormStateTy` statement:

  - the carried invariant is `NormInv` (`NormStateTy` + `NormLive` +
    `NormHist`) — the live-frame and label-history conjuncts are what the
    structured-control and `br` arms consume and re-establish;
  - `NormValidModule` supplies the whole-body validator run the `br`
    dead-walk and the `normVStep`-at-`pc + 1` witness need (`st.module`
    is step-invariant, so `hv` at the run's entry propagates);
  - `NormStepOK st` gates the documented unsafe steps — the
    W-WX002-M1/M2 machine defects, the machine-reached `.elseE`/
    `brIf`-taken/`ifE`-cond-0 os-mismatches, `br`/`return`/`call` inside
    a `br`'s skipped region, and (via `NormStepOK`'s `∃ i` conjunct) the
    none-pc `normReturn` boundary. -/
  preserve : ∀ {st st' : NormState}, NormValidModule st.module →
    NormInv st → NormStepOK st → NormStep st = .step st' →
    NormInv st'

/-! ## Machine bookkeeping: the module field is step-invariant -/

private theorem normReturn_module {st st' : NormState}
    (h : normReturn st = .step st') : st'.module = st.module := by
  unfold normReturn at h
  cases hcs : st.callStack with
  | cons fr rest =>
    simp only [hcs] at h
    rw [← NormStepResult.step.inj h]
  | nil =>
    simp only [hcs] at h
    cases har : ((st.module.funcs.get? st.funcIdx).bind
        NormFunc.result).isSome with
    | false =>
      simp only [har] at h
      exact NormStepResult.noConfusion h
    | true =>
      simp only [har] at h
      cases hop : st.operandStack with
      | nil =>
        simp only [hop] at h
        exact NormStepResult.noConfusion h
      | cons v vs =>
        simp only [hop] at h
        cases v <;> exact NormStepResult.noConfusion h

private theorem normBr_module {st st' : NormState} {n : Nat}
    (h : normBr st n = .step st') : st'.module = st.module := by
  unfold normBr at h
  cases hd : st.controlStack.drop n with
  | nil =>
    simp only [hd] at h
    split at h
    · exact normReturn_module h
    · exact NormStepResult.noConfusion h
  | cons lab outer =>
    simp only [hd] at h
    obtain ⟨k, hgt, sp, ep⟩ := lab
    cases k <;>
      rw [← NormStepResult.step.inj h]

private theorem normBinOp32_module {st st' : NormState} {F}
    (h : normBinOp32 st F = .step st') : st'.module = st.module := by
  unfold normBinOp32 at h
  cases hop : st.operandStack with
  | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
  | cons v1 r1 =>
    simp only [hop] at h
    cases v1 with
    | i64 _ => exact NormStepResult.noConfusion h
    | i32 _ =>
      cases r1 with
      | nil => exact NormStepResult.noConfusion h
      | cons v2 r2 =>
        cases v2 with
        | i64 _ => exact NormStepResult.noConfusion h
        | i32 _ =>
          rw [← NormStepResult.step.inj h]

private theorem normBinOp64_module {st st' : NormState} {F}
    (h : normBinOp64 st F = .step st') : st'.module = st.module := by
  unfold normBinOp64 at h
  cases hop : st.operandStack with
  | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
  | cons v1 r1 =>
    simp only [hop] at h
    cases v1 with
    | i32 _ => exact NormStepResult.noConfusion h
    | i64 b =>
      cases r1 with
      | nil => exact NormStepResult.noConfusion h
      | cons v2 r2 =>
        cases v2 with
        | i32 _ => exact NormStepResult.noConfusion h
        | i64 a =>
          simp only [] at h
          cases hf : F a b with
          | none => simp only [hf] at h; exact NormStepResult.noConfusion h
          | some v =>
            simp only [hf] at h
            rw [← NormStepResult.step.inj h]

private theorem normCmpOp32_module {st st' : NormState} {op}
    (h : normCmpOp32 st op = .step st') : st'.module = st.module := by
  unfold normCmpOp32 at h
  cases hop : st.operandStack with
  | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
  | cons v1 r1 =>
    simp only [hop] at h
    cases v1 with
    | i64 _ => exact NormStepResult.noConfusion h
    | i32 _ =>
      cases r1 with
      | nil => exact NormStepResult.noConfusion h
      | cons v2 r2 =>
        cases v2 with
        | i64 _ => exact NormStepResult.noConfusion h
        | i32 _ =>
          rw [← NormStepResult.step.inj h]

private theorem normCmpOp64_module {st st' : NormState} {op}
    (h : normCmpOp64 st op = .step st') : st'.module = st.module := by
  unfold normCmpOp64 at h
  cases hop : st.operandStack with
  | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
  | cons v1 r1 =>
    simp only [hop] at h
    cases v1 with
    | i32 _ => exact NormStepResult.noConfusion h
    | i64 _ =>
      cases r1 with
      | nil => exact NormStepResult.noConfusion h
      | cons v2 r2 =>
        cases v2 with
        | i32 _ => exact NormStepResult.noConfusion h
        | i64 _ =>
          rw [← NormStepResult.step.inj h]

private theorem normDivRem64_module {st st' : NormState} {F}
    (h : normDivRem64 st F = .step st') : st'.module = st.module := by
  unfold normDivRem64 at h
  cases hop : st.operandStack with
  | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
  | cons v1 r1 =>
    simp only [hop] at h
    cases v1 with
    | i32 _ => exact NormStepResult.noConfusion h
    | i64 b =>
      cases r1 with
      | nil => exact NormStepResult.noConfusion h
      | cons v2 r2 =>
        cases v2 with
        | i32 _ => exact NormStepResult.noConfusion h
        | i64 a =>
          simp only [] at h
          cases hf : F a b with
          | error r =>
            simp only [hf] at h; exact NormStepResult.noConfusion h
          | ok v =>
            simp only [hf] at h
            rw [← NormStepResult.step.inj h]

private theorem normUnOp32_module {st st' : NormState} {F}
    (h : normUnOp32 st F = .step st') : st'.module = st.module := by
  unfold normUnOp32 at h
  cases hop : st.operandStack with
  | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
  | cons v1 r1 =>
    simp only [hop] at h
    cases v1 with
    | i64 _ => exact NormStepResult.noConfusion h
    | i32 _ =>
      rw [← NormStepResult.step.inj h]

private theorem normUnOp64_module {st st' : NormState} {F}
    (h : normUnOp64 st F = .step st') : st'.module = st.module := by
  unfold normUnOp64 at h
  cases hop : st.operandStack with
  | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
  | cons v1 r1 =>
    simp only [hop] at h
    cases v1 with
    | i32 _ => exact NormStepResult.noConfusion h
    | i64 _ =>
      rw [← NormStepResult.step.inj h]

private theorem normLoad_module {st st' : NormState} {a n mk}
    (h : normLoad st a n mk = .step st') : st'.module = st.module := by
  unfold normLoad at h
  cases hop : st.operandStack with
  | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
  | cons v rest =>
    simp only [hop] at h
    cases v with
    | i64 _ => exact NormStepResult.noConfusion h
    | i32 addr =>
      simp only [] at h
      cases hm : memLoadBytes st.linearMemory (addr.toNat + a.offset) n with
      | none => simp only [hm] at h; exact NormStepResult.noConfusion h
      | some bs =>
        simp only [hm] at h
        rw [← NormStepResult.step.inj h]

private theorem normStore_module {st st' : NormState} {a bsOf}
    (h : normStore st a bsOf = .step st') : st'.module = st.module := by
  unfold normStore at h
  cases hop : st.operandStack with
  | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
  | cons v1 r1 =>
    simp only [hop] at h
    cases r1 with
    | nil => exact NormStepResult.noConfusion h
    | cons v2 r2 =>
      cases v2 with
      | i64 _ => exact NormStepResult.noConfusion h
      | i32 addr =>
        simp only [] at h
        cases hb : bsOf v1 with
        | none => simp only [hb] at h; exact NormStepResult.noConfusion h
        | some bs =>
          simp only [hb] at h
          cases hm : memStoreBytes st.linearMemory
              (addr.toNat + a.offset) bs with
          | none => simp only [hm] at h; exact NormStepResult.noConfusion h
          | some m' =>
            simp only [hm] at h
            rw [← NormStepResult.step.inj h]

/-- The inline `normStepInstr` arms — helper-call arms discharge to the
per-helper lemmas; the inline arms destruct their scrutinees and every
`.step` leaf is a record literal keeping `module`. -/
private theorem normStepInstr_module {st st' : NormState} {i : NormInstr}
    (h : normStepInstr st i = .step st') : st'.module = st.module := by
  cases i with
  | block =>
    simp only [normStepInstr] at h
    cases hend : normElseEnd
        (st.module.funcs.get? st.funcIdx |>.map NormFunc.body |>.getD [])
        st.pc with
    | none => simp only [hend] at h; exact NormStepResult.noConfusion h
    | some p =>
      simp only [hend] at h
      rw [← NormStepResult.step.inj h]
  | loop =>
    simp only [normStepInstr] at h
    cases hend : normElseEnd
        (st.module.funcs.get? st.funcIdx |>.map NormFunc.body |>.getD [])
        st.pc with
    | none => simp only [hend] at h; exact NormStepResult.noConfusion h
    | some p =>
      simp only [hend] at h
      rw [← NormStepResult.step.inj h]
  | ifE =>
    simp only [normStepInstr] at h
    cases hop : st.operandStack with
    | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
    | cons v rest =>
      simp only [hop] at h
      cases v with
      | i64 _ => exact NormStepResult.noConfusion h
      | i32 c =>
        cases hend : normElseEnd
            (st.module.funcs.get? st.funcIdx |>.map NormFunc.body |>.getD [])
            st.pc with
        | none => simp only [hend] at h; exact NormStepResult.noConfusion h
        | some p =>
          obtain ⟨el, ep⟩ := p
          simp only [hend] at h
          split at h
          · rw [← NormStepResult.step.inj h]
          · cases el <;>
              rw [← NormStepResult.step.inj h]
  | elseE =>
    simp only [normStepInstr] at h
    cases hcs : st.controlStack with
    | nil => simp only [hcs] at h; exact NormStepResult.noConfusion h
    | cons lab rest =>
      simp only [hcs] at h
      rw [← NormStepResult.step.inj h]
  | endI =>
    simp only [normStepInstr] at h
    cases hcs : st.controlStack with
    | nil => simp only [hcs] at h; exact NormStepResult.noConfusion h
    | cons lab rest =>
      simp only [hcs] at h
      rw [← NormStepResult.step.inj h]
  | br n =>
    simp only [normStepInstr] at h
    exact normBr_module h
  | brIf n =>
    simp only [normStepInstr] at h
    cases hop : st.operandStack with
    | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
    | cons v rest =>
      simp only [hop] at h
      cases v with
      | i64 _ => exact NormStepResult.noConfusion h
      | i32 c =>
        simp only [] at h
        split at h
        · have h2 := normBr_module h
          exact h2
        · rw [← NormStepResult.step.inj h]
  | call f =>
    simp only [normStepInstr] at h
    cases hf : st.module.funcs.get? f with
    | none => simp only [hf] at h; exact NormStepResult.noConfusion h
    | some callee =>
      simp only [hf] at h
      split at h
      · exact NormStepResult.noConfusion h
      · rw [← NormStepResult.step.inj h]
  | «return» =>
    simp only [normStepInstr] at h
    exact normReturn_module h
  | drop =>
    simp only [normStepInstr] at h
    cases hop : st.operandStack with
    | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
    | cons v rest =>
      simp only [hop] at h
      rw [← NormStepResult.step.inj h]
  | select =>
    simp only [normStepInstr] at h
    cases hop : st.operandStack with
    | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
    | cons v1 r1 =>
      simp only [hop] at h
      cases v1 with
      | i64 _ => exact NormStepResult.noConfusion h
      | i32 c =>
        cases r1 with
        | nil => exact NormStepResult.noConfusion h
        | cons v2 r2 =>
          cases r2 with
          | nil => exact NormStepResult.noConfusion h
          | cons v3 r3 =>
            rw [← NormStepResult.step.inj h]
  | localGet i =>
    simp only [normStepInstr] at h
    cases hl : st.locals.get? i with
    | none => simp only [hl] at h; exact NormStepResult.noConfusion h
    | some v =>
      simp only [hl] at h
      rw [← NormStepResult.step.inj h]
  | localSet i =>
    simp only [normStepInstr] at h
    cases hop : st.operandStack with
    | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
    | cons v rest =>
      simp only [hop] at h
      cases hs : normLocalsSet st.locals i v with
      | none => simp only [hs] at h; exact NormStepResult.noConfusion h
      | some ls' =>
        simp only [hs] at h
        rw [← NormStepResult.step.inj h]
  | localTee i =>
    simp only [normStepInstr] at h
    cases hop : st.operandStack with
    | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
    | cons v rest =>
      simp only [hop] at h
      cases hs : normLocalsSet st.locals i v with
      | none => simp only [hs] at h; exact NormStepResult.noConfusion h
      | some ls' =>
        simp only [hs] at h
        rw [← NormStepResult.step.inj h]
  | i32Const v =>
    simp only [normStepInstr] at h
    rw [← NormStepResult.step.inj h]
  | i32Eqz =>
    simp only [normStepInstr] at h
    exact normUnOp32_module h
  | i32Cmp op =>
    simp only [normStepInstr] at h
    exact normCmpOp32_module h
  | i32Add =>
    simp only [normStepInstr] at h
    exact normBinOp32_module h
  | i32Sub =>
    simp only [normStepInstr] at h
    exact normBinOp32_module h
  | i32Mul =>
    simp only [normStepInstr] at h
    exact normBinOp32_module h
  | i32Bit op =>
    simp only [normStepInstr] at h
    exact normBinOp32_module h
  | i32Shift op =>
    simp only [normStepInstr] at h
    exact normBinOp32_module h
  | i64Const v =>
    simp only [normStepInstr] at h
    rw [← NormStepResult.step.inj h]
  | i64Eqz =>
    simp only [normStepInstr] at h
    exact normUnOp64_module h
  | i64Cmp op =>
    simp only [normStepInstr] at h
    exact normCmpOp64_module h
  | i64Add =>
    simp only [normStepInstr] at h
    exact normBinOp64_module h
  | i64Sub =>
    simp only [normStepInstr] at h
    exact normBinOp64_module h
  | i64Mul =>
    simp only [normStepInstr] at h
    exact normBinOp64_module h
  | i64DivS =>
    simp only [normStepInstr] at h
    exact normDivRem64_module h
  | i64RemS =>
    simp only [normStepInstr] at h
    exact normDivRem64_module h
  | i64Bit op =>
    simp only [normStepInstr] at h
    exact normBinOp64_module h
  | i64Shift op =>
    simp only [normStepInstr] at h
    exact normBinOp64_module h
  | i32WrapI64 =>
    simp only [normStepInstr] at h
    cases hop : st.operandStack with
    | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
    | cons v rest =>
      simp only [hop] at h
      cases v with
      | i32 _ => exact NormStepResult.noConfusion h
      | i64 _ =>
        rw [← NormStepResult.step.inj h]
  | i64ExtendI32U =>
    simp only [normStepInstr] at h
    cases hop : st.operandStack with
    | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
    | cons v rest =>
      simp only [hop] at h
      cases v with
      | i64 _ => exact NormStepResult.noConfusion h
      | i32 _ =>
        rw [← NormStepResult.step.inj h]
  | i64ExtendI32S =>
    simp only [normStepInstr] at h
    cases hop : st.operandStack with
    | nil => simp only [hop] at h; exact NormStepResult.noConfusion h
    | cons v rest =>
      simp only [hop] at h
      cases v with
      | i64 _ => exact NormStepResult.noConfusion h
      | i32 _ =>
        rw [← NormStepResult.step.inj h]
  | i32Load a =>
    simp only [normStepInstr] at h
    exact normLoad_module h
  | i64Load a =>
    simp only [normStepInstr] at h
    exact normLoad_module h
  | i32Store a =>
    simp only [normStepInstr] at h
    exact normStore_module h
  | i64Store a =>
    simp only [normStepInstr] at h
    exact normStore_module h
  | i32Load8U a =>
    simp only [normStepInstr] at h
    exact normLoad_module h
  | i64Load8U a =>
    simp only [normStepInstr] at h
    exact normLoad_module h
  | i32Store8 a =>
    simp only [normStepInstr] at h
    exact normStore_module h
  | i64Store8 a =>
    simp only [normStepInstr] at h
    exact normStore_module h
  | memorySize =>
    simp only [normStepInstr] at h
    rw [← NormStepResult.step.inj h]

/-- `.step` outcomes never rewrite `st.module` — every `normStepInstr`
arm produces a record update on non-`module` fields.  (Pure machine
bookkeeping; the per-helper lemmas above keep the unfolded terms
small.) -/
theorem normStep_preserves_module {st st' : NormState}
    (h : NormStep st = .step st') : st'.module = st.module := by
  unfold NormStep at h
  cases hf : st.module.funcs.get? st.funcIdx with
  | none => simp only [hf] at h; exact NormStepResult.noConfusion h
  | some g =>
    simp only [hf] at h
    cases hb : g.body.get? st.pc with
    | none => simp only [hb] at h; exact normReturn_module h
    | some i => simp only [hb] at h; exact normStepInstr_module h

/-- Module invariance lifts to runs: a suspension at `st'` keeps the
source module (`.done` outcomes can't be `.suspended`; `.stuck`
suspends at the same state). -/
theorem normSteps_preserves_module (fuel : Nat) (st st' : NormState)
    (h : NormSteps fuel st = .suspended st') : st'.module = st.module := by
  induction fuel generalizing st with
  | zero =>
    have e := NormRunResult.suspended.inj h
    subst e; rfl
  | succ fuel ih =>
    rw [normSteps_succ] at h
    cases hs : NormStep st with
    | step s =>
      rw [hs] at h
      exact (ih s h).trans (normStep_preserves_module hs)
    | trap r s => rw [hs] at h; exact NormRunResult.noConfusion h
    | ret v m => rw [hs] at h; exact NormRunResult.noConfusion h
    | stuck =>
      rw [hs] at h
      have e := NormRunResult.suspended.inj h
      subst e; rfl

/-! ## Initialization -/

/-- `memStoreBytes` preserves the byte-array length — the S3
`memStoreBytes_length` (RcicWasmNormPreserve) supplies it; the local copy
was removed on import.

The input-region write keeps the buffer length — `getD` keeps
either the stored memory or the fallback, both the same length. -/
theorem memStoreBytes_getD_length (mem : NormMemory) (off : Nat)
    (bs : List UInt8) :
    (Option.getD (memStoreBytes mem off bs) mem).bytes.length =
      mem.bytes.length := by
  cases hs : memStoreBytes mem off bs with
  | some m' =>
    show (Option.getD (some m') mem).bytes.length = mem.bytes.length
    exact memStoreBytes_length hs
  | none =>
    show (Option.getD none mem).bytes.length = mem.bytes.length
    rfl

/-- The initialized linear memory is exactly `memPages` wasm pages —
each `memStoreBytes` is length-preserving or discarded, so `normInit`'s
fold/getD chain keeps the `ofPages` length. -/
theorem normInit_mem_length (m : NormModule) (input : List UInt8) :
    (normInit m input).linearMemory.bytes.length =
      m.memPages * NormWasmPage := by
  have hfold : ∀ (acc : NormMemory) (ds : List (Nat × List UInt8)),
      (ds.foldl (fun a d => match memStoreBytes a d.1 d.2 with
          | some m' => m' | none => a) acc).bytes.length
        = acc.bytes.length := by
    intro acc ds
    induction ds generalizing acc with
    | nil => rfl
    | cons d ds ih =>
      rw [List.foldl_cons, ih]
      cases hs : memStoreBytes acc d.1 d.2 with
      | some m' => exact memStoreBytes_length hs
      | none => rfl
  have hlen₀ : (NormMemory.ofPages m.memPages).bytes.length =
      m.memPages * NormWasmPage := by
    show (List.replicate (m.memPages * NormWasmPage) 0).length = _
    exact List.length_replicate _ _
  unfold normInit
  dsimp only []
  rw [memStoreBytes_getD_length]
  exact (hfold (NormMemory.ofPages m.memPages) m.datas).trans hlen₀

/-- `wx002_init_typed` (S0): the entry state is config-typed — the
validator's empty prefix run yields `normVInit f` (one live `.fn`
frame), the `residua_entry(i32,i32)` locals match, and memory is
`memPages` pages. -/
theorem wx002_init_typed (m : NormModule) (input : List UInt8)
    (hv : NormValidModule m) : NormStateTy (normInit m input) := by
  obtain ⟨f, hentry, hparams, _, _, _⟩ := hv.1
  unfold NormStateTy normInit
  dsimp only []
  refine ⟨f, hentry, ⟨normVInit f, rfl, rfl, ?_, ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · show (1 : Nat) = 0 + 1
    rfl
  · show ([⟨.fn, f.result, [], false⟩].getLast?).map NormTFrame.tag
        = some .fn
    rfl
  · intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  · show (([NormVal.i32 (UInt32.ofNat normInputRegionOffset),
        NormVal.i32 (UInt32.ofNat input.length)]
        ++ ((m.funcs.get? m.entry).getD ⟨[], [], none, []⟩).locals.map
          NormTy.zero).map NormVal.ty) = _
    rw [hentry]
    simp only [Option.getD_some, List.map_append, List.map_map,
      List.map_cons, List.map_nil, NormVal.ty]
    rw [hparams]
    have hz : ∀ l : List NormTy,
        l.map (NormVal.ty ∘ NormTy.zero) = l := by
      intro l
      induction l with
      | nil => rfl
      | cons t ts ih =>
        simp only [List.map_cons]
        rw [ih]
        cases t <;> rfl
    rw [hz]
  · intro fr hfr
    exact absurd hfr (List.not_mem_nil _)
  · exact normInit_mem_length m input

/-- `wx002_init_live`: the entry state's validator frames are the
single live `.fn` frame — `Wx002Live` holds unconditionally. -/
theorem wx002_init_live (m : NormModule) (input : List UInt8) :
    Wx002Live (normInit m input) := by
  intro f s _ hs
  have es : s = normVInit f := (Option.some.inj hs).symm
  subst es
  intro fr hfr
  simp only [normVInit, List.mem_singleton] at hfr
  subst fr
  rfl

/-! ## The run corollaries -/

/-- `wx002_run_preserve` (S0, honestly extended): the joint `NormInv`
invariant threads through fuel — `.step` transitions apply `P.preserve`
under the per-step `NormStepOK` gate, `.stuck` suspends at the same
(already-typed) state, `.done` outcomes can't be `.suspended`.  `hv`
propagates because `st.module` is step-invariant; `hsafe` is the
trace-level gate: every state visited before the last step is
step-admissible. -/
theorem wx002_run_preserve (P : Wx002Preservation)
    (st st' : NormState) (fuel : Nat)
    (hv : NormValidModule st.module) (hinv : NormInv st)
    (hsafe : ∀ k stᵢ, k < fuel → NormSteps k st = .suspended stᵢ →
        NormStepOK stᵢ)
    (h : NormSteps fuel st = .suspended st') : NormInv st' := by
  induction fuel generalizing st with
  | zero =>
    have e := NormRunResult.suspended.inj h
    subst e; exact hinv
  | succ fuel ih =>
    rw [normSteps_succ] at h
    cases hs : NormStep st with
    | step s =>
      rw [hs] at h
      have hv' : NormValidModule s.module := by
        have hm := normStep_preserves_module hs
        rw [hm]; exact hv
      have hsafe' : ∀ k stᵢ, k < fuel → NormSteps k s = .suspended stᵢ →
          NormStepOK stᵢ := by
        intro k stᵢ hk hᵢ
        exact hsafe (k + 1) stᵢ (Nat.succ_lt_succ hk)
          (by rw [normSteps_succ, hs]; exact hᵢ)
      exact ih s hv'
        (P.preserve hv hinv (hsafe 0 st (Nat.zero_lt_succ _) rfl) hs)
        hsafe' h
    | trap r s => rw [hs] at h; exact NormRunResult.noConfusion h
    | ret v m => rw [hs] at h; exact NormRunResult.noConfusion h
    | stuck =>
      rw [hs] at h
      have e := NormRunResult.suspended.inj h
      subst e; exact hinv

/-- The joint run invariant projected — `wx002_run_preserve` yields
`NormInv st'`; its `NormLive` half (definitionally `Wx002Live`) is what
the suspended state's `wx002_progress` application consumes. -/
theorem wx002_run_live (P : Wx002Preservation)
    (st st' : NormState) (fuel : Nat)
    (hv : NormValidModule st.module) (hinv : NormInv st)
    (hsafe : ∀ k stᵢ, k < fuel → NormSteps k st = .suspended stᵢ →
        NormStepOK stᵢ)
    (h : NormSteps fuel st = .suspended st') :
    NormStateTy st' ∧ Wx002Live st' :=
  let hinv' := wx002_run_preserve P st st' fuel hv hinv hsafe h
  ⟨hinv'.1, hinv'.2.1⟩

/-- `wx002_init_hist`: at entry the control stack is `[]`, so
`NormHistInner` is vacuous — the third `NormInv` conjunct for the run
theorems. -/
theorem wx002_init_hist (m : NormModule) (input : List UInt8) :
    NormHist (normInit m input) := fun _ _ _ _ => NormHistInner.nil

/-- The joint `NormInv` at `normInit` — the three S0 init lemmas
composed. -/
theorem wx002_init_inv (m : NormModule) (input : List UInt8)
    (hv : NormValidModule m) : NormInv (normInit m input) :=
  ⟨wx002_init_typed m input hv, wx002_init_live m input,
    wx002_init_hist m input⟩

/-- `wx002_validated_run_never_stuck` (S0, the row — honestly gated): a
validated module's `NormSteps` never suspends at a `.stuck` state,
provided every state the run visits before its last step is
step-admissible (`hsafe`).  The gate is the S3 exclusion surface —
`NormStepOK` excludes the W-WX002-M1/M2 machine defects, the `.elseE`/
`brIf`-taken/`ifE`-cond-0 os-mismatches, `br`/`return`/`call` in a `br`'s
skipped region, and the none-pc `normReturn` boundary.  The run keeps
`NormInv` (`wx002_run_live`), keeps the module
(`normSteps_preserves_module`), and `wx002_progress` discharges. -/
theorem wx002_validated_run_never_stuck (P : Wx002Preservation)
    (m : NormModule) (input : List UInt8) (hv : NormValidModule m)
    (fuel : Nat) (st' : NormState)
    (hsafe : ∀ k stᵢ, k < fuel →
        NormSteps k (normInit m input) = .suspended stᵢ →
        NormStepOK stᵢ)
    (h : NormSteps fuel (normInit m input) = .suspended st') :
    NormStep st' ≠ .stuck := by
  have hmod : st'.module = m :=
    normSteps_preserves_module fuel (normInit m input) st' h
  have hv' : NormValidModule st'.module := hmod.symm ▸ hv
  obtain ⟨hty, hlv⟩ := wx002_run_live P _ _ fuel hv
    (wx002_init_inv m input hv) hsafe h
  obtain ⟨f, hfunc, ⟨s, hs, hos, hcorr⟩, hloc, hfr, hmem⟩ := hty
  exact wx002_progress hv' hfunc hs hos hcorr hloc (hlv f s hfunc hs)

/-! ## The S3 instantiation -/

/-- `wx002Preservation`: the S3 hypothesis package instantiated by
`wx002_preservation` (`RcicWasmNormPreserve`'s assembled 37-ctor
dispatch).  With this structure the run corollaries become executable
theorems rather than hypotheses. -/
def wx002Preservation : Wx002Preservation := ⟨wx002_preservation⟩

end Rcic.WasmNorm

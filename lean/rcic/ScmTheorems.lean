/-
RCIC 06 §15–§16 — core semantic theorems over the K2 intrinsic machine
(#6029 K3, first segment).

Owner text (06 §16): "progress: well-typed nonfinal configs have a step;
preservation: a step preserves configuration typing; determinism: next
state/final outcome is unique; no stuck: well-formed executions are final or
step; residue-row safety; payload typing: raised payload matches catalog
type; runner soundness/completeness/resume; pure-state discipline". 06 §15
(06:297): `runSteps(m+n,c) = continueSteps(n, runSteps(m,c))`.

This segment proves, premise-free over `ScmMachine`:
  determinism             → `scmStep_deterministic`, `scmStep_not_final`
  runner resume law       → `runLoopI_resume`
  runner soundness        → `runLoopI_done_sound` (a `done` result after k
                            budget units is reached by `SCMRuns` from c)
  runner completeness     → `runLoopI_complete` (an n-step run to a final
                            configuration is `done` at every budget ≥ n)
Preservation and payload typing hold for `Config S T` / `Final S T` by their
types (a step maps `Config S T` to `Config S T`; `Final.raised` carries the
catalog proof and a `CoreVal` of that payload type); no theorem is stated for
them here because the statement would restate the type. The substantive 06
preservation clause — a raw configuration that a typed one erases to steps to
the erasure of the typed step — is the raw↔intrinsic simulation, a later K3
segment. Progress and no-stuck are `ScmProgress` / `ScmNoStuck`.
-/
import rcic.ScmMachine

namespace Rcic.Scm.Theorems
open Rcic.Scm

variable {S : Sig} {T : CoreTy} (prog : Bodies S S.fns)

/-- 06 §16 determinism: the next configuration is unique. -/
theorem scmStep_deterministic {c c₁ c₂ : Config S T} :
    SCMStep prog c c₁ → SCMStep prog c c₂ → c₁ = c₂
  | ⟨h₁, _⟩, ⟨h₂, _⟩ => StepResult.next.inj (h₁.symm.trans h₂)

/-- 06 §16 determinism: a configuration that steps has no final outcome. -/
theorem scmStep_not_final {c c' : Config S T} {o : Final S T} :
    SCMStep prog c c' → stepI prog c ≠ .final o
  | ⟨h, _⟩, hf => StepResult.noConfusion (h.symm.trans hf)

/-- 06 §5 "A reported-residue value never triggers handlers": a returned
    value (whatever its type, a sum included) pops a `handleF` frame without
    entering the handler. -/
theorem returned_passes_handler {Γ : List CoreTy} {A P B T : CoreTy} (r : RaisedRef)
    (h : catalogPt S.catalog r = some P) (env : CoreVals Γ) (hd : CoreExpr S (P :: Γ) A)
    (v : CoreVal A) (rest : Cont S A T) :
    retI prog v (.cons (.handleF r h env hd) rest) = .next ⟨A, .retC v, rest⟩ := rfl

/-- One unfolding of the runner. -/
theorem runLoopI_eq (c : Config S T) (left : Nat) (s : Int) :
    runLoopI prog c left s =
      match stepI prog c with
      | .integrity code => .integrity code
      | .final o => .done o s
      | .next c' => match left with
        | 0 => .suspended c s
        | l + 1 => runLoopI prog c' l (s + 1) := by
  cases left <;> rfl

/-- Continue a run result by `n` more units (06 §15 `continueSteps`). -/
def continueI (n : Nat) : RunI S T → RunI S T
  | .suspended c k => runLoopI prog c n k
  | r => r

/-- 06:297 the resume law: running `m + n` units is running `m`, then
    continuing a suspension by `n`. -/
theorem runLoopI_resume : ∀ (m n : Nat) (c : Config S T) (s : Int),
    runLoopI prog c (m + n) s = continueI prog n (runLoopI prog c m s)
  | 0, n, c, s => by
    rw [Nat.zero_add, runLoopI_eq prog c 0 s]
    cases h : stepI prog c with
    | integrity code => rw [runLoopI_eq prog c n s, h]; rfl
    | final o => rw [runLoopI_eq prog c n s, h]; rfl
    | next c' => rfl
  | m + 1, n, c, s => by
    rw [Nat.succ_add, runLoopI_eq prog c (m + n + 1) s, runLoopI_eq prog c (m + 1) s]
    cases h : stepI prog c with
    | integrity code => rfl
    | final o => rfl
    | next c' => exact runLoopI_resume m n c' (s + 1)

/-- 06 §16 runner soundness: a `done (final o)` result is reached from `c`
    by `SCMRuns`, and the final configuration's step is that outcome. -/
theorem runLoopI_done_sound : ∀ (left : Nat) (c : Config S T) (s : Int) (o : Final S T) (k : Int),
    runLoopI prog c left s = .done o k →
    ∃ (n : Nat) (cf : Config S T), SCMRuns prog n c cf ∧ stepI prog cf = .final o
  | 0, c, s, o, k, hr => by
    rw [runLoopI_eq prog c 0 s] at hr
    revert hr
    cases h : stepI prog c with
    | integrity code => intro hr; exact RunI.noConfusion hr
    | final o' => intro hr; exact ⟨0, c, .refl c, h.trans (congrArg StepResult.final (RunI.done.inj hr).1)⟩
    | next c' => intro hr; exact RunI.noConfusion hr
  | l + 1, c, s, o, k, hr => by
    rw [runLoopI_eq prog c (l + 1) s] at hr
    revert hr
    cases h : stepI prog c with
    | integrity code => intro hr; exact RunI.noConfusion hr
    | final o' => intro hr; exact ⟨0, c, .refl c, h.trans (congrArg StepResult.final (RunI.done.inj hr).1)⟩
    | next c' =>
      intro hr
      match runLoopI_done_sound l c' (s + 1) o k hr with
      | ⟨n, cf, hrun, hf⟩ => exact ⟨n + 1, cf, .step h hrun, hf⟩

/-- 06 §16 runner completeness: an execution of `n` steps to a final
    configuration is reported `done` by the runner at every budget `≥ n`,
    with step count `n`. -/
theorem runLoopI_complete {o : Final S T} :
    ∀ {n : Nat} {c cf : Config S T}, SCMRuns prog n c cf → stepI prog cf = .final o →
    ∀ (m : Nat), n ≤ m → ∀ (s : Int), runLoopI prog c m s = .done o (s + n)
  | _, _, _, .refl cf, hf, m, _, s => by
      rw [runLoopI_eq prog cf m s, hf, Int.ofNat_zero, Int.add_zero]
  | _, _, _, .step (n := n) (c' := c') hs hr, hf, m, hnm, s => by
      cases m with
      | zero => exact absurd hnm (Nat.not_succ_le_zero n)
      | succ m =>
        rw [runLoopI_eq prog _ (m + 1) s, hs]
        show runLoopI prog c' m (s + 1) = _
        rw [runLoopI_complete hr hf m (Nat.le_of_succ_le_succ hnm) (s + 1)]
        have e : s + 1 + (n : Int) = s + ((n + 1 : Nat) : Int) := by
          rw [Int.natCast_add, Int.add_assoc, Int.add_comm 1 (n : Int)]
          rfl
        rw [e]

/-- 06 §15 front-door refusals at the raw runner (`Raw.run`, the function
    `scmCore` form 1 dispatches to): the budget is checked before any step.
    A negative budget is refused `[rcic_scm_core_budget]` — the
    `ScmMachinePins` `-1` row's law. -/
theorem scmCore_budget_refuse (p : RawProg) (c : Raw.Config) {n : Int} :
    n < 0 → Raw.run p c n = Raw.refuse "[rcic_scm_core_budget]" := by
  intro h; unfold Raw.run; rw [if_pos h]

/-- 06 §15's upper bound: a step budget above 4096 is refused
    `[rcic_scm_core_bound]` before any step — the bound check is
    unconditional, independent of program or configuration. This is the
    `ScmMachinePins` `4097` row's law. -/
theorem scmCore_bound_refuse (p : RawProg) (c : Raw.Config) {n : Int} :
    n > 4096 → Raw.run p c n = Raw.refuse "[rcic_scm_core_bound]" := by
  intro h
  unfold Raw.run
  rw [if_neg (by omega : ¬ n < 0), if_pos h]

/-! ## Instance witnesses (M-005) -/

namespace Witness
def five : CoreVal .i64 := .i64V 5 ⟨by decide, by decide⟩
def S0 : Sig := ⟨[], [], []⟩
def c0 : Config S0 .i64 := ⟨.i64, .evalC .nil (.lit five), .nil⟩
def c1 : Config S0 .i64 := ⟨.i64, .retC five, .nil⟩
example : c1 = c1 := scmStep_deterministic (S := S0) (c := c0) .nil ⟨rfl, trivial⟩ ⟨rfl, trivial⟩
example : stepI (S := S0) .nil c0 ≠ .final (.returned five) := scmStep_not_final (S := S0) (c := c0) .nil ⟨rfl, trivial⟩
example : runLoopI (S := S0) .nil c0 (1 + 2) 0 = continueI (S := S0) .nil 2 (runLoopI (S := S0) .nil c0 1 0) :=
  runLoopI_resume (S := S0) .nil 1 2 c0 0
example : ∃ (n : Nat) (cf : Config S0 .i64), SCMRuns (S := S0) .nil n c0 cf ∧ stepI (S := S0) .nil cf = .final (.returned five) :=
  runLoopI_done_sound (S := S0) .nil 4 c0 0 (.returned five) 1 rfl
example : runLoopI (S := S0) .nil c0 4 0 = .done (.returned five) (0 + (1 : Nat)) :=
  runLoopI_complete (S := S0) .nil (.step (c := c0) (c' := c1) rfl (.refl c1)) rfl 4 (by decide) 0
example : retI (S := ⟨[], [], [⟨"r", .i64⟩]⟩) (T := .i64) .nil five
    (.cons (.handleF "r" rfl .nil (.lit five)) .nil) = .next ⟨.i64, .retC five, .nil⟩ :=
  returned_passes_handler (S := ⟨[], [], [⟨"r", .i64⟩]⟩) (B := .i64) .nil "r" rfl .nil (.lit five) five .nil
end Witness

end Rcic.Scm.Theorems

/-
RM-022 / RM-023 — the SCM↔reference refinement bridge
(docs/rcic/03_REFERENCE_MACHINE.md §15: "RM-022 SCM implementation step
refines reference step", "RM-023 SCM implementation acceptance refines
reference acceptance").

Objects, both landed: the SCM side is 06's intrinsic machine
(`Rcic.Scm.stepI` / `runLoopI` / `SCMRuns`, `ScmMachine`, with the runner
soundness/completeness of `ScmTheorems`); the reference side is 03's
`kernelStepRaw` / `runRaw` with the resumable carrier `runRawR` of
`RcicMachineResume`. A `done` run's kind-24 wire member is
`ScmBoundBridge.finOf` under `runResultRel` (`RM023_wire_member`).

- `ScmImpl` — an SCM implementation of the reference: program, the
  encoding of a reference state as an initial SCM configuration, and the
  reading of an SCM final outcome as a reference verdict.
- `StepRefines I D R` — RM-022 as a stuttering forward simulation on a
  request domain `D`: every SCM step is a reference stutter or one
  `kernelStepRaw` step, and an SCM final step at `R s c` reads as exactly
  `kernelStepRaw s`'s result.
- RM-023, proved FROM RM-022:
  * `RM023_outcome_refines` — a `done o` SCM run decodes to a verdict the
    reference reaches (`runRawR m s = .done (decode o)`);
  * `RM023_accept_refines` — SCM acceptance ⇒ reference acceptance with
    the same payload;
  * `RM023_unsound` — the UNSOUND direction: the reference refuses ⇒ the
    SCM implementation does not accept (at any budget, any payload);
  * `RM023_verdict_exact` — every non-suspended reference verdict is the
    exact decoded SCM outcome;
  * `RM023_accept_complete` / `RM023_accept_iff` — the converse, modulo
    `ImplTerminates` (06 §14 has no fuel-out outcome, but no landed
    theorem makes an arbitrary SCM program halt).

Premise scope, stated: no SCM program implementing `kernelStepRaw` exists
in `lean/` (the `ScmSrcGroups*` modules run the reference ON scm source
environments; they are not an SCM implementation OF it), so RM-022 enters
as the hypothesis `StepRefines`, and RM-023 is conditional on it. The
witnesses at the end show the hypothesis is satisfiable on a domain where
the reference both accepts and refuses, and that an always-accepting
implementation is refuted by `RM023_unsound`.

Carrier link: `apps/rcic-scm-refinement` refuses
`[rcic_scm_ref_unsound]` on "reference refused ∧ typed accepts";
`RM023_unsound` is the Lean statement that this row is unreachable under
step refinement. `closure_claim = 0`.
-/
import rcic.ScmTheorems
import rcic.ScmBoundBridge
import rcic.RcicMachineResume

namespace Rcic.ScmRefinement

open Rcic.Machine Rcic.Scm

/-! ## Reference reachability over `kernelStepRaw` -/

/-- `n` reference steps from `s` to `s'`. -/
inductive RefRuns : Nat → RawState → RawState → Prop
  | refl (s : RawState) : RefRuns 0 s s
  | step {n : Nat} {s s' s'' : RawState} :
      kernelStepRaw s = .step s' → RefRuns n s' s'' → RefRuns (n + 1) s s''

theorem runRawR_succ_step (k : Nat) {s s' : RawState} (h : kernelStepRaw s = .step s') :
    runRawR (k + 1) s = runRawR k s' := by
  simp only [runRawR, h]

theorem runRawR_succ_result (k : Nat) {s : RawState} {r : RunResult}
    (h : kernelStepRaw s = .result r) : runRawR (k + 1) s = .done r := by
  simp only [runRawR, h]

/-- A reference run of `m` steps to a state that decides `r` is a resumable
run `done r` at budget `m + 1`. -/
theorem runRawR_of_refRuns {r : RunResult} :
    ∀ {m : Nat} {s s' : RawState}, RefRuns m s s' → kernelStepRaw s' = .result r →
      runRawR (m + 1) s = .done r
  | _, _, _, .refl _, hf => runRawR_succ_result 0 hf
  | _, _, _, .step (n := n) hs hr, hf => by
      rw [runRawR_succ_step (n + 1) hs]
      exact runRawR_of_refRuns hr hf

/-- On the landed reference (one-shot: `kernelStepRaw_never_step`) every
reference run is empty. -/
theorem refRuns_landed {m : Nat} {s s' : RawState} (h : RefRuns m s s') :
    m = 0 ∧ s' = s := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step hs _ => exact absurd hs (kernelStepRaw_never_step _ _)

/-! ## Verdict stability and uniqueness over the resumable carrier -/

theorem runRawR_done_stable {m : Nat} {s : RawState} {r : RunResult}
    (h : runRawR m s = .done r) (n : Nat) : runRawR (m + n) s = .done r := by
  rw [RM004_run_decompose m n s, h]
  rfl

/-- One reference verdict per state, across all budgets. -/
theorem runRawR_done_unique {m m' : Nat} {s : RawState} {r r' : RunResult}
    (h : runRawR m s = .done r) (h' : runRawR m' s = .done r') : r = r' := by
  have e1 := runRawR_done_stable h m'
  have e2 := runRawR_done_stable h' m
  rw [Nat.add_comm m' m, e1] at e2
  exact RunResumable.done.inj e2

/-- A non-suspended landed verdict is a terminal resumable verdict. -/
theorem runRawR_of_runRaw {m : Nat} {s : RawState} {r : RunResult}
    (h : runRaw m s = r) (hne : r ≠ .suspended) : runRawR m s = .done r := by
  rw [← runRawR_forget] at h
  cases hr : runRawR m s with
  | done r' =>
    rw [hr] at h
    exact congrArg RunResumable.done h
  | suspended s' =>
    rw [hr] at h
    exact absurd h.symm hne

/-! ## RM-022: SCM implementation step refines reference step -/

/-- An SCM implementation of the reference machine. -/
structure ScmImpl where
  S : Sig
  T : CoreTy
  prog : Bodies S S.fns
  encode : RawState → Config S T
  decode : Final S T → RunResult

/-- RM-022 on request domain `D`, as a stuttering forward simulation `R`
between reference states and SCM configurations. -/
structure StepRefines (I : ScmImpl) (D : RawState → Prop)
    (R : RawState → Config I.S I.T → Prop) : Prop where
  init : ∀ {s : RawState}, D s → R s (I.encode s)
  next : ∀ {s : RawState} {c c' : Config I.S I.T}, R s c → stepI I.prog c = .next c' →
    R s c' ∨ ∃ s', kernelStepRaw s = .step s' ∧ R s' c'
  final : ∀ {s : RawState} {c : Config I.S I.T} {o : Final I.S I.T}, R s c →
    stepI I.prog c = .final o → kernelStepRaw s = .result (I.decode o)

/-- An `n`-step SCM execution from a related configuration is matched by at
most `n` reference steps, ending related. -/
theorem refines_runs {I : ScmImpl} {D : RawState → Prop} {R : RawState → Config I.S I.T → Prop}
    (h : StepRefines I D R) :
    ∀ {n : Nat} {c cf : Config I.S I.T}, SCMRuns I.prog n c cf →
      ∀ {s : RawState}, R s c → ∃ m s', m ≤ n ∧ RefRuns m s s' ∧ R s' cf
  | _, _, _, .refl _, s, hR => ⟨0, s, Nat.zero_le _, .refl s, hR⟩
  | _, _, _, .step hs hr, _, hR =>
    match h.next hR hs with
    | .inl hR' =>
      match refines_runs h hr hR' with
      | ⟨m, s', hm, hrr, hR''⟩ => ⟨m, s', Nat.le_succ_of_le hm, hrr, hR''⟩
    | .inr ⟨_, hk, hR'⟩ =>
      match refines_runs h hr hR' with
      | ⟨m, s', hm, hrr, hR''⟩ => ⟨m + 1, s', Nat.succ_le_succ hm, .step hk hrr, hR''⟩

/-! ## RM-023: SCM implementation acceptance refines reference acceptance -/

/-- SCM acceptance: the runner reports `done o` at some budget and `o` reads
as `accepted p`. -/
def ImplAccepts (I : ScmImpl) (s : RawState) (p : AcceptedPayload) : Prop :=
  ∃ (left : Nat) (st k : Int) (o : Final I.S I.T),
    runLoopI I.prog (I.encode s) left st = .done o k ∧ I.decode o = .accepted p

/-- The SCM execution from `encode s` reaches a final configuration. -/
def ImplTerminates (I : ScmImpl) (s : RawState) : Prop :=
  ∃ (n : Nat) (cf : Config I.S I.T) (o : Final I.S I.T),
    SCMRuns I.prog n (I.encode s) cf ∧ stepI I.prog cf = .final o

variable {I : ScmImpl} {D : RawState → Prop} {R : RawState → Config I.S I.T → Prop}

/-- Every `done` SCM outcome decodes to a verdict the reference reaches. -/
theorem RM023_outcome_refines (h : StepRefines I D R) {s : RawState} (hs : D s)
    {left : Nat} {st k : Int} {o : Final I.S I.T}
    (hr : runLoopI I.prog (I.encode s) left st = .done o k) :
    ∃ m, runRawR m s = .done (I.decode o) := by
  obtain ⟨n, cf, hruns, hf⟩ :=
    Rcic.Scm.Theorems.runLoopI_done_sound I.prog left (I.encode s) st o k hr
  obtain ⟨m, _, _, hrr, hR⟩ := refines_runs h hruns (h.init hs)
  exact ⟨m + 1, runRawR_of_refRuns hrr (h.final hR hf)⟩

/-- RM-023: SCM acceptance ⇒ reference acceptance, same payload. -/
theorem RM023_accept_refines (h : StepRefines I D R) {s : RawState} (hs : D s)
    {p : AcceptedPayload} (ha : ImplAccepts I s p) : ∃ m, runRaw m s = .accepted p := by
  obtain ⟨_, _, _, o, hr, hd⟩ := ha
  obtain ⟨m, hm⟩ := RM023_outcome_refines h hs hr
  refine ⟨m, ?_⟩
  rw [← runRawR_forget, hm, hd]
  rfl

/-- Every non-suspended reference verdict is the exact decoded outcome of
every `done` SCM run. -/
theorem RM023_verdict_exact (h : StepRefines I D R) {s : RawState} (hs : D s)
    {k : Nat} {r : RunResult} (hk : runRaw k s = r) (hne : r ≠ .suspended)
    {left : Nat} {st k' : Int} {o : Final I.S I.T}
    (hr : runLoopI I.prog (I.encode s) left st = .done o k') : I.decode o = r := by
  obtain ⟨m, hm⟩ := RM023_outcome_refines h hs hr
  exact runRawR_done_unique hm (runRawR_of_runRaw hk hne)

/-- RM-023, the UNSOUND direction: if the reference refuses, the SCM
implementation accepts at no budget and with no payload. -/
theorem RM023_unsound (h : StepRefines I D R) {s : RawState} (hs : D s)
    {k : Nat} {res : String} (hk : runRaw k s = .refused res) (p : AcceptedPayload) :
    ¬ ImplAccepts I s p := by
  intro ha
  obtain ⟨_, _, _, o, hr, hd⟩ := ha
  have e := RM023_verdict_exact h hs hk (fun e => nomatch e) hr
  rw [hd] at e
  exact nomatch e

/-- Reference refusal is reproduced exactly: every `done` SCM run decodes to
the same refusal residue. -/
theorem RM023_refused_exact (h : StepRefines I D R) {s : RawState} (hs : D s)
    {k : Nat} {res : String} (hk : runRaw k s = .refused res)
    {left : Nat} {st k' : Int} {o : Final I.S I.T}
    (hr : runLoopI I.prog (I.encode s) left st = .done o k') : I.decode o = .refused res :=
  RM023_verdict_exact h hs hk (fun e => nomatch e) hr

/-- The converse of RM-023 modulo termination: reference acceptance and a
halting SCM execution give SCM acceptance with the same payload. -/
theorem RM023_accept_complete (h : StepRefines I D R) {s : RawState} (hs : D s)
    (ht : ImplTerminates I s) {k : Nat} {p : AcceptedPayload}
    (hk : runRaw k s = .accepted p) : ImplAccepts I s p := by
  obtain ⟨n, cf, o, hruns, hf⟩ := ht
  have hr := Rcic.Scm.Theorems.runLoopI_complete I.prog hruns hf n (Nat.le_refl n) 0
  exact ⟨n, 0, _, o, hr, RM023_verdict_exact h hs hk (fun e => nomatch e) hr⟩

/-- RM-023 both directions on a terminating request. -/
theorem RM023_accept_iff (h : StepRefines I D R) {s : RawState} (hs : D s)
    (ht : ImplTerminates I s) (p : AcceptedPayload) :
    ImplAccepts I s p ↔ ∃ k, runRaw k s = .accepted p :=
  ⟨RM023_accept_refines h hs, fun ⟨_, hk⟩ => RM023_accept_complete h hs ht hk⟩

/-- The kind-24 member of a final SCM configuration is `finOf` of that
outcome (`ScmBoundBridge.runResultRel_of_done`), and step refinement
reads the outcome as `kernelStepRaw`'s verdict. -/
theorem RM023_wire_member (h : StepRefines I D R) {s : RawState}
    {c : Config I.S I.T} {o : Final I.S I.T}
    (hR : R s c) (hfin : IsFinalConfig c o) (hst : stepI I.prog c = .final o) :
    Rcic.Scm.BoundExec.runResultRel c 0
        (Rcic.Scm.CfgWire.CX.fin (Rcic.Scm.BoundBridge.finOf o)) ∧
      kernelStepRaw s = .result (I.decode o) :=
  ⟨Rcic.Scm.BoundBridge.runResultRel_of_done c o hfin, h.final hR hst⟩

/-! ## Instance witnesses (M-005)

`levelImpl` covers the `levelEqual` slice at positive budget. Its encoder
places the verdict bit as a literal, so it is a satisfiability witness for
`StepRefines` (the reference both accepts and refuses on its domain), not
an SCM implementation of `decEqN`. `alwaysImpl` accepts every request; the
unsound direction refutes it at the `param 0 ≠ param 1` state. -/

namespace Witness

open Rcic.Declarative

def S0 : Sig := ⟨[], [], []⟩

def levelBit (s : RawState) : Bool :=
  match s.task with
  | .levelEqual l1 l2 => decEqN l1 l2
  | _ => false

def bitCfg (b : Bool) : Config S0 .bool := ⟨.bool, .evalC .nil (.lit (.boolV b)), .nil⟩
def bitRet (b : Bool) : Config S0 .bool := ⟨.bool, .retC (.boolV b), .nil⟩

def levelDecode : Final S0 .bool → RunResult
  | .returned (.boolV b) =>
    bif b then .accepted .conversionConfirmed else .refused "[rcic_level_not_equal]"
  | .raised _ _ _ => .integrity "[rcic_scm_core_row_safety]"

def levelImpl : ScmImpl := ⟨S0, .bool, .nil, fun s => bitCfg (levelBit s), levelDecode⟩

def levelDom (s : RawState) : Prop :=
  ∃ l1 l2 b, s.task = .levelEqual l1 l2 ∧ s.budget = b + 1

def levelRel (s : RawState) (c : Config S0 .bool) : Prop :=
  levelDom s ∧ (c = bitCfg (levelBit s) ∨ c = bitRet (levelBit s))

theorem level_kernel {s : RawState} (hd : levelDom s) :
    kernelStepRaw s = .result (levelDecode (.returned (.boolV (levelBit s)))) := by
  obtain ⟨l1, l2, b, ht, hb⟩ := hd
  have hbit : levelBit s = decEqN l1 l2 := by simp only [levelBit, ht]
  rw [hbit]
  cases hdec : decEqN l1 l2 with
  | true =>
    simp only [kernelStepRaw, hb, ht, hdec, if_pos rfl, levelDecode, if_true, Bool.cond_true]
  | false =>
    have hneq : ¬ (decEqN l1 l2 = true) := by
      rw [hdec]
      intro h
      cases h
    simp only [kernelStepRaw, hb, ht, if_neg hneq, levelDecode, Bool.cond_false]

theorem levelImpl_refines : StepRefines levelImpl levelDom levelRel where
  init hd := ⟨hd, Or.inl rfl⟩
  next := by
    intro s c c' hR hs
    obtain ⟨hd, rfl | rfl⟩ := hR
    · have hs' : (StepResult.next (bitRet (levelBit s)) : StepResult S0 .bool) = .next c' := hs
      exact Or.inl ⟨hd, Or.inr (StepResult.next.inj hs').symm⟩
    · have hs' : (StepResult.final (.returned (.boolV (levelBit s))) : StepResult S0 .bool)
          = .next c' := hs
      exact StepResult.noConfusion hs'
  final := by
    intro s c o hR hs
    obtain ⟨hd, rfl | rfl⟩ := hR
    · have hs' : (StepResult.next (bitRet (levelBit s)) : StepResult S0 .bool) = .final o := hs
      exact StepResult.noConfusion hs'
    · have hs' : (StepResult.final (.returned (.boolV (levelBit s))) : StepResult S0 .bool)
          = .final o := hs
      cases StepResult.final.inj hs'
      exact level_kernel hd

theorem levelImpl_terminates (s : RawState) : ImplTerminates levelImpl s :=
  ⟨1, bitRet (levelBit s), .returned (.boolV (levelBit s)), .step rfl (.refl _), rfl⟩

/-- The wire member of `levelImpl`'s final configuration is the outcome
the reference reaches on the levelEqual slice. -/
theorem levelImpl_wire {s : RawState} (hd : levelDom s) :
    Rcic.Scm.BoundExec.runResultRel (bitRet (levelBit s)) 0
        (Rcic.Scm.CfgWire.CX.fin
          (Rcic.Scm.BoundBridge.finOf (S := S0)
            (.returned (S := S0) (.boolV (levelBit s))))) ∧
      kernelStepRaw s = .result (levelDecode (.returned (.boolV (levelBit s)))) :=
  RM023_wire_member levelImpl_refines ⟨hd, Or.inr rfl⟩ rfl rfl

/-- The reference refuses `param 0 =?= param 1` (RM-011), so `levelImpl`
accepts it at no budget. -/
theorem levelImpl_param01_not_accepted (amb : Ambient) (p : AcceptedPayload) :
    ¬ ImplAccepts levelImpl ⟨amb, .levelEqual (.param 0) (.param 1), 1⟩ p :=
  RM023_unsound levelImpl_refines ⟨.param 0, .param 1, 0, rfl, rfl⟩ (k := 1)
    (by
      show runRaw 1 ⟨amb, .levelEqual (.param 0) (.param 1), 1⟩ =
        .refused "[rcic_level_not_equal]"
      simp only [runRaw, RM011_param0_param1_refused amb])
    p

/-- Every `eqN` pair is accepted by `levelImpl` (RM-023 converse with
`RM011_levelEqual_complete`). -/
theorem levelImpl_accepts_eqN (amb : Ambient) (l1 l2 : Level) (b : Nat) (heq : eqN l1 l2) :
    ImplAccepts levelImpl ⟨amb, .levelEqual l1 l2, b + 1⟩ .conversionConfirmed :=
  RM023_accept_complete levelImpl_refines ⟨l1, l2, b, rfl, rfl⟩ (levelImpl_terminates _)
    (k := 1)
    (by
      show runRaw 1 ⟨amb, .levelEqual l1 l2, b + 1⟩ = .accepted .conversionConfirmed
      simp only [runRaw, RM011_levelEqual_complete amb l1 l2 b heq])

def alwaysImpl : ScmImpl :=
  ⟨S0, .bool, .nil, fun _ => bitCfg true, fun _ => .accepted .conversionConfirmed⟩

/-- Tooth: an implementation that accepts everything refines the reference
on no domain containing the `param 0 ≠ param 1` request, whatever the
simulation. -/
theorem alwaysImpl_not_refines (amb : Ambient) (R : RawState → Config S0 .bool → Prop) :
    ¬ StepRefines alwaysImpl (· = ⟨amb, .levelEqual (.param 0) (.param 1), 1⟩) R := by
  intro h
  exact RM023_unsound h rfl (k := 1)
    (by
      show runRaw 1 ⟨amb, .levelEqual (.param 0) (.param 1), 1⟩ =
        .refused "[rcic_level_not_equal]"
      simp only [runRaw, RM011_param0_param1_refused amb])
    .conversionConfirmed ⟨1, 0, 1, .returned (.boolV true), rfl, rfl⟩

end Witness

#print axioms runRawR_succ_step
#print axioms runRawR_succ_result
#print axioms runRawR_of_refRuns
#print axioms refRuns_landed
#print axioms runRawR_done_stable
#print axioms runRawR_done_unique
#print axioms runRawR_of_runRaw
#print axioms refines_runs
#print axioms RM023_outcome_refines
#print axioms RM023_accept_refines
#print axioms RM023_verdict_exact
#print axioms RM023_unsound
#print axioms RM023_refused_exact
#print axioms RM023_accept_complete
#print axioms RM023_accept_iff
#print axioms RM023_wire_member
#print axioms Witness.level_kernel
#print axioms Witness.levelImpl_refines
#print axioms Witness.levelImpl_terminates
#print axioms Witness.levelImpl_wire
#print axioms Witness.levelImpl_param01_not_accepted
#print axioms Witness.levelImpl_accepts_eqN
#print axioms Witness.alwaysImpl_not_refines

end Rcic.ScmRefinement

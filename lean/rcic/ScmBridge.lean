/-
RCIC — the intrinsic ↔ first-order SIMULATION for steps, runs and entry
(#6029 K3, segment 8). This is the first-order half of the 06 §19 bridge's
skeleton, NOT the 06 §19 bridge (SCM-016/017/018): that bridge is stated over
the §18 predicates on bound refs and canonical bytes, which stay NOT
TRANSCRIBED until #6029 K3c (K3 HOLD item 1).

Owner text (06:405-417): "intrinsic SCMStep → SCMStepAt; SCMStepAt →
intrinsic SCMStep; intrinsic SCMRuns → SCMRunsAt; SCMRunsAt → intrinsic
SCMRuns; entry initialization/final-outcome correspondence."

`RawStepAt` / `RawRunsAt` are the raw-layer relations of `ScmRawRelations`
over first-order configurations (`Raw.Config` records). The encoding of the
06 §18 objects is decided (#6029 K2: the §17 core-wire family); these are not
those objects. The first-order step is
`Raw.step`, pinned to the carrier `rcic-scm-core`. Every theorem below is
over an elaborated program: `hp : Bodies.erasures prog = p.fns.map body`
(`ElabErase.elabBodies_erase` supplies it).

The carrier's 2048-scalar primitive string bound (`ScmSim` header) is the one
place the first-order step refuses where the typed one steps; the run
theorems carry it as an explicit hypothesis `hns` (no reachable configuration
is refused by it), never as a hidden assumption.
-/
import rcic.ScmSim
import rcic.ScmRowSafety

namespace Rcic.Scm.Bridge
open Rcic.Scm Rcic.Scm.Sim Rcic.Scm.Erase Rcic.Scm.ElabErase

variable {S : Sig} (p : RawProg) (prog : Bodies S S.fns) (hp : Bodies.erasures prog = p.fns.map RawFnDef.body)
include hp

/-- Simulation, first-order analogue of 06 §19 (intrinsic SCMStep → SCMStepAt (read on the first-order machine):)
    a typed step's erasures are related by the first-order step, up to the
    carrier's string bound. -/
theorem stepAt_of_step {T : CoreTy} {r r' : Raw.Config} (h : RawRel.RawStepAt (T := T) prog r r') :
    Raw.step p r = Raw.next r' ∨ Raw.step p r = Raw.stuck := by
  obtain ⟨c, c', hc, hc', ⟨hs, _⟩⟩ := h
  subst hc; subst hc'
  exact step_sim p prog hp c c' hs

/-- Simulation, first-order analogue of 06 §19 (SCMStepAt → intrinsic SCMStep: a first-order step out of a)
    configuration that a well-formed typed one erases to is a typed step. -/
theorem step_of_stepAt {T : CoreTy} (c : Config S T) (hne : c.WF)
    (r' : Raw.Config) (hs : Raw.step p c.erase = Raw.next r') :
    ∃ c' : Config S T, SCMStep prog c c' ∧ c'.erase = r' := by
  cases Progress.progress prog c hne with
  | inl hn =>
    obtain ⟨c', hc'⟩ := hn
    cases step_sim p prog hp c c' hc' with
    | inl he =>
      rw [he] at hs
      exact ⟨c', ⟨hc', trivial⟩, congrArg Raw.Out.config hs⟩
    | inr hst =>
      rw [hst] at hs
      have h' : (0 : Int) = 1 := congrArg Raw.Out.ok hs
      exact absurd h' (by decide)
  | inr hf =>
    obtain ⟨o, ho⟩ := hf
    rw [final_sim p prog c o ho] at hs
    cases o with
    | returned v =>
      have h' : (1 : Int) = 0 := congrArg Raw.Out.kind hs
      exact absurd h' (by decide)
    | raised rr _ v =>
      have h' : (2 : Int) = 0 := congrArg Raw.Out.kind hs
      exact absurd h' (by decide)

/-- `n` first-order steps. -/
inductive RawRuns : Nat → Raw.Config → Raw.Config → Prop where
  | refl (r : Raw.Config) : RawRuns 0 r r
  | step {n : Nat} {r r' r'' : Raw.Config} : Raw.step p r = Raw.next r' → RawRuns n r' r'' → RawRuns (n + 1) r r''

/-- Simulation, first-order analogue of 06 §19 (intrinsic SCMRuns → SCMRunsAt: a typed run is the first-order run)
    of the erasures, when no reachable configuration hits the carrier's
    string bound. -/
theorem rawRuns_of_runs {T : CoreTy} :
    ∀ {n : Nat} {c c' : Config S T}, SCMRuns prog n c c' →
    (∀ (m : Nat) (d : Config S T), SCMRuns prog m c d → Raw.step p d.erase ≠ Raw.stuck) →
    RawRuns p n c.erase c'.erase
  | _, _, _, .refl c, _ => .refl c.erase
  | _, c, _, .step (c' := c₁) hs hr, hns => by
    have h1 : Raw.step p c.erase = Raw.next c₁.erase := by
      cases step_sim p prog hp c c₁ hs with
      | inl he => exact he
      | inr hst => exact absurd hst (hns 0 c (.refl c))
    exact .step h1 (rawRuns_of_runs hr (fun m d hd => hns (m + 1) d (.step hs hd)))

/-- Simulation, first-order analogue of 06 §19 (SCMRunsAt → intrinsic SCMRuns: a first-order run out of a)
    well-formed typed configuration is a typed run. -/
theorem runs_of_rawRuns (hpn : prog.WF) {T : CoreTy} :
    ∀ {n : Nat} {r r' : Raw.Config}, RawRuns p n r r' → ∀ (c : Config S T), c.erase = r → c.WF →
    ∃ c' : Config S T, SCMRuns prog n c c' ∧ c'.erase = r'
  | _, _, _, .refl _, c, hc, _ => ⟨c, .refl c, hc⟩
  | _, _, _, .step hs hr, c, hc, hne => by
    subst hc
    obtain ⟨c₁, ⟨h1, _⟩, he1⟩ := step_of_stepAt p prog hp c hne _ hs
    obtain ⟨c', hrun, he'⟩ := runs_of_rawRuns hpn hr c₁ he1 (NoStuck.stepI_wf prog hpn c c₁ hne h1)
    exact ⟨c', .step h1 hrun, he'⟩

/-- Simulation, first-order analogue of 06 §19 (entry initialization: the typed entry configuration erases to the)
    first-order entry configuration `eval args body` (the one `Raw.entry`
    runs), for elaborated arguments. -/
theorem entry_init (i : Nat) (f : FnSig) (hf : S.fns.get? i = some f) (args : List Val)
    (env : CoreVals f.params) (henv : toCoreVals f.params args = some env) :
    ∃ fd : RawFnDef, p.fns.get? i = some fd ∧
      (⟨f.result, .evalC env (prog.at i f hf), .nil⟩ : Config S f.result).erase = ⟨.evalC args fd.body, []⟩ := by
  obtain ⟨fd, hfd, hbody⟩ := body_at_erase p prog hp i f hf
  refine ⟨fd, hfd, ?_⟩
  show (⟨.evalC env.erase (prog.at i f hf).erase, []⟩ : Raw.Config) = ⟨.evalC args fd.body, []⟩
  rw [toCoreVals_erase _ args env henv, hbody]

/-- Simulation, first-order analogue of 06 §19 (final-outcome correspondence: a typed final outcome is the)
    first-order final outcome of the erased configuration (`Sim.final_sim`). -/
theorem final_corr {T : CoreTy} (c : Config S T) (o : Final S T) (h : stepI prog c = .final o) :
    Raw.step p c.erase = finalOut o :=
  final_sim p prog c o h

/-- 06 §16 payload typing, on the first-order outcome: a final raised outcome
    reports the erased payload, and that payload elaborates at the catalog
    payload type of its ref. -/
theorem raw_payload_typed {T P : CoreTy} (c : Config S T) (r : RaisedRef) (hP : catalogPt S.catalog r = some P)
    (v : CoreVal P) (h : stepI prog c = .final (.raised r hP v)) :
    Raw.step p c.erase = Raw.final 2 v.erase r ∧ catalogPt S.catalog r = some P ∧ valOfTy v.erase P = true := by
  refine ⟨final_sim p prog c _ h, hP, ?_⟩
  unfold valOfTy
  rw [erase_toCore v]
  rfl

omit hp in
/-- 06 §16 pure-state discipline: the machine has no external effect — an
    external call is never executed, it is the integrity refusal (and the
    step is a function of the configuration alone, `Theorems.scmStep_deterministic`). -/
theorem external_call_refused {Γ : List CoreTy} {T : CoreTy} (env : CoreVals Γ) (r : String) (e : ExtSig)
    (hx : S.ext.find? (fun x => x.ref == r) = some e) (args : Args S Γ e.params) (k : Cont S e.result T) :
    evalI prog env (.call (.external r e hx) args) k = .integrity "[rcic_scm_core_external_call]" := rfl

/-! ## Instance witnesses (M-005) -/

namespace Witness
open Rcic.Scm.NoStuck.Witness Rcic.Scm.Sim.Witness
example : ∃ c' : Config S1 .i64, SCMRuns (S := S1) .nil 1 c0 c' ∧ c'.erase = c1.erase :=
  runs_of_rawRuns (S := S1) P1 .nil rfl trivial (.step (r := c0.erase) (r' := c1.erase) rfl (.refl _)) c0 rfl ⟨trivial, trivial⟩
example : Raw.step P1 c0.erase = Raw.next c1.erase ∨ Raw.step P1 c0.erase = Raw.stuck :=
  stepAt_of_step (S := S1) (T := .i64) P1 .nil rfl ⟨c0, c1, rfl, rfl, rfl, trivial⟩
section
open Rcic.Scm.RowSafety.Witness
def P2 : RawProg := ⟨[⟨[], unitTy, body.erase⟩], [], [⟨"bad_input", unitTy⟩], 0⟩
example : Raw.step P2 c3.erase = Raw.final 2 unitV.erase "bad_input" ∧
    catalogPt S2.catalog "bad_input" = some unitTy ∧ valOfTy unitV.erase unitTy = true :=
  raw_payload_typed (S := S2) P2 prog2 rfl c3 "bad_input" rfl unitV rfl
end
def S3 : Sig := ⟨[], [⟨"ext.len", [.str], .i64⟩], []⟩
example : evalI (S := S3) (T := .i64) .nil .nil (.call (.external "ext.len" ⟨"ext.len", [.str], .i64⟩ rfl)
    (.cons (.lit (.strV "abc")) .nil)) .nil = .integrity "[rcic_scm_core_external_call]" :=
  external_call_refused (S := S3) .nil .nil "ext.len" ⟨"ext.len", [.str], .i64⟩ rfl _ .nil
end Witness

end Rcic.Scm.Bridge

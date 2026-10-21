/-
Shared big-step view of the SCM machine (`run` / `runEntry`).

`run` is the value `Raw.runLoop` returns. It is not a second evaluator.
`run_agrees_runLoopI` says that on every typed program, a `runLoopI` that
returns a value is that same value erased, provided each `stepI` next-step
is the raw next-step. `Sim.step_sim` gives next or the carrier's
`primBound` stuck refusal; `step_next_of_not_stuck` is that disjunct.
`run_agrees_runLoopI_of_erasures` discharges that premise from
`Bodies.erasures`. The residual is the refusal (`Raw.stuck`, not `.next`).
`returned` and `runEntry` are definitions (a value projection and an entry
lookup), not propositions, so they are not sealed.
`closure_claim` stays 0.
-/
import rcic.ScmSim
import rcic.ScmTheorems

namespace Rcic.Scm.Run
open Rcic.Scm

def returned (o : Raw.Out) : Option Val :=
  if o.ok = 1 ∧ o.kind = 1 then some o.v else none

/-- Value of `e` in `env` under `p`, if the runner returns one. -/
def run (fuel : Nat) (p : RawProg) (env : List Val) (e : RawExpr) : Option Val :=
  returned (Raw.runLoop p ⟨.evalC env e, []⟩ fuel 0)

/-- Entry body of `p` on `args` (argument 0 at de Bruijn 0). -/
def runEntry (fuel : Nat) (p : RawProg) (args : List Val) : Option Val :=
  if 0 ≤ p.entry then
    match p.fns.get? p.entry.toNat with
    | some fd => run fuel p args fd.body
    | none => none
  else none

theorem runEntry_eq (fuel : Nat) (p : RawProg) (args : List Val)
    (h0 : 0 ≤ p.entry) (fd : RawFnDef)
    (hfd : p.fns.get? p.entry.toNat = some fd) :
    runEntry fuel p args = run fuel p args fd.body := by
  unfold runEntry
  rw [if_pos h0, hfd]

theorem step_next_of_not_stuck
    {S : Sig} (p : RawProg) (prog : Bodies S S.fns)
    (hp : ElabErase.Bodies.erasures prog = p.fns.map RawFnDef.body)
    {T : CoreTy} {c c' : Config S T}
    (h : stepI prog c = .next c')
    (hn : Raw.step p c.erase ≠ Raw.stuck) :
    Raw.step p c.erase = Raw.next c'.erase := by
  cases Sim.step_sim p prog hp c c' h with
  | inl hnext => exact hnext
  | inr hstuck => exact absurd hstuck hn

private theorem runLoop_stop (p : RawProg) (c c' : Raw.Config) (steps : Int)
    (hs : Raw.step p c = Raw.next c') :
    Raw.runLoop p c 0 steps = Raw.runRes 3 c unitRaw "" steps := by
  conv => lhs; unfold Raw.runLoop
  rw [hs]
  simp only [Raw.next]
  rw [if_neg (by decide : ¬ ((1 : Int) = 0)), if_true]

private theorem runLoop_go (p : RawProg) (c c' : Raw.Config) (l : Nat) (steps : Int)
    (hs : Raw.step p c = Raw.next c') :
    Raw.runLoop p c (l + 1) steps = Raw.runLoop p c' l (steps + 1) := by
  conv => lhs; unfold Raw.runLoop
  rw [hs]
  simp only [Raw.next]
  rw [if_neg (by decide : ¬ ((1 : Int) = 0)), if_true]

private theorem runLoop_done
    {S : Sig} (p : RawProg) (prog : Bodies S S.fns) {T : CoreTy}
    (c : Config S T) (o : Final S T) (left : Nat) (steps : Int)
    (h : stepI prog c = .final o) :
    Raw.runLoop p c.erase left steps = (RunI.done o steps).toOut := by
  have hs : Raw.step p c.erase = Sim.finalOut o := Sim.final_sim p prog c o h
  cases o with
  | returned v =>
    unfold Raw.runLoop
    rw [hs]
    simp only [Sim.finalOut, Raw.final]
    rw [if_neg (by decide : ¬ ((1 : Int) = 0))]
    rw [if_neg (by decide : ¬ ((1 : Int) = 0))]
    rw [if_neg (by decide : ¬ ((1 : Int) = 2))]
    rfl
  | raised r _ v =>
    unfold Raw.runLoop
    rw [hs]
    simp only [Sim.finalOut, Raw.final]
    rw [if_neg (by decide : ¬ ((1 : Int) = 0))]
    rw [if_neg (by decide : ¬ ((2 : Int) = 0))]
    rw [if_true]
    rfl

/-- `Raw.runLoop` is `runLoopI` on every configuration reachable from `c0`
whose next-steps are raw next-steps, when the run is not an integrity
residue. -/
theorem runLoop_agrees
    {S : Sig} (p : RawProg) (prog : Bodies S S.fns) {T : CoreTy}
    (left : Nat) (c0 : Config S T) (steps : Int)
    (hok : ∀ {n : Nat} {c' : Config S T}, SCMRuns prog n c0 c' →
      ∀ c'', stepI prog c' = .next c'' →
        Raw.step p c'.erase = Raw.next c''.erase)
    (hnot : ∀ code, runLoopI prog c0 left steps ≠ .integrity code) :
    Raw.runLoop p c0.erase left steps = (runLoopI prog c0 left steps).toOut := by
  induction left generalizing c0 steps hok with
  | zero =>
    cases hstep : stepI prog c0 with
    | integrity code =>
      exact absurd (by rw [Theorems.runLoopI_eq prog c0 0 steps, hstep]) (hnot code)
    | final o =>
      have hI : runLoopI prog c0 0 steps = .done o steps := by
        rw [Theorems.runLoopI_eq prog c0 0 steps, hstep]
      rw [hI]
      exact runLoop_done p prog c0 o 0 steps hstep
    | next c1 =>
      have hraw := hok (SCMRuns.refl c0) c1 hstep
      have hI : runLoopI prog c0 0 steps = .suspended c0 steps := by
        rw [Theorems.runLoopI_eq prog c0 0 steps, hstep]
      rw [hI]
      exact runLoop_stop p c0.erase c1.erase steps hraw
  | succ l ih =>
    cases hstep : stepI prog c0 with
    | integrity code =>
      exact absurd (by rw [Theorems.runLoopI_eq prog c0 (l + 1) steps, hstep]) (hnot code)
    | final o =>
      have hI : runLoopI prog c0 (l + 1) steps = .done o steps := by
        rw [Theorems.runLoopI_eq prog c0 (l + 1) steps, hstep]
      rw [hI]
      exact runLoop_done p prog c0 o (l + 1) steps hstep
    | next c1 =>
      have hraw := hok (SCMRuns.refl c0) c1 hstep
      have hI : runLoopI prog c0 (l + 1) steps = runLoopI prog c1 l (steps + 1) := by
        rw [Theorems.runLoopI_eq prog c0 (l + 1) steps, hstep]
      have hnot1 : ∀ code, runLoopI prog c1 l (steps + 1) ≠ .integrity code := by
        intro code hbad
        exact hnot code (hI.trans hbad)
      have hok1 : ∀ {n : Nat} {c' : Config S T}, SCMRuns prog n c1 c' →
          ∀ c'', stepI prog c' = .next c'' →
            Raw.step p c'.erase = Raw.next c''.erase := by
        intro n c' hrun c'' hs
        exact hok (SCMRuns.step hstep hrun) c'' hs
      rw [runLoop_go p c0.erase c1.erase l steps hraw, hI]
      exact ih c1 (steps + 1) hok1 hnot1

/-- On every typed program, a returning `runLoopI` is `run` of the
erased expression. `hok` is `stepI`'s next-step along this run. -/
theorem run_agrees_runLoopI
    {S : Sig} {Γ : List CoreTy} {T : CoreTy}
    (p : RawProg) (prog : Bodies S S.fns)
    (env : CoreVals Γ) (e : CoreExpr S Γ T)
    (left : Nat) (v : CoreVal T) (k : Int)
    (hok : ∀ {n : Nat} {c' : Config S T},
      SCMRuns prog n ⟨T, .evalC env e, .nil⟩ c' →
      ∀ c'', stepI prog c' = .next c'' →
        Raw.step p c'.erase = Raw.next c''.erase)
    (hr : runLoopI prog ⟨T, .evalC env e, .nil⟩ left 0 = .done (.returned v) k) :
    run left p env.erase e.erase = some v.erase := by
  have hnot : ∀ code, runLoopI prog ⟨T, .evalC env e, .nil⟩ left 0 ≠ .integrity code := by
    intro code hbad
    rw [hbad] at hr
    exact RunI.noConfusion hr
  have hloop := runLoop_agrees p prog left ⟨T, .evalC env e, .nil⟩ 0 hok hnot
  have herase :
      (⟨T, .evalC env e, .nil⟩ : Config S T).erase =
        (⟨.evalC env.erase e.erase, []⟩ : Raw.Config) := rfl
  rw [hr, herase] at hloop
  simp only [run, returned]
  rw [hloop]
  simp only [RunI.toOut, Raw.runRes]
  rw [if_pos (And.intro trivial trivial)]

/-- `hok` from the erasure pin. `Sim.step_sim` gives a raw next-step or
the carrier's `primBound` refusal. That refusal is `Raw.stuck`, not
`Raw.next`, so `hbound` is the residual: no reachable next-step is it. -/
theorem run_agrees_runLoopI_of_erasures
    {S : Sig} {Γ : List CoreTy} {T : CoreTy}
    (p : RawProg) (prog : Bodies S S.fns)
    (hp : ElabErase.Bodies.erasures prog = p.fns.map RawFnDef.body)
    (env : CoreVals Γ) (e : CoreExpr S Γ T)
    (left : Nat) (v : CoreVal T) (k : Int)
    (hbound : ∀ {n : Nat} {c' : Config S T},
      SCMRuns prog n ⟨T, .evalC env e, .nil⟩ c' →
      ∀ c'', stepI prog c' = .next c'' →
        Raw.step p c'.erase ≠ Raw.stuck)
    (hr : runLoopI prog ⟨T, .evalC env e, .nil⟩ left 0 = .done (.returned v) k) :
    run left p env.erase e.erase = some v.erase := by
  refine run_agrees_runLoopI p prog env e left v k ?_ hr
  intro n c' hrun c'' hs
  exact step_next_of_not_stuck p prog hp hs (hbound hrun c'' hs)

#print axioms Rcic.Scm.Run.runEntry_eq
#print axioms Rcic.Scm.Run.step_next_of_not_stuck
#print axioms runLoop_stop
#print axioms runLoop_go
#print axioms runLoop_done
#print axioms Rcic.Scm.Run.runLoop_agrees
#print axioms Rcic.Scm.Run.run_agrees_runLoopI
#print axioms Rcic.Scm.Run.run_agrees_runLoopI_of_erasures

end Rcic.Scm.Run

/-
M3 — 06 §18 execution predicates `SCMStepAt` / `SCMRunsAt` / `EntryRunsAt`
(06:397-399) as R-CIC propositions over bound references and canonical
bytes, on the K3b carriers.

§18 names the three predicates with no signatures (`[spec_ambiguity]` —
recorded in `ScmBoundProgramAt`); they are transcribed mirroring
`ScmRawRelations.lean`'s `RawStepAt`/`RawRunsAt`/`EntryRunsAt`, with the
wire values replaced by existentially-quantified typed configurations whose
`erase`/`cfgToRaw` agree on both sides, per 06 §18's "bound objects +
canonical bytes" statement form:

* `SCMStepAt(P, ri, bi, ro, bo)` — the program checks at some fuel
  (`progCheck`, as `ProgramAt`'s closure carries it), both endpoints are
  `ConfigAt`s of `P.prog`, their decodes `cfgToRaw`-erase to the typed
  endpoints, and the intrinsic `SCMStep` holds.
* `SCMRunsAt(P, n, ri, bi, rr, br)` — same setup, `SCMRuns` `n` steps to
  `c'`, and the kind-24 member `runResultRel`-relates to `c'`: done
  members carry a `finalErase`-equal outcome (`IsFinalConfig`), suspended
  members carry `c'`'s raw form (the config `runRes` reports).
* `EntryRunsAt(P, argBytes, n, rr, br)` — the entry function exists in
  `P`'s signature, every argument byte-string is a `ValueAt` at its
  parameter type, and `SCMRuns` runs the typed entry configuration to the
  result's member.

Each ∃-predicate ships with its tooth (`…_step_refused`,
`…_arity_refused`, `…_valueAt_refused`, the member-shape eliminators and
the `RawRuns` endpoint correspondence) next to the corpus pins, per the
review rule that existential predicates carry substantive refusal
theorems.

Nat-count discipline: `RawStepAt`/`RawRunsAt` count `Nat` steps and the
shadow (`scmStepAtDec`/`scmRunsAtDec`/`entryRunsAtDec`) mirrors them
natively over `Raw.step`/`Raw.run`/`Raw.entry` — the Bool shadows are the
natively-checkable half of the proposition (they assert the raw machine's
concrete outcome agrees with the claimed wire objects); a `false` shadow
on a concrete non-stuck step *is* a genuine refusal
(`scmStepAt_step_refused`), while a `true` shadow does not itself prove
the ∃-typed proposition, which needs the typed witnesses.

Pins are in `BoundExec.Pins`: real `rcic-scm-core` corpus rows —
cfgO0's step to its `letF`-binding eval, the done run cfgO23 → B118
(`.i 5` in 5 steps), the suspended run cfgO23 → B119 (member `cfgO0`),
and `Raw.entry`'s 11-step `done1 (.i 3)` on the bound corpus program —
plus refusal mutants beside each.
-/

import rcic.ScmBoundConfig
import rcic.ScmBoundProgramAt
import rcic.ScmBoundCoreTV
import rcic.ScmBridge

namespace Rcic.Scm.BoundExec
open Rcic.Scm Rcic.Scm.Wire Rcic.BoundObject Rcic.Scm.Raw Rcic.Scm.CfgWire
open Rcic.Scm.BoundCfg Rcic.Scm.BoundProgAt Rcic.Scm.BoundTV
open Rcic.Scm.Sim Rcic.Scm.Bridge Rcic.Scm.RawRel Rcic.Scm.ElabErase

section
variable {profile : String}

/-- The kind-24 member relation at a run's endpoint `c'`: a done member
    claims a final outcome of `c'` with the `finToRaw`-exact raw
    `(kind, v, r)`; a suspended member claims `c'`'s raw configuration —
    the config `Raw.runLoop`'s `runRes` reports when the step budget is
    exhausted.  `runToRaw`-invalid members relate to nothing. -/
def runResultRel {S : Sig} {T : CoreTy} (c' : Config S T) (tag : Int) (m : CX) : Prop :=
  match runToRaw tag m with
  | some (.done k v r) => ∃ o : Final S T, IsFinalConfig c' o ∧ finalErase o = (k, v, r)
  | some (.suspended rc) => rc = c'.erase
  | none => False

/-- 06 §18 `SCMStepAt` (06:397, `[spec_ambiguity]` — the spec names the
    predicate without a signature; this is the `RawStepAt`-mirrored
    reading): `P`'s form-3 closure checks at some fuel, both refs are
    `ConfigAt`s of `P.prog`, their kind-22 decodes erase to the typed
    endpoints, and the intrinsic `SCMStep` holds. -/
def SCMStepAt {profile : String} (P : BoundCoreProgram profile)
    (ri : Ref) (bi : String) (ro : Ref) (bo : String) : Prop :=
  ∃ T : CoreTy, ∃ c c' : Config (sigOf P.prog) T,
  ∃ out : Σ' (_ : Bodies (sigOf P.prog) (sigOf P.prog).fns), CoreTy,
  ∃ F : Int, ∃ ci co : CfgO,
    progCheck F P.prog = .ok out ∧
    ConfigAt P.prog ri bi ∧ cfgSchema.decode bi = some ci ∧ cfgToRaw ci = c.erase ∧
    ConfigAt P.prog ro bo ∧ cfgSchema.decode bo = some co ∧ cfgToRaw co = c'.erase ∧
    SCMStep out.1 c c'

/-- 06 §18 `SCMRunsAt` (06:398): the `RawRunsAt`-mirrored reading — `P`
    checks, the initial config is `ConfigAt`, the kind-24 result is
    `RunResultAt`, its member `runResultRel`-relates to the typed
    endpoint, and `SCMRuns` holds for exactly `n` steps. -/
def SCMRunsAt {profile : String} (P : BoundCoreProgram profile) (n : Nat)
    (ri : Ref) (bi : String) (rr : Ref) (br : String) : Prop :=
  ∃ T : CoreTy, ∃ c c' : Config (sigOf P.prog) T,
  ∃ out : Σ' (_ : Bodies (sigOf P.prog) (sigOf P.prog).fns), CoreTy,
  ∃ F : Int, ∃ ci : CfgO, ∃ tag : Int, ∃ m : CX,
    progCheck F P.prog = .ok out ∧
    ConfigAt P.prog ri bi ∧ cfgSchema.decode bi = some ci ∧ cfgToRaw ci = c.erase ∧
    RunResultAt P.prog rr br ∧ runSchema.decode br = some (tag, m) ∧
    runResultRel c' tag m ∧ SCMRuns out.1 n c c'

/-- The entry-argument condition: the byte count matches the parameter
    count and each argument's bytes are a `ValueAt` at its parameter
    type, under some bound kind-16 type object (`argsValueAt` —
    `rawToCore`'s wire-side half). -/
def argsValueAt (params : List CoreTy) (argBytes : List String) : Prop :=
  argBytes.length = params.length ∧
  ∀ i : Fin argBytes.length, ∃ Tb : BoundCoreType, ∃ pt : CoreTy,
    params.get? i.val = some pt ∧ Tb.ty = pt ∧ ValueAt Tb argBytes[i.val]

/-- 06 §18 `EntryRunsAt` (06:399): the 07 §7 five-place reading — `P`
    checks, its entry function exists in the signature, the arguments are
    `ValueAt`s at the entry parameter types, the kind-24 result is
    `RunResultAt` whose member `runResultRel`-relates to the endpoint,
    and `SCMRuns` runs the typed entry configuration (`evalC env` over
    the elaborated body, `entry_init`'s typed form) `n` steps to it. -/
def EntryRunsAt {profile : String} (P : BoundCoreProgram profile)
    (argBytes : List String) (n : Nat) (rr : Ref) (br : String) : Prop :=
  ∃ out : Σ' (_ : Bodies (sigOf P.prog) (sigOf P.prog).fns), CoreTy,
  ∃ F : Int, ∃ ef : FnSig,
  ∃ hf : (sigOf P.prog).fns.get? P.prog.entry.toNat = some ef,
  ∃ env : CoreVals ef.params, ∃ c' : Config (sigOf P.prog) ef.result,
  ∃ tag : Int, ∃ m : CX,
    progCheck F P.prog = .ok out ∧
    argsValueAt ef.params argBytes ∧
    RunResultAt P.prog rr br ∧ runSchema.decode br = some (tag, m) ∧
    runResultRel c' tag m ∧
    SCMRuns out.1 n ⟨ef.result, .evalC env (out.1.at P.prog.entry.toNat ef hf), .nil⟩ c'

/-! ## Executable shadows -/

/-- Native check that a kind-24 member matches a concrete `Raw.run`
    outcome: done members must equal the reported `(kind, v, r)`;
    suspended members must equal the reported configuration. -/
def runResultOk (o : Raw.Out) (tag : Int) (m : CX) : Bool :=
  match runToRaw tag m with
  | some (.done k v r) => o.ok == 1 && o.kind == k && o.v == v && o.r == r
  | some (.suspended rc) => o.ok == 1 && o.kind == 3 && o.config == rc
  | none => false

/-- `SCMStepAt`'s natively-checkable half at `fuel`: the program checks,
    both objects are `ConfigAt`s, and `Raw.step` on the decoded input
    takes the decoded output — a `next` exactly to `cfgToRaw co`
    (`Raw.stuck` cannot be confirmed natively: it is the carrier's
    string-bound case, `step_sim`'s second disjunct). -/
def scmStepAtDec (fuel : Int) (P : RawProg) (ri : Ref) (bi : String)
    (ro : Ref) (bo : String) : Bool :=
  (progCheck fuel P).toOption.isSome && configAtB P ri bi && configAtB P ro bo &&
    match cfgSchema.decode bi, cfgSchema.decode bo with
    | some ci, some co =>
      let s := Raw.step P (cfgToRaw ci)
      s.ok == 1 && s.kind == 0 && s.config == cfgToRaw co
    | _, _ => false

/-- `SCMRunsAt`'s natively-checkable half: `Raw.run` `n` steps ends in a
    result the kind-24 member's `runResultOk` confirms at exactly `n`
    counted steps. -/
def scmRunsAtDec (fuel : Int) (P : RawProg) (n : Nat) (ri : Ref) (bi : String)
    (rr : Ref) (br : String) : Bool :=
  (progCheck fuel P).toOption.isSome && configAtB P ri bi && runResultAtB P rr br &&
    match cfgSchema.decode bi, runSchema.decode br with
    | some ci, some (tag, m) =>
      let o := Raw.run P (cfgToRaw ci) (n : Int)
      o.ok == 1 && o.steps == some (n : Int) && runResultOk o tag m
    | _, _ => false

/-- `EntryRunsAt`'s natively-checkable half: the arguments decode to raw
    values and `Raw.entry` `n` steps ends in the result the member
    confirms. -/
def entryRunsAtDec (fuel : Int) (P : RawProg) (argBytes : List String)
    (n : Nat) (rr : Ref) (br : String) : Bool :=
  runResultAtB P rr br &&
    match runSchema.decode br with
    | some (tag, m) =>
      let args := argBytes.filterMap valueBytesAt
      args.length == argBytes.length &&
      (let o := Raw.entry fuel P args (n : Int)
       o.ok == 1 && o.steps == some (n : Int) && runResultOk o tag m)
    | _ => false

/-! ## Consequences and teeth -/

/-- `runToRaw` on a done member is `finToRaw`'s triple. -/
theorem runToRaw_fin (f : FinO) :
    runToRaw 0 (.fin f) =
      some (.done (finToRaw f).1 (finToRaw f).2.1 (finToRaw f).2.2) := rfl

/-- `runToRaw` on a suspended member (`tag ≠ 0`) is the member's raw
    configuration — `cfgToRaw`'s erasure. -/
theorem runToRaw_suspended {tag : Int} {c : CfgO} (hne : tag ≠ 0) :
    runToRaw tag (.cfg c) = some (.suspended (cfgToRaw c)) := by
  simp [runToRaw, hne]

/-- `progCheck` acceptance supplies the body-erasure `step_sim` needs:
    the elaborated bodies erase to the raw bodies. -/
theorem progCheck_bodies_erase {p : RawProg} {F : Int}
    {out : Σ' (_ : Bodies (sigOf p) (sigOf p).fns), CoreTy}
    (h : progCheck F p = .ok out) :
    Bodies.erasures out.1 = p.fns.map RawFnDef.body := by
  obtain ⟨_, _, _, _, _, he⟩ := progCheck_ok h
  exact elabBodies_erase _ _ _ _ he

/-- `SCMStepAt` forces `ConfigAt` on the input object. -/
theorem scmStepAt_configAt_in {P : BoundCoreProgram profile}
    (h : SCMStepAt P ri bi ro bo) : ConfigAt P.prog ri bi := by
  obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ := h
  exact hc

/-- `SCMStepAt` forces `ConfigAt` on the output object. -/
theorem scmStepAt_configAt_out {P : BoundCoreProgram profile}
    (h : SCMStepAt P ri bi ro bo) : ConfigAt P.prog ro bo := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, _⟩ := h
  exact hc

/-- `SCMStepAt`'s raw-step consequence: `Raw.step` on the claimed input's
    `cfgToRaw` either steps to the claimed output's `cfgToRaw` or hits
    the carrier's string bound (`Raw.stuck`) — `step_sim` under the
    form-3 closure's `progCheck` evidence. -/
theorem scmStepAt_step_out {P : BoundCoreProgram profile}
    (h : SCMStepAt P ri bi ro bo) :
    ∃ ci co : CfgO, cfgSchema.decode bi = some ci ∧ cfgSchema.decode bo = some co ∧
      (Raw.step P.prog (cfgToRaw ci) = Raw.next (cfgToRaw co) ∨
       Raw.step P.prog (cfgToRaw ci) = Raw.stuck) := by
  obtain ⟨_, _, _, out, _, ci, co, hpc, _, hd, he, _, hdo, heo, hst⟩ := h
  refine ⟨ci, co, hd, hdo, ?_⟩
  have hp := progCheck_bodies_erase hpc
  have sim := step_sim P.prog out.1 hp _ _ hst.1
  rw [← he, ← heo] at sim
  exact sim

/-- The step tooth: when `Raw.step` on the claimed input is a concrete
    step to a *different* configuration — or anything else concrete —
    `SCMStepAt` cannot hold. -/
theorem scmStepAt_step_refused {P : BoundCoreProgram profile}
    (hdi : cfgSchema.decode bi = some ci) (hdo : cfgSchema.decode bo = some co)
    (hne : Raw.step P.prog (cfgToRaw ci) ≠ Raw.next (cfgToRaw co))
    (hns : Raw.step P.prog (cfgToRaw ci) ≠ Raw.stuck) :
    ¬ SCMStepAt P ri bi ro bo := by
  intro h
  obtain ⟨_, _, hd', hdo', hor⟩ := scmStepAt_step_out h
  rw [hdi] at hd'; cases hd'
  rw [hdo] at hdo'; cases hdo'
  exact hor.elim hne hns

/-- `SCMRunsAt` forces `ConfigAt` on the input object. -/
theorem scmRunsAt_configAt {P : BoundCoreProgram profile}
    (h : SCMRunsAt P n ri bi rr br) : ConfigAt P.prog ri bi := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hc, _⟩ := h
  exact hc

/-- `SCMRunsAt` forces `RunResultAt` on the result object. -/
theorem scmRunsAt_runResultAt {P : BoundCoreProgram profile}
    (h : SCMRunsAt P n ri bi rr br) : RunResultAt P.prog rr br := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc, _⟩ := h
  exact hc

/-- The done-member eliminator: a kind-24 `.fin` member claims the
    endpoint has a final configuration with the `finToRaw`-exact raw
    outcome. -/
theorem scmRunsAt_done_final {P : BoundCoreProgram profile}
    (h : SCMRunsAt P n ri bi rr br)
    (hdr : runSchema.decode br = some (0, .fin f)) :
    ∃ T : CoreTy, ∃ c' : Config (sigOf P.prog) T, ∃ o : Final (sigOf P.prog) T,
      IsFinalConfig c' o ∧ finalErase o = finToRaw f := by
  obtain ⟨T, _, c', _, _, _, _, _, _, _, _, _, _, hdr', hrel, hst⟩ := h
  rw [hdr] at hdr'; cases hdr'
  refine ⟨T, c', ?_⟩
  unfold runResultRel at hrel
  rw [runToRaw_fin] at hrel
  dsimp only at hrel
  obtain ⟨o, hfin, he⟩ := hrel
  exact ⟨o, hfin, by simpa using he⟩

/-- The suspended-member eliminator: a kind-24 `.cfg` member is literally
    the endpoint's raw configuration — the config `runRes` reports. -/
theorem scmRunsAt_suspended_endpoint {P : BoundCoreProgram profile}
    (h : SCMRunsAt P n ri bi rr br)
    (hdr : runSchema.decode br = some (tag, .cfg c2)) (hne : tag ≠ 0) :
    ∃ T : CoreTy, ∃ c' : Config (sigOf P.prog) T, cfgToRaw c2 = c'.erase := by
  obtain ⟨T, _, c', _, _, _, _, _, _, _, _, _, _, hdr', hrel, hst⟩ := h
  rw [hdr] at hdr'; cases hdr'
  refine ⟨T, c', ?_⟩
  unfold runResultRel at hrel
  rw [runToRaw_suspended hne] at hrel
  dsimp only at hrel
  exact hrel

/-- The zero-step suspended tooth: a `0`-step suspended run must report
    the input configuration itself — a member that is not the input's
    `cfgToRaw` cannot hold. -/
theorem scmRunsAt_zero_suspended_refused {P : BoundCoreProgram profile}
    (hdi : cfgSchema.decode bi = some ci)
    (hdr : runSchema.decode br = some (tag, .cfg c2)) (hne : tag ≠ 0)
    (hneq : cfgToRaw c2 ≠ cfgToRaw ci) :
    ¬ SCMRunsAt P 0 ri bi rr br := by
  intro h
  obtain ⟨_, _, c', _, _, _, _, _, _, _, hd, he, _, hdr', hrel, hst⟩ := h
  rw [hdi] at hd; cases hd
  rw [hdr] at hdr'; cases hdr'
  cases hst
  unfold runResultRel at hrel
  rw [runToRaw_suspended hne] at hrel
  dsimp only at hrel
  exact hneq (hrel.trans he.symm)

/-- `SCMRunsAt`'s raw-chain consequence: under the semantic no-stuck
    premise (no reachable typed configuration hits the carrier's string
    bound), the decoded input's `cfgToRaw` runs `RawRuns` `n` steps to
    the endpoint's erasure — `rawRuns_of_runs` under the form-3 closure's
    `progCheck` evidence. -/
theorem scmRunsAt_raw_runs {P : BoundCoreProgram profile}
    (h : SCMRunsAt P n ri bi rr br) :
    ∃ T : CoreTy, ∃ c c' : Config (sigOf P.prog) T,
    ∃ out : Σ' (_ : Bodies (sigOf P.prog) (sigOf P.prog).fns), CoreTy,
    ∃ ci : CfgO, ∃ tag : Int, ∃ m : CX,
      cfgSchema.decode bi = some ci ∧ cfgToRaw ci = c.erase ∧
      runSchema.decode br = some (tag, m) ∧ runResultRel c' tag m ∧
      ((∀ m' (d : Config (sigOf P.prog) T), SCMRuns out.1 m' c d →
          Raw.step P.prog d.erase ≠ Raw.stuck) →
        RawRuns P.prog n (cfgToRaw ci) c'.erase) := by
  obtain ⟨T, c, c', out, _, ci, tag, m, hpc, _, hd, he, _, hdr, hrel, hst⟩ := h
  refine ⟨T, c, c', out, ci, tag, m, hd, he, hdr, hrel, fun hns => ?_⟩
  have hp := progCheck_bodies_erase hpc
  have hrr := rawRuns_of_runs P.prog out.1 hp hst hns
  rw [← he] at hrr
  exact hrr

/-- `RawRuns` is deterministic — the raw step is a function, so two
    `n`-step chains from one configuration reach one endpoint.  The
    endpoint tooth: a claimed suspended member that is not this endpoint
    cannot hold (with the no-stuck premise supplied to reach the
    `RawRuns`). -/
theorem rawRuns_deterministic {p : RawProg} {n : Nat} {r r₁ r₂ : Raw.Config}
    (h₁ : RawRuns p n r r₁) (h₂ : RawRuns p n r r₂) : r₁ = r₂ := by
  induction h₁ generalizing r₂ with
  | refl => cases h₂; rfl
  | step hs hr ih =>
    cases h₂ with
    | step hs' hr' =>
      rw [hs] at hs'; cases hs'
      exact ih hr'

/-- `EntryRunsAt` forces `RunResultAt` on the result object. -/
theorem entryRunsAt_runResultAt {P : BoundCoreProgram profile}
    (h : EntryRunsAt P argBytes n rr br) : RunResultAt P.prog rr br := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hc, _⟩ := h
  exact hc

/-- `EntryRunsAt` forces each argument to be a `ValueAt` at its
    parameter type — the argument tooth's positive half. -/
theorem entryRunsAt_arg_valueAt {P : BoundCoreProgram profile}
    (h : EntryRunsAt P argBytes n rr br)
    (hfn : (sigOf P.prog).fns.get? P.prog.entry.toNat = some ef)
    (i : Fin argBytes.length) :
    ∃ Tb : BoundCoreType, ∃ pt : CoreTy,
      ef.params.get? i.val = some pt ∧ Tb.ty = pt ∧ ValueAt Tb argBytes[i.val] := by
  obtain ⟨_, _, _, hf, _, _, _, _, _, hargs, _⟩ := h
  rw [hfn] at hf; cases hf
  exact hargs.2 i

/-- The arity tooth: the entry function's parameter count must equal the
    argument count. -/
theorem entryRunsAt_arity_refused {P : BoundCoreProgram profile}
    (hfn : (sigOf P.prog).fns.get? P.prog.entry.toNat = some ef)
    (hne : argBytes.length ≠ ef.params.length) :
    ¬ EntryRunsAt P argBytes n rr br := by
  intro h
  obtain ⟨_, _, _, hf, _, _, _, _, _, hargs, _⟩ := h
  rw [hfn] at hf; cases hf
  exact hne hargs.1

/-- The argument tooth: an argument that is no `ValueAt` at its
    parameter type refuses the whole `EntryRunsAt`. -/
theorem entryRunsAt_valueAt_refused {P : BoundCoreProgram profile}
    (hfn : (sigOf P.prog).fns.get? P.prog.entry.toNat = some ef)
    (i : Fin argBytes.length)
    (hbad : ∀ Tb : BoundCoreType, ∀ pt : CoreTy,
      ef.params.get? i.val = some pt → Tb.ty ≠ pt ∨ ¬ ValueAt Tb argBytes[i.val]) :
    ¬ EntryRunsAt P argBytes n rr br := by
  intro h
  obtain ⟨Tb, pt, hpt, hty, hv⟩ := entryRunsAt_arg_valueAt h hfn i
  obtain h | h := hbad Tb pt hpt
  · exact h hty
  · exact h hv

end

/-! ## Pins (real `rcic-scm-core` corpus rows) -/

namespace Pins

open Rcic.Scm Rcic.Scm.Wire Rcic.BoundObject Rcic.Scm.Raw Rcic.Scm.CfgWire
open Rcic.Scm.BoundCfg Rcic.Scm.BoundCfg.Pins Rcic.Scm.BoundProgAt
open Rcic.Scm.BoundTV Rcic.Scm.CfgAt.Pins

/-- The bound corpus program. -/
abbrev PRG : RawProg := Rcic.Scm.BoundProg.Pins.PROG

/-- The kind-22 decode against `Option CfgO` (named so the `==` in pins
    sees `BEq (Option CfgO)` rather than a `schema.Obj` projection; not
    `CfgWire.decCfg`, which is the `fuel → Except` wire decode). -/
def cfgDecW (b : String) : Option CfgO := cfgSchema.decode b

/-- The kind-24 decode against `Option (Int × CX)`. -/
def runDecW (b : String) : Option (Int × CX) := runSchema.decode b

/-- cfgO0's real next configuration: `letF` binds `5` and runs `add01` —
    `⟨evalC [.i 5] add01, []⟩`, the canonical bytes `cfgSchema.encode`
    produces for it (`Ci26:…;I5;…` — the `I4`-row `B23`'s sibling). -/
def cfgO0s : CfgO := ⟨I, ctlEval [I] [iv 5] add01, []⟩

/-- The corpus-level suspended-at-member check: `Raw.run` of `cfgO23`'s
    raw form with budget `3` suspends at exactly `cfgToRaw cfgO0` —
    corpus row 119 (`B119`) is that suspended member. -/
def Bstep : String := cfgSchema.encode cfgO0s

/-- `Bstep`'s bound ref. -/
def Rstep : Ref := rf Bstep 22

/-- The entry-run done result: `Raw.entry 256 PRG [] 11 = done1 (.i 3) 11`
    — `fin (1, .i 3, "")` as a kind-24 member. -/
def Bdone3 : String := runSchema.encode (0, .fin ⟨I, 0, [Vv (.i 3)]⟩)

/-- `Bdone3`'s bound ref. -/
def Rdone3 : Ref := rf Bdone3 24

/-- The entry-run suspended-at-0 result: `Raw.entry 256 PRG [] 0` reports
    the initial configuration — the member is that init `CfgO`. -/
def Bsusp0 : String := runSchema.encode (1, .cfg ⟨I, ctlEval [] [] (.call (.local 0) [li 1, li 2]), []⟩)

/-- `Bsusp0`'s bound ref. -/
def Rsusp0 : Ref := rf Bsusp0 24

-- The step target's canonical bytes decode back to `cfgO0s`, and its
-- ref binds — the `ConfigAt` side of the step pin is the corpus'
-- own byte discipline.
#guard cfgSchema.encode cfgO0s == "Ci26:0;1;i1;I5;f3:add2;10;0I1;i0;"
#guard cfgDecW Bstep == some cfgO0s

-- cfgO0's step is real: `retC 5` into a `letF` frame →
-- `evalC (5 :: []) add01`.
#guard Raw.step PRG (cfgToRaw cfgO0) == Raw.next ⟨.evalC [.i 5] add01, []⟩
#guard Raw.step PRG (cfgToRaw cfgO0) != Raw.next (cfgToRaw cfgO23)

-- The done run: `cfgO23`'s raw form runs `done1 (.i 5)` in `5` steps —
-- corpus row 118 (`B118` = `D1;37:<B110>`) is its `fin (1, .i 5, "")`
-- member, and `runSchema.encode` reproduces it byte-for-byte.
#guard (Raw.run PRG (cfgToRaw cfgO23) 5).v == .i 5
#guard (Raw.run PRG (cfgToRaw cfgO23) 5).steps == some 5
#guard runSchema.encode (0, .fin finO110) == B118
#guard runSchema.encode (1, .cfg cfgO0) == B119
#guard runDecW B118 == some (0, .fin finO110)
#guard runDecW B119 == some (1, .cfg cfgO0)

-- The suspended run: `Raw.run` of `cfgO0` with budget `0` suspends at
-- `cfgO0` itself with `steps = 0` — corpus row 119 is that member
-- (`runRes` reports the configuration stepped from, `runLoop` discards
-- the over-budget step). -/
#guard (Raw.run PRG (cfgToRaw cfgO0) 0).kind == 3
#guard (Raw.run PRG (cfgToRaw cfgO0) 0).config == cfgToRaw cfgO0
#guard (Raw.run PRG (cfgToRaw cfgO0) 0).steps == some 0

-- The entry run: `Raw.entry` on the bound corpus program runs to a
-- done-1 `.i 3` outcome in 11 counted transitions, and its budget-0
-- suspension reports the `evalC [] (local-0 call)` initial
-- configuration — the corpus' `D1;…` entry-done row shape.
#guard (Raw.entry 256 PRG [] 11).kind == 1
#guard (Raw.entry 256 PRG [] 11).v == .i 3
#guard (Raw.entry 256 PRG [] 11).steps == some 11
#guard (Raw.entry 256 PRG [] 0).kind == 3
#guard (Raw.entry 256 PRG [] 0).steps == some 0
#guard (Raw.entry 256 PRG [] 0).config ==
  ⟨.evalC [] (.call (.local 0) [li 1, li 2]), []⟩

-- Positive shadows.
#guard scmStepAtDec 256 PRG R0 B0 Rstep Bstep == true
#guard scmRunsAtDec 256 PRG 5 R23 B23 R118 B118 == true
#guard scmRunsAtDec 256 PRG 0 R0 B0 R119 B119 == true
#guard entryRunsAtDec 256 PRG [] 11 Rdone3 Bdone3 == true
#guard entryRunsAtDec 256 PRG [] 0 Rsusp0 Bsusp0 == true

-- Refusal pins: wrong step targets, wrong step counts, member-shape
-- mismatches, ref-binding violations and ill-typed entry args, all on
-- real corpus bytes.
#guard scmStepAtDec 256 PRG R0 B0 R23 B23 == false
#guard scmStepAtDec 256 PRG R23 B23 R0 B0 == false
#guard scmStepAtDec 256 PRG R0 B0 R23 Bstep == false
#guard scmRunsAtDec 256 PRG 6 R23 B23 R118 B118 == false
#guard scmRunsAtDec 256 PRG 5 R23 B23 R119 B119 == false
#guard scmRunsAtDec 256 PRG 4 R0 B0 R118 B118 == false
#guard entryRunsAtDec 256 PRG [] 10 Rdone3 Bdone3 == false
#guard entryRunsAtDec 256 PRG ["B1;"] 11 Rdone3 Bdone3 == false

/-- Step tooth at real corpus bytes: rows `B0`→`B23` both decode
    (the `hdi`/`hdo` premises — each `#guard`-verified beside the byte
    literals; the wire decode is kernel-opaque, so the corpus facts ride
    as hypotheses), but `B0`'s `letF`-binding step reaches
    `evalC (5 :: env) add01`, never `B23`'s `evalC (4 :: env)` —
    `SCMStepAt` cannot hold. -/
theorem scmStepAt_row0_row23_refused {profile : String}
    (P : BoundCoreProgram profile) (hprog : P.prog = PRG)
    (hdi : cfgSchema.decode B0 = some cfgO0)
    (hdo : cfgSchema.decode B23 = some cfgO23) :
    ¬ SCMStepAt P R0 B0 R23 B23 := by
  refine scmStepAt_step_refused hdi hdo ?_ ?_
  · rw [hprog]
    have hs : Raw.step PRG (cfgToRaw cfgO0)
        = Raw.next ⟨.evalC [.i 5] add01, []⟩ := by rfl
    rw [hs, cfgToRaw_row23]
    intro h
    have hc := congrArg Raw.Out.config h
    injection hc with hctl _
    injection hctl with henv _
    injection henv with hh _
    injection hh with h54
    exact absurd h54 (by decide)
  · rw [hprog]
    have hs : Raw.step PRG (cfgToRaw cfgO0)
        = Raw.next ⟨.evalC [.i 5] add01, []⟩ := by rfl
    rw [hs]
    intro h
    have hc := congrArg Raw.Out.ok h
    exact absurd hc (by decide)

/-- Runs tooth at real corpus bytes: `B119` decodes to the suspended
    member `cfg cfgO0` (`hdr`, `#guard`-verified), but a `0`-step
    suspended run must report the input configuration itself — and row
    `B23`'s input (`hdi`) is `evalC (4 :: env)`, not `retC 5` —
    `SCMRunsAt` cannot hold. -/
theorem scmRunsAt_zero_row23_member119_refused {profile : String}
    (P : BoundCoreProgram profile)
    (hdi : cfgSchema.decode B23 = some cfgO23)
    (hdr : runSchema.decode B119 = some (1, .cfg cfgO0)) :
    ¬ SCMRunsAt P 0 R23 B23 R119 B119 :=
  scmRunsAt_zero_suspended_refused hdi hdr (by decide)
    (by rw [cfgToRaw_row0, cfgToRaw_row23]
        intro h
        injection h with hctl _
        exact Raw.Ctl.noConfusion hctl)

/-- Entry tooth at real corpus bytes: `Bdone3` decodes to the done
    member `fin (1, .i 3, "")` (`hdr`, `#guard`-verified), but a `0`-step
    entry run ends at the entry's `evalC` initial configuration, which is
    final for no outcome — `EntryRunsAt` cannot hold. -/
theorem entryRunsAt_zero_done_member_refused {profile : String}
    (P : BoundCoreProgram profile)
    (hdr : runSchema.decode Bdone3 = some (0, .fin ⟨I, 0, [Vv (.i 3)]⟩)) :
    ¬ EntryRunsAt P [] 0 Rdone3 Bdone3 := by
  rintro ⟨out, F, ef, hf, env, c', tag, m, hpc, hargs, hrr, hdr', hrel, hst⟩
  cases hst
  rw [hdr] at hdr'
  cases hdr'
  unfold runResultRel at hrel
  rw [runToRaw_fin] at hrel
  obtain ⟨o, hfin, -⟩ := hrel
  nomatch hfin

end Pins
end Rcic.Scm.BoundExec

/-
WX bridge S2 segment 3 — L2 agreement with the bootstrap machine,
STATEMENTS ONLY (#6609 plan §2; cc ruling). Target: `stepWasm0Machine`
at `origin/bootstrap` `639a1cb1f0`, READ-ONLY.

Why abstract: the machine surface is NOT on main — measured (two
searches): main's `lean/Residua/Bootstrap/` carries only
`Wasm0Red.lean`; `Wasm0.lean`/`Wasm0Machine.lean` exist only on the
bootstrap branch. Until Codex lands the surface on main AND seals the
hand-back list (step/run/determinism + state-name stability, S2_PLAN
§"what L2 needs"), the agreement statements are quantified over an
abstract machine face whose vocabulary is pinned to the measured
surface at the ref:

- `Wasm0MachineStatus` (:2787): `running | returned (Option val) |
  residue reason | sourceFuelExhausted | validationFailure` — the
  step-level outcome here keeps the three machine-arm statuses;
  `sourceFuelExhausted` is run-level and `validationFailure` is
  unreachable from validated `Rel`-states; both exclusions are the S3
  companion lemma's job (a lemma, not an assumption baked here).
- `Wasm0MachineResidue` (:2771), 13 reasons; `mapReason` must cover
  the overlap `divisionByZero ↦ divZero`,
  `signedDivisionOverflow ↦ intOverflow`,
  `memoryOutOfBounds ↦ oobMemory` (the table's frozen profile traps).

No proofs of agreement here (S3+, gated on the Codex seals); nothing
assumed. `closure_claim = 0`.
-/
import rcic.RcicWasmNormStep

namespace Rcic.WasmNorm.WxL2

/-- Step-level outcome vocabulary for the abstract machine face,
mirroring `Wasm0MachineStatus@639a1cb1f0` (read-only): `steps st'` ↔
`.running` (machine advanced), `rets v` ↔ `.returned (Option val)`,
`traps r` ↔ `.residue reason`. -/
inductive Outcome (M V R : Type) where
  | steps (st' : M)
  | rets (v : Option V)
  | traps (r : R)
  deriving Repr

/-- L2 statement 2 (S2_PLAN): step agreement on the frozen profile.
`rel` is the state relation (canonical-initialized machines only);
`inProfile` is the shared frozen opcode profile; `mapOptVal`/`mapMem`/
`mapReason` translate the machine's observables to the normative
machine's `.ret`/`.trap` payload. -/
def stepAgreement (M V R : Type)
    (step : M → M) (outcome : M → Outcome M V R)
    (rel : M → NormState → Prop) (inProfile : M → Prop)
    (mapOptVal : Option V → Int) (mapMem : M → NormMemory)
    (mapReason : R → NormTrapReason) : Prop :=
  ∀ st s, inProfile st → rel st s →
    match outcome (step st) with
    | .steps st' => ∃ s', NormStep s = .step s' ∧ rel st' s'
    | .rets v => NormStep s = .ret (mapOptVal v) (mapMem st)
    | .traps r => NormStep s = .trap (mapReason r) s

/-- L2 statement 3 (S2_PLAN): run agreement at the outcome level, fuel
bookkeeping stated. `run fuel st` is the machine's bounded run (its
`finalState` at the ref); `final` plays the plan's `mapFinal`,
translating a non-running machine state to the normative `NormFinal`. -/
def runAgreement (M : Type)
    (run : Nat → M → M) (rel : M → NormState → Prop)
    (isRunning : M → Bool) (final : M → NormFinal) : Prop :=
  ∀ fuel st s, rel st s → isRunning (run fuel st) = false →
    ∃ fuel', NormSteps fuel' s = .done (final (run fuel st))

/-- L2 trap arm (BRIDGE_S0 (c)): the residue vocabulary and the
normative trap vocabulary agree through `mapReason` — each abstract
residue predicate holds exactly when the mapped normative trap does. -/
def trapAgreement (R : Type)
    (mapReason : R → NormTrapReason)
    (residuePred : R → Prop) (normTrapPred : NormTrapReason → Prop) : Prop :=
  ∀ r, residuePred r ↔ normTrapPred (mapReason r)

end Rcic.WasmNorm.WxL2

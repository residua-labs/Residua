import rcic.RcicMachine
import rcic.RcicTypedConv

/-!
# T1-T R-3 — the typed machine

Ruling R-3 (cc as architect, 2026-10-09): the typed acceptance rows
(`RM015T_infer_sound` / `RM016T_check_sound` step and run, in
`RcicTypedMachineAccept`) are restated against a TYPED machine whose
infer/check arms are built over the certified typed checkers, so the
ACCEPTANCE ITSELF carries the derivation. This module is that machine,
a new layer BESIDE the legacy one (`RcicMachine.lean`, not edited).

* `TypedTask` — the two task forms the acceptance rows need:
  `.inferT e` and `.checkT2 A e` (`checkT2` named to stay clear of the
  syntactic checker `checkT`, `RcicTypedCheck.lean:39`).
* `TypedAccepted amb` / `TypedResult amb` — the payload/result layer:
  an ACCEPTED payload IS the derivation (`.inferred e T d` with
  `d : HasTyT amb.env amb.univs amb.ctx e T`; `.checked e A d` with
  `d : HasTyT amb.env amb.univs amb.ctx e A` — `HasTyT` is Type-valued,
  `RcicDeclarative.lean:3184`, so the payload carries it directly); a
  refusal carries a NAMED residue.
* `typedStep` — the encoding function, mirroring `kernelStepRaw`'s
  shape (budget 0 suspends; the arms pass the budget to the certifier
  as fuel, exactly as the raw arms pass `s.budget`). The infer arm
  calls `checkC` — `inferC` is `checkC`'s type projection
  (`RcicTypedConv.lean:351`), discarding exactly the derivation the
  payload is for — and the check arm calls `tyAtC`, whose answer
  already IS the derivation (`CheckerT.der` pattern).
* `typedRun` — the run layer, mirroring `runRaw`'s shape. The typed
  machine is one-shot exactly as the raw one is
  (`kernelStepRaw_never_step`, `RcicMachine.lean:509` — the raw step
  outcome's `.step` ctor is never produced), so the recursion settles
  at `typedStep`.

REFUSALS (R-3 clause 5): when the certified checker answers `none`,
the arm refuses with a NAMED residue — `"[rcic_typed_infer_refused]"` /
`"[rcic_typed_check_refused]"`. These cover every input class the
typed checker does not reach (the ι/η/ζ/irrelevance/congruence slice
boundary recorded in `RcicTypedConv`'s own "What it does not do" note,
`RcicTypedConv.lean:37`). The certifiers are NOT widened and no
premises are added; the gaps come back in the segment report.

closure_claim 0; axioms within {propext, Quot.sound}.
-/

namespace Rcic.Machine

open Rcic.Declarative

/-! ## the typed task and state -/

/-- The typed machine's task forms — only the two the acceptance rows
    consume (infer, check). -/
inductive TypedTask : Type
  | inferT (e : Expr Nat)
  | checkT2 (A e : Expr Nat)

/-- The typed machine's state — the legacy `Ambient` (`RcicMachine.lean:21`)
    with a typed task and the budget that doubles as certifier fuel. -/
structure TypedState where
  ambient : Ambient
  task : TypedTask
  budget : Nat

/-! ## the payload/result layer — the derivation IN the payload -/

/-- The ACCEPTED payload: the derivation itself. `HasTyT` is Type-valued
    so the payload carries it directly — this is the whole point of
    R-3: an acceptance of this shape cannot exist without the typing. -/
inductive TypedAccepted (amb : Ambient) : Type
  | inferred (e T : Expr Nat) (d : HasTyT amb.env amb.univs amb.ctx e T) :
      TypedAccepted amb
  | checked (e A : Expr Nat) (d : HasTyT amb.env amb.univs amb.ctx e A) :
      TypedAccepted amb

/-- The typed machine's run result: an acceptance carrying its payload,
    a refusal carrying a NAMED residue, or suspension. -/
inductive TypedResult (amb : Ambient) : Type
  | accepted (p : TypedAccepted amb)
  | refused (residue : String)
  | suspended

/-! ## the encoding function and the run layer -/

/-- The typed machine's step: budget 0 suspends (mirroring
    `kernelStepRaw`); the infer arm calls `checkC` (of which `inferC`
    is the type projection) so the payload keeps the derivation; the
    check arm calls `tyAtC`. A `none` from the certifier is a refusal
    with a NAMED residue. -/
def typedStep (s : TypedState) : TypedResult s.ambient :=
  match s.budget with
  | 0 => .suspended
  | _ + 1 =>
    match s.task with
    | .inferT e =>
        match checkC s.ambient.env s.ambient.univs s.budget
            s.ambient.ctx e with
        | some ⟨T, d⟩ => .accepted (.inferred e T d)
        | none => .refused "[rcic_typed_infer_refused]"
    | .checkT2 A e =>
        match tyAtC s.ambient.env s.ambient.univs s.budget
            s.ambient.ctx e A with
        | some d => .accepted (.checked e A d)
        | none => .refused "[rcic_typed_check_refused]"

/-- The typed machine's run, mirroring `runRaw`'s shape: fuel 0
    suspends, one step decides (the typed machine is one-shot exactly
    as the raw one is — `kernelStepRaw_never_step` — so there is no
    `.step` continuation to recurse through). -/
def typedRun : Nat → (s : TypedState) → TypedResult s.ambient
  | 0, _ => .suspended
  | _ + 1, s => typedStep s

end Rcic.Machine

#print axioms Rcic.Machine.typedStep
#print axioms Rcic.Machine.typedRun

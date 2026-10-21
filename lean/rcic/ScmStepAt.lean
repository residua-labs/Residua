/-
RCIC 06 §15 / §18 — `SCMStepAt` over a step TABLE of wire configurations
(carrier `apps/rcic-scm-step-at`, SCM-016 data half).

Owner text: 06 §15 "`SCMStep` performs one local semantic transition";
"`scmStep(c) = next c' ↔ SCMStep(c,c')`, `scmStep(c) = final o ↔ c is a final
configuration for o`"; runner soundness/completeness and "Suspension is not
evidence of divergence or a program residue." 06 §18 `SCMStepAt` is an R-CIC
proposition over bound refs and canonical bytes.

The carrier decides a presented table of rows `{config_in kind config_out
outcome}` (kind 0 a step, kind 1 a final): every row well-formed (frame-chain
check, one frame consumed per step, finality only at the single body frame,
a well-formed outcome envelope), and the table a function of `config_in`.
Form 1 runs a start config through the table.

PIN (M-002): `scmStepAt` is `rcic.scm_step_at form table fuel start steps`,
11 rows below. The frame-chain check is `ScmExec.configAt` (the same
composed `rcic.config_outcome_config_at`, transcribed once).
STAND-IN (#6029 K2 HOLD item 1, K2 decision): this file pins a carrier
stand-in (M-002). It is NOT the 06 §18 / §19 object of the same name: those are
stated over bound refs and canonical core-wire bytes and are NOT TRANSCRIBED
until K3b/K3c (see `ScmRawRelations`). The table below maps the CARRIER's
rules; the 06 sections are those the carrier cites.

CARRIER RULE TABLE (rcic-scm-step-at, cites 06 §15/§18 → Lean):
  §15 one local transition (exactly one frame consumed) → `rowOk` kind 0
        (`[rcic_step_multi_frame]`)
  §15 final only at a final configuration (single body frame) → `rowOk`
        kind 1 (`[rcic_step_final_not_terminal]`)
  §15 scmStep is a function (determinism)          → `rowConflicts`
  §15 runner, suspension not a residue             → `run`
  §14 SCMFinal envelopes (returned / raised)       → `Exec.envelopeCheck`
        (the one transcription of `rcic.outcome_envelope_check`)
-/
import rcic.ScmExec

namespace Rcic.Scm.StepAt
open Rcic.BoundObject Rcic.Scm.Exec

structure Row where
  configIn : String
  kind : Int
  configOut : String
  outcome : String

def frames (c : String) : List String := c.splitOn "~"

def rowOk (r : Row) (fuel : Int) : Option String :=
  if r.kind = 0 then
    match configAt r.configIn fuel with
    | some c => some c
    | none =>
      match configAt r.configOut fuel with
      | some _ => some "[rcic_step_chain_malformed]"
      | none => if frames r.configOut == (frames r.configIn).drop 1 then none else some "[rcic_step_multi_frame]"
  else if r.kind = 1 then
    match configAt r.configIn fuel with
    | some c => some c
    | none =>
      if (frames r.configIn).length ≠ 1 then some "[rcic_step_final_not_terminal]"
      else match envelopeCheck 0 r.outcome with
        | none => none
        | some c0 => match envelopeCheck 1 r.outcome with
          | none => none
          | some _ => some c0
  else some "[rcic_step_unknown_kind]"

def resultOf (r : Row) : String := if r.kind = 0 then r.configOut else r.outcome

def rowConflicts (r : Row) (seen : List Row) : Bool :=
  seen.any (fun s => s.configIn = r.configIn && (s.kind ≠ r.kind || resultOf s ≠ resultOf r))

structure SOut where
  ok : Int
  form : Int
  nRows : Int
  suspended : Int
  config : String
  outcome : String
  code : String
  deriving BEq

def sRefuse (form : Int) (code : String) : SOut := ⟨0, form, 0, 0, "", "", code⟩

def checkWalk : List Row → Int → List Row → Int → SOut
  | table, fuel, seen, n =>
    if fuel < 0 then sRefuse 0 "[rcic_step_fuel]" else
    match table with
    | [] => ⟨1, 0, n, 0, "", "", ""⟩
    | r :: rest =>
      match rowOk r fuel with
      | some c => sRefuse 0 c
      | none =>
        if rowConflicts r seen then sRefuse 0 "[rcic_step_nondeterministic]"
        else checkWalk rest (fuel - 1) (seen ++ [r]) (n + 1)

def findRow (table : List Row) (c : String) : Option Row := table.find? (fun r => r.configIn = c)

def run (table : List Row) : String → Nat → Int → SOut
  | config, steps, fuel =>
    if fuel < 0 then sRefuse 1 "[rcic_step_fuel]" else
    match findRow table config with
    | none => ⟨1, 1, 0, 1, config, "", "[rcic_step_suspended]"⟩
    | some r =>
      if r.kind = 1 then ⟨1, 1, 0, 0, config, r.outcome, ""⟩
      else match steps with
        | 0 => ⟨1, 1, 0, 1, config, "", "[rcic_step_suspended]"⟩
        | s + 1 => if fuel = 0 then sRefuse 1 "[rcic_step_fuel]" else run table r.configOut s (fuel - 1)

def scmStepAt (form : Int) (table : List Row) (fuel : Int) (start : String) (steps : Int) : SOut :=
  if form = 0 then checkWalk table fuel [] 0
  else if form = 1 then
    if steps < 0 then sRefuse form "[rcic_step_fuel]" else run table start steps.toNat fuel
  else sRefuse form "[rcic_scm_step_unknown_form]"

/-! ## Pins: apps/rcic-scm-step-at/rcic_scm_step_at_corpus.json, 11 rows -/

namespace Pins
def c3 : String := "t:0|arg:1|fn:f~t:1|val:2~t:2|expr:e"
def c2 : String := "t:1|val:2~t:2|expr:e"
def c1 : String := "t:2|expr:e"
def stepR (i o : String) : Row := ⟨i, 0, o, ""⟩
def finR (i o : String) : Row := ⟨i, 1, "", o⟩
def chain : List Row := [stepR c3 c2, stepR c2 c1, finR c1 "output:1|post:s"]

-- 0 check_table 3-chain accept: two one-frame steps + final row (SCM-016 data half, GM-MACHINE-004, 06 S15 L284/L288)
#guard scmStepAt 0 chain 10 "" 0 == ⟨1, 0, 3, 0, "", "", ""⟩
-- 1 check_table single-frame final row accept (06 S15 L285/L288)
#guard scmStepAt 0 [finR c1 "output:1|post:s"] 10 "" 0 == ⟨1, 0, 1, 0, "", "", ""⟩
-- 2 check_table 2-frame jump refused: one local semantic transition per step (GM-MACHINE-004, 06 S15 L288)
#guard scmStepAt 0 [stepR c3 c1] 10 "" 0 == sRefuse 0 "[rcic_step_multi_frame]"
-- 3 check_table malformed out-chain refused as integrity, never treated as an outcome (06 S15 L284)
#guard scmStepAt 0 [stepR c2 "t:1|val:2"] 10 "" 0 == sRefuse 0 "[rcic_step_chain_malformed]"
-- 4 check_table two finals on one config refused: the table is a step function (06 S15 L284)
#guard scmStepAt 0 [finR c1 "output:1|post:s", finR c1 "output:2|post:s"] 10 "" 0
  == sRefuse 0 "[rcic_step_nondeterministic]"
-- 5 check_table final row on 2-frame config refused: finality is the single body frame (06 S15 L285/L288)
#guard scmStepAt 0 [finR c2 "output:1|post:s"] 10 "" 0 == sRefuse 0 "[rcic_step_final_not_terminal]"
-- 6 run completes: exact-count 2-step run reaches the final outcome (06 S15 L297 additivity, GM-OUT-004)
#guard scmStepAt 1 chain 5 c3 2 == ⟨1, 1, 0, 0, c1, "output:1|post:s", ""⟩
-- 7 run table-ends mid-run: SUSPENDED with current config, never a final outcome, never a residue
#guard scmStepAt 1 [stepR c3 c2] 5 c3 3 == ⟨1, 1, 0, 1, c2, "", "[rcic_step_suspended]"⟩
-- 8 run fuel exhausted mid-run refuses: no fuel-exhausted outcome exists (06 S14 L272, S15 L300)
#guard scmStepAt 1 [stepR c3 c2, stepR c2 c1] 1 c3 3 == sRefuse 1 "[rcic_step_fuel]"
-- 9 unknown form refused (06 S15)
#guard scmStepAt 2 [] 10 "" 0 == sRefuse 2 "[rcic_scm_step_unknown_form]"
-- 10 R-CIC S7 killer: kind=2 + garbage config refused as unknown KIND before shape
#guard scmStepAt 0 [⟨"", 2, "", ""⟩] 5 "" 0 == sRefuse 0 "[rcic_step_unknown_kind]"
end Pins

end Rcic.Scm.StepAt

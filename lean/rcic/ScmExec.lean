/-
RCIC 06 §13–§15 — the first-storey executing machine over the frame-chain
WIRE configuration (carrier `apps/rcic-scm-exec`).

Owner text: 06 §13 "The first-order wire configuration stores closed tags and
payloads. Its decoder reconstructs a raw configuration and validates the
frame-chain typing before producing the typed semantic configuration." §14
"There is no `none`, stuck, trap, or fuel-exhausted source outcome." §15
"`SCMStep` performs one local semantic transition"; "Suspension is not
evidence of divergence or a program residue."

This carrier's calculus is deliberately tiny (its APP.md): frames
`t:0|arg:…|fn:…` (call), `t:1|val:…` (let), `t:2|expr:…` (body) joined by
`~`; an expr is `env;…;body` with literal bodies `L<digits>` and unary de
Bruijn variables `V…V`. It is a fragment of the full machine of
`ScmMachine.lean` (#6029 K2 records the relation; this file only pins it).
Digit and variable scans are bounded at 64 characters and refuse an
unfinished scan (#6037).

PIN (M-002): `scmExecAt` is `rcic.scm_exec_at form config steps fuel`, 17
rows below. The frame-chain check is the carrier's composed
`rcic.config_outcome_config_at`, transcribed here (`configAt`); the envelope
check is `rcic.outcome_envelope_check` (status 0 path). `canonPartOk` /
`canonBytesOk` are `RcicBoundObject`'s (called).
STAND-IN (#6029 K2 HOLD item 1, K2 decision): this file pins a carrier
stand-in (M-002). It is NOT the 06 §18 / §19 object of the same name: those are
stated over bound refs and canonical core-wire bytes and are NOT TRANSCRIBED
until K3b/K3c (see `ScmRawRelations`). The table below maps the CARRIER's
rules; the 06 sections are those the carrier cites.

CARRIER RULE TABLE (rcic-scm-exec, cites 06 §13–§15 → Lean):
  the carrier's 3-frame chain encoding (rcic-config-outcome-at's
        declared stand-in; cites §13's first-order wire configuration, which
        it does not express: no fold/fix/prim/handle/raise frames)
                                                 → frame strings, `configAt`
  §13 decoder validates the frame chain first   → `step` checks the
        in-config with `configAt`, then the out-config
  §14 SCMFinal returned (raised path unbuilt in this calculus) → `final`
        with envelope `output:<v>|post:1`
  §14 no stuck / fuel-exhausted source outcome  → refusals are a separate
        `ok = 0` channel; a variable that misses stays with a named marker
  §15 one local transition                      → `act` acts on the head
        frame once
  §15 runner, finality before budget            → `run`
-/
import rcic.RcicBoundObject

namespace Rcic.Scm.Exec
open Rcic.BoundObject

def keyOf (part : String) : String := (part.splitOn ":").headD ""
def valOf (part : String) : String := ((part.splitOn ":").drop 1).headD ""

/-- `rcic.scm_exec_join`: the carrier's fold join (an empty accumulator
    restarts the join). -/
def join (xs : List String) (sep : String) : String :=
  xs.foldl (fun acc x => if acc = "" then x else acc ++ sep ++ x) ""

/-- `rcic.value_at_digits_ok`: 1–64 ASCII digits (an unfinished 64-step scan
    refuses). -/
def digitsOk (s : String) : Bool := 0 < s.length && s.length ≤ 64 && s.toList.all Char.isDigit
/-- `rcic.scm_exec_var_ok`: 1–64 `V`s. -/
def varOk (s : String) : Bool := 0 < s.length && s.length ≤ 64 && s.toList.all (· = 'V')
def litOk (s : String) : Bool := s.length > 1 && s.get 0 = 'L' && digitsOk (s.drop 1)

def exprOk (e : String) : Bool :=
  let parts := e.splitOn ";"
  let body := parts.getLastD ""
  (parts.dropLast).all digitsOk && (litOk body || varOk body)

def instantiate (arg template : String) : String :=
  let parts := template.splitOn ";"
  let body := parts.getLastD ""
  let nb := if varOk body then (if body.length = 1 then "L" ++ arg else body.drop 1) else body
  join (parts.dropLast ++ [nb]) ";"

def partOf (payload key : String) : String :=
  (payload.splitOn "|").foldl (fun acc p => if acc = "" then (if keyOf p = key then p else "") else acc) ""

def hasKey (bytes key : String) : Bool := (bytes.splitOn "|").any (fun p => keyOf p = key)
def shapeOk (env k1 k2 : String) : Bool := (env.splitOn "|").length = 2 && hasKey env k1 && hasKey env k2

/-! ## The frame-chain check (`rcic.config_outcome_config_at`) -/

def frameParts (f : String) : List String := f.splitOn "|"
def frameTag (f : String) : Int := (valOf ((frameParts f).headD "")).toInt?.getD 0
def payloadOf (f : String) : String := join ((frameParts f).drop 1) "|"

def frameTagOk (f : String) : Bool :=
  match frameParts f with
  | fp :: _ => canonPartOk fp && keyOf fp = "t" && (valOf fp = "0" || valOf fp = "1" || valOf fp = "2")
  | [] => false

def payloadOk (tag : Int) (payload : String) : Bool :=
  if tag = 0 then canonBytesOk payload && shapeOk payload "arg" "fn"
  else
    match payload.splitOn "|" with
    | [p] => canonPartOk p && keyOf p = (if tag = 1 then "val" else "expr")
    | _ => false

def chainWalk (fuel : Int) : List String → Option String
  | [] => none
  | f :: fs =>
    if fuel ≤ 0 then some "[rcic_config_fuel]"
    else if !frameTagOk f then some "[rcic_config_unknown_frame]"
    else if !payloadOk (frameTag f) (payloadOf f) then some "[rcic_config_payload_shape]"
    else chainWalk (fuel - 1) fs

def configAt (config : String) (fuel : Int) : Option String :=
  if config = "" then some "[rcic_config_chain_empty]"
  else if fuel < 0 then some "[rcic_config_fuel]"
  else
    let frames := config.splitOn "~"
    match chainWalk fuel frames with
    | some c => some c
    | none => if frameTag (frames.getLastD "") = 2 then none else some "[rcic_config_chain_open]"

/-! ## One action on the head frame -/

structure Act where
  ok : Bool
  kind : Int
  config : String
  value : String
  outcome : String
  code : String

def actErr (c : String) : Act := ⟨false, 0, "", "", "", c⟩

def valueIs (bytes key v : String) : Bool :=
  (bytes.splitOn "|").any (fun p => match p.splitOn ":" with | [k, x] => k = key && x = v | _ => false)

/-- `rcic.outcome_envelope_check status envelope`: `none` = accepted, else the
    refusal code. Status 0 returned, 1 raised, 2 trapped (empty envelope),
    3 suspended (never a verdict). -/
def envelopeCheck (status : Int) (env : String) : Option String :=
  if status < 0 || status > 3 then some "[rcic_outcome_unknown_status]"
  else if status = 3 then some "[rcic_outcome_suspended_not_verdict]"
  else if status = 2 then (if env = "" then none else some "[rcic_outcome_trap_has_envelope]")
  else if !canonBytesOk env then some "[rcic_outcome_envelope_noncanonical]"
  else if status = 0 then
    if shapeOk env "output" "post" then none else some "[rcic_outcome_envelope_shape_mismatch]"
  else if shapeOk env "payload" "residue" then
    if valueIs env "residue" "trap" then some "[rcic_outcome_raised_as_trap]" else none
  else some "[rcic_outcome_envelope_shape_mismatch]"

def envelopeOk (env : String) : Bool := (envelopeCheck 0 env).isNone

def bodyStep (expr : String) (tail : List String) : Act :=
  if !exprOk expr then actErr "[rcic_exec_expr_shape]" else
  let parts := expr.splitOn ";"
  let body := parts.getLastD ""
  if litOk body then
    let v := body.drop 1
    if tail.isEmpty then
      let env := "output:" ++ v ++ "|post:1"
      if envelopeOk env then ⟨true, 1, "", v, env, ""⟩ else actErr "[rcic_exec_chain_malformed]"
    else ⟨true, 0, join tail "~", v, "", ""⟩
  else
    let m := parts.length - 1
    let i := body.length - 1
    if i < m then
      let nb := "L" ++ (parts.drop i).headD ""
      ⟨true, 0, join (("t:2|expr:" ++ join (parts.take m ++ [nb]) ";") :: tail) "~", "", "", ""⟩
    else ⟨true, 0, join (("t:2|expr:" ++ expr) :: tail) "~", "", "", "[rcic_exec_stays]"⟩

def callStep (arg fn : String) (tail : List String) : Act :=
  if exprOk fn then ⟨true, 0, join (("t:2|expr:" ++ instantiate arg fn) :: tail) "~", "", "", ""⟩
  else actErr "[rcic_exec_fn_not_literal]"

def act (frames : List String) : Act :=
  let head := frames.headD ""
  let payload := payloadOf head
  let tail := frames.drop 1
  match frameTag head with
  | 0 => callStep (valOf (partOf payload "arg")) (valOf (partOf payload "fn")) tail
  | 1 => ⟨true, 0, join tail "~", valOf (partOf payload "val"), "", ""⟩
  | 2 => bodyStep (valOf (partOf payload "expr")) tail
  | _ => actErr "[rcic_config_unknown_frame]"

/-! ## Step, run, entry point -/

structure ExecOut where
  ok : Int
  form : Int
  kind : Int
  suspended : Int
  config : String
  value : String
  outcome : String
  code : String
  deriving BEq

def refuse (form : Int) (code : String) : ExecOut := ⟨0, form, 0, 0, "", "", "", code⟩

def step (config : String) (fuel : Int) : ExecOut :=
  if fuel < 1 then refuse 0 "[rcic_exec_fuel]" else
  match configAt config fuel with
  | some c => refuse 0 c
  | none =>
    let a := act (config.splitOn "~")
    if !a.ok then refuse 0 a.code
    else if a.kind = 1 then ⟨1, 0, 1, 0, config, a.value, a.outcome, ""⟩
    else match configAt a.config fuel with
      | none => ⟨1, 0, 0, 0, a.config, a.value, "", a.code⟩
      | some _ => refuse 0 "[rcic_exec_chain_malformed]"

def run : String → Nat → Int → ExecOut
  | config, steps, fuel =>
    let p := step config (if fuel < 1 then 1 else fuel)
    if p.ok = 1 ∧ p.kind = 1 then ⟨1, 1, 1, 0, config, "", p.outcome, ""⟩
    else match steps with
      | 0 => ⟨1, 1, 0, 1, config, "", "", "[rcic_exec_suspended]"⟩
      | s + 1 =>
        if fuel = 0 then refuse 1 "[rcic_exec_fuel]" else
        let r := step config fuel
        if r.ok = 0 then refuse 1 r.code
        else if r.kind = 1 then ⟨1, 1, 1, 0, r.config, "", r.outcome, ""⟩
        else run r.config s (fuel - 1)

def scmExecAt (form : Int) (config : String) (steps fuel : Int) : ExecOut :=
  if form = 0 then step config fuel
  else if form = 1 then
    if steps < 0 then refuse 1 "[rcic_exec_fuel]"
    else if fuel < 0 then refuse 1 "[rcic_exec_fuel]"
    else run config steps.toNat fuel
  else refuse form "[rcic_scm_exec_unknown_form]"

/-! ## The carrier `apps/rcic-config-outcome-at` (stand-in; K2 HOLD item 5)

`rcic.config_outcome_at form config fuel status class kind digest outcome`:
form 0 is the frame-chain check above (`configAt`, reporting the frame
count); form 1 binds an outcome envelope: trapped / suspended statuses are not
final outcomes, the envelope must pass `envelopeCheck`, and the typed-ref
digest of the envelope must be the presented one (`RcicTypedRef.deriveDigest`).
It cites 06 §13/§14/§18 and is the declared 3-frame stand-in, not 06 §18's
`ConfigAt` / `OutcomeAt` (`ScmRawRelations` header). -/

structure COOut where
  ok : Int
  form : Int
  nFrames : Option Int
  status : Option Int
  digest : Option String
  code : String
  deriving BEq

def configOutcomeAt (form : Int) (config : String) (fuel status cls kind : Int) (digest outcome : String) : COOut :=
  if form = 0 then
    match configAt config fuel with
    | some c => ⟨0, 0, some 0, none, none, c⟩
    | none => ⟨1, 0, some (config.splitOn "~").length, none, none, ""⟩
  else if form = 1 then
    let no (d c : String) : COOut := ⟨0, 1, none, some status, some d, c⟩
    if status = 2 || status = 3 then no digest "[rcic_outcome_at_not_final]"
    else match envelopeCheck status outcome with
    | some c => no digest c
    | none =>
      if kind < 0 then no "" "[typed_ref_unknown_kind]"
      else if !classOk cls then no "" "[typed_ref_unknown_class]"
      else if Rcic.TypedRef.deriveDigest cls.toNat kind outcome = digest then ⟨1, 1, none, some status, some digest, ""⟩
      else no digest "[rcic_outcome_at_digest_mismatch]"
  else ⟨0, form, none, none, none, "[rcic_config_outcome_unknown_form]"⟩

namespace COPins
def c3 : String := "t:0|arg:1|fn:f~t:1|val:2~t:2|expr:e"
def cfg (config : String) (fuel : Int) : COOut := configOutcomeAt 0 config fuel 0 0 0 "" ""
def okC (n : Int) : COOut := ⟨1, 0, some n, none, none, ""⟩
def noC (c : String) : COOut := ⟨0, 0, some 0, none, none, c⟩
def oat (status : Int) (digest outcome : String) : COOut := configOutcomeAt 1 "" 0 status 0 0 digest outcome
def okO (st : Int) (d : String) : COOut := ⟨1, 1, none, some st, some d, ""⟩
def noO (st : Int) (d c : String) : COOut := ⟨0, 1, none, some st, some d, c⟩

-- 0 ConfigAt 3-frame call/let/body chain accept (06 S13 L254-256, S18 L395)
#guard cfg c3 10 == okC 3
-- 1 ConfigAt single body-frame chain accept (06 S13 L254-256, S18 L395)
#guard cfg "t:2|expr:e" 5 == okC 1
-- 2 ConfigAt unknown frame tag 3 refused (06 S13 L254)
#guard cfg "t:0|arg:1|fn:f~t:3|val:2~t:2|expr:e" 10 == noC "[rcic_config_unknown_frame]"
-- 3 ConfigAt call payload missing fn key refused (06 S13 L254-256)
#guard cfg "t:0|arg:1~t:2|expr:e" 10 == noC "[rcic_config_payload_shape]"
-- 4 ConfigAt let payload extra key refused (06 S13 L254-256)
#guard cfg "t:1|val:2|extra:x~t:2|expr:e" 10 == noC "[rcic_config_payload_shape]"
-- 5 ConfigAt chain ending in let frame open refused (06 S13 L256)
#guard cfg "t:0|arg:1|fn:f~t:1|val:2" 10 == noC "[rcic_config_chain_open]"
-- 6 ConfigAt empty chain refused (06 S13 L256)
#guard cfg "" 10 == noC "[rcic_config_chain_empty]"
-- 7 ConfigAt walk fuel 0 refused (06 S13 L256 fuel-bounded walk)
#guard cfg "t:2|expr:e" 0 == noC "[rcic_config_fuel]"
-- 8 OutcomeAt returned envelope bound ok (06 S14 L260-262, S18 L396)
#guard oat 0 "1cb441fb46b4a79363a38fc0821a651fc45fd960acddc6208eb4a54ea104cdc5" "output:5|post:p"
  == okO 0 "1cb441fb46b4a79363a38fc0821a651fc45fd960acddc6208eb4a54ea104cdc5"
-- 9 OutcomeAt raised envelope bound ok (06 S14 L260-262, S18 L396)
#guard oat 1 "2855e3ad7f5d79dffaf9f5c8e43b4f3cb563823396ca1230f333339f86f04960" "payload:q|residue:r"
  == okO 1 "2855e3ad7f5d79dffaf9f5c8e43b4f3cb563823396ca1230f333339f86f04960"
-- 10 OutcomeAt trapped status not a final outcome refused (06 S14 L272)
#guard oat 2 "d1cf3fbecdadbde9e9ace371e0cfd17e1f38afa336c52c760cc2d169b1534718" ""
  == noO 2 "d1cf3fbecdadbde9e9ace371e0cfd17e1f38afa336c52c760cc2d169b1534718" "[rcic_outcome_at_not_final]"
-- 11 OutcomeAt suspended status not a final outcome refused (06 S14 L260-263,272)
#guard oat 3 "" "output:1|post:p" == noO 3 "" "[rcic_outcome_at_not_final]"
-- 12 OutcomeAt digest mismatch refused (06 S18 L396)
#guard oat 0 "" "output:5|post:p" == noO 0 "" "[rcic_outcome_at_digest_mismatch]"
-- 13 unknown form refused (06 S18 L395-396)
#guard configOutcomeAt 7 "" 0 0 0 0 "" "" == ⟨0, 7, none, none, none, "[rcic_config_outcome_unknown_form]"⟩
-- 14 C3 ConfigAt trailing empty frame from trailing ~ refused never trimmed (RED-set 2026-08-29 06 S13 L254)
#guard cfg "t:2|expr:e~" 5 == noC "[rcic_config_unknown_frame]"
end COPins

/-! ## Pins: apps/rcic-scm-exec/rcic_scm_exec_corpus.json, 17 rows -/

namespace Pins
def stepOk (c v code : String) : ExecOut := ⟨1, 0, 0, 0, c, v, "", code⟩
def fin0 (c v o : String) : ExecOut := ⟨1, 0, 1, 0, c, v, o, ""⟩
def fin1 (c o : String) : ExecOut := ⟨1, 1, 1, 0, c, "", o, ""⟩
def rep (n : Nat) (s : String) : String := String.join (List.replicate n s)

-- 0 let-step: one frame action, control moves to the next frame (06 S13/S15 L288, GM-MACHINE-004)
#guard scmExecAt 0 "t:1|val:2~t:2|expr:L5" 0 10 == stepOk "t:2|expr:L5" "2" ""
-- 1 call-step: literal-value substitution into the fn template, call frame replaced by body frame
#guard scmExecAt 0 "t:0|arg:9|fn:4;V~t:2|expr:L3" 0 10 == stepOk "t:2|expr:4;L9~t:2|expr:L3" "" ""
-- 2 body literal on the single body frame: FINAL returned outcome (06 S14 L261/L267)
#guard scmExecAt 0 "t:2|expr:7;L5" 0 10 == fin0 "t:2|expr:7;L5" "5" "output:5|post:1"
-- 3 var lookup step: one constructor step var to literal against the literal env part (06 S13)
#guard scmExecAt 0 "t:2|expr:4;5;VV~t:2|expr:L3" 0 10 == stepOk "t:2|expr:4;5;L5~t:2|expr:L3" "" ""
-- 4 run completes: fold of step reaches the final outcome (06 S15 L297, GM-OUT-004)
#guard scmExecAt 1 "t:1|val:2~t:2|expr:L5" 2 10 == fin1 "t:2|expr:L5" "output:5|post:1"
-- 5 run budget ending ON a final-shaped config is DONE with its envelope
#guard scmExecAt 1 "t:1|val:2~t:2|expr:L5" 1 10 == fin1 "t:2|expr:L5" "output:5|post:1"
-- 6 two-frame config steps to one-frame then final through a call (06 S15 L288/L297)
#guard scmExecAt 1 "t:0|arg:9|fn:V~t:2|expr:L7" 3 10 == fin1 "t:2|expr:L7" "output:7|post:1"
-- 7 malformed out-config refused: a body expr outside the calculus is an integrity refusal
#guard scmExecAt 0 "t:2|expr:Lx~t:2|expr:L3" 0 10 == refuse 0 "[rcic_exec_expr_shape]"
-- 8 budget zero suspension: run at steps=0 suspends on the start config (GM-OUT-004, 06 S15 L300)
#guard scmExecAt 1 "t:1|val:2~t:2|expr:L5" 0 10
  == ⟨1, 1, 0, 1, "t:1|val:2~t:2|expr:L5", "", "", "[rcic_exec_suspended]"⟩
-- 9 unknown form refused (06 S13/S15)
#guard scmExecAt 2 "t:2|expr:L5" 0 10 == refuse 2 "[rcic_scm_exec_unknown_form]"
-- 10 call with fn not a literal template refused: no closures in the first storey (06 S13)
#guard scmExecAt 0 "t:0|arg:9|fn:X~t:2|expr:L3" 0 10 == refuse 0 "[rcic_exec_fn_not_literal]"
-- 11 sealed in-config chain refusal propagates: open chain (ends in let)
#guard scmExecAt 0 "t:1|val:2" 0 10 == refuse 0 "[rcic_config_chain_open]"
-- 12 var lookup miss stays: no progress, config unchanged, named marker, never silent
#guard scmExecAt 0 "t:2|expr:4;VVV~t:2|expr:L3" 0 10 == stepOk "t:2|expr:4;VVV~t:2|expr:L3" "" "[rcic_exec_stays]"
-- 13 run(final, 0, 0): a final-shaped config at zero steps and zero fuel is DONE, never suspended
#guard scmExecAt 1 "t:2|expr:L7" 0 0 == fin1 "t:2|expr:L7" "output:7|post:1"
-- 14 run(final, 5, 0): finality precedes the fuel gate too
#guard scmExecAt 1 "t:2|expr:L7" 5 0 == fin1 "t:2|expr:L7" "output:7|post:1"
-- 15 malformed out-config refused: a literal of 64 digits then x is outside the calculus
#guard scmExecAt 0 ("t:2|expr:L" ++ rep 64 "1" ++ "x~t:2|expr:L3") 0 10 == refuse 0 "[rcic_exec_expr_shape]"
-- 16 malformed out-config refused: a variable of 64 V then x is outside the calculus
#guard scmExecAt 0 ("t:2|expr:" ++ rep 64 "V" ++ "x~t:2|expr:L3") 0 10 == refuse 0 "[rcic_exec_expr_shape]"
end Pins

end Rcic.Scm.Exec

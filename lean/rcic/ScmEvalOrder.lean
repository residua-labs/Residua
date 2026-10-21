/-
RCIC 06 §10 — evaluation order, decided on a recorded event trace
(SCM-003 order clauses; carrier `apps/rcic-eval-order`).

Owner text (06:202-218): "Evaluation is strict left-to-right: let value
before body … pair left before right … call arguments in signature order and
caller environment … Calls evaluate all arguments in the caller local
environment, then create a fresh callee local environment containing only the
exact argument values."

The carrier decides a trace of events `{kind idx env}`: 0 call argument `idx`,
1 let value / 2 let body of block `idx`, 3 pair left / 4 pair right of pair
`idx`, 5 callee entry, 6 return. A truncated trace (a call still open) is a
suspension, never a verdict (06:300).

PIN (M-002): `evalOrder` is `rcic.eval_order form trace sig_len fuel`, 14 rows
below.

TRANSCRIPTION TABLE (06 §10 → Lean):
  "let value before body"                     → kinds 1/2, pending-let set
  "pair left before right"                    → kinds 3/4, pending-pair set
  "call arguments in signature order"         → kind 0, `nextIdx`
  "… and caller environment"                  → kind 0 `callerTag` equality
  "then create a fresh callee local environment containing only the exact
   argument values"                           → kind 5: all `sigLen`
        arguments seen, callee env differs from the caller env
  if/record/cons/fold/fix order clauses       → not in the carrier's event
        alphabet (its DOES NOT DECIDE); the machine of `ScmMachine` pins them
-/
import rcic.ScmCore

namespace Rcic.Scm.EvalOrder

structure Event where
  kind : Int
  idx : Int
  env : String

structure St where
  code : String := ""
  isOpen : Bool := false
  stage : Int := 0
  nargs : Int := 0
  nextIdx : Int := 0
  callerTag : String := ""
  pendLet : List Int := []
  pendPair : List Int := []

def removeFirst (xs : List Int) (x : Int) : List Int :=
  match xs with
  | [] => []
  | y :: ys => if y = x then ys else y :: removeFirst ys x

def err (st : St) (c : String) : St := { st with code := c }

def step (st : St) (ev : Event) (sigLen : Int) : St :=
  match ev.kind with
  | 0 =>
    if st.stage = 1 then err st "[rcic_eval_order_args_out_of_order]"
    else if st.nargs ≥ sigLen then err st "[rcic_eval_order_args_out_of_order]"
    else if ev.idx ≠ st.nextIdx then err st "[rcic_eval_order_args_out_of_order]"
    else if st.nargs = 0 then { st with isOpen := true, nargs := 1, nextIdx := ev.idx + 1, callerTag := ev.env }
    else if ev.env ≠ st.callerTag then err st "[rcic_eval_order_arg_in_callee_env]"
    else { st with nargs := st.nargs + 1, nextIdx := st.nextIdx + 1 }
  | 1 => { st with pendLet := st.pendLet ++ [ev.idx] }
  | 2 =>
    if st.pendLet.contains ev.idx then { st with pendLet := removeFirst st.pendLet ev.idx }
    else err st "[rcic_eval_order_let_before_body]"
  | 3 => { st with pendPair := st.pendPair ++ [ev.idx] }
  | 4 =>
    if st.pendPair.contains ev.idx then { st with pendPair := removeFirst st.pendPair ev.idx }
    else err st "[rcic_eval_order_pair_order]"
  | 5 =>
    if st.stage = 1 then err st "[rcic_eval_order_args_out_of_order]"
    else if st.nargs < sigLen then err st "[rcic_eval_order_args_incomplete]"
    else if st.nargs = 0 then { st with isOpen := true, stage := 1 }
    else if ev.env = st.callerTag then err st "[rcic_eval_order_arg_in_callee_env]"
    else { st with stage := 1 }
  | 6 =>
    if st.stage = 1 then { st with isOpen := false, stage := 0, nargs := 0, nextIdx := 0, callerTag := "" }
    else err st "[rcic_eval_order_args_out_of_order]"
  | _ => err st "[rcic_eval_order_unknown_event]"

structure EOOut where
  ok : Int
  sigLen : Int
  code : String
  deriving BEq

def scan (sigLen : Int) : List Event → Int → St → EOOut
  | trace, fuel, st =>
    if fuel < 0 then ⟨0, sigLen, "[rcic_eval_order_fuel]"⟩ else
    match trace with
    | [] =>
      if st.code ≠ "" then ⟨0, sigLen, st.code⟩
      else if st.isOpen then ⟨0, sigLen, "[rcic_eval_order_trace_suspended]"⟩
      else ⟨1, sigLen, ""⟩
    | ev :: rest =>
      let st2 := step st ev sigLen
      if st2.code = "" then scan sigLen rest (fuel - 1) st2 else ⟨0, sigLen, st2.code⟩

def evalOrder (form : Int) (trace : List Event) (sigLen fuel : Int) : EOOut :=
  if form = 0 then
    if fuel < 0 then ⟨0, sigLen, "[rcic_eval_order_fuel]"⟩ else scan sigLen trace fuel {}
  else ⟨0, sigLen, "[rcic_eval_order_unknown_form]"⟩

/-! ## Pins: apps/rcic-eval-order/rcic_eval_order_corpus.json, 14 rows -/

namespace Pins
def e (k i : Int) (env : String) : Event := ⟨k, i, env⟩
def A : String := "callerA"
def Bc : String := "calleeB"
def ok (n : Int) : EOOut := ⟨1, n, ""⟩
def no (n : Int) (c : String) : EOOut := ⟨0, n, c⟩

-- 0 06 §10 GM-SCM-003 compliant two-arg call: args 0,1 in caller env, fresh callee entry, return
#guard evalOrder 0 [e 0 0 A, e 0 1 A, e 5 0 Bc, e 6 0 A] 2 64 == ok 2
-- 1 06 §10 GM-SCM-003 compliant zero-arg call: no arg events, one fresh callee entry, return
#guard evalOrder 0 [e 5 0 Bc, e 6 0 A] 0 64 == ok 0
-- 2 GM-SCM-003a 06 §10 call arguments evaluated right-to-left (idx 1 before 0) refused
#guard evalOrder 0 [e 0 1 A, e 0 0 A, e 5 0 Bc, e 6 0 A] 2 64 == no 2 "[rcic_eval_order_args_out_of_order]"
-- 3 06 §10 GM-SCM-003 missing argument: one of two signature args seen before callee entry
#guard evalOrder 0 [e 0 0 A, e 5 0 Bc, e 6 0 A] 2 64 == no 2 "[rcic_eval_order_args_incomplete]"
-- 4 06 §10 GM-SCM-003 extra argument beyond the two-arg signature refused
#guard evalOrder 0 [e 0 0 A, e 0 1 A, e 0 2 A, e 5 0 Bc, e 6 0 A] 2 64 == no 2 "[rcic_eval_order_args_out_of_order]"
-- 5 GM-SCM-003b 06 §10 argument idx 1 evaluated in the callee environment refused
#guard evalOrder 0 [e 0 0 A, e 0 1 Bc, e 5 0 Bc, e 6 0 A] 2 64 == no 2 "[rcic_eval_order_arg_in_callee_env]"
-- 6 06 §10 let: value event strictly before body event of the same block id
#guard evalOrder 0 [e 1 7 A, e 2 7 A] 0 64 == ok 0
-- 7 06 §10 let: body event before value event of the same block id refused
#guard evalOrder 0 [e 2 7 A, e 1 7 A] 0 64 == no 0 "[rcic_eval_order_let_before_body]"
-- 8 06 §10 pair: left event strictly before right event of the same pair id
#guard evalOrder 0 [e 3 4 A, e 4 4 A] 0 64 == ok 0
-- 9 06 §10 pair: right event before left event of the same pair id refused
#guard evalOrder 0 [e 4 4 A, e 3 4 A] 0 64 == no 0 "[rcic_eval_order_pair_order]"
-- 10 06 §10 line 300 truncated call trace (one of two args seen, no return) suspends — never a verdict
#guard evalOrder 0 [e 0 0 A] 2 64 == no 2 "[rcic_eval_order_trace_suspended]"
-- 11 06 §10 GM-SCM-003 unknown event kind 9 in the trace refused by name
#guard evalOrder 0 [e 0 0 A, e 9 0 A] 2 64 == no 2 "[rcic_eval_order_unknown_event]"
-- 12 06 §10 GM-SCM-003 form 9 unknown form
#guard evalOrder 9 [e 0 0 A, e 0 1 A, e 5 0 Bc, e 6 0 A] 2 64 == no 2 "[rcic_eval_order_unknown_form]"
-- 13 F8 pending-set id matching: let value block 7 then let body block 8 — a DIFFERENT pending id is not a match
#guard evalOrder 0 [e 1 7 A, e 2 8 A] 0 64 == no 0 "[rcic_eval_order_let_before_body]"
end Pins

end Rcic.Scm.EvalOrder

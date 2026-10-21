/-
RCIC 06 §10, §12–§15 — the RAW machine: the carrier `apps/rcic-scm-core`
(#6043) transcribed transition for transition.

Configurations here are the carrier's first-order records (06 §13: "The
first-order wire configuration stores closed tags and payloads"): a control
`{c 0 env e}` / `{c 1 v}` / `{c 2 r v}` and a list of frames, top first,
frame tags 0–21 as in `apps/rcic-scm-core/APP.md` Encoding. Raw configs need
not be typable (the carrier's form 0/1 accept any record, and the stuck
refusal is part of the observable behaviour), so this machine is the pinned
model of the carrier's raw step; the intrinsic, typed machine of 06 §13–§15
is `ScmMachine.lean`, pinned through the carrier's entry runs.

PIN (M-002): `scmCore` is `rcic.scm_core form fuel prog config args steps
more`; all 40 corpus rows are pinned in `ScmMachinePins.lean`.
-/
import rcic.ScmExpr

namespace Rcic.Scm.Raw
open Rcic.Scm

/-! ## First-order configurations -/

inductive Frame where
  | letF (env : List Val) (b : RawExpr)
  | ifF (env : List Val) (th el : RawExpr)
  | pairL (env : List Val) (b : RawExpr)
  | pairR (v : Val)
  | fstF
  | sndF
  | injF (i : Int)
  | matchF (env : List Val) (bs : List RawExpr)
  | recF (env : List Val) (done : List Val) (rest : List RawExpr)
  | fieldF (i : Int)
  | consH (env : List Val) (tl : RawExpr)
  | consT (v : Val)
  | foldL (env : List Val) (init body : RawExpr)
  | foldI (env : List Val) (xs : List Val) (body : RawExpr)
  | fixI (env : List Val) (limit stop step : RawExpr)
  | fixL (env : List Val) (s : Val) (stop step : RawExpr)
  | fixS (env : List Val) (s : Val) (left count : Int) (stop step : RawExpr)
  | fixT (env : List Val) (left count : Int) (stop step : RawExpr)
  | argsF (env : List Val) (kind : Int) (op : String) (fn : Int) (done : List Val) (rest : List RawExpr)
  | retF
  | handleF (r : String) (env : List Val) (h : RawExpr)
  | raiseF (r : String)
  deriving BEq, Inhabited

inductive Ctl where
  | evalC (env : List Val) (e : RawExpr)
  | retC (v : Val)
  | raiseC (r : String) (v : Val)
  deriving BEq, Inhabited

structure Config where
  ctl : Ctl
  k : List Frame
  deriving BEq, Inhabited

/-- The carrier's output record. `steps` is absent from step-form outputs and
    from refusals; `law` only in resume outputs. -/
structure Out where
  ok : Int
  kind : Int
  config : Config
  v : Val
  r : String
  steps : Option Int
  law : Option Int
  code : String
  deriving BEq, Inhabited

def unitCfg : Config := ⟨.retC unitRaw, []⟩
def refuse (code : String) : Out := ⟨0, 0, unitCfg, unitRaw, "", none, none, code⟩
def next (c : Config) : Out := ⟨1, 0, c, unitRaw, "", none, none, ""⟩
def evalTo (env : List Val) (e : RawExpr) (k : List Frame) : Out := next ⟨.evalC env e, k⟩
def retTo (v : Val) (k : List Frame) : Out := next ⟨.retC v, k⟩
def raiseTo (r : String) (v : Val) (k : List Frame) : Out := next ⟨.raiseC r v, k⟩
def final (kind : Int) (v : Val) (r : String) : Out :=
  ⟨1, kind, ⟨if kind = 2 then .raiseC r v else .retC v, []⟩, v, r, none, none, ""⟩
def stuck : Out := refuse "[rcic_scm_core_stuck]"

def fixOut (converged : Int) (s : Val) (count : Int) : Val := .r [.b converged, s, .i count]

def nth? {α : Type} (xs : List α) (i : Int) : Option α := if i < 0 then none else xs.get? i.toNat

/-- Enter a local function with a fresh environment of exactly the
    arguments (06:218). -/
def enter (p : RawProg) (i : Int) (args : List Val) (k : List Frame) : Out :=
  match nth? p.fns i with
  | some f => evalTo args f.body (.retF :: k)
  | none => stuck

/-! ## One transition -/

def evalStep (p : RawProg) (env : List Val) (e : RawExpr) (k : List Frame) : Out :=
  match e with
  | .lit v _ => retTo v k
  | .var i => match nth? env i with
    | some v => retTo v k
    | none => stuck
  | .letE a b => evalTo env a (.letF env b :: k)
  | .ifE c th el => evalTo env c (.ifF env th el :: k)
  | .pair a b => evalTo env a (.pairL env b :: k)
  | .fst a => evalTo env a (.fstF :: k)
  | .snd a => evalTo env a (.sndF :: k)
  | .inj i _ a => evalTo env a (.injF i :: k)
  | .matchE s bs => evalTo env s (.matchF env bs :: k)
  | .recordE _ fs => match fs with
    | [] => retTo (.r []) k
    | f :: rest => evalTo env f (.recF env [] rest :: k)
  | .field r i => evalTo env r (.fieldF i :: k)
  | .nil _ => retTo (.l []) k
  | .cons h tl => evalTo env h (.consH env tl :: k)
  | .fold l init body => evalTo env l (.foldL env init body :: k)
  | .fix init limit stop step => evalTo env init (.fixI env limit stop step :: k)
  | .prim op args => match args with
    | [] => stuck
    | a :: rest => evalTo env a (.argsF env 0 op 0 [] rest :: k)
  | .call (.local i) args => match args with
    | [] => enter p i [] k
    | a :: rest => evalTo env a (.argsF env 1 "" i [] rest :: k)
  | .call (.ext _) _ => refuse "[rcic_scm_core_external_call]"
  | .raise r pe _ => evalTo env pe (.raiseF r :: k)
  | .handle r body h => evalTo env body (.handleF r env h :: k)
  | .unknown _ => stuck

def retStep (p : RawProg) (v : Val) : List Frame → Out
  | [] => final 1 v ""
  | fr :: rest =>
    match fr with
    | .letF env b => evalTo (v :: env) b rest
    | .ifF env th el => match v with
      | .b x => evalTo env (if x = 1 then th else el) rest
      | _ => stuck
    | .pairL env b => evalTo env b (.pairR v :: rest)
    | .pairR a => retTo (.p a v) rest
    | .fstF => match v with
      | .p a _ => retTo a rest
      | _ => stuck
    | .sndF => match v with
      | .p _ b => retTo b rest
      | _ => stuck
    | .injF i => retTo (.j i v) rest
    | .matchF env bs => match v with
      | .j i w => match nth? bs i with
        | some b => evalTo (w :: env) b rest
        | none => stuck
      | _ => stuck
    | .recF env done more =>
      let done' := done ++ [v]
      match more with
      | [] => retTo (.r done') rest
      | f :: more' => evalTo env f (.recF env done' more' :: rest)
    | .fieldF i => match v with
      | .r fs => match nth? fs i with
        | some x => retTo x rest
        | none => stuck
      | _ => stuck
    | .consH env tl => evalTo env tl (.consT v :: rest)
    | .consT h => match v with
      | .l xs => retTo (.l (h :: xs)) rest
      | _ => stuck
    | .foldL env init body => match v with
      | .l xs => evalTo env init (.foldI env xs body :: rest)
      | _ => stuck
    | .foldI env xs body => match xs with
      | [] => retTo v rest
      | x :: xs' => evalTo (x :: v :: env) body (.foldI env xs' body :: rest)
    | .fixI env limit stop step => evalTo env limit (.fixL env v stop step :: rest)
    | .fixL env s stop step => match v with
      | .i n =>
        if n < 0 then raiseTo "negative_loop_bound" unitRaw rest
        else evalTo (s :: env) stop (.fixS env s n 0 stop step :: rest)
      | _ => stuck
    | .fixS env s left count stop step => match v with
      | .b x =>
        if x = 1 then retTo (fixOut 1 s count) rest
        else if left = 0 then retTo (fixOut 0 s count) rest
        else evalTo (s :: env) step (.fixT env (left - 1) (count + 1) stop step :: rest)
      | _ => stuck
    | .fixT env left count stop step =>
        evalTo (v :: env) stop (.fixS env v left count stop step :: rest)
    | .argsF env kind op fn done more =>
      let done' := done ++ [v]
      match more with
      | a :: more' => evalTo env a (.argsF env kind op fn done' more' :: rest)
      | [] =>
        if kind = 0 then
          let o := scmPrim 0 op done' 0
          if o.ok = 0 then stuck
          else if o.kind = 0 then retTo o.v rest
          else raiseTo o.r o.v rest
        else enter p fn done' rest
    | .retF => retTo v rest
    | .handleF _ _ _ => retTo v rest
    | .raiseF r => raiseTo r v rest

def raiseStep (r : String) (v : Val) : List Frame → Out
  | [] => final 2 v r
  | .handleF r' env h :: rest =>
      if r' = r then evalTo (v :: env) h rest else raiseTo r v rest
  | _ :: rest => raiseTo r v rest

/-- 06 §15 `scmStep`, raw: one local transition, a final outcome, or the
    stuck integrity refusal. -/
def step (p : RawProg) (c : Config) : Out :=
  match c.ctl with
  | .evalC env e => evalStep p env e c.k
  | .retC v => retStep p v c.k
  | .raiseC r v => raiseStep r v c.k

/-! ## The runner -/

def runRes (kind : Int) (c : Config) (v : Val) (r : String) (steps : Int) : Out :=
  ⟨1, kind, c, v, r, some steps, none, ""⟩

/-- Finality before budget; an exhausted budget on a nonfinal config is
    `suspended` (kind 3) with the current config. -/
def runLoop (p : RawProg) (c : Config) : Nat → Int → Out
  | left, steps =>
    let s := step p c
    if s.ok = 0 then refuse s.code
    else if s.kind = 0 then
      match left with
      | 0 => runRes 3 c unitRaw "" steps
      | l + 1 => runLoop p s.config l (steps + 1)
    else runRes s.kind s.config s.v s.r steps

def run (p : RawProg) (c : Config) (n : Int) : Out :=
  if n < 0 then refuse "[rcic_scm_core_budget]"
  else if n > 4096 then refuse "[rcic_scm_core_bound]"
  else runLoop p c n.toNat 0

/-- Entry run: type the program, type the arguments, run from
    `eval args body`, then check a final raised outcome against the catalog
    (06 §16 residue-row safety and payload typing, per instance). -/
def entry (fuel : Int) (p : RawProg) (args : List Val) (n : Int) : Out :=
  match progCheck fuel p with
  | .error c => refuse c
  | .ok _ =>
    match nth? p.fns p.entry with
    | none => refuse "[rcic_scm_typing_entry]"
    | some f =>
      if !valsOfTys args f.params then refuse "[rcic_scm_core_ill_typed_args]" else
      let res := run p ⟨.evalC args f.body, []⟩ n
      if res.ok = 0 then res
      else if res.kind = 2 then
        match catalogPt p.catalog res.r with
        | none => refuse "[rcic_scm_core_row_safety]"
        | some pt => if valOfTy res.v pt then res else refuse "[rcic_scm_core_payload]"
      else res

/-- 06:297 `runSteps(m+n,c) = continueSteps(n, runSteps(m,c))`, reported as
    the law bit beside `run(m+n)`. -/
def resume (p : RawProg) (c : Config) (m n : Int) : Out :=
  let whole := run p c (m + n)
  let head := run p c m
  let split :=
    if head.ok = 0 then head
    else if head.kind = 3 then
      let second := run p head.config n
      if second.ok = 0 then second
      else runRes second.kind second.config second.v second.r
        ((head.steps.getD 0) + (second.steps.getD 0))
    else head
  if whole.ok = 0 then whole
  else { whole with law := some (if whole == split then 1 else 0) }

def scmCore (form fuel : Int) (p : RawProg) (c : Config) (args : List Val) (steps more : Int) : Out :=
  if form = 0 then step p c
  else if form = 1 then run p c steps
  else if form = 2 then entry fuel p args steps
  else if form = 3 then resume p c steps more
  else refuse "[rcic_scm_core_unknown_form]"

end Rcic.Scm.Raw

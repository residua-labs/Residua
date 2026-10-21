/-
RCIC 06 §13–§14 over 01 §6 and 06 §18 — the carrier `apps/rcic-scm-config`
(#6029 K3b, segment 3): bound configurations with their frame-chain typing,
final outcomes and run results, under a bound program.

Owner text:
  06 §13 "Typed frames and continuations ensure returned values resume only
      compatible control frames. An SCM configuration is a dependent pair of
      current result type, control, and typed continuation. The first-order
      wire configuration stores closed tags and payloads. Its decoder
      reconstructs a raw configuration and validates the frame-chain typing
      before producing the typed semantic configuration."
  06 §14 `SCMFinal T`, `SCMRunResult T`; "There is no `none`, stuck, trap, or
      fuel-exhausted source outcome."
  06 §18 `ConfigAt`, `OutcomeAt` "are R-CIC propositions over bound refs and
      canonical bytes".

PIN (M-002): `scmCF` is `rcic.scm_cf form fuel profile ref bytes ref2 bytes2
ref3 bytes3 x` (131 rows in `Pins`, hand-transcribed). Forms 0, 1, 2 bind a
configuration (kind 22), a final outcome (23) or a run result (24; kinds
registered in `docs/rcic/SEMANTIC_OBJECT_KIND_REGISTRY.md`) at
`ref3` / `bytes3` under the bound program `ref`/`bytes` (root) and
`ref2`/`bytes2` (bundle), then type it; form 3 encodes an object and
re-checks it. The carrier's `x` is `{kind, o}`: here `xk` and `xo`.

TRANSCRIPTION TABLE (06 §13 → Lean, the typed machine `ScmMachine.Frame`):
  control `eval Γ env e` → tag 0 `[Γ, env, e]`: env typed by Γ, e typed in Γ
  control `returning v` → tag 1 `[A, v]`: v : A
  control `raising r v` → tag 2 `[A, r, v]`: r catalogued with payload P, v : P
  each frame `Frame S A B` → its tag with items `[A, B, …]`, checked by
      `frameOk` clause for clause against the constructor's typing
      (`letF` … `raiseF`, tags 0–21 as in `apps/rcic-scm-core`; `foldI`
      stores its element type; `fixS`/`fixT` check `FixBound`)
  "typed continuation" → `cfgTy`: each frame's A is the previous output,
      the last output is the configuration's result type
  06 §14 `SCMFinal`, `SCMRunResult` → `finOk`, `cfCheck` kind 24
NOT TRANSCRIBED here (#6029 K3c): `ConfigAt` / `OutcomeAt` as R-CIC
propositions, elaboration of a checked wire configuration to an intrinsic
`Config`, and the §19 directions.
-/
import rcic.ScmBoundProgram

namespace Rcic.Scm.CfgAt
open Rcic.Scm Rcic.Scm.Wire Rcic.Scm.CfgWire Rcic.Scm.BoundProg Rcic.BoundObject

def itm (xs : List Item) (i : Nat) : Item := xs.getD i default
def tyL (x : Item) : List CoreTy := (asList x).map asTy
def valL (x : Item) : List Val := (asList x).map asVal
def exL (x : Item) : List RawExpr := (asList x).map asExpr

/-- `rcic.scm_val_of_ty`, modelled by `toCore` (pinned in K2). -/
def valOk (v : Val) (t : CoreTy) : Bool := (toCore t v).isSome

/-- `rcic.scm_cfg_vals_ok`. -/
def valsOk (vs : List Val) (ts : List CoreTy) : Bool :=
  vs.length == ts.length && (vs.zip ts).all (fun (v, t) => valOk v t)

/-- `rcic.scm_cfg_has_ty`: `rcic.scm_ty_infer` (modelled by `elabE`) types `e`
    in `g` at `t`. -/
def hasTy (fuel : Int) (p : RawProg) (g : List CoreTy) (e : RawExpr) (t : CoreTy) : Bool :=
  match elabE (fuelN fuel) (sigOf p) g e with
  | .ok ⟨t', _⟩ => t' == t
  | .error _ => false

/-- `rcic.scm_cfg_exprs_ok`. -/
def exprsOk (fuel : Int) (p : RawProg) (g : List CoreTy) (es : List RawExpr) (ts : List CoreTy) : Bool :=
  es.length == ts.length && (es.zip ts).all (fun (e, t) => hasTy fuel p g e t)

/-- `rcic.scm_cfg_fix_state`: the state type of a three-field record. -/
def fixState : CoreTy → Option CoreTy
  | .record fs => if fs.length = 3 then some (fs.getD 1 ("", .i64)).2 else none
  | _ => none

/-- `rcic.scm_cfg_fix_steps_ok`. -/
def fixSteps (fuel : Int) (p : RawProg) (g : List CoreTy) (st : CoreTy) (stop step : RawExpr) : Bool :=
  hasTy fuel p (st :: g) stop .bool && hasTy fuel p (st :: g) step st

/-- `rcic.scm_cfg_fix_bound`, the last conjunct of `FixBound` (the decoder's
    natural numbers give the first two). -/
def fixBound (left count : Int) : Bool := decide (left ≤ i64Max - count)

/-- `rcic.scm_cfg_frame_env_ok`: let, if, pair-left, match, record, cons-head,
    handle. -/
def envOk (fuel : Int) (p : RawProg) (f : Int) (ta tb : CoreTy) (g : List CoreTy) (xs : List Item) : Bool :=
  if f = 0 then hasTy fuel p (ta :: g) (asExpr (itm xs 4)) tb
  else if f = 1 then ta == .bool && hasTy fuel p g (asExpr (itm xs 4)) tb && hasTy fuel p g (asExpr (itm xs 5)) tb
  else if f = 2 then
    match tb with
    | .pair a b => a == ta && hasTy fuel p g (asExpr (itm xs 4)) b
    | _ => false
  else if f = 7 then
    match ta with
    | .sum ts =>
      let bs := exL (itm xs 4)
      bs.length == ts.length && (bs.zip ts).all (fun (b, t) => hasTy fuel p (t :: g) b tb)
    | _ => false
  else if f = 8 then
    match tb with
    | .record fs =>
      let done := valL (itm xs 4)
      let n := done.length
      decide (n < fs.length) && (fs.getD n ("", .i64)).2 == ta &&
        valsOk done ((fs.take n).map Prod.snd) &&
        exprsOk fuel p g (exL (itm xs 5)) ((fs.drop (n + 1)).map Prod.snd)
    | _ => false
  else if f = 10 then
    match tb with
    | .list t => t == ta && hasTy fuel p g (asExpr (itm xs 4)) tb
    | _ => false
  else
    ta == tb &&
      (match catalogPt p.catalog (asStr (itm xs 2)) with
       | some pt => hasTy fuel p (pt :: g) (asExpr (itm xs 5)) tb
       | none => false)

/-- `rcic.scm_cfg_frame_loop_ok`: fold-list, fold-iterate and the four
    bounded-fix frames. -/
def loopOk (fuel : Int) (p : RawProg) (f : Int) (ta tb : CoreTy) (g : List CoreTy) (xs : List Item) : Bool :=
  if f = 12 then
    match ta with
    | .list t => hasTy fuel p g (asExpr (itm xs 4)) tb && hasTy fuel p (t :: tb :: g) (asExpr (itm xs 5)) tb
    | _ => false
  else if f = 13 then
    let x := asTy (itm xs 2)
    ta == tb && (valL (itm xs 5)).all (fun v => valOk v x) && hasTy fuel p (x :: tb :: g) (asExpr (itm xs 6)) tb
  else if f = 14 then
    tb == fixTy ta && hasTy fuel p g (asExpr (itm xs 4)) .i64 &&
      fixSteps fuel p g ta (asExpr (itm xs 5)) (asExpr (itm xs 6))
  else if f = 17 then
    tb == fixTy ta && fixBound (asNum (itm xs 4)) (asNum (itm xs 5)) &&
      fixSteps fuel p g ta (asExpr (itm xs 6)) (asExpr (itm xs 7))
  else
    match fixState tb with
    | none => false
    | some st =>
      tb == fixTy st && valOk (asVal (itm xs 4)) st &&
        (if f = 15 then ta == .i64 && fixSteps fuel p g st (asExpr (itm xs 5)) (asExpr (itm xs 6))
         else ta == .bool && fixBound (asNum (itm xs 5)) (asNum (itm xs 6)) &&
           fixSteps fuel p g st (asExpr (itm xs 7)) (asExpr (itm xs 8)))

/-- `rcic.scm_cfg_frame_args_ok`: an argument frame of a primitive (kind 0)
    or a local call (kind 1). -/
def argsOk (fuel : Int) (p : RawProg) (ta tb : CoreTy) (g : List CoreTy) (xs : List Item) : Bool :=
  let kind := asNum (itm xs 4)
  let sig : Option (List CoreTy × CoreTy) :=
    if kind = 0 then
      match primOfString (asStr (itm xs 5)) with
      | some o => some ((primSig o).ps, (primSig o).rt)
      | none => none
    else if kind = 1 then
      let fn := asNum (itm xs 6)
      if fn < p.fns.length then
        let fd := p.fns.getD fn.toNat ⟨[], .i64, .unknown 0⟩
        some (fd.params, fd.result)
      else none
    else none
  match sig with
  | none => false
  | some (ps, rt) =>
    let done := valL (itm xs 7)
    let n := done.length
    decide (n < ps.length) && ps.getD n .i64 == ta && rt == tb && valsOk done (ps.take n) &&
      exprsOk fuel p g (exL (itm xs 8)) (ps.drop (n + 1))

/-- `rcic.scm_cfg_frame_ok`: one frame against its stored input and output
    types. -/
def frameOk (fuel : Int) (p : RawProg) (fr : Tagged) : Bool :=
  let xs := fr.xs
  let ta := asTy (itm xs 0)
  let tb := asTy (itm xs 1)
  let f := fr.tag
  if f = 3 then
    match tb with
    | .pair a b => b == ta && valOk (asVal (itm xs 2)) a
    | _ => false
  else if f = 4 then
    match ta with
    | .pair a _ => a == tb
    | _ => false
  else if f = 5 then
    match ta with
    | .pair _ b => b == tb
    | _ => false
  else if f = 6 then
    match tb with
    | .sum ts => let i := asNum (itm xs 2); decide (i < ts.length) && ts.getD i.toNat .i64 == ta
    | _ => false
  else if f = 9 then
    match ta with
    | .record fs => let i := asNum (itm xs 2); decide (i < fs.length) && (fs.getD i.toNat ("", .i64)).2 == tb
    | _ => false
  else if f = 11 then
    match ta with
    | .list t => ta == tb && valOk (asVal (itm xs 2)) t
    | _ => false
  else if f = 19 then ta == tb
  else if f = 21 then
    match catalogPt p.catalog (asStr (itm xs 2)) with
    | some pt => pt == ta
    | none => false
  else
    let o := if f = 13 then 3 else if f = 20 then 3 else 2
    let g := tyL (itm xs o)
    if !valsOk (valL (itm xs (o + 1))) g then false
    else if f = 18 then argsOk fuel p ta tb g xs
    else if f > 11 then (if f < 18 then loopOk fuel p f ta tb g xs else envOk fuel p f ta tb g xs)
    else envOk fuel p f ta tb g xs

/-- `rcic.scm_cfg_ctl_ty`: the control's type. -/
def ctlTy (fuel : Int) (p : RawProg) (c : Tagged) : Except String CoreTy :=
  let xs := c.xs
  if c.tag = 0 then
    let g := tyL (itm xs 0)
    if valsOk (valL (itm xs 1)) g then
      match elabE (fuelN fuel) (sigOf p) g (asExpr (itm xs 2)) with
      | .ok ⟨t, _⟩ => .ok t
      | .error e => .error e
    else .error "[rcic_scm_cf_env]"
  else if c.tag = 1 then
    if valOk (asVal (itm xs 1)) (asTy (itm xs 0)) then .ok (asTy (itm xs 0)) else .error "[rcic_scm_cf_control]"
  else
    match catalogPt p.catalog (asStr (itm xs 1)) with
    | some pt => if valOk (asVal (itm xs 2)) pt then .ok (asTy (itm xs 0)) else .error "[rcic_scm_cf_control]"
    | none => .error "[rcic_scm_cf_control]"

/-- `rcic.scm_cfg_ty`: the frame chain from the control's type to the
    configuration's result type. -/
def cfgTy (fuel : Int) (p : RawProg) (c : CfgO) : Except String CoreTy :=
  match ctlTy fuel p c.ctl with
  | .error e => .error e
  | .ok t0 =>
    let r := c.k.foldl (fun (acc : Except String CoreTy) fr =>
      match acc with
      | .error e => .error e
      | .ok cur =>
        if asTy (itm fr.xs 0) == cur then
          (if frameOk fuel p fr then .ok (asTy (itm fr.xs 1)) else .error "[rcic_scm_cf_frame]")
        else .error "[rcic_scm_cf_chain]") (.ok t0)
    match r with
    | .error e => .error e
    | .ok cur => if cur == c.t then .ok c.t else .error "[rcic_scm_cf_result]"

/-- `rcic.scm_cfg_fin_ok`. -/
def finOk (p : RawProg) (f : FinO) : Bool :=
  if f.tag = 0 then valOk (asVal (itm f.xs 0)) f.t
  else
    match catalogPt p.catalog (asStr (itm f.xs 0)) with
    | some pt => valOk (asVal (itm f.xs 1)) pt
    | none => false

inductive CFX where
  | unit
  | obj (o : CX)
  | enc (b d : String) (o : CX)
  deriving BEq

/-- The carrier's output record `{ok, x, code}`. -/
structure CFOut where
  ok : Int
  x : CFX
  code : String
  deriving BEq

def cfOk (x : CFX) : CFOut := ⟨1, x, ""⟩
def cfRefuse (c : String) : CFOut := ⟨0, .unit, c⟩

/-- `rcic.scm_cf_check`. -/
def cfCheck (fuel : Int) (p : RawProg) (kind : Int) (x : CX) : CFOut :=
  if kind = 22 then
    match x with
    | .cfg c => (match cfgTy fuel p c with | .ok _ => cfOk (.obj x) | .error e => cfRefuse e)
    | _ => cfRefuse ""
  else if kind = 23 then
    match x with
    | .fin f => if finOk p f then cfOk (.obj x) else cfRefuse "[rcic_scm_cf_outcome]"
    | _ => cfRefuse ""
  else
    match x with
    | .run tag m =>
      if tag = 0 then
        match m with
        | .fin f => if finOk p f then cfOk (.obj x) else cfRefuse "[rcic_scm_cf_outcome]"
        | _ => cfRefuse ""
      else
        match m with
        | .cfg c => (match cfgTy fuel p c with | .ok _ => cfOk (.obj x) | .error e => cfRefuse e)
        | _ => cfRefuse ""
    | _ => cfRefuse ""

/-- `rcic.scm_cf_at`: the bound program, the object binding, the typing. -/
def cfAt (fuel : Int) (profile : String) (rr : Ref) (rb : String) (br : Ref) (bb : String)
    (kind : Int) (orf : Ref) (ob : String) : CFOut :=
  let pr := bpProgram fuel profile rr rb br bb
  if pr.ok = 0 then cfRefuse pr.code else
  let o := objBind fuel orf kind ob
  if o.ok = 0 then cfRefuse o.code else
  match pr.x, o.x with
  | .bound p _, .cx x => cfCheck fuel p kind x
  | _, _ => cfRefuse ""

/-- `rcic.scm_cf`, the carrier entry point. -/
def scmCF (form fuel : Int) (profile : String) (r : Ref) (b : String) (r2 : Ref) (b2 : String)
    (r3 : Ref) (b3 : String) (xk : Int) (xo : CX) : CFOut :=
  if form < 0 then cfRefuse "[rcic_scm_cf_unknown_form]" else
  if form > 3 then cfRefuse "[rcic_scm_cf_unknown_form]" else
  if form < 3 then cfAt fuel profile r b r2 b2 (form + 22) r3 b3 else
  if xk < 22 then cfRefuse "[rcic_scm_cf_unknown_form]" else
  if xk > 24 then cfRefuse "[rcic_scm_cf_unknown_form]" else
  let bs := objEnc (.cx xo)
  let d := Rcic.TypedRef.deriveDigest 3 xk bs
  let o := cfAt fuel profile r b r2 b2 xk ⟨3, xk, d⟩ bs
  if o.ok = 0 then o else
  match o.x with
  | .obj ob => cfOk (.enc bs d ob)
  | _ => cfRefuse ""

/-! ## What an accepting answer establishes -/

/-- An accepted configuration types at its stored result type, and its
    control types (the start of the 06 §13 frame chain). The frame-by-frame
    statement is the fold in `cfgTy` itself; its correspondence to the typed
    `Cont` is #6029 K3c. -/
theorem cfgTy_ok_result (fuel : Int) (p : RawProg) (c : CfgO) (t : CoreTy) (h : cfgTy fuel p c = .ok t) :
    t = c.t ∧ ∃ t0, ctlTy fuel p c.ctl = .ok t0 := by
  unfold cfgTy at h
  cases hc : ctlTy fuel p c.ctl with
  | error e =>
    rw [hc] at h
    exact absurd h (fun h' => Except.noConfusion h')
  | ok t0 =>
    rw [hc] at h
    dsimp only at h
    split at h
    · exact absurd h (fun h' => Except.noConfusion h')
    · rename_i cur _
      by_cases hcur : (cur == c.t) = true
      · rw [if_pos hcur] at h
        exact ⟨(Except.ok.inj h).symm, t0, rfl⟩
      · rw [if_neg hcur] at h
        exact absurd h (fun h' => Except.noConfusion h')

end Rcic.Scm.CfgAt

/-! ## Pins: apps/rcic-scm-config/rcic_scm_config_corpus.json, 131 rows

Hand-transcribed (§18.3 rule 4). The objects are built the way the corpus
builds them (`apps/rcic-scm-config` generator: a control, frames with their
input and output types, the program of `ScmBoundProgram.Pins`); `enc k o` is
`objEnc` of the object, a ref `rf b k` carries `deriveDigest 3 k b`. The
corpus' bytes and digests come from the engine; the two are compared row for
row. Every row runs at fuel 64 under `SCM-Core-0`. -/

namespace Rcic.Scm.CfgAt.Pins
open Rcic.Scm Rcic.Scm.Wire Rcic.Scm.CfgWire Rcic.Scm.CfgAt Rcic.BoundObject

def I : CoreTy := .i64
def B : CoreTy := .bool
def Str : CoreTy := .str
def li (n : Int) : RawExpr := .lit (.i n) .i64
def lb (b : Int) : RawExpr := .lit (.b b) .bool
def ls (s : String) : RawExpr := .lit (.s s) .str
def v (i : Int) : RawExpr := .var i
def iv (n : Int) : Val := .i n
def bv (b : Int) : Val := .b b
def P0 : String := "SCM-Core-0"
def rf (b : String) (k : Int) : Ref := ⟨3, k, Rcic.TypedRef.deriveDigest 3 k b⟩
def RB : String := Rcic.Scm.BoundProg.Pins.Pp.rb
def BB : String := Rcic.Scm.BoundProg.Pins.Pp.bb
def enc (o : CX) : String := Rcic.Scm.BoundProg.objEnc (.cx o)

def T (t : CoreTy) : Item := .ty t
def Vv (x : Val) : Item := .val x
def E (e : RawExpr) : Item := .expr e
def N (n : Int) : Item := .num n
def Ss (s : String) : Item := .str s
def TL (ts : List CoreTy) : Item := .list (ts.map .ty)
def VL (vs : List Val) : Item := .list (vs.map .val)
def EL (es : List RawExpr) : Item := .list (es.map .expr)

def ctlEval (g : List CoreTy) (env : List Val) (e : RawExpr) : Tagged := ⟨0, [TL g, VL env, E e]⟩
def ctlRet (a : CoreTy) (x : Val) : Tagged := ⟨1, [T a, Vv x]⟩
def ctlRaise (a : CoreTy) (r : String) (x : Val) : Tagged := ⟨2, [T a, Ss r, Vv x]⟩
def fr (tag : Int) (ta tb : CoreTy) (ps : List Item) : Tagged := ⟨tag, T ta :: T tb :: ps⟩
def cfg (t : CoreTy) (c : Tagged) (k : List Tagged) : CX := .cfg ⟨t, c, k⟩
def one (c : Tagged) (f : Tagged) (t : CoreTy) : CX := cfg t c [f]
def finRet (t : CoreTy) (x : Val) : CX := .fin ⟨t, 0, [Vv x]⟩
def finRaise (t : CoreTy) (r : String) (x : Val) : CX := .fin ⟨t, 1, [Ss r, Vv x]⟩

def PIB : CoreTy := .pair I B
def SIB : CoreTy := .sum [I, B]
def REC3 : CoreTy := .record [("a", I), ("b", B), ("c", Str)]
def RA : CoreTy := .record [("a", I)]
def FX : CoreTy := fixTy I
def add01 : RawExpr := .prim "add" [v 0, li 1]
def addv : RawExpr := .prim "add" [v 0, v 1]
def stop : RawExpr := .prim "lt" [li 2, v 0]
def step : RawExpr := .prim "add" [v 0, li 1]
def emptyL : Val := .l []
def nog : List Item := [TL [], VL []]
def dummy : CX := finRet I (iv 5)
def C1 : CX := one (ctlRet I (iv 5)) (fr 0 I I (nog ++ [E add01])) I

def form (n : Int) (b3 : String) (k : Int) (rr : Ref := rf RB 20) : CFOut :=
  scmCF n 64 P0 rr RB (rf BB 21) BB (rf b3 k) b3 0 dummy
def c0 (o : CX) : CFOut := form 0 (enc o) 22
def c1 (o : CX) : CFOut := form 1 (enc o) 23
def c2 (o : CX) : CFOut := form 2 (enc o) 24
def e3 (k : Int) (o : CX) : CFOut := scmCF 3 64 P0 (rf RB 20) RB (rf BB 21) BB ⟨0, 0, ""⟩ "" k o
def okO (o : CX) : CFOut := cfOk (.obj o)
def okE (k : Int) (o : CX) : CFOut := cfOk (.enc (enc o) (Rcic.TypedRef.deriveDigest 3 k (enc o)) o)
def F : CFOut := cfRefuse "[rcic_scm_cf_frame]"
def no (c : String) : CFOut := cfRefuse c

def r0 : CX := one (ctlRet I (iv 5)) (fr 0 I I (nog ++ [E add01])) I
def r1 : CX := one (ctlRet B (bv 1)) (fr 1 B I (nog ++ [E (li 1), E (li 2)])) I
def r2 : CX := one (ctlRet I (iv 1)) (fr 2 I PIB (nog ++ [E (lb 1)])) PIB
def r3 : CX := one (ctlRet B (bv 1)) (fr 3 B PIB [Vv (iv 7)]) PIB
def r4 : CX := one (ctlRet PIB (.p (iv 1) (bv 1))) (fr 4 PIB I []) I
def r5 : CX := one (ctlRet PIB (.p (iv 1) (bv 1))) (fr 5 PIB B []) B
def r6 : CX := one (ctlRet I (iv 3)) (fr 6 I SIB [N 0]) SIB
def r7 : CX := one (ctlRet SIB (.j 0 (iv 3))) (fr 7 SIB I (nog ++ [EL [v 0, li 0]])) I
def r8 : CX := one (ctlRet B (bv 1)) (fr 8 B REC3 (nog ++ [VL [iv 1], EL [ls "x"]])) REC3
def r9 : CX := one (ctlRet RA (.r [iv 1])) (fr 9 RA I [N 0]) I
def r10 : CX := one (ctlRet I (iv 1)) (fr 10 I (.list I) (nog ++ [E (.nil I)])) (.list I)
def r11 : CX := one (ctlRet (.list I) emptyL) (fr 11 (.list I) (.list I) [Vv (iv 1)]) (.list I)
def r12 : CX := one (ctlRet (.list I) emptyL) (fr 12 (.list I) I (nog ++ [E (li 0), E addv])) I
def r13 : CX := one (ctlRet I (iv 0)) (fr 13 I I ([T I] ++ nog ++ [VL [iv 1, iv 2], E addv])) I
def r14 : CX := one (ctlRet I (iv 0)) (fr 14 I FX (nog ++ [E (li 3), E stop, E step])) FX
def r15 : CX := one (ctlRet I (iv 3)) (fr 15 I FX (nog ++ [Vv (iv 0), E stop, E step])) FX
def r16 : CX := one (ctlRet B (bv 0)) (fr 16 B FX (nog ++ [Vv (iv 0), N 3, N 0, E stop, E step])) FX
def r17 : CX := one (ctlRet I (iv 1)) (fr 17 I FX (nog ++ [N 2, N 1, E stop, E step])) FX
def r18 : CX := one (ctlRet I (iv 1)) (fr 18 I I (nog ++ [N 0, Ss "add", N 0, VL [], EL [li 2]])) I
def r19 : CX := one (ctlRet I (iv 2)) (fr 18 I I (nog ++ [N 1, Ss "", N 0, VL [iv 1], EL []])) I
def r20 : CX := one (ctlRet I (iv 5)) (fr 19 I I []) I
def r21 : CX := one (ctlRet I (iv 5)) (fr 20 I I ([Ss "range_violation"] ++ nog ++ [E (v 0)])) I
def r22 : CX := one (ctlRet I (iv 5)) (fr 21 I B [Ss "range_violation"]) B
def r23 : CX := cfg I (ctlEval [I] [iv 4] add01) []
def r24 : CX := cfg I (ctlRaise I "range_violation" (iv 9)) [fr 20 I I ([Ss "range_violation"] ++ nog ++ [E (v 0)])]
def r25 : CX := cfg I (ctlRet I (iv 1)) [fr 2 I (.pair I I) (nog ++ [E (li 2)]), fr 4 (.pair I I) I [], fr 19 I I []]
def r26 : CX := one (ctlRet I (iv 1)) (fr 0 I I [TL [I], VL [iv 7], E addv]) I
def r27 : CX := cfg (.list B) (ctlRet (.list B) emptyL) []
def r28 : CX := cfg (.list I) (ctlRet (.list I) emptyL) []

-- 0–28 one valid configuration per frame kind, controls and chains
#guard c0 r0 == okO r0
#guard c0 r1 == okO r1
#guard c0 r2 == okO r2
#guard c0 r3 == okO r3
#guard c0 r4 == okO r4
#guard c0 r5 == okO r5
#guard c0 r6 == okO r6
#guard c0 r7 == okO r7
#guard c0 r8 == okO r8
#guard c0 r9 == okO r9
#guard c0 r10 == okO r10
#guard c0 r11 == okO r11
#guard c0 r12 == okO r12
#guard c0 r13 == okO r13
#guard c0 r14 == okO r14
#guard c0 r15 == okO r15
#guard c0 r16 == okO r16
#guard c0 r17 == okO r17
#guard c0 r18 == okO r18
#guard c0 r19 == okO r19
#guard c0 r20 == okO r20
#guard c0 r21 == okO r21
#guard c0 r22 == okO r22
#guard c0 r23 == okO r23
#guard c0 r24 == okO r24
#guard c0 r25 == okO r25
#guard c0 r26 == okO r26
#guard c0 r27 == okO r27
#guard c0 r28 == okO r28
-- 29 a frame whose input is not the control's type refused
#guard c0 (one (ctlRet B (bv 1)) (fr 0 I I (nog ++ [E add01])) I) == no "[rcic_scm_cf_chain]"
-- 30 a last frame whose output is not the configuration type refused
#guard c0 (one (ctlRet I (iv 5)) (fr 0 I I (nog ++ [E add01])) B) == no "[rcic_scm_cf_result]"
-- 31 an evaluating control whose environment is not its context refused
#guard c0 (cfg I (ctlEval [I] [bv 1] (v 0)) []) == no "[rcic_scm_cf_env]"
-- 32 an evaluating control whose expression does not type refused by typing
#guard c0 (cfg I (ctlEval [] [] (v 0)) []) == no "[rcic_scm_typing_var_scope]"
-- 33 a returned value not of its stored type refused
#guard c0 (cfg I (ctlRet I (bv 1)) []) == no "[rcic_scm_cf_control]"
-- 34 a raising control with a ref outside the catalog refused
#guard c0 (cfg I (ctlRaise I "zz_missing" (.r [])) []) == no "[rcic_scm_cf_control]"
-- 35 a raising control whose payload is not the catalog type refused
#guard c0 (cfg I (ctlRaise I "range_violation" (bv 1)) []) == no "[rcic_scm_cf_control]"
-- 36–75 frame refusals, one per rule
#guard c0 (one (ctlRet I (iv 5)) (fr 0 I B (nog ++ [E add01])) B) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 1 I I (nog ++ [E (li 1), E (li 2)])) I) == F
#guard c0 (one (ctlRet B (bv 1)) (fr 1 B I (nog ++ [E (li 1), E (lb 1)])) I) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 2 I I (nog ++ [E (lb 1)])) I) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 2 I PIB (nog ++ [E (li 2)])) PIB) == F
#guard c0 (one (ctlRet B (bv 1)) (fr 3 B PIB [Vv (bv 1)]) PIB) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 4 I I []) I) == F
#guard c0 (one (ctlRet PIB (.p (iv 1) (bv 1))) (fr 5 PIB I []) I) == F
#guard c0 (one (ctlRet I (iv 3)) (fr 6 I SIB [N 5]) SIB) == F
#guard c0 (one (ctlRet I (iv 3)) (fr 6 I SIB [N 1]) SIB) == F
#guard c0 (one (ctlRet SIB (.j 0 (iv 3))) (fr 7 SIB I (nog ++ [EL [v 0]])) I) == F
#guard c0 (one (ctlRet SIB (.j 0 (iv 3))) (fr 7 SIB I (nog ++ [EL [v 0, lb 1]])) I) == F
#guard c0 (one (ctlRet B (bv 1)) (fr 8 B (.record [("a", I), ("b", I), ("c", Str)]) (nog ++ [VL [iv 1], EL [ls "x"]]))
    (.record [("a", I), ("b", I), ("c", Str)])) == F
#guard c0 (one (ctlRet B (bv 1)) (fr 8 B REC3 (nog ++ [VL [bv 1], EL [ls "x"]])) REC3) == F
#guard c0 (one (ctlRet B (bv 1)) (fr 8 B REC3 (nog ++ [VL [iv 1], EL [li 1]])) REC3) == F
#guard c0 (one (ctlRet RA (.r [iv 1])) (fr 9 RA I [N 3]) I) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 10 I (.list I) (nog ++ [E (.nil B)])) (.list I)) == F
#guard c0 (one (ctlRet (.list I) emptyL) (fr 11 (.list I) (.list I) [Vv (bv 1)]) (.list I)) == F
#guard c0 (one (ctlRet (.list I) emptyL) (fr 12 (.list I) I (nog ++ [E (lb 1), E addv])) I) == F
#guard c0 (one (ctlRet (.list I) emptyL) (fr 12 (.list I) I (nog ++ [E (li 0), E (lb 1)])) I) == F
#guard c0 (one (ctlRet I (iv 0)) (fr 13 I I ([T I] ++ nog ++ [VL [bv 1], E addv])) I) == F
#guard c0 (one (ctlRet I (iv 0)) (fr 14 I FX (nog ++ [E (lb 1), E stop, E step])) FX) == F
#guard c0 (one (ctlRet I (iv 0)) (fr 14 I FX (nog ++ [E (li 3), E (li 1), E step])) FX) == F
#guard c0 (one (ctlRet B (bv 1)) (fr 15 B FX (nog ++ [Vv (iv 0), E stop, E step])) FX) == F
#guard c0 (one (ctlRet I (iv 3)) (fr 15 I FX (nog ++ [Vv (bv 1), E stop, E step])) FX) == F
#guard c0 (one (ctlRet B (bv 0)) (fr 16 B FX (nog ++ [Vv (iv 0), N 9223372036854775807, N 1, E stop, E step])) FX) == F
#guard c0 (one (ctlRet I (iv 0)) (fr 16 I FX (nog ++ [Vv (iv 0), N 3, N 0, E stop, E step])) FX) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 17 I I (nog ++ [N 2, N 1, E stop, E step])) I) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 17 I FX (nog ++ [N 9223372036854775807, N 1, E stop, E step])) FX) == F
#guard c0 (one (ctlRet B (bv 1)) (fr 18 B I (nog ++ [N 0, Ss "add", N 0, VL [], EL [li 2]])) I) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 18 I I (nog ++ [N 0, Ss "zz", N 0, VL [], EL [li 2]])) I) == F
#guard c0 (one (ctlRet I (iv 2)) (fr 18 I I (nog ++ [N 1, Ss "", N 7, VL [iv 1], EL []])) I) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 18 I B (nog ++ [N 0, Ss "add", N 0, VL [], EL [li 2]])) B) == F
#guard c0 (one (ctlRet I (iv 2)) (fr 18 I I (nog ++ [N 1, Ss "", N 0, VL [bv 1], EL []])) I) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 18 I I (nog ++ [N 0, Ss "add", N 0, VL [], EL [lb 1]])) I) == F
#guard c0 (one (ctlRet I (iv 5)) (fr 19 I B []) B) == F
#guard c0 (one (ctlRet I (iv 5)) (fr 20 I I ([Ss "zz_missing"] ++ nog ++ [E (li 0)])) I) == F
#guard c0 (one (ctlRet I (iv 5)) (fr 20 I I ([Ss "range_violation"] ++ nog ++ [E (lb 1)])) I) == F
#guard c0 (one (ctlRet B (bv 1)) (fr 21 B I [Ss "range_violation"]) I) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 0 I I [TL [I], VL [bv 1], E addv]) I) == F
-- 76 an evaluating control environment shorter than its context refused
#guard c0 (cfg I (ctlEval [I] [] (v 0)) []) == no "[rcic_scm_cf_env]"
-- 77–101 further single-clause frame refusals
#guard c0 (one (ctlRet B (bv 1)) (fr 8 B REC3 (nog ++ [VL [iv 1], EL []])) REC3) == F
#guard c0 (one (ctlRet B (bv 1)) (fr 8 B REC3 (nog ++ [VL [iv 1, bv 1, .s "x"], EL []])) REC3) == F
#guard c0 (one (ctlRet B (bv 1)) (fr 8 B I (nog ++ [VL [], EL []])) I) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 18 I I (nog ++ [N 0, Ss "add", N 0, VL [], EL []])) I) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 18 I I (nog ++ [N 0, Ss "add", N 0, VL [iv 1, iv 2], EL []])) I) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 18 I I (nog ++ [N 2, Ss "add", N 0, VL [], EL [li 2]])) I) == F
#guard c0 (one (ctlRet I (iv 3)) (fr 15 I RA (nog ++ [Vv (iv 0), E stop, E step])) RA) == F
#guard c0 (one (ctlRet I (iv 3)) (fr 15 I REC3 (nog ++ [Vv (bv 1), E (v 0), E (v 0)])) REC3) == F
#guard c0 (one (ctlRet I (iv 3)) (fr 15 I FX (nog ++ [Vv (iv 0), E (li 1), E step])) FX) == F
#guard c0 (one (ctlRet B (bv 0)) (fr 16 B FX (nog ++ [Vv (iv 0), N 3, N 0, E stop, E (lb 1)])) FX) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 17 I FX (nog ++ [N 2, N 1, E stop, E (lb 1)])) FX) == F
#guard c0 (one (ctlRet I (iv 0)) (fr 14 I (fixTy B) (nog ++ [E (li 3), E stop, E step])) (fixTy B)) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 3 I PIB [Vv (iv 7)]) PIB) == F
#guard c0 (one (ctlRet RA (.r [iv 1])) (fr 9 RA B [N 0]) B) == F
#guard c0 (one (ctlRet (.list I) emptyL) (fr 11 (.list I) (.list B) [Vv (iv 1)]) (.list B)) == F
#guard c0 (one (ctlRet unitTy (.r [])) (fr 21 unitTy B [Ss "zz_missing"]) B) == F
#guard c0 (one (ctlRet B (bv 1)) (fr 1 B I (nog ++ [E (lb 1), E (li 2)])) I) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 2 I (.pair B B) (nog ++ [E (lb 1)])) (.pair B B)) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 7 I I (nog ++ [EL [v 0]])) I) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 10 I I (nog ++ [E (.nil I)])) I) == F
#guard c0 (one (ctlRet B (bv 1)) (fr 10 B (.list I) (nog ++ [E (.nil I)])) (.list I)) == F
#guard c0 (one (ctlRet I (iv 5)) (fr 20 I B ([Ss "range_violation"] ++ nog ++ [E (lb 1)])) B) == F
#guard c0 (one (ctlRet I (iv 1)) (fr 12 I I (nog ++ [E (li 0), E addv])) I) == F
#guard c0 (one (ctlRet I (iv 0)) (fr 13 I B ([T I] ++ nog ++ [VL [iv 1], E (v 1)])) B) == F
#guard c0 (one (ctlRet I (iv 0)) (fr 13 I I ([T I] ++ nog ++ [VL [iv 1], E (lb 1)])) I) == F
-- 102 encoding an object of a kind beyond the configuration kinds refused
#guard e3 25 dummy == no "[rcic_scm_cf_unknown_form]"
-- 103 an unknown frame tag refused
#guard form 0 "Ci6:1;iI5;1;5:22;ii" 22 == no "[rcic_scm_cf_tag]"
-- 104 an unknown control tag refused
#guard form 0 "Ci6:3;iI5;0;" 22 == no "[rcic_scm_cf_tag]"
-- 105 a frame count written with a leading zero is not canonical
#guard form 0 "Ci6:1;iI5;01;5:19;ii" 22 == no "[rcic_scm_obj_noncanonical]"
-- 106 trailing bytes inside a frame are not canonical
#guard form 0 "Ci6:1;iI5;1;6:19;iiZ" 22 == no "[rcic_scm_obj_noncanonical]"
-- 107 a configuration ref of another kind refused
#guard scmCF 0 64 P0 (rf RB 20) RB (rf BB 21) BB (rf "Ci6:1;iI5;1;5:19;ii" 23) "Ci6:1;iI5;1;5:19;ii" 0 dummy
  == no "[rcic_scm_obj_class_kind]"
-- 108 a configuration digest derived from other bytes refused
#guard scmCF 0 64 P0 (rf RB 20) RB (rf BB 21) BB (rf "Ci6:3;iI5;0;" 22) "Ci6:1;iI5;1;5:19;ii" 0 dummy
  == no "[rcic_scm_obj_digest]"
-- 109 a configuration under a root ref of other bytes refused by the program binding
#guard form 0 "Ci6:1;iI5;1;5:19;ii" 22 (rf BB 20) == no "[rcic_scm_obj_digest]"
-- 110–117 final outcomes
#guard c1 (finRet I (iv 5)) == okO (finRet I (iv 5))
#guard c1 (finRet I (bv 1)) == no "[rcic_scm_cf_outcome]"
#guard c1 (finRaise I "range_violation" (iv 9)) == okO (finRaise I "range_violation" (iv 9))
#guard c1 (finRaise I "zz_missing" (.r [])) == no "[rcic_scm_cf_outcome]"
#guard c1 (finRaise I "range_violation" (bv 1)) == no "[rcic_scm_cf_outcome]"
#guard c1 (finRet (.list B) emptyL) == okO (finRet (.list B) emptyL)
#guard form 1 "Fi2;I1;" 23 == no "[rcic_scm_cf_tag]"
#guard form 1 "Fi00;I5;" 23 == no "[rcic_scm_obj_noncanonical]"
-- 118–123 run results
#guard c2 (.run 0 (finRet I (iv 5))) == okO (.run 0 (finRet I (iv 5)))
#guard c2 (.run 1 C1) == okO (.run 1 C1)
#guard c2 (.run 0 (finRet I (bv 1))) == no "[rcic_scm_cf_outcome]"
#guard c2 (.run 1 (cfg B (ctlRet I (iv 5)) [])) == no "[rcic_scm_cf_result]"
#guard form 2 "D2;7:Fi0;I5;" 24 == no "[rcic_scm_cf_tag]"
#guard form 2 "D0;8:Fi00;I5;" 24 == no "[rcic_scm_obj_noncanonical]"
-- 124–128 encode
#guard e3 22 C1 == okE 22 C1
#guard e3 22 (cfg B (ctlRet I (iv 5)) []) == no "[rcic_scm_cf_result]"
#guard e3 23 (finRaise I "range_violation" (iv 9)) == okE 23 (finRaise I "range_violation" (iv 9))
#guard e3 24 (.run 1 C1) == okE 24 (.run 1 C1)
#guard e3 18 dummy == no "[rcic_scm_cf_unknown_form]"
-- 129 unknown form 4 refused
#guard scmCF 4 64 P0 (rf RB 20) RB (rf BB 21) BB ⟨0, 0, ""⟩ "" 0 dummy == no "[rcic_scm_cf_unknown_form]"
-- 130 unknown form -1 refused
#guard scmCF (-1) 64 P0 (rf RB 20) RB (rf BB 21) BB ⟨0, 0, ""⟩ "" 0 dummy == no "[rcic_scm_cf_unknown_form]"

end Rcic.Scm.CfgAt.Pins

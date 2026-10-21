/-
RCIC 06 §17 — the canonical core-program wire (K2 statement layer).

Owner text (06:319-341): "The canonical core-program wire binds: SCM
semantics profile, residue catalog, function groups with relative refs,
exact typed signatures and bodies, entry function ref." Decode order 1–7.
"Accepted bytes re-encode exactly; unknown fields, trailing bytes, invalid
refs, bad de Bruijn indices, signature mismatch, or row mismatch are
refused/integrity failures as appropriate."

The byte grammar is the carrier's recorded `[spec_ambiguity]`
(`apps/rcic-scm-wire/APP.md` Encoding): numbers `-?[0-9]+;`, strings
`<count>:<scalars>`, lists `<count>;<elements>`, one-letter type / value /
expression tags, program `M profile catalog ext fns entry`.

PIN (M-002): `scmWire` is `rcic.scm_wire form fuel bytes prog profile`
(#6046), all 22 rows pinned in `ScmWirePins.lean`. Decoding is modelled
call for call: the carrier's `fuel` (decremented per nested element, refusal
`[rcic_scm_wire_fuel]` when negative at `rcic.scm_wire_dec`) is an `Int`
argument exactly as in the carrier; a separate structural `gas` argument
only proves termination and is always supplied large enough
(`gasFor fuel`, every call path decrements carrier fuel at least once per
four calls) — it never runs out on a carrier input. Number syntax is the
landed `parseI64` law of `ScmPrim` (the carrier reuses
`rcic.scm_prim_parse_i64`). Bounded loops (24-character number scan,
1024-element list) refuse when unfinished, as the carrier does.

TRANSCRIPTION TABLE (06 §17 → Lean):
  binds profile / catalog / groups / signatures+bodies / entry → `WireProg`,
        `encProg`, `decProg` field order
  decode order 1 (profiles, catalog) → `decProg` first fields; 2–4
        (signatures, external refs, local scope, bodies) → ext list, fns
        list, then `progCheck` (`ScmExpr`) on the decoded program; 5–6
        (row least fixed points, checked group refs) → NOT DECIDED by the
        carrier (its DOES NOT DECIDE) — not transcribed (M-002b); 7 (close
        local refs, resolve entry) → `progCheck` entry/local-ref refusals
  "accepted bytes re-encode exactly"               → `scmWire` form 0
        compares `encProg (decoded)` with the input
  "unknown fields" → tag refusals; "trailing bytes" → `decProg` length
        check; "invalid refs, bad de Bruijn indices, signature mismatch" →
        `progCheck` refusals propagated by name
-/
import rcic.ScmExpr

namespace Rcic.Scm.Wire
open Rcic.Scm

/-- A core program as the wire binds it: semantics profile + program. -/
structure WireProg where
  profile : String
  prog : RawProg

/-! ## Encoder -/

def encNat (n : Int) : String := toString n ++ ";"
def encStr (x : String) : String := toString x.length ++ ":" ++ x

mutual
def encTy : CoreTy → String
  | .i64 => "i"
  | .bool => "b"
  | .str => "s"
  | .bytes => "y"
  | .list t => "L" ++ encTy t
  | .pair a b => "P" ++ encTy a ++ encTy b
  | .sum ts => "S" ++ encNat ts.length ++ encTys ts
  | .record fs => "R" ++ encNat fs.length ++ encFieldTys fs
def encTys : List CoreTy → String
  | [] => ""
  | t :: ts => encTy t ++ encTys ts
def encFieldTys : List (String × CoreTy) → String
  | [] => ""
  | (k, t) :: fs => encStr k ++ encTy t ++ encFieldTys fs
end

mutual
def encVal : Val → String
  | .i n => "I" ++ encNat n
  | .b b => "B" ++ encNat b
  | .s s => "T" ++ encStr s
  | .y bs => "Y" ++ encNat bs.length ++ String.join (bs.map encNat)
  | .l xs => "L" ++ encNat xs.length ++ encVals xs
  | .p a b => "P" ++ encVal a ++ encVal b
  | .j i x => "J" ++ encNat i ++ encVal x
  | .r fs => "R" ++ encNat fs.length ++ encVals fs
def encVals : List Val → String
  | [] => ""
  | x :: xs => encVal x ++ encVals xs
end

mutual
def encExpr : RawExpr → String
  | .lit x t => "0" ++ encVal x ++ encTy t
  | .var i => "1" ++ encNat i
  | .letE a b => "2" ++ encExpr a ++ encExpr b
  | .ifE c th el => "3" ++ encExpr c ++ encExpr th ++ encExpr el
  | .pair a b => "4" ++ encExpr a ++ encExpr b
  | .fst a => "5" ++ encExpr a
  | .snd a => "6" ++ encExpr a
  | .inj i ts a => "7" ++ encNat i ++ encNat ts.length ++ encTys ts ++ encExpr a
  | .matchE s bs => "8" ++ encExpr s ++ encNat bs.length ++ encExprs bs
  | .recordE keys fs => "9" ++ encNat keys.length ++ String.join (keys.map encStr) ++
      encNat fs.length ++ encExprs fs
  | .field r i => "a" ++ encExpr r ++ encNat i
  | .nil t => "b" ++ encTy t
  | .cons h tl => "c" ++ encExpr h ++ encExpr tl
  | .fold l init body => "d" ++ encExpr l ++ encExpr init ++ encExpr body
  | .fix init limit stop step => "e" ++ encExpr init ++ encExpr limit ++ encExpr stop ++ encExpr step
  | .prim op args => "f" ++ encStr op ++ encNat args.length ++ encExprs args
  | .call (.local i) args => "g" ++ "l" ++ encNat i ++ encNat args.length ++ encExprs args
  | .call (.ext r) args => "g" ++ "x" ++ encStr r ++ encNat args.length ++ encExprs args
  | .raise r p t => "h" ++ encStr r ++ encExpr p ++ encTy t
  | .handle r body h => "j" ++ encStr r ++ encExpr body ++ encExpr h
  | .unknown _ => ""
def encExprs : List RawExpr → String
  | [] => ""
  | e :: es => encExpr e ++ encExprs es
end

def encFns : List RawFnDef → String
  | [] => ""
  | f :: fs => encNat f.params.length ++ encTys f.params ++ encTy f.result ++ encExpr f.body ++ encFns fs

def encProg (w : WireProg) : String :=
  "M" ++ encStr w.profile ++
  encNat w.prog.catalog.length ++ String.join (w.prog.catalog.map (fun c => encStr c.ref ++ encTy c.pt)) ++
  encNat w.prog.ext.length ++
    String.join (w.prog.ext.map (fun e => encStr e.ref ++ encNat e.params.length ++ encTys e.params ++ encTy e.result)) ++
  encNat w.prog.fns.length ++ encFns w.prog.fns ++
  encNat w.prog.entry

/-! ## Decoder -/

/-- A decoded item of any of the carrier's element kinds. -/
inductive Item where
  | ty (t : CoreTy)
  | val (v : Val)
  | expr (e : RawExpr)
  | num (n : Int)
  | str (s : String)
  | cat (c : CatalogEntry)
  | ext (e : ExtSig)
  | fn (f : RawFnDef)
  | field (k : String) (t : CoreTy)
  | list (xs : List Item)
  deriving Inhabited

abbrev Dec := Except String (Item × Nat)

def wErr (c : String) : Except String α := .error ("[rcic_scm_wire_" ++ c ++ "]")

def charAt (cs : Array Char) (p : Nat) : Option Char := cs[p]?

/-- `rcic.scm_wire_scan_to`: the first `c` at or after `p` within 24
    positions; `-1` at end of input, `-2` when the bounded scan did not
    finish. -/
def scanTo (cs : Array Char) (c : Char) : Nat → Nat → Int
  | i, n =>
    if i ≥ cs.size then -1
    else match n with
      | 0 => -2
      | n + 1 => if cs[i]! = c then i else scanTo cs c (i + 1) n

def sliceStr (cs : Array Char) (a b : Nat) : String := String.mk ((cs.toList.drop a).take (b - a))

/-- `rcic.scm_wire_dec_num`: a number up to the terminator `term`, parsed
    by the landed `-?[0-9]+` law `parseI64` (`ScmPrim`). -/
def decNum (cs : Array Char) (p : Nat) (term : Char) : Except String (Int × Nat) :=
  let j := scanTo cs term p 24
  if j = -1 then wErr "truncated"
  else if j = -2 then wErr "number"
  else match parseI64 (sliceStr cs p j.toNat) with
    | .returned (.i64V n _) => .ok (n, j.toNat + 1)
    | .raised _ => wErr "number"

def decNat (cs : Array Char) (p : Nat) : Except String (Int × Nat) := do
  let (n, q) ← decNum cs p ';'
  if n < 0 then wErr "number" else pure (n, q)

def decStr (cs : Array Char) (p : Nat) : Except String (String × Nat) := do
  let (n, q) ← decNum cs p ':'
  if n < 0 then wErr "number"
  else if q + n.toNat > cs.size then wErr "truncated"
  else pure (sliceStr cs q (q + n.toNat), q + n.toNat)

def asTy : Item → CoreTy | .ty t => t | _ => .i64
def asVal : Item → Val | .val v => v | _ => .i 0
def asExpr : Item → RawExpr | .expr e => e | _ => .unknown 0
def asNum : Item → Int | .num n => n | _ => 0
def asStr : Item → String | .str s => s | _ => ""
def asList : Item → List Item | .list xs => xs | _ => []
def asField : Item → String × CoreTy | .field k t => (k, t) | _ => ("", .i64)

/-- The expression schemas (`rcic.scm_wire_expr_schema`): element kinds in
    field order; `5` a natural number, `≥ 10` a list of kind `- 10`. -/
def exprSchema : Nat → List Nat
  | 0 => [1, 0] | 1 => [5] | 2 => [2, 2] | 3 => [2, 2, 2] | 4 => [2, 2] | 5 => [2] | 6 => [2]
  | 7 => [5, 10, 2] | 8 => [2, 12] | 9 => [14, 12] | 10 => [2, 5] | 11 => [0] | 12 => [2, 2]
  | 13 => [2, 2, 2] | 14 => [2, 2, 2, 2] | 15 => [4, 12] | 17 => [4, 2, 0] | _ => [4, 2, 2]

/-- `rcic.scm_wire_expr_build`. -/
def exprBuild (k : Nat) (xs : List Item) : RawExpr :=
  let x0 := xs.headD default
  let x1 := (xs.drop 1).headD default
  let x2 := (xs.drop 2).headD default
  let x3 := (xs.drop 3).headD default
  match k with
  | 0 => .lit (asVal x0) (asTy x1)
  | 1 => .var (asNum x0)
  | 2 => .letE (asExpr x0) (asExpr x1)
  | 3 => .ifE (asExpr x0) (asExpr x1) (asExpr x2)
  | 4 => .pair (asExpr x0) (asExpr x1)
  | 5 => .fst (asExpr x0)
  | 6 => .snd (asExpr x0)
  | 7 => .inj (asNum x0) ((asList x1).map asTy) (asExpr x2)
  | 8 => .matchE (asExpr x0) ((asList x1).map asExpr)
  | 9 => .recordE ((asList x0).map asStr) ((asList x1).map asExpr)
  | 10 => .field (asExpr x0) (asNum x1)
  | 11 => .nil (asTy x0)
  | 12 => .cons (asExpr x0) (asExpr x1)
  | 13 => .fold (asExpr x0) (asExpr x1) (asExpr x2)
  | 14 => .fix (asExpr x0) (asExpr x1) (asExpr x2) (asExpr x3)
  | 15 => .prim (asStr x0) ((asList x1).map asExpr)
  | 17 => .raise (asStr x0) (asExpr x1) (asTy x2)
  | _ => .handle (asStr x0) (asExpr x1) (asExpr x2)

def exprTagKind (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 97 ≤ n ∧ n ≤ 104 then some (n - 87)
  else if n = 106 then some 18
  else none

mutual
/-- `rcic.scm_wire_dec`: the kind dispatcher; the only fuel check. -/
def dec (cs : Array Char) : Nat → Nat → Int → Nat → Dec
  | 0, _, _, _ => .error "[gas]"
  | g + 1, kind, fuel, p =>
    if fuel < 0 then wErr "fuel" else
    match kind with
    | 0 => decTy cs g fuel p
    | 1 => decVal cs g fuel p
    | 2 => decExpr cs g fuel p
    | 3 => (decNum cs p ';').map (fun (n, q) => (.num n, q))
    | 4 => (decStr cs p).map (fun (s, q) => (.str s, q))
    | 6 => do
        let (r, q1) ← decStr cs p
        let (ps, q2) ← decList cs g 0 fuel q1
        let (t, q3) ← decTy cs g (fuel - 1) q2
        pure (.ext ⟨r, (asList ps).map asTy, asTy t⟩, q3)
    | 7 => do
        let (ps, q1) ← decList cs g 0 fuel p
        let (t, q2) ← decTy cs g (fuel - 1) q1
        let (b, q3) ← decExpr cs g (fuel - 1) q2
        pure (.fn ⟨(asList ps).map asTy, asTy t, asExpr b⟩, q3)
    | 5 => do
        let (r, q1) ← decStr cs p
        let (t, q2) ← decTy cs g (fuel - 1) q1
        pure (.cat ⟨r, asTy t⟩, q2)
    | _ => do
        let (k, q1) ← decStr cs p
        let (t, q2) ← decTy cs g (fuel - 1) q1
        pure (.field k (asTy t), q2)
/-- `rcic.scm_wire_dec_ty`. -/
def decTy (cs : Array Char) : Nat → Int → Nat → Dec
  | 0, _, _ => .error "[gas]"
  | g + 1, fuel, p =>
    let q := p + 1
    match charAt cs p with
    | some 'i' => .ok (.ty .i64, q)
    | some 'b' => .ok (.ty .bool, q)
    | some 's' => .ok (.ty .str, q)
    | some 'y' => .ok (.ty .bytes, q)
    | some 'L' => do
        let (a, q1) ← dec cs g 0 (fuel - 1) q
        pure (.ty (.list (asTy a)), q1)
    | some 'P' => do
        let (a, q1) ← dec cs g 0 (fuel - 1) q
        let (b, q2) ← dec cs g 0 (fuel - 1) q1
        pure (.ty (.pair (asTy a) (asTy b)), q2)
    | some 'S' => do
        let (xs, q1) ← decList cs g 0 fuel q
        pure (.ty (.sum ((asList xs).map asTy)), q1)
    | some 'R' => do
        let (xs, q1) ← decList cs g 8 fuel q
        pure (.ty (.record ((asList xs).map asField)), q1)
    | none => wErr "truncated"
    | some _ => wErr "tag"
/-- `rcic.scm_wire_dec_val`. -/
def decVal (cs : Array Char) : Nat → Int → Nat → Dec
  | 0, _, _ => .error "[gas]"
  | g + 1, fuel, p =>
    let q := p + 1
    match charAt cs p with
    | some 'I' => (decNum cs q ';').map (fun (n, q1) => (.val (.i n), q1))
    | some 'B' => (decNat cs q).map (fun (n, q1) => (.val (.b n), q1))
    | some 'T' => (decStr cs q).map (fun (s, q1) => (.val (.s s), q1))
    | some 'Y' => do
        let (xs, q1) ← decList cs g 3 fuel q
        pure (.val (.y ((asList xs).map asNum)), q1)
    | some 'L' => do
        let (xs, q1) ← decList cs g 1 fuel q
        pure (.val (.l ((asList xs).map asVal)), q1)
    | some 'P' => do
        let (a, q1) ← dec cs g 1 (fuel - 1) q
        let (b, q2) ← dec cs g 1 (fuel - 1) q1
        pure (.val (.p (asVal a) (asVal b)), q2)
    | some 'J' => do
        let (i, q1) ← decNat cs q
        let (b, q2) ← dec cs g 1 (fuel - 1) q1
        pure (.val (.j i (asVal b)), q2)
    | some 'R' => do
        let (xs, q1) ← decList cs g 1 fuel q
        pure (.val (.r ((asList xs).map asVal)), q1)
    | none => wErr "truncated"
    | some _ => wErr "tag"
/-- `rcic.scm_wire_dec_expr`. -/
def decExpr (cs : Array Char) : Nat → Int → Nat → Dec
  | 0, _, _ => .error "[gas]"
  | g + 1, fuel, p =>
    let q := p + 1
    match charAt cs p with
    | none => wErr "truncated"
    | some 'g' => do
        let (f, q1) ← match charAt cs q with
          | some 'l' => (decNat cs (q + 1)).map (fun (i, q1) => (RawFn.local i, q1))
          | some 'x' => (decStr cs (q + 1)).map (fun (r, q1) => (RawFn.ext r, q1))
          | none => wErr "truncated"
          | some _ => wErr "tag"
        let (xs, q2) ← decList cs g 2 fuel q1
        pure (.expr (.call f ((asList xs).map asExpr)), q2)
    | some c =>
      match exprTagKind c with
      | none => wErr "tag"
      | some k => do
          let (xs, q1) ← decSeq cs g fuel q (exprSchema k)
          pure (.expr (exprBuild k xs), q1)
/-- `rcic.scm_wire_dec_seq`: decode the fields of a schema in order. -/
def decSeq (cs : Array Char) : Nat → Int → Nat → List Nat → Except String (List Item × Nat)
  | 0, _, _, _ => .error "[gas]"
  | _, _, p, [] => .ok ([], p)
  | g + 1, fuel, p, kd :: kds => do
      let (x, q) ←
        if kd ≥ 10 then decList cs g (kd - 10) fuel p
        else if kd = 5 then (decNat cs p).map (fun (n, q) => (Item.num n, q))
        else dec cs g kd (fuel - 1) p
      let (xs, q') ← decSeq cs g fuel q kds
      pure (x :: xs, q')
/-- `rcic.scm_wire_dec_list`: a counted list, at most 1024 elements. -/
def decList (cs : Array Char) : Nat → Nat → Int → Nat → Dec
  | 0, _, _, _ => .error "[gas]"
  | g + 1, kind, fuel, p => do
      let (n, q) ← decNat cs p
      let (xs, q') ← decElems cs g kind fuel n q 1024
      pure (.list xs, q')
/-- The list loop: `left` elements still to read, `iters` loop steps left
    (the carrier's 1024-step `fix`; an unfinished loop is `bound`). -/
def decElems (cs : Array Char) : Nat → Nat → Int → Int → Nat → Nat → Except String (List Item × Nat)
  | 0, _, _, _, _, _ => .error "[gas]"
  | g + 1, kind, fuel, left, p, iters =>
    if left ≤ 0 then .ok ([], p) else
    match iters with
    | 0 => wErr "bound"
    | it + 1 => do
        let (x, q) ← dec cs g kind (fuel - 1) p
        let (xs, q') ← decElems cs g kind fuel (left - 1) q it
        pure (x :: xs, q')
end

/-- Termination gas for a carrier fuel: generous enough that the carrier's
    own fuel / bound refusals always come first. -/
def gasFor (fuel : Int) (len : Nat) : Nat := 8 * (fuel.toNat + 4) + 4 * len + 4200

/-- `rcic.scm_wire_dec_prog`. -/
def decProg (s : String) (fuel : Int) : Except String WireProg :=
  let cs := s.toList.toArray
  match charAt cs 0 with
  | some 'M' => do
      let (xs, q) ← decSeq cs (gasFor fuel cs.size) fuel 1 [4, 15, 16, 17, 5]
      if q ≠ cs.size then wErr "trailing" else
      let x0 := xs.headD default
      let x1 := (xs.drop 1).headD default
      let x2 := (xs.drop 2).headD default
      let x3 := (xs.drop 3).headD default
      let x4 := (xs.drop 4).headD default
      pure ⟨asStr x0,
        ⟨(asList x3).map (fun i => match i with | .fn f => f | _ => ⟨[], .i64, .unknown 0⟩),
         (asList x2).map (fun i => match i with | .ext e => e | _ => ⟨"", [], .i64⟩),
         (asList x1).map (fun i => match i with | .cat c => c | _ => ⟨"", .i64⟩),
         asNum x4⟩⟩
  | none => wErr "truncated"
  | some _ => wErr "tag"

/-! ## The carrier entry point -/

structure WireOut where
  ok : Int
  t : CoreTy
  bytes : Option String
  code : String
  deriving BEq

def scmWire (form fuel : Int) (bytes : String) (w : WireProg) (profile : String) : WireOut :=
  if form = 0 then
    match decProg bytes fuel with
    | .error c => ⟨0, unitTy, none, c⟩
    | .ok d =>
      if encProg d ≠ bytes then ⟨0, unitTy, none, "[rcic_scm_wire_noncanonical]"⟩
      else if d.profile ≠ profile then ⟨0, unitTy, none, "[rcic_scm_wire_profile]"⟩
      else
        let o := scmTyping 0 fuel d.prog [] (.nil .i64)
        ⟨o.ok, o.t, none, o.code⟩
  else if form = 1 then ⟨1, unitTy, some (encProg w), ""⟩
  else ⟨0, unitTy, none, "[rcic_scm_wire_unknown_form]"⟩

end Rcic.Scm.Wire

/-
RCIC 07 §22 — the compact instantiate program, version 1 (#6029 K4-2):
its representation, its SCM-Core-0 program, and the facts the first
certificate needs about it, on the first-order machine `Raw.step` (the
model pinned to `apps/rcic-scm-core`).

Owner text: 07 §22 "The first native certificate targets the exact
`instantiate.scm` core program." State = Unit; ResidueRow = ∅; Pre "term well
scoped at depth+1 and replacement well scoped at depth"; ReturnPost "output
equals declarative capture-free substitution and remains well scoped";
"Bound = exact affine function of input syntax sizes".

Reading: 00 §19.7 E-07CompactInstantiate. The output is compact: the
processed skeleton of `e`, with each substituted position a marker `SUB(d)`,
and `r` once. `expandCompact` reads only those two and puts `lift 0 d r` at a
marker; the production `instantiate0` (`RcicDeclarative`) is the semantic
reference. V1's Pre adds the capacity condition `N_e < 2^63 − 1`.

Representation (V1). A token is the record `{k, l, n}` (`tokV`):
  k 0 bvar (n index), 1 sort (l level), 2 const (n ref, l level list),
  3 app, 4 lam, 5 pi, 6 letE, 7 lit (n value), 8 ENTER, 9 EXIT,
  10 SUB (output only, n depth).
A term is its prefix token list (`encToks`). ENTER and EXIT enclose exactly
a binder's body: a lam / pi domain, and a let's type and value, stay outside
them. Naturals are i64 payloads, so `encToks` is `none` when one is ≥ 2^63
(a representation limit, recorded in the erratum, not a narrowing of
`Expr Nat`).
-/
import rcic.ScmRawRun
import rcic.ScmBoundProgram
import rcic.RcicSubstCalc
import rcic.ScmRowDerive

namespace Rcic.Scm.Inst
open Rcic.Scm Rcic.Scm.Raw Rcic.Declarative

/-! ## Representation -/

def tokV (k : Int) (l : String) (n : Int) : Val := .r [.i k, .s l, .i n]
def enterT : Val := tokV 8 "" 0
def exitT : Val := tokV 9 "" 0
def subT (d : Int) : Val := tokV 10 "" d

/-- Canonical level bytes: a prefix code. -/
def encLevel : Level → String
  | .zero => "z"
  | .succ l => "s" ++ encLevel l
  | .max a b => "m" ++ encLevel a ++ encLevel b
  | .imax a b => "i" ++ encLevel a ++ encLevel b
  | .param i => "p" ++ toString i ++ ";"

def encLevels (ls : List Level) : String := toString ls.length ++ ";" ++ String.join (ls.map encLevel)

/-- A natural the i64 payload carries losslessly. -/
def repN (n : Nat) : Bool := decide ((n : Int) ≤ i64Max)

/-- The V1 input encoding of a term; `none` when a natural is not
    representable. -/
def encToks : Expr Nat → Option (List Val)
  | .bvar i => if repN i then some [tokV 0 "" i] else none
  | .sort l => some [tokV 1 (encLevel l) 0]
  | .const r ls => if repN r then some [tokV 2 (encLevels ls) r] else none
  | .app f x =>
    match encToks f, encToks x with
    | some a, some b => some ([tokV 3 "" 0] ++ a ++ b)
    | _, _ => none
  | .lam a b =>
    match encToks a, encToks b with
    | some ta, some tb => some ([tokV 4 "" 0] ++ ta ++ [enterT] ++ tb ++ [exitT])
    | _, _ => none
  | .pi a b =>
    match encToks a, encToks b with
    | some ta, some tb => some ([tokV 5 "" 0] ++ ta ++ [enterT] ++ tb ++ [exitT])
    | _, _ => none
  | .letE a v b =>
    match encToks a, encToks v, encToks b with
    | some ta, some tv, some tb => some ([tokV 6 "" 0] ++ ta ++ tv ++ [enterT] ++ tb ++ [exitT])
    | _, _, _ => none
  | .lit t => if repN t then some [tokV 7 "" t] else none

/-- The skeleton the program produces from `e` at binder depth `d`: hits
    become `SUB(d)`, indices above the hit drop by one, the rest is kept. -/
def skelOf (d : Nat) : Expr Nat → List Val
  | .bvar i => if i = d then [subT d] else if d < i then [tokV 0 "" ((i : Int) - 1)] else [tokV 0 "" i]
  | .sort l => [tokV 1 (encLevel l) 0]
  | .const r ls => [tokV 2 (encLevels ls) r]
  | .app f x => [tokV 3 "" 0] ++ skelOf d f ++ skelOf d x
  | .lam a b => [tokV 4 "" 0] ++ skelOf d a ++ [enterT] ++ skelOf (d + 1) b ++ [exitT]
  | .pi a b => [tokV 5 "" 0] ++ skelOf d a ++ [enterT] ++ skelOf (d + 1) b ++ [exitT]
  | .letE a v b => [tokV 6 "" 0] ++ skelOf d a ++ skelOf d v ++ [enterT] ++ skelOf (d + 1) b ++ [exitT]
  | .lit t => [tokV 7 "" t]

/-- The input value `{depth, e, r}`. -/
def inputV (D : Int) (te tr : List Val) : Val := .r [.i D, .l te, .l tr]

/-- The output value `{repl, skel}`. -/
def outV (tr skel : List Val) : Val := .r [.l tr, .l skel]

/-! ## The program (V1) -/

def TOK : CoreTy := .record [("k", .i64), ("l", .str), ("n", .i64)]
def ACC : CoreTy := .record [("d", .i64), ("out", .list TOK)]
def INP : CoreTy := .record [("depth", .i64), ("e", .list TOK), ("r", .list TOK)]
def OUT : CoreTy := .record [("repl", .list TOK), ("skel", .list TOK)]
def OV : String := "signed_overflow"

def li (n : Int) : RawExpr := .lit (.i n) .i64
def lstr (s : String) : RawExpr := .lit (.s s) .str
def fld (r : RawExpr) (i : Int) : RawExpr := .field r i
def tokE (k l n : RawExpr) : RawExpr := .recordE ["k", "l", "n"] [k, l, n]
def accE (d out : RawExpr) : RawExpr := .recordE ["d", "out"] [d, out]

/-- In the fold body, after `let kk`: 0 = kk, 1 = the token, 2 = the
    accumulator; under a handler every index moves up by one. -/
def enterB : RawExpr :=
  accE (.handle OV (.prim "add" [fld (.var 2) 0, li 1]) (fld (.var 3) 0)) (.cons (.var 1) (fld (.var 2) 1))
def exitB : RawExpr :=
  accE (.handle OV (.prim "sub" [fld (.var 2) 0, li 1]) (fld (.var 3) 0)) (.cons (.var 1) (fld (.var 2) 1))
/-- After `let i`: 0 = i, 1 = kk, 2 = the token, 3 = the accumulator. -/
def bvarTok : RawExpr :=
  .ifE (.prim "eq" [.var 0, fld (.var 3) 0]) (tokE (li 10) (lstr "") (fld (.var 3) 0))
    (.ifE (.prim "lt" [fld (.var 3) 0, .var 0])
      (tokE (li 0) (lstr "") (.handle OV (.prim "sub" [.var 0, li 1]) (.var 1)))
      (.var 2))
def bvarB : RawExpr := .letE (fld (.var 1) 2) (accE (fld (.var 3) 0) (.cons bvarTok (fld (.var 3) 1)))
def otherB : RawExpr := accE (fld (.var 2) 0) (.cons (.var 1) (fld (.var 2) 1))
def BODY : RawExpr :=
  .letE (fld (.var 0) 0)
    (.ifE (.prim "eq" [.var 0, li 8]) enterB
      (.ifE (.prim "eq" [.var 0, li 9]) exitB
        (.ifE (.prim "eq" [.var 0, li 0]) bvarB otherB)))
def INIT : RawExpr := accE (li 0) (.nil TOK)
def REV : RawExpr := .cons (.var 0) (.var 1)
def MAIN : RawExpr :=
  .letE (.fold (fld (.var 0) 1) INIT BODY)
    (.pair (.recordE ["repl", "skel"] [fld (.var 1) 2, .fold (fld (.var 0) 1) (.nil TOK) REV]) (.var 2))

def instProg : RawProg := ⟨[⟨[INP, unitTy], .pair OUT unitTy, MAIN⟩], [], [⟨OV, unitTy⟩], 0⟩

/-- The program's root digest, as pinned in `scm/rcic/scm_inst.scm`. -/
def instRoot : String := "8a69f424e0cda33f9d1045c36b8573b25bba73422c2f6fd967c65a62252a4a39"

-- The Lean program is the carrier's program: its canonical root bytes derive the pinned digest.
#guard Rcic.TypedRef.deriveDigest 3 20 (BoundProg.Pins.parts instProg).rb == instRoot
-- It is well typed, and its derived entry row is empty (06 §7, the landed row derivation).
def progOk : Bool := match progCheck 64 instProg with | .ok _ => true | .error _ => false
#guard progOk
#guard (RowDerive.scmRows 0 64 instProg []).ok == 1 && (RowDerive.scmRows 0 64 instProg []).row == []

/-! ## The four primitives on in-range integers -/

theorem prim_eq {a b : Int} (ha : inI64 a) (hb : inI64 b) :
    scmPrim 0 "eq" [.i a, .i b] 0 = ⟨1, 0, .b (if a = b then 1 else 0), "", 1, ""⟩ := by
  simp [scmPrim, primOfString, primSig, toCoreVals, toCore, ha, hb, firstStrLen, primBound, primCost,
    primLaw, PrimOut.ofLaw, boolResult, CoreVal.erase]

theorem prim_lt {a b : Int} (ha : inI64 a) (hb : inI64 b) :
    scmPrim 0 "lt" [.i a, .i b] 0 = ⟨1, 0, .b (if a < b then 1 else 0), "", 1, ""⟩ := by
  simp [scmPrim, primOfString, primSig, toCoreVals, toCore, ha, hb, firstStrLen, primBound, primCost,
    primLaw, PrimOut.ofLaw, boolResult, CoreVal.erase]

theorem prim_add {a b : Int} (ha : inI64 a) (hb : inI64 b) (hab : inI64 (a + b)) :
    scmPrim 0 "add" [.i a, .i b] 0 = ⟨1, 0, .i (a + b), "", 1, ""⟩ := by
  simp [scmPrim, primOfString, primSig, toCoreVals, toCore, ha, hb, hab, firstStrLen, primBound, primCost,
    primLaw, PrimOut.ofLaw, checkedI64, CoreVal.erase]

theorem prim_sub {a b : Int} (ha : inI64 a) (hb : inI64 b) (hab : inI64 (a - b)) :
    scmPrim 0 "sub" [.i a, .i b] 0 = ⟨1, 0, .i (a - b), "", 1, ""⟩ := by
  simp [scmPrim, primOfString, primSig, toCoreVals, toCore, ha, hb, hab, firstStrLen, primBound, primCost,
    primLaw, PrimOut.ofLaw, checkedI64, CoreVal.erase]

/-! ## The fold body, branch by branch (exact SCM-Cost-0 counts) -/

def accV (d : Int) (out : List Val) : Val := .r [.i d, .l out]


theorem nth_0 (a : Val) (xs : List Val) : nth? (a :: xs) 0 = some a := by simp [nth?]
theorem nth_1 (a b : Val) (xs : List Val) : nth? (a :: b :: xs) 1 = some b := by simp [nth?]
theorem nth_2 (a b c : Val) (xs : List Val) : nth? (a :: b :: c :: xs) 2 = some c := by simp [nth?]
theorem nth_3 (a b c d : Val) (xs : List Val) : nth? (a :: b :: c :: d :: xs) 3 = some d := by simp [nth?]

theorem inI64_of {n : Int} (h0 : 0 ≤ n) (h1 : n ≤ i64Max) : inI64 n :=
  ⟨Int.le_trans (by decide) h0, h1⟩

/-- The token's kind, read by `let kk`. -/
theorem ev_kind (env0 : List Val) (k : Int) (l : String) (n : Int) (acc : Val) :
    Evals instProg (tokV k l n :: acc :: env0) (fld (.var 0) 0) (.i k) 3 :=
  ev_field (ev_var (nth_0 _ _)) (by simp [nth?, tokV])

/-- `eq kk c` on the bound kind. -/
theorem ev_eqk (E : List Val) (k c : Int) (hk : inI64 k) (hc : inI64 c) :
    Evals instProg (.i k :: E) (.prim "eq" [.var 0, li c]) (.b (if k = c then 1 else 0)) 5 :=
  (ev_prim2 (ev_var (nth_0 _ _)) (ev_lit _ _ (.i c) .i64) (prim_eq hk hc)).cast rfl rfl

theorem body_enter (env0 : List Val) (l : String) (n d : Int) (out : List Val)
    (hd : 0 ≤ d) (hd1 : d + 1 ≤ i64Max) :
    Evals instProg (tokV 8 l n :: accV d out :: env0) BODY (accV (d + 1) (tokV 8 l n :: out)) 31 := by
  have hdi : inI64 d := inI64_of hd (by omega)
  have hd1i : inI64 (d + 1) := inI64_of (by omega) hd1
  have e1 : Evals instProg (.i 8 :: tokV 8 l n :: accV d out :: env0)
      (.handle OV (.prim "add" [fld (.var 2) 0, li 1]) (fld (.var 3) 0)) (.i (d + 1)) 9 :=
    ev_handle ((ev_prim2 (ev_field (ev_var (nth_2 _ _ _ _)) (by simp [nth?, accV]))
      (ev_lit _ _ (.i 1) .i64) (prim_add hdi (by decide) hd1i)).cast rfl rfl)
  have e2 : Evals instProg (.i 8 :: tokV 8 l n :: accV d out :: env0)
      (.cons (.var 1) (fld (.var 2) 1)) (.l (tokV 8 l n :: out)) 7 :=
    ev_cons (ev_var (nth_1 _ _ _)) (ev_field (ev_var (nth_2 _ _ _ _)) (by simp [nth?, accV]))
  have eB : Evals instProg (.i 8 :: tokV 8 l n :: accV d out :: env0) enterB
      (accV (d + 1) (tokV 8 l n :: out)) 19 := (ev_rec2 e1 e2).cast rfl rfl
  have hc : Evals instProg (.i 8 :: tokV 8 l n :: accV d out :: env0)
      (.prim "eq" [.var 0, li 8]) (.b 1) 5 := (ev_eqk _ 8 8 (by decide) (by decide)).cast (by simp) rfl
  have eI := ev_if_true hc eB
    (el := .ifE (.prim "eq" [.var 0, li 9]) exitB (.ifE (.prim "eq" [.var 0, li 0]) bvarB otherB))
  exact (ev_let (ev_kind env0 8 l n (accV d out)) eI).cast rfl rfl

theorem body_exit (env0 : List Val) (l : String) (n d : Int) (out : List Val)
    (hd : 1 ≤ d) (hd1 : d ≤ i64Max) :
    Evals instProg (tokV 9 l n :: accV d out :: env0) BODY (accV (d - 1) (tokV 9 l n :: out)) 38 := by
  have hdi : inI64 d := inI64_of (by omega) hd1
  have hd1i : inI64 (d - 1) := inI64_of (by omega) (by omega)
  have e1 : Evals instProg (.i 9 :: tokV 9 l n :: accV d out :: env0)
      (.handle OV (.prim "sub" [fld (.var 2) 0, li 1]) (fld (.var 3) 0)) (.i (d - 1)) 9 :=
    ev_handle ((ev_prim2 (ev_field (ev_var (nth_2 _ _ _ _)) (by simp [nth?, accV]))
      (ev_lit _ _ (.i 1) .i64) (prim_sub hdi (by decide) hd1i)).cast rfl rfl)
  have e2 : Evals instProg (.i 9 :: tokV 9 l n :: accV d out :: env0)
      (.cons (.var 1) (fld (.var 2) 1)) (.l (tokV 9 l n :: out)) 7 :=
    ev_cons (ev_var (nth_1 _ _ _)) (ev_field (ev_var (nth_2 _ _ _ _)) (by simp [nth?, accV]))
  have eB : Evals instProg (.i 9 :: tokV 9 l n :: accV d out :: env0) exitB
      (accV (d - 1) (tokV 9 l n :: out)) 19 := (ev_rec2 e1 e2).cast rfl rfl
  have hc2 : Evals instProg (.i 9 :: tokV 9 l n :: accV d out :: env0)
      (.prim "eq" [.var 0, li 9]) (.b 1) 5 := (ev_eqk _ 9 9 (by decide) (by decide)).cast (by simp) rfl
  have eI2 := ev_if_true hc2 eB (el := .ifE (.prim "eq" [.var 0, li 0]) bvarB otherB)
  have hc1 : Evals instProg (.i 9 :: tokV 9 l n :: accV d out :: env0)
      (.prim "eq" [.var 0, li 8]) (.b 0) 5 := (ev_eqk _ 9 8 (by decide) (by decide)).cast (by simp) rfl
  have eI1 := ev_if_false hc1 (by decide) eI2 (th := enterB)
  exact (ev_let (ev_kind env0 9 l n (accV d out)) eI1).cast rfl rfl

theorem body_other (env0 : List Val) (k : Int) (l : String) (n d : Int) (out : List Val)
    (hk : inI64 k) (h8 : k ≠ 8) (h9 : k ≠ 9) (h0 : k ≠ 0) :
    Evals instProg (tokV k l n :: accV d out :: env0) BODY (accV d (tokV k l n :: out)) 39 := by
  have eB : Evals instProg (.i k :: tokV k l n :: accV d out :: env0) otherB (accV d (tokV k l n :: out)) 13 :=
    (ev_rec2 (ev_field (ev_var (nth_2 _ _ _ _)) (by simp [nth?, accV]))
      (ev_cons (ev_var (nth_1 _ _ _)) (ev_field (ev_var (nth_2 _ _ _ _)) (by simp [nth?, accV])))).cast rfl rfl
  have hc3 : Evals instProg (.i k :: tokV k l n :: accV d out :: env0)
      (.prim "eq" [.var 0, li 0]) (.b 0) 5 := (ev_eqk _ k 0 hk (by decide)).cast (by simp [h0]) rfl
  have eI3 := ev_if_false hc3 (by decide) eB (th := bvarB)
  have hc2 : Evals instProg (.i k :: tokV k l n :: accV d out :: env0)
      (.prim "eq" [.var 0, li 9]) (.b 0) 5 := (ev_eqk _ k 9 hk (by decide)).cast (by simp [h9]) rfl
  have eI2 := ev_if_false hc2 (by decide) eI3 (th := exitB)
  have hc1 : Evals instProg (.i k :: tokV k l n :: accV d out :: env0)
      (.prim "eq" [.var 0, li 8]) (.b 0) 5 := (ev_eqk _ k 8 hk (by decide)).cast (by simp [h8]) rfl
  have eI1 := ev_if_false hc1 (by decide) eI2 (th := enterB)
  exact (ev_let (ev_kind env0 k l n (accV d out)) eI1).cast rfl rfl

/-- The token a `bvar` becomes at depth `d`. -/
def bvarOut (l : String) (n d : Int) : Val :=
  if n = d then subT d else if d < n then tokV 0 "" (n - 1) else tokV 0 l n

/-- The cost of `bvarTok`'s branch. -/
def bvarCost (n d : Int) : Nat := if n = d then 18 else if d < n then 31 else 19

theorem ev_bvarTok (E : List Val) (l : String) (n d : Int) (out : List Val)
    (hd : 0 ≤ d) (hdm : d ≤ i64Max) (hn : 0 ≤ n) (hnm : n ≤ i64Max) :
    Evals instProg (.i n :: .i 0 :: tokV 0 l n :: accV d out :: E) bvarTok (bvarOut l n d) (bvarCost n d) := by
  have hdi : inI64 d := inI64_of hd hdm
  have hni : inI64 n := inI64_of hn hnm
  have eD : Evals instProg (.i n :: .i 0 :: tokV 0 l n :: accV d out :: E) (fld (.var 3) 0) (.i d) 3 :=
    ev_field (ev_var (nth_3 _ _ _ _ _)) (by simp [nth?, accV])
  have eC : Evals instProg (.i n :: .i 0 :: tokV 0 l n :: accV d out :: E)
      (.prim "eq" [.var 0, fld (.var 3) 0]) (.b (if n = d then 1 else 0)) 7 :=
    (ev_prim2 (ev_var (nth_0 _ _)) eD (prim_eq hni hdi)).cast rfl rfl
  have eEQ : Evals instProg (.i n :: .i 0 :: tokV 0 l n :: accV d out :: E)
      (.prim "eq" [.var 0, fld (.var 3) 0]) (.b (if n = d then 1 else 0)) 7 := eC.cast rfl rfl
  by_cases hnd : n = d
  · have eT : Evals instProg (.i n :: .i 0 :: tokV 0 l n :: accV d out :: E) (tokE (li 10) (lstr "") (fld (.var 3) 0))
        (subT d) 9 := (ev_rec3 (ev_lit _ _ (.i 10) .i64) (ev_lit _ _ (.s "") .str) eD).cast rfl rfl
    have eC1 : Evals instProg (.i n :: .i 0 :: tokV 0 l n :: accV d out :: E)
        (.prim "eq" [.var 0, fld (.var 3) 0]) (.b 1) 7 := eEQ.cast (by simp [hnd]) rfl
    exact (ev_if_true eC1 eT).cast (by simp [bvarOut, hnd]) (by simp [bvarCost, hnd])
  · have eL : Evals instProg (.i n :: .i 0 :: tokV 0 l n :: accV d out :: E)
        (.prim "lt" [fld (.var 3) 0, .var 0]) (.b (if d < n then 1 else 0)) 7 :=
      (ev_prim2 eD (ev_var (nth_0 _ _)) (prim_lt hdi hni)).cast rfl rfl
    have eC0 : Evals instProg (.i n :: .i 0 :: tokV 0 l n :: accV d out :: E)
        (.prim "eq" [.var 0, fld (.var 3) 0]) (.b 0) 7 := eEQ.cast (by simp [hnd]) rfl
    by_cases hlt : d < n
    · have hn1 : inI64 (n - 1) := inI64_of (by omega) (by omega)
      have eS : Evals instProg (.i n :: .i 0 :: tokV 0 l n :: accV d out :: E)
          (.handle OV (.prim "sub" [.var 0, li 1]) (.var 1)) (.i (n - 1)) 7 :=
        ev_handle ((ev_prim2 (ev_var (nth_0 _ _)) (ev_lit _ _ (.i 1) .i64) (prim_sub hni (by decide) hn1)).cast rfl rfl)
      have eT : Evals instProg (.i n :: .i 0 :: tokV 0 l n :: accV d out :: E)
          (tokE (li 0) (lstr "") (.handle OV (.prim "sub" [.var 0, li 1]) (.var 1))) (tokV 0 "" (n - 1)) 13 :=
        (ev_rec3 (ev_lit _ _ (.i 0) .i64) (ev_lit _ _ (.s "") .str) eS).cast rfl rfl
      have eL1 : Evals instProg (.i n :: .i 0 :: tokV 0 l n :: accV d out :: E)
          (.prim "lt" [fld (.var 3) 0, .var 0]) (.b 1) 7 := eL.cast (by simp [hlt]) rfl
      have eI := ev_if_true eL1 eT (el := .var 2)
      exact (ev_if_false eC0 (by decide) eI).cast (by simp [bvarOut, hnd, hlt])
        (by simp [bvarCost, hnd, hlt])
    · have eL0 : Evals instProg (.i n :: .i 0 :: tokV 0 l n :: accV d out :: E)
          (.prim "lt" [fld (.var 3) 0, .var 0]) (.b 0) 7 := eL.cast (by simp [hlt]) rfl
      have eI := ev_if_false eL0 (by decide) (ev_var (nth_2 _ _ _ _))
        (th := tokE (li 0) (lstr "") (.handle OV (.prim "sub" [.var 0, li 1]) (.var 1)))
      exact (ev_if_false eC0 (by decide) eI).cast (by simp [bvarOut, hnd, hlt])
        (by simp [bvarCost, hnd, hlt])

theorem body_bvar (env0 : List Val) (l : String) (n d : Int) (out : List Val)
    (hd : 0 ≤ d) (hdm : d ≤ i64Max) (hn : 0 ≤ n) (hnm : n ≤ i64Max) :
    Evals instProg (tokV 0 l n :: accV d out :: env0) BODY (accV d (bvarOut l n d :: out)) (bvarCost n d + 43) := by
  have hdi : inI64 d := inI64_of hd hdm
  have eT := ev_bvarTok env0 l n d out hd hdm hn hnm
  have eD : Evals instProg (.i n :: .i 0 :: tokV 0 l n :: accV d out :: env0) (fld (.var 3) 0) (.i d) 3 :=
    ev_field (ev_var (nth_3 _ _ _ _ _)) (by simp [nth?, accV])
  have eO : Evals instProg (.i n :: .i 0 :: tokV 0 l n :: accV d out :: env0) (fld (.var 3) 1) (.l out) 3 :=
    ev_field (ev_var (nth_3 _ _ _ _ _)) (by simp [nth?, accV])
  have eC2 : Evals instProg (.i n :: .i 0 :: tokV 0 l n :: accV d out :: env0)
      (.cons bvarTok (fld (.var 3) 1)) (.l (bvarOut l n d :: out)) (bvarCost n d + 6) :=
    (ev_cons eT eO).cast rfl (by omega)
  have eR : Evals instProg (.i n :: .i 0 :: tokV 0 l n :: accV d out :: env0)
      (accE (fld (.var 3) 0) (.cons bvarTok (fld (.var 3) 1)))
      (accV d (bvarOut l n d :: out)) (bvarCost n d + 12) := (ev_rec2 eD eC2).cast rfl (by omega)
  have eH : Evals instProg (.i 0 :: tokV 0 l n :: accV d out :: env0) (fld (.var 1) 2) (.i n) 3 :=
    ev_field (ev_var (nth_1 _ _ _)) (by simp [nth?, tokV])
  have eW : Evals instProg (.i 0 :: tokV 0 l n :: accV d out :: env0) bvarB
      (accV d (bvarOut l n d :: out)) (bvarCost n d + 17) := (ev_let eH eR).cast rfl (by omega)
  have hc3 : Evals instProg (.i 0 :: tokV 0 l n :: accV d out :: env0)
      (.prim "eq" [.var 0, li 0]) (.b 1) 5 := (ev_eqk _ 0 0 (by decide) (by decide)).cast (by simp) rfl
  have eI3 := ev_if_true hc3 eW (el := otherB)
  have hc2 : Evals instProg (.i 0 :: tokV 0 l n :: accV d out :: env0)
      (.prim "eq" [.var 0, li 9]) (.b 0) 5 := (ev_eqk _ 0 9 (by decide) (by decide)).cast (by simp) rfl
  have eI2 := ev_if_false hc2 (by decide) eI3 (th := exitB)
  have hc1 : Evals instProg (.i 0 :: tokV 0 l n :: accV d out :: env0)
      (.prim "eq" [.var 0, li 8]) (.b 0) 5 := (ev_eqk _ 0 8 (by decide) (by decide)).cast (by simp) rfl
  have eI1 := ev_if_false hc1 (by decide) eI2 (th := enterB)
  exact (ev_let (ev_kind env0 0 l n (accV d out)) eI1).cast rfl (by omega)

/-! ## Folding over an encoding -/

theorem toNat_add_one {d : Int} (h : 0 ≤ d) : (d + 1).toNat = d.toNat + 1 := by
  have := Int.toNat_add (a := d) (b := 1) h (by decide)
  simpa using this

theorem int_eq_toNat {i : Nat} {d : Int} (hd : 0 ≤ d) : ((i : Int) = d ↔ i = d.toNat) := by
  constructor
  · intro h; have h2 := congrArg Int.toNat h; simpa using h2
  · intro h; rw [h, Int.toNat_of_nonneg hd]

theorem int_lt_toNat {i : Nat} {d : Int} (hd : 0 ≤ d) : (d < (i : Int) ↔ d.toNat < i) := by
  have hd' : (d.toNat : Int) = d := Int.toNat_of_nonneg hd
  constructor
  · intro h; rw [← hd'] at h; exact Int.ofNat_lt.mp h
  · intro h; rw [← hd']; exact Int.ofNat_lt.mpr h

theorem bvarCost_le (n d : Int) : bvarCost n d ≤ 31 := by
  unfold bvarCost
  split
  · decide
  · split <;> decide

/-- The accumulator after a `bvar` token is exactly `skelOf`'s singleton. -/
theorem bvarOut_eq (i : Nat) (d : Int) (out : List Val) (hd : 0 ≤ d) :
    bvarOut "" (i : Int) d :: out = List.reverse (skelOf d.toNat (.bvar i)) ++ out := by
  unfold bvarOut skelOf
  by_cases h1 : i = d.toNat
  · subst h1
    rw [if_pos rfl]
    rw [if_pos (Int.toNat_of_nonneg hd), Int.toNat_of_nonneg hd]
    simp
  · rw [if_neg h1]
    have hn1 : ¬ (i : Int) = d := fun hc => h1 ((int_eq_toNat hd).mp hc)
    rw [if_neg hn1]
    by_cases h2 : d.toNat < i
    · rw [if_pos h2, if_pos ((int_lt_toNat hd).mpr h2)]
      simp
    · rw [if_neg h2, if_neg (fun h => h2 ((int_lt_toNat hd).mp h))]
      simp

theorem repN_of {n : Nat} (h : repN n) : (n : Int) ≤ i64Max := by simpa [repN] using h

theorem d_bound {d0 : Int} {a b : Nat} (h : d0 + ((a + b : Nat) : Int) ≤ i64Max) :
    d0 ≤ i64Max := by omega

theorem skelOf_length (e : Expr Nat) : ∀ (d : Nat) (ts : List Val),
    encToks e = some ts → (skelOf d e).length = ts.length := by
  induction e with
  | bvar i =>
    intro d ts he; unfold encToks at he
    by_cases h : repN i
    · simp [h] at he; subst he
      simp only [skelOf]
      split
      · rfl
      · split <;> rfl
    · simp [h] at he
  | sort l => intro d ts he; simp [encToks] at he; subst he; rfl
  | const r ls =>
    intro d ts he; unfold encToks at he
    by_cases h : repN r
    · simp [h] at he; subst he; rfl
    · simp [h] at he
  | lit t =>
    intro d ts he; unfold encToks at he
    by_cases h : repN t
    · simp [h] at he; subst he; rfl
    · simp [h] at he
  | app f x ihf ihx =>
    intro d ts he; unfold encToks at he
    cases haf : encToks f <;> cases hax : encToks x <;> simp [haf, hax] at he
    subst he; simp [skelOf, List.length_append, ihf _ _ haf, ihx _ _ hax]
  | lam a b iha ihb =>
    intro d ts he; unfold encToks at he
    cases haa : encToks a <;> cases hab : encToks b <;> simp [haa, hab] at he
    subst he; simp [skelOf, List.length_append, iha _ _ haa, ihb _ _ hab]
  | pi a b iha ihb =>
    intro d ts he; unfold encToks at he
    cases haa : encToks a <;> cases hab : encToks b <;> simp [haa, hab] at he
    subst he; simp [skelOf, List.length_append, iha _ _ haa, ihb _ _ hab]
  | letE a v b iha ihv ihb =>
    intro d ts he; unfold encToks at he
    cases haa : encToks a <;> cases hav : encToks v <;> cases hab : encToks b <;> simp [haa, hav, hab] at he
    subst he; simp [skelOf, List.length_append, iha _ _ haa, ihv _ _ hav, ihb _ _ hab]

theorem fold_encToks (e : Expr Nat) :
    ∀ (ts rest : List Val) (d0 : Int) (out : List Val) (r' : Val) (m' : Nat) (env0 : List Val),
    encToks e = some ts →
    0 ≤ d0 → d0 + ((ts.length + rest.length : Nat) : Int) ≤ i64Max →
    FoldRuns instProg env0 rest BODY (accV d0 (List.reverse (skelOf d0.toNat e) ++ out)) r' m' →
    ∃ m, m ≤ 75 * ts.length + m' ∧
      FoldRuns instProg env0 (ts ++ rest) BODY (accV d0 out) r' m := by
  induction e with
  | bvar i =>
    intro ts rest d0 out r' m' env0 he hd hdm hrest
    unfold encToks at he
    by_cases hi : repN i
    · simp [hi] at he; subst he
      have hni : (i : Int) ≤ i64Max := repN_of hi
      rw [← bvarOut_eq i d0 out hd] at hrest
      have hbc := bvarCost_le (i : Int) d0
      refine ⟨_, ?_, foldRuns_cons
        (body_bvar env0 "" (i : Int) d0 out hd (d_bound hdm) (by omega) hni) hrest⟩
      simp only [List.length_cons, List.length_nil]; omega
    · simp [hi] at he
  | sort l =>
    intro ts rest d0 out r' m' env0 he hd hdm hrest
    unfold encToks at he
    simp at he; subst he
    have hb := body_other env0 1 (encLevel l) 0 d0 out (by decide) (by decide) (by decide) (by decide)
    refine ⟨_, ?_, foldRuns_cons hb (by simpa [skelOf] using hrest)⟩
    simp only [List.length_append, List.length_cons, List.length_nil, List.cons_append, List.nil_append]; omega
  | const r ls =>
    intro ts rest d0 out r' m' env0 he hd hdm hrest
    unfold encToks at he
    by_cases hi : repN r
    · simp [hi] at he; subst he
      have hb := body_other env0 2 (encLevels ls) (r : Int) d0 out
        (by decide) (by decide) (by decide) (by decide)
      refine ⟨_, ?_, foldRuns_cons hb (by simpa [skelOf] using hrest)⟩
      simp only [List.length_append, List.length_cons, List.length_nil, List.cons_append, List.nil_append]; omega
    · simp [hi] at he
  | lit t =>
    intro ts rest d0 out r' m' env0 he hd hdm hrest
    unfold encToks at he
    by_cases hi : repN t
    · simp [hi] at he; subst he
      have hb := body_other env0 7 "" (t : Int) d0 out (by decide) (by decide) (by decide) (by decide)
      refine ⟨_, ?_, foldRuns_cons hb (by simpa [skelOf] using hrest)⟩
      simp only [List.length_append, List.length_cons, List.length_nil, List.cons_append, List.nil_append]; omega
    · simp [hi] at he
  | app f x ihf ihx =>
    intro ts rest d0 out r' m' env0 he hd hdm hrest
    unfold encToks at he
    cases haf : encToks f with
    | none => simp [haf] at he
    | some ta =>
      cases hax : encToks x with
      | none => simp [haf, hax] at he
      | some tb =>
        simp [haf, hax] at he; subst he
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        simp only [List.length_append, List.length_cons, List.length_nil, List.cons_append,
          List.nil_append] at hdm
        have hA : skelOf d0.toNat (.app f x) =
            [tokV 3 "" 0] ++ skelOf d0.toNat f ++ skelOf d0.toNat x := rfl
        have hacc : accV d0 (List.reverse (skelOf d0.toNat (.app f x)) ++ out) =
            accV d0 (List.reverse (skelOf d0.toNat x) ++
              (List.reverse (skelOf d0.toNat f) ++ (tokV 3 "" 0 :: out))) := by
          rw [hA]; simp [List.reverse_append, List.append_assoc]
        rw [hacc] at hrest
        obtain ⟨mx, hmx, hx⟩ := ihx tb rest d0
          (List.reverse (skelOf d0.toNat f) ++ (tokV 3 "" 0 :: out)) r' m' env0
          hax hd (by (try simp only [List.length_append, List.length_cons]); omega) hrest
        obtain ⟨mf, hmf, hf⟩ := ihf ta (tb ++ rest) d0 (tokV 3 "" 0 :: out) r' mx env0
          haf hd (by (try simp only [List.length_append, List.length_cons]); omega) hx
        have hb := body_other env0 3 "" 0 d0 out (by decide) (by decide) (by decide) (by decide)
        refine ⟨_, ?_, foldRuns_cons hb hf⟩
        simp only [List.length_append, List.length_cons, List.length_nil, List.cons_append, List.nil_append]; omega
  | lam a b iha ihb =>
    intro ts rest d0 out r' m' env0 he hd hdm hrest
    unfold encToks at he
    cases haa : encToks a with
    | none => simp [haa] at he
    | some ta =>
      cases hab : encToks b with
      | none => simp [haa, hab] at he
      | some tb =>
        simp [haa, hab] at he; subst he
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        simp only [List.length_append, List.length_cons, List.length_nil, List.cons_append,
          List.nil_append] at hdm
        have hdn : (d0 + 1).toNat = d0.toNat + 1 := toNat_add_one hd
        have hA : skelOf d0.toNat (.lam a b) =
            [tokV 4 "" 0] ++ skelOf d0.toNat a ++ [enterT] ++ skelOf (d0.toNat + 1) b ++ [exitT] := rfl
        have hacc : accV d0 (List.reverse (skelOf d0.toNat (.lam a b)) ++ out) =
            accV (d0 + 1 - 1) (exitT :: (List.reverse (skelOf (d0 + 1).toNat b) ++
              (enterT :: (List.reverse (skelOf d0.toNat a) ++ (tokV 4 "" 0 :: out))))) := by
          rw [hA]; simp [List.reverse_append, List.append_assoc, hdn,
            show d0 + 1 - 1 = d0 from by omega]
        rw [hacc] at hrest
        have hb5 := body_exit env0 "" 0 (d0 + 1)
          (List.reverse (skelOf (d0 + 1).toNat b) ++
            (enterT :: (List.reverse (skelOf d0.toNat a) ++ (tokV 4 "" 0 :: out))))
          (by omega) (by omega)
        have hRE : FoldRuns instProg env0 (exitT :: rest) BODY
            (accV (d0 + 1) (List.reverse (skelOf (d0 + 1).toNat b) ++
              (enterT :: (List.reverse (skelOf d0.toNat a) ++ (tokV 4 "" 0 :: out))))) r' (38 + m' + 1) :=
          foldRuns_cons hb5 hrest
        obtain ⟨mb, hmb, hbR⟩ := ihb tb (exitT :: rest) (d0 + 1)
          (enterT :: (List.reverse (skelOf d0.toNat a) ++ (tokV 4 "" 0 :: out))) r' (38 + m' + 1) env0
          hab (by omega) (by (try simp only [List.length_append, List.length_cons]); omega) hRE
        have hRA : FoldRuns instProg env0 (enterT :: (tb ++ (exitT :: rest))) BODY
            (accV d0 (List.reverse (skelOf d0.toNat a) ++ (tokV 4 "" 0 :: out))) r' (31 + mb + 1) :=
          foldRuns_cons (body_enter env0 "" 0 d0
            (List.reverse (skelOf d0.toNat a) ++ (tokV 4 "" 0 :: out)) hd (by omega)) hbR
        obtain ⟨ma, hma, haR⟩ := iha ta (enterT :: (tb ++ (exitT :: rest))) d0
          (tokV 4 "" 0 :: out) r' (31 + mb + 1) env0
          haa hd (by (try simp only [List.length_append, List.length_cons]); omega) hRA
        have hb0 := body_other env0 4 "" 0 d0 out (by decide) (by decide) (by decide) (by decide)
        refine ⟨_, ?_, foldRuns_cons hb0 haR⟩
        simp only [List.length_append, List.length_cons, List.length_nil, List.cons_append, List.nil_append]; omega
  | pi a b iha ihb =>
    intro ts rest d0 out r' m' env0 he hd hdm hrest
    unfold encToks at he
    cases haa : encToks a with
    | none => simp [haa] at he
    | some ta =>
      cases hab : encToks b with
      | none => simp [haa, hab] at he
      | some tb =>
        simp [haa, hab] at he; subst he
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        simp only [List.length_append, List.length_cons, List.length_nil, List.cons_append,
          List.nil_append] at hdm
        have hdn : (d0 + 1).toNat = d0.toNat + 1 := toNat_add_one hd
        have hA : skelOf d0.toNat (.pi a b) =
            [tokV 5 "" 0] ++ skelOf d0.toNat a ++ [enterT] ++ skelOf (d0.toNat + 1) b ++ [exitT] := rfl
        have hacc : accV d0 (List.reverse (skelOf d0.toNat (.pi a b)) ++ out) =
            accV (d0 + 1 - 1) (exitT :: (List.reverse (skelOf (d0 + 1).toNat b) ++
              (enterT :: (List.reverse (skelOf d0.toNat a) ++ (tokV 5 "" 0 :: out))))) := by
          rw [hA]; simp [List.reverse_append, List.append_assoc, hdn,
            show d0 + 1 - 1 = d0 from by omega]
        rw [hacc] at hrest
        have hb5 := body_exit env0 "" 0 (d0 + 1)
          (List.reverse (skelOf (d0 + 1).toNat b) ++
            (enterT :: (List.reverse (skelOf d0.toNat a) ++ (tokV 5 "" 0 :: out))))
          (by omega) (by omega)
        have hRE : FoldRuns instProg env0 (exitT :: rest) BODY
            (accV (d0 + 1) (List.reverse (skelOf (d0 + 1).toNat b) ++
              (enterT :: (List.reverse (skelOf d0.toNat a) ++ (tokV 5 "" 0 :: out))))) r' (38 + m' + 1) :=
          foldRuns_cons hb5 hrest
        obtain ⟨mb, hmb, hbR⟩ := ihb tb (exitT :: rest) (d0 + 1)
          (enterT :: (List.reverse (skelOf d0.toNat a) ++ (tokV 5 "" 0 :: out))) r' (38 + m' + 1) env0
          hab (by omega) (by (try simp only [List.length_append, List.length_cons]); omega) hRE
        have hRA : FoldRuns instProg env0 (enterT :: (tb ++ (exitT :: rest))) BODY
            (accV d0 (List.reverse (skelOf d0.toNat a) ++ (tokV 5 "" 0 :: out))) r' (31 + mb + 1) :=
          foldRuns_cons (body_enter env0 "" 0 d0
            (List.reverse (skelOf d0.toNat a) ++ (tokV 5 "" 0 :: out)) hd (by omega)) hbR
        obtain ⟨ma, hma, haR⟩ := iha ta (enterT :: (tb ++ (exitT :: rest))) d0
          (tokV 5 "" 0 :: out) r' (31 + mb + 1) env0
          haa hd (by (try simp only [List.length_append, List.length_cons]); omega) hRA
        have hb0 := body_other env0 5 "" 0 d0 out (by decide) (by decide) (by decide) (by decide)
        refine ⟨_, ?_, foldRuns_cons hb0 haR⟩
        simp only [List.length_append, List.length_cons, List.length_nil, List.cons_append, List.nil_append]; omega
  | letE a v b iha ihv ihb =>
    intro ts rest d0 out r' m' env0 he hd hdm hrest
    unfold encToks at he
    cases haa : encToks a with
    | none => simp [haa] at he
    | some ta =>
      cases hav : encToks v with
      | none => simp [haa, hav] at he
      | some tv =>
        cases hab : encToks b with
        | none => simp [haa, hav, hab] at he
        | some tb =>
          simp [haa, hav, hab] at he; subst he
          simp only [List.append_assoc, List.cons_append, List.nil_append]
          simp only [List.length_append, List.length_cons, List.length_nil, List.cons_append,
            List.nil_append] at hdm
          have hdn : (d0 + 1).toNat = d0.toNat + 1 := toNat_add_one hd
          have hA : skelOf d0.toNat (.letE a v b) =
              [tokV 6 "" 0] ++ skelOf d0.toNat a ++ skelOf d0.toNat v ++ [enterT] ++
                skelOf (d0.toNat + 1) b ++ [exitT] := rfl
          have hacc : accV d0 (List.reverse (skelOf d0.toNat (.letE a v b)) ++ out) =
              accV (d0 + 1 - 1) (exitT :: (List.reverse (skelOf (d0 + 1).toNat b) ++ (enterT ::
                (List.reverse (skelOf d0.toNat v) ++
                  (List.reverse (skelOf d0.toNat a) ++ (tokV 6 "" 0 :: out)))))) := by
            rw [hA]; simp [List.reverse_append, List.append_assoc, hdn,
              show d0 + 1 - 1 = d0 from by omega]
          rw [hacc] at hrest
          have hb5 := body_exit env0 "" 0 (d0 + 1)
            (List.reverse (skelOf (d0 + 1).toNat b) ++ (enterT ::
              (List.reverse (skelOf d0.toNat v) ++
                (List.reverse (skelOf d0.toNat a) ++ (tokV 6 "" 0 :: out)))))
            (by omega) (by omega)
          have hRE : FoldRuns instProg env0 (exitT :: rest) BODY
              (accV (d0 + 1) (List.reverse (skelOf (d0 + 1).toNat b) ++ (enterT ::
                (List.reverse (skelOf d0.toNat v) ++
                  (List.reverse (skelOf d0.toNat a) ++ (tokV 6 "" 0 :: out))))))
              r' (38 + m' + 1) :=
            foldRuns_cons hb5 hrest
          obtain ⟨mb, hmb, hbR⟩ := ihb tb (exitT :: rest) (d0 + 1)
            (enterT :: (List.reverse (skelOf d0.toNat v) ++
              (List.reverse (skelOf d0.toNat a) ++ (tokV 6 "" 0 :: out)))) r' (38 + m' + 1) env0
            hab (by omega) (by (try simp only [List.length_append, List.length_cons]); omega) hRE
          have hRA : FoldRuns instProg env0 (enterT :: (tb ++ (exitT :: rest))) BODY
              (accV d0 (List.reverse (skelOf d0.toNat v) ++
                (List.reverse (skelOf d0.toNat a) ++ (tokV 6 "" 0 :: out)))) r' (31 + mb + 1) :=
            foldRuns_cons (body_enter env0 "" 0 d0
              (List.reverse (skelOf d0.toNat v) ++
                (List.reverse (skelOf d0.toNat a) ++ (tokV 6 "" 0 :: out))) hd (by omega)) hbR
          obtain ⟨mv, hmv, hvR⟩ := ihv tv (enterT :: (tb ++ (exitT :: rest))) d0
            (List.reverse (skelOf d0.toNat a) ++ (tokV 6 "" 0 :: out)) r' (31 + mb + 1) env0
            hav hd (by (try simp only [List.length_append, List.length_cons]); omega) hRA
          obtain ⟨ma, hma, haR⟩ := iha ta (tv ++ (enterT :: (tb ++ (exitT :: rest)))) d0
            (tokV 6 "" 0 :: out) r' mv env0
            haa hd (by (try simp only [List.length_append, List.length_cons]); omega) hvR
          have hb0 := body_other env0 6 "" 0 d0 out (by decide) (by decide) (by decide) (by decide)
          refine ⟨_, ?_, foldRuns_cons hb0 haR⟩
          simp only [List.length_append, List.length_cons, List.length_nil, List.cons_append, List.nil_append]; omega

/-- The reversal fold conses each element onto the accumulator. -/
theorem fold_rev (env0 : List Val) (xs : List Val) :
    ∀ (acc : List Val) (r' : Val) (m' : Nat),
    FoldRuns instProg env0 [] REV (.l (xs.reverse ++ acc)) r' m' →
    ∃ m, m ≤ 6 * xs.length + m' ∧ FoldRuns instProg env0 xs REV (.l acc) r' m := by
  induction xs with
  | nil => intro acc r' m' hrest; exact ⟨m', by omega, hrest⟩
  | cons x xs ih =>
    intro acc r' m' hrest
    have hb : Evals instProg (x :: .l acc :: env0) REV (.l (x :: acc)) 5 :=
      ev_cons (ev_var (nth_0 _ _)) (ev_var (nth_1 _ _ _))
    obtain ⟨m, hm, hf⟩ := ih (x :: acc) r' m' (by
      have hrl : (x :: xs).reverse ++ acc = xs.reverse ++ (x :: acc) := by simp
      rwa [hrl] at hrest)
    exact ⟨5 + m + 1, by simp only [List.length_cons]; omega, foldRuns_cons hb hf⟩

/-- The entry body: folds `e` into a reversed skeleton, reverses it, and
    pairs `{repl, skel}` with the unit state. -/
theorem evals_main (D : Int) (e : Expr Nat) (te tr : List Val)
    (he : encToks e = some te) (hcap : (te.length : Int) < i64Max) :
    ∃ n ≤ 81 * te.length + 30,
      Evals instProg [inputV D te tr, unitRaw] MAIN (.p (outV tr (skelOf 0 e)) unitRaw) n := by
  have hnil1 : FoldRuns instProg [inputV D te tr, unitRaw] [] BODY
      (accV 0 (List.reverse (skelOf 0 e) ++ [])) (accV 0 (List.reverse (skelOf 0 e) ++ [])) 1 :=
    foldRuns_nil _ _ _ _
  obtain ⟨m1, hm1, h1⟩ := fold_encToks e te [] 0 []
    (accV 0 (List.reverse (skelOf 0 e) ++ [])) 1
    [inputV D te tr, unitRaw] he (by decide) (by simp; omega) hnil1
  simp only [List.append_nil] at h1
  have eL : Evals instProg [inputV D te tr, unitRaw] (fld (.var 0) 1) (.l te) 3 :=
    ev_field (ev_var (nth_0 _ _)) (by simp [nth?, inputV])
  have eI : Evals instProg [inputV D te tr, unitRaw] INIT (accV 0 []) 5 :=
    (ev_rec2 (ev_lit _ _ (.i 0) .i64) (ev_nil _ _ TOK)).cast rfl rfl
  have eF1 : Evals instProg [inputV D te tr, unitRaw] (.fold (fld (.var 0) 1) INIT BODY)
      (accV 0 (List.reverse (skelOf 0 e))) (m1 + 10) := (ev_fold eL eI h1).cast rfl (by omega)
  have hrlen : (skelOf 0 e).length = te.length := skelOf_length e 0 te he
  have hnil2 : FoldRuns instProg
      [accV 0 (List.reverse (skelOf 0 e)), inputV D te tr, unitRaw] [] REV
      (.l (skelOf 0 e)) (.l (skelOf 0 e)) 1 := foldRuns_nil _ _ _ _
  obtain ⟨m2, hm2, h2⟩ := fold_rev
    [accV 0 (List.reverse (skelOf 0 e)), inputV D te tr, unitRaw] (List.reverse (skelOf 0 e)) []
    (.l (skelOf 0 e)) 1 (by simpa using hnil2)
  rw [List.length_reverse, hrlen] at hm2
  have eR : Evals instProg [accV 0 (List.reverse (skelOf 0 e)), inputV D te tr, unitRaw]
      (fld (.var 1) 2) (.l tr) 3 :=
    ev_field (ev_var (nth_1 _ _ _)) (by simp [nth?, inputV])
  have eS : Evals instProg [accV 0 (List.reverse (skelOf 0 e)), inputV D te tr, unitRaw]
      (fld (.var 0) 1) (.l (List.reverse (skelOf 0 e))) 3 :=
    ev_field (ev_var (nth_0 _ _)) (by simp [nth?, accV])
  have eF2 : Evals instProg [accV 0 (List.reverse (skelOf 0 e)), inputV D te tr, unitRaw]
      (.fold (fld (.var 0) 1) (.nil TOK) REV) (.l (skelOf 0 e)) (m2 + 6) :=
    (ev_fold eS (ev_nil _ _ TOK) h2).cast rfl (by omega)
  have eRc : Evals instProg [accV 0 (List.reverse (skelOf 0 e)), inputV D te tr, unitRaw]
      (.recordE ["repl", "skel"] [fld (.var 1) 2, .fold (fld (.var 0) 1) (.nil TOK) REV])
      (outV tr (skelOf 0 e)) (m2 + 12) := (ev_rec2 eR eF2).cast rfl (by omega)
  have eU : Evals instProg [accV 0 (List.reverse (skelOf 0 e)), inputV D te tr, unitRaw]
      (.var 2) unitRaw 1 := ev_var (nth_2 _ _ _ _)
  have eP : Evals instProg [accV 0 (List.reverse (skelOf 0 e)), inputV D te tr, unitRaw]
      (.pair (.recordE ["repl", "skel"] [fld (.var 1) 2, .fold (fld (.var 0) 1) (.nil TOK) REV]) (.var 2))
      (.p (outV tr (skelOf 0 e)) unitRaw) (m2 + 16) := (ev_pair eRc eU).cast rfl (by omega)
  refine ⟨m1 + m2 + 28, ?_, ?_⟩
  · omega
  · exact (ev_let eF1 eP).cast rfl (by omega)

/-! ## The unconditional encoding and the compact expander -/

/-- `encToks` without the i64 check — every `Expr Nat` encodes, since the
    token payload is `Int`, which is unbounded. The i64 restriction is a
    property of the wire contract, not of `Expr Nat`. -/
def encToksU : Expr Nat → List Val
  | .bvar i => [tokV 0 "" i]
  | .sort l => [tokV 1 (encLevel l) 0]
  | .const r ls => [tokV 2 (encLevels ls) r]
  | .app f x => [tokV 3 "" 0] ++ encToksU f ++ encToksU x
  | .lam a b => [tokV 4 "" 0] ++ encToksU a ++ [enterT] ++ encToksU b ++ [exitT]
  | .pi a b => [tokV 5 "" 0] ++ encToksU a ++ [enterT] ++ encToksU b ++ [exitT]
  | .letE a v b =>
    [tokV 6 "" 0] ++ encToksU a ++ encToksU v ++ [enterT] ++ encToksU b ++ [exitT]
  | .lit t => [tokV 7 "" t]

/-- The i64 contract accepts exactly the canonical encodings: whenever
    `encToks` succeeds it produces `encToksU`'s output. -/
theorem encToks_eq_encToksU {e : Expr Nat} {ts : List Val} :
    encToks e = some ts → encToksU e = ts := by
  induction e generalizing ts with
  | bvar i =>
    intro h; unfold encToks at h; split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · simp at h
  | sort l => intro h; simp [encToks] at h; subst h; rfl
  | const r ls =>
    intro h; unfold encToks at h; split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · simp at h
  | lit t =>
    intro h; unfold encToks at h; split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · simp at h
  | app f x ihf ihx =>
    intro h; unfold encToks at h
    cases haf : encToks f with
    | none => simp [haf] at h
    | some ta =>
      cases hax : encToks x with
      | none => simp [haf, hax] at h
      | some tb =>
        simp [haf, hax] at h; subst h
        simp [encToksU, ihf haf, ihx hax]
  | lam a b iha ihb =>
    intro h; unfold encToks at h
    cases haa : encToks a with
    | none => simp [haa] at h
    | some ta =>
      cases hab : encToks b with
      | none => simp [haa, hab] at h
      | some tb =>
        simp [haa, hab] at h; subst h
        simp [encToksU, iha haa, ihb hab]
  | pi a b iha ihb =>
    intro h; unfold encToks at h
    cases haa : encToks a with
    | none => simp [haa] at h
    | some ta =>
      cases hab : encToks b with
      | none => simp [haa, hab] at h
      | some tb =>
        simp [haa, hab] at h; subst h
        simp [encToksU, iha haa, ihb hab]
  | letE a v b iha ihv ihb =>
    intro h; unfold encToks at h
    cases haa : encToks a with
    | none => simp [haa] at h
    | some ta =>
      cases hav : encToks v with
      | none => simp [haa, hav] at h
      | some tv =>
        cases hab : encToks b with
        | none => simp [haa, hav, hab] at h
        | some tb =>
          simp [haa, hav, hab] at h; subst h
          simp [encToksU, iha haa, ihv hav, ihb hab]

/-! ## The V1 input decode — `decodeInputV1` (E-07CompactInstantiate)

`decodeInputV1` is the contract's syntactic front door: an input value
either decodes to `(D, e, r)` or it does not. It is a pure syntactic
decode — it carries no target-correctness field and no execution-success
field. Every representation condition is a CHECK, never a repair:
a negative or out-of-i64-range payload, a non-canonical level or level
count, a stray or unbalanced ENTER/EXIT, an output-only `SUB` token, an
unknown tag, or a negative depth makes the decode `none`. `Int.toNat`
appears only on a checked `0 ≤ n ≤ i64Max` branch — a conversion, not a
truncation (`toNat` repair of out-of-range values is forbidden). -/

/-- Decimal digit value: `'0' ↦ 0`, …, `'9' ↦ 9`. -/
def digitVal (c : Char) : Nat := c.toNat - 48

theorem digitVal_digitChar : ∀ m : Nat, m < 10 → digitVal (Nat.digitChar m) = m
  | 0, _ => by decide | 1, _ => by decide | 2, _ => by decide | 3, _ => by decide
  | 4, _ => by decide | 5, _ => by decide | 6, _ => by decide | 7, _ => by decide
  | 8, _ => by decide | 9, _ => by decide
  | m + 10, h => by omega

theorem digitChar_isDigit : ∀ m : Nat, m < 10 → Char.isDigit (Nat.digitChar m) = true
  | 0, _ => by decide | 1, _ => by decide | 2, _ => by decide | 3, _ => by decide
  | 4, _ => by decide | 5, _ => by decide | 6, _ => by decide | 7, _ => by decide
  | 8, _ => by decide | 9, _ => by decide
  | m + 10, h => by omega

/-- The numeral a digit list denotes (most significant first). -/
def numOf (ds : List Char) : Nat := ds.foldl (fun a c => a * 10 + digitVal c) 0

/-- The fold's accumulator is shifted by the list length. -/
theorem numFold : ∀ (ds : List Char) (a : Nat),
    ds.foldl (fun a c => a * 10 + digitVal c) a =
      a * 10 ^ ds.length + ds.foldl (fun a c => a * 10 + digitVal c) 0 := by
  intro ds; induction ds with
  | nil => intro a; simp
  | cons c cs ih =>
    intro a
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (a * 10 + digitVal c), ih (0 * 10 + digitVal c)]
    simp only [Nat.zero_mul, Nat.zero_add]
    have hpow : a * 10 ^ (cs.length + 1) = a * 10 * 10 ^ cs.length := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_right_comm]
    rw [Nat.add_mul, hpow, ← Nat.add_assoc]

/-- `toDigitsCore`'s tail argument is a literal suffix of the output. -/
theorem toDigitsCore_eq : ∀ (fuel n : Nat) (ds : List Char),
    Nat.toDigitsCore 10 fuel n ds = Nat.toDigitsCore 10 fuel n [] ++ ds := by
  intro fuel; induction fuel with
  | zero => intro n ds; rfl
  | succ fuel ih =>
    intro n ds
    have step : ∀ ds : List Char, Nat.toDigitsCore 10 (fuel + 1) n ds =
        if n / 10 = 0 then Nat.digitChar (n % 10) :: ds
        else Nat.toDigitsCore 10 fuel (n / 10) (Nat.digitChar (n % 10) :: ds) := fun _ => rfl
    rw [step]
    by_cases h : n / 10 = 0
    · rw [if_pos h, step [], if_pos h]
      simp
    · rw [if_neg h, ih (n / 10) (Nat.digitChar (n % 10) :: ds), step [], if_neg h,
        ih (n / 10) [Nat.digitChar (n % 10)]]
      simp

/-- The decimal parse of `n`'s own digits is `n`, extended by a suffix. -/
theorem numOf_toDigitsCore : ∀ (fuel n : Nat) (ds : List Char), n < fuel →
    numOf (Nat.toDigitsCore 10 fuel n ds) = n * 10 ^ ds.length + numOf ds := by
  intro fuel; induction fuel with
  | zero => intro n ds h; omega
  | succ fuel ih =>
    intro n ds h
    have step : ∀ ds : List Char, Nat.toDigitsCore 10 (fuel + 1) n ds =
        if n / 10 = 0 then Nat.digitChar (n % 10) :: ds
        else Nat.toDigitsCore 10 fuel (n / 10) (Nat.digitChar (n % 10) :: ds) := fun _ => rfl
    rw [step]
    have h1 : numOf (Nat.digitChar (n % 10) :: ds) =
        digitVal (Nat.digitChar (n % 10)) * 10 ^ ds.length + numOf ds := by
      show List.foldl (fun a c => a * 10 + digitVal c) 0 (Nat.digitChar (n % 10) :: ds) = _
      rw [List.foldl_cons]
      simp only [Nat.zero_mul, Nat.zero_add]
      exact numFold ds _
    have hmod : digitVal (Nat.digitChar (n % 10)) = n % 10 :=
      digitVal_digitChar _ (Nat.mod_lt _ (by decide))
    by_cases hn : n / 10 = 0
    · rw [if_pos hn, h1, hmod]
      have : n % 10 = n := Nat.mod_eq_of_lt (by omega)
      rw [this]
    · rw [if_neg hn]
      have hn' : n / 10 < fuel := by omega
      rw [ih (n / 10) _ hn', h1, hmod, List.length_cons, Nat.pow_succ,
        ← Nat.mul_assoc, Nat.mul_right_comm (n / 10) _ 10,
        ← Nat.add_assoc, ← Nat.add_mul]
      have hdm : n / 10 * 10 + n % 10 = n := by omega
      rw [hdm]

/-- The parse of `toString n`'s digits is `n`. -/
theorem numOf_toString (n : Nat) : numOf (toString n).data = n := by
  have h : numOf (Nat.toDigitsCore 10 (n + 1) n []) =
      n * 10 ^ [].length + numOf [] :=
    numOf_toDigitsCore (n + 1) n [] (by omega)
  simpa [numOf] using h

/-- Every character of `toDigitsCore`'s output is an emitted digit or a tail
    element. -/
theorem toDigitsCore_digits : ∀ (fuel n : Nat) (ds : List Char) (c : Char),
    c ∈ Nat.toDigitsCore 10 fuel n ds → c ∈ ds ∨ c.isDigit = true := by
  intro fuel; induction fuel with
  | zero => intro n ds c h; exact Or.inl h
  | succ fuel ih =>
    intro n ds c h
    have step : ∀ ds : List Char, Nat.toDigitsCore 10 (fuel + 1) n ds =
        if n / 10 = 0 then Nat.digitChar (n % 10) :: ds
        else Nat.toDigitsCore 10 fuel (n / 10) (Nat.digitChar (n % 10) :: ds) := fun _ => rfl
    rw [step] at h
    by_cases hn : n / 10 = 0
    · rw [if_pos hn] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact Or.inr (digitChar_isDigit _ (Nat.mod_lt _ (by decide)))
      · exact Or.inl h'
    · rw [if_neg hn] at h
      rcases ih (n / 10) (Nat.digitChar (n % 10) :: ds) c h with h' | h'
      · rcases List.mem_cons.mp h' with rfl | h''
        · exact Or.inr (digitChar_isDigit _ (Nat.mod_lt _ (by decide)))
        · exact Or.inl h''
      · exact Or.inr h'

/-- Every character of `toString n` is a digit. -/
theorem toString_digits (n : Nat) (c : Char) (h : c ∈ (toString n).data) :
    c.isDigit = true := by
  have h' : c ∈ Nat.toDigits 10 n := h
  rcases toDigitsCore_digits (n + 1) n [] c h' with h'' | h''
  · exact absurd h'' (by simp)
  · exact h''

/-- A canonical `n;` numeral: at least one digit, a `;` terminator, the
    digits parsed by the decimal fold, and they must be `n`'s own
    rendering — no leading zeros accepted, nothing repaired. -/
def decNatStr (cs : List Char) : Option (Nat × List Char) :=
  match cs.dropWhile Char.isDigit with
  | ';' :: rest =>
    if cs.takeWhile Char.isDigit = [] then none
    else if toString (numOf (cs.takeWhile Char.isDigit)) =
        String.mk (cs.takeWhile Char.isDigit) then
      some (numOf (cs.takeWhile Char.isDigit), rest)
    else none
  | _ => none

/-- `toDigitsCore` keeps a nonempty tail nonempty. -/
theorem toDigitsCore_ne_nil : ∀ (fuel n : Nat) (ds : List Char),
    ds ≠ [] → Nat.toDigitsCore 10 fuel n ds ≠ [] := by
  intro fuel; induction fuel with
  | zero => intro n ds h; exact h
  | succ fuel ih =>
    intro n ds h
    have step : ∀ ds : List Char, Nat.toDigitsCore 10 (fuel + 1) n ds =
        if n / 10 = 0 then Nat.digitChar (n % 10) :: ds
        else Nat.toDigitsCore 10 fuel (n / 10) (Nat.digitChar (n % 10) :: ds) := fun _ => rfl
    rw [step]
    by_cases hn : n / 10 = 0
    · rw [if_pos hn]; simp
    · rw [if_neg hn]; exact ih (n / 10) _ (by simp)

/-- `toString n` is never empty. -/
theorem toString_ne_nil (n : Nat) : (toString n).data ≠ [] := by
  show Nat.toDigits 10 n ≠ []
  show Nat.toDigitsCore 10 (n + 1) n [] ≠ []
  have step : Nat.toDigitsCore 10 (n + 1) n [] =
      if n / 10 = 0 then Nat.digitChar (n % 10) :: []
      else Nat.toDigitsCore 10 n (n / 10) (Nat.digitChar (n % 10) :: []) := rfl
  rw [step]
  by_cases hn : n / 10 = 0
  · rw [if_pos hn]; simp
  · rw [if_neg hn]; exact toDigitsCore_ne_nil n (n / 10) _ (by simp)

/-- `toString n` repacks to itself. -/
theorem toString_mk (n : Nat) : toString n = String.mk (toString n).data := rfl

theorem decNatStr_self (n : Nat) (rest : List Char) :
    decNatStr ((toString n).data ++ ';' :: rest) = some (n, rest) := by
  have hd : ∀ c ∈ (toString n).data, c.isDigit = true := toString_digits n
  have h9 : ¬ (';' : Char).isDigit = true := by decide
  unfold decNatStr
  rw [List.dropWhile_append_of_pos hd, List.dropWhile_cons_of_neg h9,
    List.takeWhile_append_of_pos hd, List.takeWhile_cons_of_neg h9,
    List.append_nil]
  show (if (toString n).data = [] then none
    else if toString (numOf (toString n).data) = String.mk (toString n).data then
      some (numOf (toString n).data, rest) else none) = some (n, rest)
  rw [if_neg (toString_ne_nil n), numOf_toString, if_pos (toString_mk n)]

/-- `decNatStr` only succeeds on canonical numerals: the consumed part is
    exactly `toString n ++ ";"`. -/
theorem decNatStr_sound {cs rest : List Char} {n : Nat}
    (h : decNatStr cs = some (n, rest)) :
    cs = (toString n).data ++ ';' :: rest := by
  unfold decNatStr at h
  split at h
  · rename_i rest' hdr
    split at h
    · simp at h
    · rename_i hne
      split at h
      · rename_i hcan
        obtain ⟨he, hr⟩ := Prod.mk.inj (Option.some.inj h)
        subst hr; subst he
        have hd : (toString (numOf (cs.takeWhile Char.isDigit))).data =
            cs.takeWhile Char.isDigit := congrArg String.data hcan
        rw [hd, ← hdr]
        exact (List.takeWhile_append_dropWhile Char.isDigit cs).symm
      · simp at h
  · simp at h


/-! ### The level field decode -/

theorem encLevel_zero : (encLevel .zero).data = ['z'] := rfl

theorem encLevel_succ (l : Level) :
    (encLevel (.succ l)).data = 's' :: (encLevel l).data := rfl

theorem encLevel_max (a b : Level) :
    (encLevel (.max a b)).data = 'm' :: ((encLevel a).data ++ (encLevel b).data) :=
  rfl

theorem encLevel_imax (a b : Level) :
    (encLevel (.imax a b)).data = 'i' :: ((encLevel a).data ++ (encLevel b).data) :=
  rfl

theorem encLevel_param (i : Nat) :
    (encLevel (.param i)).data = 'p' :: ((toString i).data ++ [';']) := rfl

/-- Decode one level from a character stream, returning the remainder.
    `encLevel` is a prefix code (`z`, `s`, `m`, `i`, `p<n>;`), so the parse
    is unambiguous; `gas` is termination fuel only — any `gas ≥` the
    encoded length suffices, never a semantic condition. -/
def decLevelG : Nat → List Char → Option (Level × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | g + 1, c :: cs =>
    match c with
    | 'z' => some (.zero, cs)
    | 's' => (decLevelG g cs).map fun (l, r) => (.succ l, r)
    | 'm' =>
      (decLevelG g cs).bind fun (a, r1) =>
        (decLevelG g r1).bind fun (b, r2) => some (.max a b, r2)
    | 'i' =>
      (decLevelG g cs).bind fun (a, r1) =>
        (decLevelG g r1).bind fun (b, r2) => some (.imax a b, r2)
    | 'p' =>
      (decNatStr cs).bind fun (n, r) => some (.param n, r)
    | _ => none

/-- A whole level field: a level followed by end of string. -/
def decLevel (s : String) : Option Level :=
  match decLevelG s.data.length s.data with
  | some (l, []) => some l
  | _ => none

/-- The character list `encLevels`'s `join` actually emits. -/
def encLvlSeq : List Level → List Char := fun ls => ls.flatMap fun l => (encLevel l).data

theorem decLevelG_enc : ∀ (l : Level) (g : Nat) (rest : List Char),
    (encLevel l).data.length ≤ g →
    decLevelG g ((encLevel l).data ++ rest) = some (l, rest) := by
  intro l; induction l with
  | zero =>
    intro g rest hg
    show decLevelG g ('z' :: rest) = some (.zero, rest)
    cases g with
    | zero => simp [encLevel_zero] at hg
    | succ g' => rfl
  | succ a iha =>
    intro g rest hg
    show decLevelG g ('s' :: ((encLevel a).data ++ rest)) = some (.succ a, rest)
    cases g with
    | zero => simp [encLevel_succ] at hg
    | succ g' =>
      have hga : (encLevel a).data.length ≤ g' := by
        simp only [encLevel_succ, List.length_cons] at hg; omega
      rw [decLevelG, iha g' rest hga]
      rfl
  | max a b iha ihb =>
    intro g rest hg
    rw [encLevel_max, List.cons_append, List.append_assoc]
    cases g with
    | zero =>
      rw [encLevel_max, List.length_cons] at hg; omega
    | succ g' =>
      have hga : (encLevel a).data.length ≤ g' := by
        simp only [encLevel_max, List.cons_append, List.length_cons,
          List.length_append] at hg; omega
      have hgb : (encLevel b).data.length ≤ g' := by
        simp only [encLevel_max, List.cons_append, List.length_cons,
          List.length_append] at hg; omega
      rw [decLevelG]
      exact Option.bind_eq_some.mpr ⟨(a, (encLevel b).data ++ rest),
        iha g' _ hga, Option.bind_eq_some.mpr ⟨(b, rest), ihb g' rest hgb, rfl⟩⟩
  | imax a b iha ihb =>
    intro g rest hg
    rw [encLevel_imax, List.cons_append, List.append_assoc]
    cases g with
    | zero =>
      rw [encLevel_imax, List.length_cons] at hg; omega
    | succ g' =>
      have hga : (encLevel a).data.length ≤ g' := by
        simp only [encLevel_imax, List.cons_append, List.length_cons,
          List.length_append] at hg; omega
      have hgb : (encLevel b).data.length ≤ g' := by
        simp only [encLevel_imax, List.cons_append, List.length_cons,
          List.length_append] at hg; omega
      rw [decLevelG]
      exact Option.bind_eq_some.mpr ⟨(a, (encLevel b).data ++ rest),
        iha g' _ hga, Option.bind_eq_some.mpr ⟨(b, rest), ihb g' rest hgb, rfl⟩⟩
  | param i =>
    intro g rest hg
    rw [encLevel_param, List.cons_append, List.append_assoc]
    show decLevelG g ('p' :: ((toString i).data ++ ';' :: rest)) = some (.param i, rest)
    cases g with
    | zero =>
      rw [encLevel_param, List.length_cons] at hg; omega
    | succ g' =>
      rw [decLevelG]
      exact Option.bind_eq_some.mpr ⟨(i, rest), decNatStr_self i rest, rfl⟩

theorem decLevelG_sound : ∀ {g : Nat} {cs rest : List Char} {l : Level},
    decLevelG g cs = some (l, rest) → cs = (encLevel l).data ++ rest := by
  intro g; induction g with
  | zero => intro cs rest l h; simp [decLevelG] at h
  | succ g ih =>
    intro cs rest l h
    cases cs with
    | nil => simp [decLevelG] at h
    | cons c cs' =>
      simp only [decLevelG] at h
      split at h
      · obtain ⟨he, hr⟩ := Prod.mk.inj (Option.some.inj h)
        subst he; subst hr; rfl
      · simp only [Option.map_eq_some'] at h
        obtain ⟨⟨l', r'⟩, hd, hfr⟩ := h
        simp only [Prod.mk.injEq] at hfr
        obtain ⟨rfl, rfl⟩ := hfr
        rw [encLevel_succ, List.cons_append, ih hd]
      · simp only [Option.bind_eq_some] at h
        obtain ⟨⟨a, r1⟩, h1, ⟨b, r2⟩, h2, h3⟩ := h
        have h2' : decLevelG g r1 = some (b, r2) := h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        rw [encLevel_max, List.cons_append, List.append_assoc, ih h1, ih h2']
      · simp only [Option.bind_eq_some] at h
        obtain ⟨⟨a, r1⟩, h1, ⟨b, r2⟩, h2, h3⟩ := h
        have h2' : decLevelG g r1 = some (b, r2) := h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        rw [encLevel_imax, List.cons_append, List.append_assoc, ih h1, ih h2']
      · simp only [Option.bind_eq_some] at h
        obtain ⟨⟨n, r⟩, hd, h3⟩ := h
        simp only [Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        rw [encLevel_param, List.cons_append, List.append_assoc, decNatStr_sound hd,
          List.cons_append, List.nil_append]
      · simp at h

/-- Decode exactly `n` levels, returning the remainder. -/
def decLevelSeq : Nat → List Char → Option (List Level × List Char)
  | 0, cs => some ([], cs)
  | n + 1, cs =>
    (decLevelG cs.length cs).bind fun (l, r) =>
      (decLevelSeq n r).bind fun (ls, r2) => some (l :: ls, r2)

/-- The level field of a `const` token: `count;` then that many levels,
    ending exactly at end of string. -/
def decLevels (s : String) : Option (List Level) :=
  (decNatStr s.data).bind fun (n, rest) =>
    (decLevelSeq n rest).bind fun (ls, rest2) =>
      if rest2 = [] then some ls else none

theorem join_data (ss : List String) :
    (String.join ss).data = ss.flatMap String.data := by
  have go : ∀ (ss : List String) (init : String),
      (List.foldl (fun r s => r ++ s) init ss).data =
        init.data ++ ss.flatMap String.data := by
    intro ss; induction ss with
    | nil => intro init; simp
    | cons s ss ih =>
      intro init
      rw [List.foldl_cons, ih, List.flatMap_cons, String.data_append,
        ← List.append_assoc]
  have := go ss ""
  simpa [String.join] using this

theorem encLvlSeq_cons (l : Level) (ls : List Level) :
    encLvlSeq (l :: ls) = (encLevel l).data ++ encLvlSeq ls := rfl

theorem decLevelSeq_enc : ∀ (ls : List Level) (rest : List Char),
    decLevelSeq ls.length (encLvlSeq ls ++ rest) = some (ls, rest) := by
  intro ls; induction ls with
  | nil => intro rest; rfl
  | cons l ls ih =>
    intro rest
    show decLevelSeq (ls.length + 1) ((encLevel l).data ++ encLvlSeq ls ++ rest) = _
    rw [decLevelSeq, List.append_assoc]
    apply Option.bind_eq_some.mpr
    exact ⟨(l, encLvlSeq ls ++ rest),
      decLevelG_enc l ((encLevel l).data ++ (encLvlSeq ls ++ rest)).length
        (encLvlSeq ls ++ rest)
        (by rw [List.length_append]; exact Nat.le_add_right _ _),
      Option.bind_eq_some.mpr ⟨(ls, rest), ih rest, rfl⟩⟩

theorem decLevelSeq_sound {n : Nat} {cs rest : List Char} {ls : List Level}
    (h : decLevelSeq n cs = some (ls, rest)) :
    ls.length = n ∧ cs = encLvlSeq ls ++ rest := by
  induction n generalizing cs ls with
  | zero =>
    simp only [decLevelSeq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [decLevelSeq] at h
    simp only [Option.bind_eq_some] at h
    obtain ⟨⟨l, r1⟩, h1, hrest⟩ := h
    simp only [Option.bind_eq_some] at hrest
    obtain ⟨⟨ls', r2⟩, h2, h3⟩ := hrest
    have h2' : decLevelSeq n r1 = some (ls', r2) := h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    obtain ⟨hl, hcs⟩ := ih h2'
    refine ⟨?_, ?_⟩
    · rw [List.length_cons, hl]
    · rw [decLevelG_sound h1, hcs, encLvlSeq_cons, List.append_assoc]

theorem decLevel_self (l : Level) : decLevel (encLevel l) = some l := by
  show (match decLevelG (encLevel l).data.length (encLevel l).data with
        | some (l', []) => some l' | _ => none) = some l
  have h2 := decLevelG_enc l (encLevel l).data.length [] (Nat.le_refl _)
  rw [List.append_nil] at h2
  rw [h2]

theorem decLevel_sound {s : String} {l : Level} (h : decLevel s = some l) :
    s = encLevel l := by
  unfold decLevel at h
  split at h
  · rename_i x hx
    obtain rfl := Option.some.inj h
    have hd := decLevelG_sound hx
    rw [List.append_nil] at hd
    exact String.ext hd
  · simp at h

theorem decLevels_self (ls : List Level) : decLevels (encLevels ls) = some ls := by
  have hdata : (toString ls.length ++ ";" ++ String.join (ls.map encLevel)).data =
      (toString ls.length).data ++ ';' :: encLvlSeq ls := by
    rw [String.data_append, String.data_append, join_data, List.flatMap_map]
    rw [show (";" : String).data = [';'] from rfl]
    rw [List.append_assoc, List.cons_append, List.nil_append]
    rw [show encLvlSeq ls = ls.flatMap fun a => (encLevel a).data from rfl]
  unfold decLevels encLevels
  rw [hdata, decNatStr_self]
  apply Option.bind_eq_some.mpr
  exact ⟨(ls.length, encLvlSeq ls), rfl,
    Option.bind_eq_some.mpr ⟨(ls, []),
      by rw [← List.append_nil (encLvlSeq ls)]; exact decLevelSeq_enc ls [],
      by simp⟩⟩

theorem decLevels_sound {s : String} {ls : List Level}
    (h : decLevels s = some ls) :
    s.data = (toString ls.length).data ++ ';' :: encLvlSeq ls := by
  unfold decLevels at h
  simp only [Option.bind_eq_some] at h
  obtain ⟨⟨n', r1⟩, h1, hrest⟩ := h
  simp only [Option.bind_eq_some] at hrest
  obtain ⟨⟨ls', r2⟩, h2, h3⟩ := hrest
  have h2' : decLevelSeq n' r1 = some (ls', r2) := h2
  dsimp only at h3
  split at h3
  · rename_i hr2
    obtain rfl := Option.some.inj h3
    have hd' := decNatStr_sound h1
    obtain ⟨hl, hs'⟩ := decLevelSeq_sound h2'
    rw [hd', ← hl, hs', hr2, List.append_nil]
  · simp at h3

/-! ### The token-stream decode -/

/-- An i64 payload decodes to a `Nat` only inside the checked non-negative
    i64 range — `toNat` is a conversion on a checked branch, not a repair
    (negative and out-of-range payloads are refused, never truncated or
    wrapped). -/
def decNatTok (n : Int) : Option Nat :=
  if 0 ≤ n ∧ n ≤ i64Max then some n.toNat else none

theorem decNatTok_eq {n : Int} {i : Nat} :
    decNatTok n = some i ↔ 0 ≤ n ∧ n ≤ i64Max ∧ i = n.toNat := by
  unfold decNatTok
  by_cases h : 0 ≤ n ∧ n ≤ i64Max
  · rw [if_pos h]
    constructor
    · intro h2; exact ⟨h.1, h.2, (Option.some.inj h2).symm⟩
    · rintro ⟨_, _, rfl⟩; rfl
  · rw [if_neg h]
    constructor
    · intro h2; simp at h2
    · intro hc; exact absurd ⟨hc.1, hc.2.1⟩ h

theorem decNatTok_nat (i : Nat) (h : (i : Int) ≤ i64Max) :
    decNatTok (i : Int) = some i := by
  unfold decNatTok
  rw [if_pos ⟨Int.ofNat_nonneg i, h⟩, Int.toNat_ofNat]

/-- Consume one marker token: `tokV k "" 0` for `k ∈ {8,9}` — the canonical
    marker payload; anything else is refused. -/
def expectMarker (k : Int) : List Val → Option (List Val)
  | .r [.i k', .s l', .i n'] :: ts =>
    if k' = k ∧ l' = "" ∧ n' = 0 then some ts else none
  | _ => none

theorem expectMarker_self {k : Int} {rest : List Val} :
    expectMarker k (tokV k "" 0 :: rest) = some rest := by
  simp [expectMarker, tokV]

theorem expectMarker_enter {rest : List Val} :
    expectMarker 8 (enterT :: rest) = some rest := expectMarker_self

theorem expectMarker_exit {rest : List Val} :
    expectMarker 9 (exitT :: rest) = some rest := expectMarker_self

theorem expectMarker_sound {k : Int} {r1 r1' : List Val}
    (h : expectMarker k r1 = some r1') : r1 = tokV k "" 0 :: r1' := by
  unfold expectMarker at h
  split at h
  · rename_i k' l' n' ts
    by_cases hcond : k' = k ∧ l' = "" ∧ n' = 0
    · simp only [if_pos hcond, Option.some.injEq] at h
      obtain ⟨hk, hl, hn⟩ := hcond
      subst hk; subst hl; subst hn; subst h
      rfl
    · rw [if_neg hcond] at h
      exact Option.noConfusion h
  · simp at h

/-- The token-stream decode: `gas` tokens of fuel. Every token must be the
    record `{k, l, n}` with a legal tag and a canonical payload; ENTER/EXIT
    are consumed only at exact binder-body boundaries by the grammar, so a
    lone marker, an unbalanced close, or a negative-balance prefix is
    refused — and `SUB` (k = 10), which is output-only, never occurs in a
    legal input. Returns the term and the unconsumed rest. -/
def decToksG : Nat → List Val → Option (Expr Nat × List Val)
  | 0, _ => none
  | _ + 1, [] => none
  | g + 1, t :: ts =>
    match t with
    | .r [.i k, .s l, .i n] =>
      if k = 0 then
        if l = "" then (decNatTok n).map fun i => (.bvar i, ts) else none
      else if k = 1 then
        if n = 0 then (decLevel l).map fun lv => (.sort lv, ts) else none
      else if k = 2 then
        (decNatTok n).bind fun r => (decLevels l).map fun ls => (.const r ls, ts)
      else if k = 3 then
        if l = "" ∧ n = 0 then
          (decToksG g ts).bind fun (f, r1) =>
            (decToksG g r1).bind fun (x, r2) => some (.app f x, r2)
        else none
      else if k = 4 then
        if l = "" ∧ n = 0 then
          (decToksG g ts).bind fun (a, r1) =>
            (expectMarker 8 r1).bind fun r1' =>
              (decToksG g r1').bind fun (b, r2) =>
                (expectMarker 9 r2).bind fun r2' => some (.lam a b, r2')
        else none
      else if k = 5 then
        if l = "" ∧ n = 0 then
          (decToksG g ts).bind fun (a, r1) =>
            (expectMarker 8 r1).bind fun r1' =>
              (decToksG g r1').bind fun (b, r2) =>
                (expectMarker 9 r2).bind fun r2' => some (.pi a b, r2')
        else none
      else if k = 6 then
        if l = "" ∧ n = 0 then
          (decToksG g ts).bind fun (a, r1) =>
            (decToksG g r1).bind fun (v, r2) =>
              (expectMarker 8 r2).bind fun r2' =>
                (decToksG g r2').bind fun (b, r3) =>
                  (expectMarker 9 r3).bind fun r3' => some (.letE a v b, r3')
        else none
      else if k = 7 then
        if l = "" then (decNatTok n).map fun t' => (.lit t', ts) else none
      else none
    | _ => none

/-- A whole token list: a term followed by end of list. -/
def decToks (ts : List Val) : Option (Expr Nat) :=
  match decToksG ts.length ts with
  | some (e, []) => some e
  | _ => none

/-- The V1 input decode (E-07CompactInstantiate, reworked): the input
    record `{depth, e, r}` decodes iff `depth` is a non-negative i64 (the
    declared field type; `D = depth.toNat` is a conversion on a checked
    branch, not a repair) and each token list is exactly the encoding of a
    term. `some (D, e, r)` carries no target-correctness field and no
    execution-success field — it is a pure syntactic decode. -/
def decodeInputV1 : Val → Option (Nat × Expr Nat × Expr Nat)
  | .r [.i d, .l te, .l tr] =>
    if 0 ≤ d ∧ d ≤ i64Max then
      match decToks te, decToks tr with
      | some e, some r => some (d.toNat, e, r)
      | _, _ => none
    else none
  | _ => none

/-- `e` is in the V1 representation domain: `encToks` succeeds and yields
    the unconditional encoding. -/
def repOk (e : Expr Nat) : Prop := encToks e = some (encToksU e)

theorem repN_of_decNatTok {n : Int} {i : Nat} (h : decNatTok n = some i) :
    repN i := by
  rw [decNatTok_eq] at h
  obtain ⟨h0, hM, rfl⟩ := h
  show decide ((n.toNat : Int) ≤ i64Max) = true
  rw [decide_eq_true_eq, Int.toNat_of_nonneg h0]
  exact hM

theorem repOk_bvar {i : Nat} (h : repN i) : repOk (.bvar i) := by
  show (if repN i then some [tokV 0 "" (i : Int)] else none) =
    some [tokV 0 "" (i : Int)]
  rw [if_pos h]

theorem repOk_sort (l : Level) : repOk (.sort l) := rfl

theorem repOk_const {r : Nat} {ls : List Level} (h : repN r) :
    repOk (.const r ls) := by
  show (if repN r then some [tokV 2 (encLevels ls) r] else none) =
    some [tokV 2 (encLevels ls) r]
  rw [if_pos h]

theorem repOk_lit {t : Nat} (h : repN t) : repOk (.lit t) := by
  show (if repN t then some [tokV 7 "" t] else none) = some [tokV 7 "" t]
  rw [if_pos h]

theorem repOk_app {f x : Expr Nat} (hf : repOk f) (hx : repOk x) :
    repOk (.app f x) := by
  have hf' : encToks f = some (encToksU f) := hf
  have hx' : encToks x = some (encToksU x) := hx
  simp [repOk, encToks, encToksU, hf', hx']

theorem repOk_lam {a b : Expr Nat} (ha : repOk a) (hb : repOk b) :
    repOk (.lam a b) := by
  have ha' : encToks a = some (encToksU a) := ha
  have hb' : encToks b = some (encToksU b) := hb
  simp [repOk, encToks, encToksU, ha', hb']

theorem repOk_pi {a b : Expr Nat} (ha : repOk a) (hb : repOk b) :
    repOk (.pi a b) := by
  have ha' : encToks a = some (encToksU a) := ha
  have hb' : encToks b = some (encToksU b) := hb
  simp [repOk, encToks, encToksU, ha', hb']

theorem repOk_letE {a v b : Expr Nat} (ha : repOk a) (hv : repOk v)
    (hb : repOk b) : repOk (.letE a v b) := by
  have ha' : encToks a = some (encToksU a) := ha
  have hv' : encToks v = some (encToksU v) := hv
  have hb' : encToks b = some (encToksU b) := hb
  simp [repOk, encToks, encToksU, ha', hv', hb']

theorem repOk_app_inv {f x : Expr Nat} (h : repOk (.app f x)) :
    repOk f ∧ repOk x := by
  unfold repOk at h
  unfold encToks at h
  split at h
  · rename_i a b hf hx
    have ha := encToks_eq_encToksU hf
    have hb := encToks_eq_encToksU hx
    constructor <;> show encToks _ = some _
    · rw [ha]; exact hf
    · rw [hb]; exact hx
  · simp at h

theorem repOk_lam_inv {a b : Expr Nat} (h : repOk (.lam a b)) :
    repOk a ∧ repOk b := by
  unfold repOk at h
  unfold encToks at h
  split at h
  · rename_i ta tb ha' hb'
    have ha := encToks_eq_encToksU ha'
    have hb := encToks_eq_encToksU hb'
    constructor <;> show encToks _ = some _
    · rw [ha]; exact ha'
    · rw [hb]; exact hb'
  · simp at h

theorem repOk_pi_inv {a b : Expr Nat} (h : repOk (.pi a b)) :
    repOk a ∧ repOk b := by
  unfold repOk at h
  unfold encToks at h
  split at h
  · rename_i ta tb ha' hb'
    have ha := encToks_eq_encToksU ha'
    have hb := encToks_eq_encToksU hb'
    constructor <;> show encToks _ = some _
    · rw [ha]; exact ha'
    · rw [hb]; exact hb'
  · simp at h

theorem repOk_letE_inv {a v b : Expr Nat} (h : repOk (.letE a v b)) :
    repOk a ∧ repOk v ∧ repOk b := by
  unfold repOk at h
  unfold encToks at h
  split at h
  · rename_i ta tv tb ha' hv' hb'
    have ha := encToks_eq_encToksU ha'
    have hv := encToks_eq_encToksU hv'
    have hb := encToks_eq_encToksU hb'
    refine ⟨?_, ?_, ?_⟩ <;> show encToks _ = some _
    · rw [ha]; exact ha'
    · rw [hv]; exact hv'
    · rw [hb]; exact hb'
  · simp at h

/-- Every canonical encoding decodes back to its term. -/
theorem decToksG_enc : ∀ (e : Expr Nat) (g : Nat) (rest : List Val),
    repOk e → (encToksU e).length ≤ g →
    decToksG g (encToksU e ++ rest) = some (e, rest) := by
  intro e; induction e with
  | bvar i =>
    intro g rest hr hg
    have hN : repN i := by
      have hr' : (if repN i then some [tokV 0 "" (i : Int)] else none) =
          some [tokV 0 "" (i : Int)] := hr
      split at hr'
      · rename_i hN'; exact hN'
      · simp at hr'
    have hle : (i : Int) ≤ i64Max := of_decide_eq_true hN
    show decToksG g (tokV 0 "" (i : Int) :: rest) = some (.bvar i, rest)
    cases g with
    | zero => simp [encToksU] at hg
    | succ g' =>
      simp [decToksG, tokV, decNatTok_nat i hle]
  | sort l =>
    intro g rest hr hg
    show decToksG g (tokV 1 (encLevel l) 0 :: rest) = some (.sort l, rest)
    cases g with
    | zero => simp [encToksU] at hg
    | succ g' =>
      simp [decToksG, tokV, decLevel_self]
  | const r ls =>
    intro g rest hr hg
    have hN : repN r := by
      have hr' : (if repN r then some [tokV 2 (encLevels ls) (r : Int)] else none) =
          some [tokV 2 (encLevels ls) (r : Int)] := hr
      split at hr'
      · rename_i hN'; exact hN'
      · simp at hr'
    have hle : (r : Int) ≤ i64Max := of_decide_eq_true hN
    show decToksG g (tokV 2 (encLevels ls) r :: rest) = some (.const r ls, rest)
    cases g with
    | zero => simp [encToksU] at hg
    | succ g' =>
      simp [decToksG, tokV, decNatTok_nat r hle, decLevels_self]
  | lit t =>
    intro g rest hr hg
    have hN : repN t := by
      have hr' : (if repN t then some [tokV 7 "" (t : Int)] else none) =
          some [tokV 7 "" (t : Int)] := hr
      split at hr'
      · rename_i hN'; exact hN'
      · simp at hr'
    have hle : (t : Int) ≤ i64Max := of_decide_eq_true hN
    show decToksG g (tokV 7 "" t :: rest) = some (.lit t, rest)
    cases g with
    | zero => simp [encToksU] at hg
    | succ g' =>
      simp [decToksG, tokV, decNatTok_nat t hle]
  | app f x ihf ihx =>
    intro g rest hr hg
    obtain ⟨hf, hx⟩ := repOk_app_inv hr
    have hx0 : encToksU (.app f x) ++ rest =
        tokV 3 "" 0 :: (encToksU f ++ encToksU x ++ rest) := by
      simp [encToksU, List.append_assoc]
    rw [hx0]
    cases g with
    | zero => simp [encToksU] at hg
    | succ g' =>
      have hf' : (encToksU f).length ≤ g' := by
        simp only [encToksU, List.cons_append, List.length_cons,
          List.length_append] at hg; omega
      have hx' : (encToksU x).length ≤ g' := by
        simp only [encToksU, List.cons_append, List.length_cons,
          List.length_append] at hg; omega
      simp [decToksG, tokV, ihf g' (encToksU x ++ rest) hf hf',
        ihx g' rest hx hx']
  | lam a b iha ihb =>
    intro g rest hr hg
    obtain ⟨ha, hb⟩ := repOk_lam_inv hr
    have hx0 : encToksU (.lam a b) ++ rest =
        tokV 4 "" 0 :: (encToksU a ++ enterT :: (encToksU b ++ exitT :: rest)) := by
      simp [encToksU, List.append_assoc]
    rw [hx0]
    cases g with
    | zero => simp [encToksU] at hg
    | succ g' =>
      have ha' : (encToksU a).length ≤ g' := by
        simp only [encToksU, List.cons_append, List.length_cons,
          List.length_append] at hg; omega
      have hb' : (encToksU b).length ≤ g' := by
        simp only [encToksU, List.cons_append, List.length_cons,
          List.length_append] at hg; omega
      simp [decToksG, tokV,
        iha g' (enterT :: (encToksU b ++ exitT :: rest)) ha ha',
        expectMarker_enter, ihb g' (exitT :: rest) hb hb', expectMarker_exit]
  | pi a b iha ihb =>
    intro g rest hr hg
    obtain ⟨ha, hb⟩ := repOk_pi_inv hr
    have hx0 : encToksU (.pi a b) ++ rest =
        tokV 5 "" 0 :: (encToksU a ++ enterT :: (encToksU b ++ exitT :: rest)) := by
      simp [encToksU, List.append_assoc]
    rw [hx0]
    cases g with
    | zero => simp [encToksU] at hg
    | succ g' =>
      have ha' : (encToksU a).length ≤ g' := by
        simp only [encToksU, List.cons_append, List.length_cons,
          List.length_append] at hg; omega
      have hb' : (encToksU b).length ≤ g' := by
        simp only [encToksU, List.cons_append, List.length_cons,
          List.length_append] at hg; omega
      simp [decToksG, tokV,
        iha g' (enterT :: (encToksU b ++ exitT :: rest)) ha ha',
        expectMarker_enter, ihb g' (exitT :: rest) hb hb', expectMarker_exit]
  | letE a v b iha ihv ihb =>
    intro g rest hr hg
    obtain ⟨ha, hv, hb⟩ := repOk_letE_inv hr
    have hx0 : encToksU (.letE a v b) ++ rest = tokV 6 "" 0 ::
        (encToksU a ++ encToksU v ++ enterT :: (encToksU b ++ exitT :: rest)) := by
      simp [encToksU, List.append_assoc]
    rw [hx0]
    cases g with
    | zero => simp [encToksU] at hg
    | succ g' =>
      have ha' : (encToksU a).length ≤ g' := by
        simp only [encToksU, List.cons_append, List.length_cons,
          List.length_append] at hg; omega
      have hv' : (encToksU v).length ≤ g' := by
        simp only [encToksU, List.cons_append, List.length_cons,
          List.length_append] at hg; omega
      have hb' : (encToksU b).length ≤ g' := by
        simp only [encToksU, List.cons_append, List.length_cons,
          List.length_append] at hg; omega
      simp [decToksG, tokV,
        iha g' (encToksU v ++ enterT :: (encToksU b ++ exitT :: rest)) ha ha',
        ihv g' (enterT :: (encToksU b ++ exitT :: rest)) hv hv',
        expectMarker_enter, ihb g' (exitT :: rest) hb hb', expectMarker_exit]

/-- The decoded stream is exactly the canonical encoding of the decoded
    term, and the term is in the V1 representation domain. -/
theorem decToksG_sound : ∀ {g : Nat} {ts rest : List Val} {e : Expr Nat},
    decToksG g ts = some (e, rest) → ts = encToksU e ++ rest ∧ repOk e := by
  intro g; induction g with
  | zero => intro ts rest e h; simp [decToksG] at h
  | succ g ih =>
    intro ts rest e h
    cases ts with
    | nil => simp [decToksG] at h
    | cons t ts' =>
      simp only [decToksG] at h
      split at h
      · rename_i k l n
        by_cases h0 : k = 0
        · rw [if_pos h0] at h
          by_cases hl : l = ""
          · rw [if_pos hl] at h
            simp only [Option.map_eq_some'] at h
            obtain ⟨i, hd, hfr⟩ := h
            obtain ⟨he, hr⟩ := Prod.mk.inj hfr
            subst he; subst hr
            rw [decNatTok_eq] at hd
            obtain ⟨h0n, hMn, hi⟩ := hd
            have hn : (i : Int) = n := by rw [hi]; exact Int.toNat_of_nonneg h0n
            subst h0; subst hl
            constructor
            · rw [encToksU]; simp [tokV]; rw [hn]
            · exact repOk_bvar (repN_of_decNatTok (by rw [decNatTok_eq]; exact ⟨h0n, hMn, hi⟩))
          · rw [if_neg hl] at h; simp at h
        · rw [if_neg h0] at h
          by_cases h1 : k = 1
          · rw [if_pos h1] at h
            by_cases hn0 : n = 0
            · rw [if_pos hn0] at h
              simp only [Option.map_eq_some'] at h
              obtain ⟨lv, hd, hfr⟩ := h
              obtain ⟨he, hr⟩ := Prod.mk.inj hfr
              subst he; subst hr
              subst h1; subst hn0
              constructor
              · rw [encToksU, decLevel_sound hd]; rfl
              · exact repOk_sort lv
            · rw [if_neg hn0] at h; simp at h
          · rw [if_neg h1] at h
            by_cases h2 : k = 2
            · rw [if_pos h2] at h
              simp only [Option.bind_eq_some] at h
              obtain ⟨r, hdr, hfr⟩ := h
              simp only [Option.map_eq_some'] at hfr
              obtain ⟨ls, hdl, hfr⟩ := hfr
              obtain ⟨he, hr⟩ := Prod.mk.inj hfr
              subst he; subst hr
              rw [decNatTok_eq] at hdr
              obtain ⟨h0n, hMn, hi⟩ := hdr
              have hn : (r : Int) = n := by rw [hi]; exact Int.toNat_of_nonneg h0n
              subst h2
              constructor
              · have hlv : l = encLevels ls := by
                  apply String.ext
                  show l.data = (toString ls.length ++ ";" ++
                      String.join (ls.map encLevel)).data
                  rw [decLevels_sound hdl, String.data_append, String.data_append,
                    join_data, List.flatMap_map]
                  rw [show (";" : String).data = [';'] from rfl]
                  rw [List.append_assoc, List.cons_append, List.nil_append]
                  rw [show encLvlSeq ls = ls.flatMap fun a => (encLevel a).data from rfl]
                rw [encToksU, hlv]; simp [tokV]; rw [hn]
              · exact repOk_const
                  (repN_of_decNatTok (by rw [decNatTok_eq]; exact ⟨h0n, hMn, hi⟩))
            · rw [if_neg h2] at h
              by_cases h3 : k = 3
              · rw [if_pos h3] at h
                split at h
                · rename_i hln
                  obtain ⟨hl, hn⟩ := hln
                  simp only [Option.bind_eq_some] at h
                  obtain ⟨⟨f, r1⟩, h1, ⟨x, r2⟩, h2, hfin⟩ := h
                  have h2' : decToksG g r1 = some (x, r2) := h2
                  simp only [Option.some.injEq, Prod.mk.injEq] at hfin
                  obtain ⟨rfl, rfl⟩ := hfin
                  obtain ⟨tsf, hf⟩ := ih h1
                  obtain ⟨tsx, hx⟩ := ih h2'
                  subst h3; subst hl; subst hn
                  rw [tsf, tsx]
                  constructor
                  · simp [encToksU, tokV, List.append_assoc]
                  · exact repOk_app hf hx
                · simp at h
              · rw [if_neg h3] at h
                by_cases h4 : k = 4
                · rw [if_pos h4] at h
                  split at h
                  · rename_i hln
                    obtain ⟨hl, hn⟩ := hln
                    simp only [Option.bind_eq_some] at h
                    obtain ⟨⟨a, r1⟩, h1, r1', hm1, ⟨b, r2⟩, h2, r2', hm2, hfin⟩ := h
                    simp only [Option.some.injEq, Prod.mk.injEq] at hfin
                    obtain ⟨rfl, rfl⟩ := hfin
                    have hm1' : r1 = enterT :: r1' := expectMarker_sound hm1
                    have hm2' : r2 = exitT :: r2' := expectMarker_sound hm2
                    obtain ⟨tsa, ha⟩ := ih h1
                    obtain ⟨tsb, hb⟩ := ih h2
                    subst h4; subst hl; subst hn
                    rw [tsa, hm1', tsb, hm2']
                    constructor
                    · simp [encToksU, tokV, enterT, exitT, List.append_assoc]
                    · exact repOk_lam ha hb
                  · simp at h
                · rw [if_neg h4] at h
                  by_cases h5 : k = 5
                  · rw [if_pos h5] at h
                    split at h
                    · rename_i hln
                      obtain ⟨hl, hn⟩ := hln
                      simp only [Option.bind_eq_some] at h
                      obtain ⟨⟨a, r1⟩, h1, r1', hm1, ⟨b, r2⟩, h2, r2', hm2, hfin⟩ := h
                      simp only [Option.some.injEq, Prod.mk.injEq] at hfin
                      obtain ⟨rfl, rfl⟩ := hfin
                      have hm1' : r1 = enterT :: r1' := expectMarker_sound hm1
                      have hm2' : r2 = exitT :: r2' := expectMarker_sound hm2
                      obtain ⟨tsa, ha⟩ := ih h1
                      obtain ⟨tsb, hb⟩ := ih h2
                      subst h5; subst hl; subst hn
                      rw [tsa, hm1', tsb, hm2']
                      constructor
                      · simp [encToksU, tokV, enterT, exitT, List.append_assoc]
                      · exact repOk_pi ha hb
                    · simp at h
                  · rw [if_neg h5] at h
                    by_cases h6 : k = 6
                    · rw [if_pos h6] at h
                      split at h
                      · rename_i hln
                        obtain ⟨hl, hn⟩ := hln
                        simp only [Option.bind_eq_some] at h
                        obtain ⟨⟨a, r1⟩, h1, ⟨v, r2⟩, h2, r2', hm1, ⟨b, r3⟩, h3',
                          r3', hm2, hfin⟩ := h
                        have h2' : decToksG g r1 = some (v, r2) := h2
                        simp only [Option.some.injEq, Prod.mk.injEq] at hfin
                        obtain ⟨rfl, rfl⟩ := hfin
                        have hm1' : r2 = enterT :: r2' := expectMarker_sound hm1
                        have hm2' : r3 = exitT :: r3' := expectMarker_sound hm2
                        obtain ⟨tsa, ha⟩ := ih h1
                        obtain ⟨tsv, hv⟩ := ih h2'
                        obtain ⟨tsb, hb⟩ := ih h3'
                        subst h6; subst hl; subst hn
                        rw [tsa, tsv, hm1', tsb, hm2']
                        constructor
                        · simp [encToksU, tokV, enterT, exitT, List.append_assoc]
                        · exact repOk_letE ha hv hb
                      · simp at h
                    · rw [if_neg h6] at h
                      by_cases h7 : k = 7
                      · rw [if_pos h7] at h
                        by_cases hl : l = ""
                        · rw [if_pos hl] at h
                          simp only [Option.map_eq_some'] at h
                          obtain ⟨t', hd, hfr⟩ := h
                          obtain ⟨he, hr⟩ := Prod.mk.inj hfr
                          subst he; subst hr
                          rw [decNatTok_eq] at hd
                          obtain ⟨h0n, hMn, hi⟩ := hd
                          have hn : (t' : Int) = n := by
                            rw [hi]; exact Int.toNat_of_nonneg h0n
                          subst h7; subst hl
                          constructor
                          · rw [encToksU]; simp [tokV]; rw [hn]
                          · exact repOk_lit
                              (repN_of_decNatTok (by rw [decNatTok_eq]; exact ⟨h0n, hMn, hi⟩))
                        · rw [if_neg hl] at h; simp at h
                      · rw [if_neg h7] at h; simp at h
      · simp at h

theorem decToks_enc {e : Expr Nat} (hr : repOk e) :
    decToks (encToksU e) = some e := by
  show (match decToksG (encToksU e).length (encToksU e) with
        | some (e', []) => some e' | _ => none) = some e
  have h2 := decToksG_enc e (encToksU e).length [] hr (Nat.le_refl _)
  rw [List.append_nil] at h2
  rw [h2]

theorem decToks_sound {ts : List Val} {e : Expr Nat} (h : decToks ts = some e) :
    ts = encToksU e ∧ repOk e := by
  unfold decToks at h
  split at h
  · rename_i e' hx
    obtain rfl := Option.some.inj h
    obtain ⟨hts, hrep⟩ := decToksG_sound hx
    rw [List.append_nil] at hts
    exact ⟨hts, hrep⟩
  · simp at h

/-- Any input value built from two encodings and a non-negative i64 depth
    decodes — the contract side of the decode. -/
theorem decodeInputV1_complete {D : Int} {e r : Expr Nat}
    (hD : 0 ≤ D) (hDM : D ≤ i64Max) (he : repOk e) (hr : repOk r) :
    decodeInputV1 (inputV D (encToksU e) (encToksU r)) = some (D.toNat, e, r) := by
  show decodeInputV1 (.r [.i D, .l (encToksU e), .l (encToksU r)]) = _
  simp only [decodeInputV1]
  rw [if_pos ⟨hD, hDM⟩, decToks_enc he, decToks_enc hr]

/-- A successful decode determines the input record, the depth field, and
    both term encodings — the exact premises `instV1_total`'s derivation
    consumes. -/
theorem decodeInputV1_sound {input : Val} {D : Nat} {e r : Expr Nat}
    (h : decodeInputV1 input = some (D, e, r)) :
    input = inputV (D : Int) (encToksU e) (encToksU r) ∧
    (D : Int) ≤ i64Max ∧ repOk e ∧ repOk r := by
  unfold decodeInputV1 at h
  split at h
  · rename_i d te tr
    split at h
    · rename_i hD
      split at h
      · rename_i e' r' he' hr'
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨hte, he_rep⟩ := decToks_sound he'
        obtain ⟨htr, hr_rep⟩ := decToks_sound hr'
        subst hte; subst htr
        refine ⟨?_, ?_, he_rep, hr_rep⟩
        · show Val.r [Val.i d, Val.l (encToksU e'), Val.l (encToksU r')] =
            Val.r [Val.i (d.toNat : Int), Val.l (encToksU e'), Val.l (encToksU r')]
          rw [Int.toNat_of_nonneg hD.1]
        · rw [Int.toNat_of_nonneg hD.1]; exact hD.2
      · simp at h
    · simp at h
  · simp at h

/-- The kind/payload view of a token-shaped value. -/
def tokKL : Val → Option (Int × String × Int)
  | .r [.i k, .s l, .i n] => some (k, l, n)
  | _ => none

theorem tokKL_tok (k : Int) (l : String) (n : Int) :
    tokKL (tokV k l n) = some (k, l, n) := rfl

/-- `lift` on a token stream: the walk tracks the local binder depth `m` via
    the stream's own ENTER/EXIT markers; a `bvar` token with `m ≤ n` gains
    `amt`. This is the token-level image of `lift m.toNat amt.toNat` on the
    rooted encoding. -/
def liftToksBy (amt m : Int) : List Val → List Val
  | [] => []
  | t :: ts =>
    match tokKL t with
    | some (k, l, n) =>
      if k = 8 then t :: liftToksBy amt (m + 1) ts
      else if k = 9 then t :: liftToksBy amt (m - 1) ts
      else if k = 0 ∧ m ≤ n then tokV 0 l (n + amt) :: liftToksBy amt m ts
      else t :: liftToksBy amt m ts
    | none => t :: liftToksBy amt m ts

/-- The compact skeleton's `SUB(d)` marker splices in the replacement lifted
    by `d`. Every other token is carried verbatim. -/
def expandSkel (repl : List Val) : List Val → List Val
  | [] => []
  | t :: ts =>
    match tokKL t with
    | some (k, _, d) =>
      if k = 10 then liftToksBy d 0 repl ++ expandSkel repl ts
      else t :: expandSkel repl ts
    | none => t :: expandSkel repl ts

/-- The V1 compact-output interpretation (E-07CompactInstantiate): read the
    `{repl, skel}` fields — nothing else — and splice each `SUB(d)` into the
    replacement lifted at `d`. It never calls `instantiate`; the correctness
    theorem below relates it to the declarative reference. -/
def expandCompact : Val → Option Val
  | .r [.l repl, .l skel] => some (.l (expandSkel repl skel))
  | _ => none

theorem int_le_toNat {i : Nat} {d : Int} (hd : 0 ≤ d) :
    (d ≤ (i : Int) ↔ d.toNat ≤ i) := by
  have hd' : (d.toNat : Int) = d := Int.toNat_of_nonneg hd
  constructor
  · intro h; rw [← hd'] at h; exact Int.ofNat_le.mp h
  · intro h; rw [← hd']; exact Int.ofNat_le.mpr h

theorem liftToksBy_enter (amt m : Int) (l : String) (n : Int) (ts : List Val) :
    liftToksBy amt m (tokV 8 l n :: ts) = tokV 8 l n :: liftToksBy amt (m + 1) ts := by
  simp [liftToksBy, tokKL, tokV]

theorem liftToksBy_exit (amt m : Int) (l : String) (n : Int) (ts : List Val) :
    liftToksBy amt m (tokV 9 l n :: ts) = tokV 9 l n :: liftToksBy amt (m - 1) ts := by
  simp [liftToksBy, tokKL, tokV]

theorem liftToksBy_bvar (amt m : Int) (l : String) (n : Int) (ts : List Val) :
    liftToksBy amt m (tokV 0 l n :: ts) =
      (if m ≤ n then tokV 0 l (n + amt) else tokV 0 l n) :: liftToksBy amt m ts := by
  by_cases hmn : m ≤ n <;> simp [liftToksBy, tokKL, tokV, hmn]

theorem liftToksBy_keep (amt m : Int) (k : Int) (l : String) (n : Int) (ts : List Val)
    (h8 : k ≠ 8) (h9 : k ≠ 9) (h0 : ¬ (k = 0 ∧ m ≤ n)) :
    liftToksBy amt m (tokV k l n :: ts) = tokV k l n :: liftToksBy amt m ts := by
  simp [liftToksBy, tokKL, tokV, h8, h9, h0]

/-- The walk over a rooted encoding of `e` returns `e`'s tokens lifted at
    the entry depth and leaves `rest` to be walked at the same depth (the
    encoding's markers are balanced). -/
theorem liftToksBy_enc (a : Nat) :
    ∀ (e : Expr Nat) (m : Int) (rest : List Val), 0 ≤ m →
    liftToksBy (a : Int) m (encToksU e ++ rest) =
      encToksU (lift m.toNat a e) ++ liftToksBy (a : Int) m rest := by
  intro e; induction e with
  | bvar i =>
    intro m rest hm
    have hA : encToksU (.bvar i) ++ rest = tokV 0 "" (i : Int) :: rest := rfl
    rw [hA, liftToksBy_bvar, lift]
    by_cases hmi : m ≤ (i : Int)
    · rw [if_pos hmi, if_pos ((int_le_toNat hm).mp hmi)]
      simp [encToksU, tokV]
    · rw [if_neg hmi, if_neg (fun h => hmi ((int_le_toNat hm).mpr h))]
      simp [encToksU, tokV]
  | sort l =>
    intro m rest hm
    have hA : encToksU (.sort l) ++ rest = tokV 1 (encLevel l) 0 :: rest := rfl
    rw [hA, liftToksBy_keep _ _ _ _ _ _ (by decide) (by decide) (by simp), lift]
    simp [encToksU, tokV]
  | const r' ls =>
    intro m rest hm
    have hA : encToksU (.const r' ls) ++ rest = tokV 2 (encLevels ls) (r' : Int) :: rest := rfl
    rw [hA, liftToksBy_keep _ _ _ _ _ _ (by decide) (by decide) (by simp), lift]
    simp [encToksU, tokV]
  | lit t =>
    intro m rest hm
    have hA : encToksU (.lit t) ++ rest = tokV 7 "" (t : Int) :: rest := rfl
    rw [hA, liftToksBy_keep _ _ _ _ _ _ (by decide) (by decide) (by simp), lift]
    simp [encToksU, tokV]
  | app f x ihf ihx =>
    intro m rest hm
    have hA : encToksU (.app f x) ++ rest =
        tokV 3 "" 0 :: (encToksU f ++ (encToksU x ++ rest)) := by
      simp [encToksU, List.append_assoc]
    rw [hA, liftToksBy_keep _ _ _ _ _ _ (by decide) (by decide) (by simp)]
    rw [ihf m _ hm, ihx m _ hm]
    simp [encToksU, lift, List.append_assoc]
  | lam a' b' iha ihb =>
    intro m rest hm
    have hA : encToksU (.lam a' b') ++ rest =
        tokV 4 "" 0 :: (encToksU a' ++ (enterT :: (encToksU b' ++ (exitT :: rest)))) := by
      simp [encToksU, List.append_assoc]
    rw [hA, liftToksBy_keep _ _ _ _ _ _ (by decide) (by decide) (by simp)]
    rw [iha m _ hm]
    rw [show enterT = tokV 8 "" 0 from rfl, liftToksBy_enter]
    rw [ihb (m + 1) _ (by omega)]
    rw [show exitT = tokV 9 "" 0 from rfl, liftToksBy_exit]
    rw [show m + 1 - 1 = m from by omega]
    have hmd : (m + 1).toNat = m.toNat + 1 := toNat_add_one hm
    simp [encToksU, lift, List.append_assoc, hmd, enterT, exitT]
  | pi a' b' iha ihb =>
    intro m rest hm
    have hA : encToksU (.pi a' b') ++ rest =
        tokV 5 "" 0 :: (encToksU a' ++ (enterT :: (encToksU b' ++ (exitT :: rest)))) := by
      simp [encToksU, List.append_assoc]
    rw [hA, liftToksBy_keep _ _ _ _ _ _ (by decide) (by decide) (by simp)]
    rw [iha m _ hm]
    rw [show enterT = tokV 8 "" 0 from rfl, liftToksBy_enter]
    rw [ihb (m + 1) _ (by omega)]
    rw [show exitT = tokV 9 "" 0 from rfl, liftToksBy_exit]
    rw [show m + 1 - 1 = m from by omega]
    have hmd : (m + 1).toNat = m.toNat + 1 := toNat_add_one hm
    simp [encToksU, lift, List.append_assoc, hmd, enterT, exitT]
  | letE a' v' b' iha ihv ihb =>
    intro m rest hm
    have hA : encToksU (.letE a' v' b') ++ rest =
        tokV 6 "" 0 :: (encToksU a' ++ (encToksU v' ++
          (enterT :: (encToksU b' ++ (exitT :: rest))))) := by
      simp [encToksU, List.append_assoc]
    rw [hA, liftToksBy_keep _ _ _ _ _ _ (by decide) (by decide) (by simp)]
    rw [iha m _ hm, ihv m _ hm]
    rw [show enterT = tokV 8 "" 0 from rfl, liftToksBy_enter]
    rw [ihb (m + 1) _ (by omega)]
    rw [show exitT = tokV 9 "" 0 from rfl, liftToksBy_exit]
    rw [show m + 1 - 1 = m from by omega]
    have hmd : (m + 1).toNat = m.toNat + 1 := toNat_add_one hm
    simp [encToksU, lift, List.append_assoc, hmd, enterT, exitT]

/-- At the root the token-level lift is exactly `lift 0 a`. -/
theorem liftToksBy_enc_root (a : Nat) (e : Expr Nat) :
    liftToksBy (a : Int) 0 (encToksU e) = encToksU (lift 0 a e) := by
  have h := liftToksBy_enc a e 0 [] (by decide)
  simpa [liftToksBy] using h

theorem expandSkel_nil (repl : List Val) : expandSkel repl [] = [] := rfl

theorem expandSkel_tok (repl : List Val) (k : Int) (l : String) (n : Int)
    (ts : List Val) (hk : k ≠ 10) :
    expandSkel repl (tokV k l n :: ts) = tokV k l n :: expandSkel repl ts := by
  simp [expandSkel, tokKL, tokV, hk]

theorem expandSkel_sub (repl : List Val) (d : Int) (ts : List Val) :
    expandSkel repl (subT d :: ts) = liftToksBy d 0 repl ++ expandSkel repl ts := by
  simp [expandSkel, tokKL, tokV, subT]

theorem expandSkel_append (repl : List Val) :
    ∀ (a b : List Val), expandSkel repl (a ++ b) = expandSkel repl a ++ expandSkel repl b := by
  intro a; induction a with
  | nil => intro b; simp [expandSkel]
  | cons t ts ih =>
    intro b
    simp only [List.cons_append, expandSkel]
    cases hk : tokKL t with
    | none => simp [hk, ih]
    | some v =>
      obtain ⟨k, l, n⟩ := v
      simp only [hk]
      by_cases h10 : k = 10
      · simp [h10, ih, List.append_assoc]
      · simp [h10, ih]

/-- The correspondence: expanding the skeleton the program produces is the
    declarative `instantiate d (lift 0 d r)`. The `lift 0 d r` appearing here
    is exactly what `SUB(d)` splices. -/
theorem expandSkel_inst (r : Expr Nat) :
    ∀ (e : Expr Nat) (d : Nat),
    expandSkel (encToksU r) (skelOf d e) = encToksU (instantiate d (lift 0 d r) e) := by
  intro e; induction e with
  | bvar i =>
    intro d
    by_cases hid : i = d
    · subst hid
      have h1 : skelOf i (.bvar i) = [subT (i : Int)] := by simp [skelOf]
      rw [h1]
      have h2 : expandSkel (encToksU r) [subT (i : Int)] = liftToksBy (i : Int) 0 (encToksU r) := by
        rw [show [subT (i : Int)] = subT (i : Int) :: [] from rfl, expandSkel_sub, expandSkel_nil,
          List.append_nil]
      rw [h2, liftToksBy_enc_root]
      simp [instantiate]
    · have hne : ¬ (i : Int) = (d : Int) := by omega
      by_cases hlt : d < i
      · have h1 : skelOf d (.bvar i) = [tokV 0 "" ((i : Int) - 1)] := by
          simp [skelOf, hid, hlt]
        rw [h1]
        have h2 : expandSkel (encToksU r) [tokV 0 "" ((i : Int) - 1)] =
            [tokV 0 "" ((i : Int) - 1)] := by
          rw [show [tokV 0 "" ((i : Int) - 1)] = tokV 0 "" ((i : Int) - 1) :: [] from rfl,
            expandSkel_tok _ 0 "" _ [] (by decide), expandSkel_nil]
        rw [h2]
        have hsub : ((i - 1 : Nat) : Int) = (i : Int) - 1 := by omega
        simp [instantiate, hid, hlt, encToksU, tokV, hsub]
      · have h1 : skelOf d (.bvar i) = [tokV 0 "" (i : Int)] := by
          simp [skelOf, hid, hlt]
        rw [h1]
        have h2 : expandSkel (encToksU r) [tokV 0 "" (i : Int)] = [tokV 0 "" (i : Int)] := by
          rw [show [tokV 0 "" (i : Int)] = tokV 0 "" (i : Int) :: [] from rfl,
            expandSkel_tok _ 0 "" _ [] (by decide), expandSkel_nil]
        rw [h2]
        simp [instantiate, hid, hlt, encToksU, tokV]
  | sort l =>
    intro d
    have h1 : skelOf d (.sort l) = [tokV 1 (encLevel l) 0] := rfl
    rw [h1]
    have h2 : expandSkel (encToksU r) [tokV 1 (encLevel l) 0] = [tokV 1 (encLevel l) 0] := by
      rw [show [tokV 1 (encLevel l) 0] = tokV 1 (encLevel l) 0 :: [] from rfl,
        expandSkel_tok _ 1 _ 0 [] (by decide), expandSkel_nil]
    rw [h2]
    simp [instantiate, encToksU]
  | const r' ls =>
    intro d
    have h1 : skelOf d (.const r' ls) = [tokV 2 (encLevels ls) r'] := rfl
    rw [h1]
    have h2 : expandSkel (encToksU r) [tokV 2 (encLevels ls) (r' : Int)] =
        [tokV 2 (encLevels ls) (r' : Int)] := by
      rw [show [tokV 2 (encLevels ls) (r' : Int)] = tokV 2 (encLevels ls) (r' : Int) :: [] from rfl,
        expandSkel_tok _ 2 _ _ [] (by decide), expandSkel_nil]
    rw [h2]
    simp [instantiate, encToksU]
  | lit t =>
    intro d
    have h1 : skelOf d (.lit t) = [tokV 7 "" (t : Int)] := rfl
    rw [h1]
    have h2 : expandSkel (encToksU r) [tokV 7 "" (t : Int)] = [tokV 7 "" (t : Int)] := by
      rw [show [tokV 7 "" (t : Int)] = tokV 7 "" (t : Int) :: [] from rfl,
        expandSkel_tok _ 7 "" _ [] (by decide), expandSkel_nil]
    rw [h2]
    simp [instantiate, encToksU]
  | app f x ihf ihx =>
    intro d
    rw [show skelOf d (.app f x) = tokV 3 "" 0 :: (skelOf d f ++ skelOf d x) from rfl]
    rw [expandSkel_tok _ 3 "" 0 _ (by decide), expandSkel_append, ihf d, ihx d]
    simp [instantiate, encToksU]
  | lam a' b' iha ihb =>
    intro d
    rw [show skelOf d (.lam a' b') =
          tokV 4 "" 0 :: (skelOf d a' ++ enterT :: (skelOf (d + 1) b' ++ [exitT])) from by
        simp [skelOf, List.append_assoc]]
    rw [expandSkel_tok _ 4 "" 0 _ (by decide), expandSkel_append, iha d]
    rw [show enterT = tokV 8 "" 0 from rfl, expandSkel_tok _ 8 "" 0 _ (by decide)]
    rw [expandSkel_append, ihb (d + 1)]
    rw [show [exitT] = exitT :: [] from rfl, show exitT = tokV 9 "" 0 from rfl,
        expandSkel_tok _ 9 "" 0 [] (by decide), expandSkel_nil]
    rw [← lift_lift_merge 1 d 0 0 (by omega) (by omega) r]
    simp [instantiate, encToksU, List.append_assoc, enterT, exitT]
  | pi a' b' iha ihb =>
    intro d
    rw [show skelOf d (.pi a' b') =
          tokV 5 "" 0 :: (skelOf d a' ++ enterT :: (skelOf (d + 1) b' ++ [exitT])) from by
        simp [skelOf, List.append_assoc]]
    rw [expandSkel_tok _ 5 "" 0 _ (by decide), expandSkel_append, iha d]
    rw [show enterT = tokV 8 "" 0 from rfl, expandSkel_tok _ 8 "" 0 _ (by decide)]
    rw [expandSkel_append, ihb (d + 1)]
    rw [show [exitT] = exitT :: [] from rfl, show exitT = tokV 9 "" 0 from rfl,
        expandSkel_tok _ 9 "" 0 [] (by decide), expandSkel_nil]
    rw [← lift_lift_merge 1 d 0 0 (by omega) (by omega) r]
    simp [instantiate, encToksU, List.append_assoc, enterT, exitT]
  | letE a' v' b' iha ihv ihb =>
    intro d
    rw [show skelOf d (.letE a' v' b') =
          tokV 6 "" 0 :: (skelOf d a' ++ (skelOf d v' ++ enterT ::
            (skelOf (d + 1) b' ++ [exitT]))) from by
        simp [skelOf, List.append_assoc]]
    rw [expandSkel_tok _ 6 "" 0 _ (by decide), expandSkel_append, iha d, expandSkel_append, ihv d]
    rw [show enterT = tokV 8 "" 0 from rfl, expandSkel_tok _ 8 "" 0 _ (by decide)]
    rw [expandSkel_append, ihb (d + 1)]
    rw [show [exitT] = exitT :: [] from rfl, show exitT = tokV 9 "" 0 from rfl,
        expandSkel_tok _ 9 "" 0 [] (by decide), expandSkel_nil]
    rw [← lift_lift_merge 1 d 0 0 (by omega) (by omega) r]
    simp [instantiate, encToksU, List.append_assoc, enterT, exitT]

/-- `expandCompact` on the program's output yields the declarative
    substitution — the V1 ReturnPost's equality leg. -/
theorem expandCompact_out (r e : Expr Nat) (tr : List Val)
    (hr : encToks r = some tr) :
    expandCompact (outV tr (skelOf 0 e)) = some (.l (encToksU (instantiate0 r e))) := by
  show expandCompact (.r [.l tr, .l (skelOf 0 e)]) = _
  simp only [expandCompact]
  rw [← encToks_eq_encToksU hr, expandSkel_inst r e 0]
  simp [instantiate0, lift_zero]

/-! ## Scope (07 §22 "well scoped at depth") -/

/-- `WellScoped d e`: every `bvar` in `e` is below `d` — `e` fits a context
    of `d` slots. -/
def WellScoped : Nat → Expr Nat → Prop
  | d, .bvar i => i < d
  | _, .sort _ => True
  | _, .const _ _ => True
  | d, .app f x => WellScoped d f ∧ WellScoped d x
  | d, .lam a b => WellScoped d a ∧ WellScoped (d + 1) b
  | d, .pi a b => WellScoped d a ∧ WellScoped (d + 1) b
  | d, .letE a v b => WellScoped d a ∧ WellScoped d v ∧ WellScoped (d + 1) b
  | _, .lit _ => True

theorem ws_mono {e : Expr Nat} : ∀ {d d' : Nat}, WellScoped d e → d ≤ d' →
    WellScoped d' e := by
  induction e with
  | bvar i => intro d d' h hd; exact Nat.lt_of_lt_of_le h hd
  | sort l => intro _ _ _ _; trivial
  | const r ls => intro _ _ _ _; trivial
  | lit t => intro _ _ _ _; trivial
  | app f x ihf ihx =>
    intro d d' h hd
    exact ⟨ihf h.1 hd, ihx h.2 hd⟩
  | lam a b iha ihb =>
    intro d d' h hd
    exact ⟨iha h.1 hd, ihb h.2 (by omega)⟩
  | pi a b iha ihb =>
    intro d d' h hd
    exact ⟨iha h.1 hd, ihb h.2 (by omega)⟩
  | letE a v b iha ihv ihb =>
    intro d d' h hd
    exact ⟨iha h.1 hd, ihv h.2.1 hd, ihb h.2.2 (by omega)⟩

/-- Lifting by `k` widens the needed context by `k`, at any cutoff. -/
theorem ws_lift {e : Expr Nat} : ∀ {d c k : Nat}, WellScoped d e →
    WellScoped (d + k) (lift c k e) := by
  induction e with
  | bvar i =>
    intro d c k h; simp only [WellScoped] at h
    simp only [lift]; split <;> simp only [WellScoped] <;> omega
  | sort l => intro _ _ _ _; trivial
  | const r ls => intro _ _ _ _; trivial
  | lit t => intro _ _ _ _; trivial
  | app f x ihf ihx =>
    intro d c k h
    simp only [WellScoped] at h
    simp only [lift, WellScoped]
    exact ⟨ihf h.1, ihx h.2⟩
  | lam a b iha ihb =>
    intro d c k h
    simp only [WellScoped] at h
    simp only [lift, WellScoped]
    refine ⟨iha h.1, ?_⟩
    have hb := ihb (c := c + 1) (k := k) h.2
    rwa [show d + 1 + k = d + k + 1 from by omega] at hb
  | pi a b iha ihb =>
    intro d c k h
    simp only [WellScoped] at h
    simp only [lift, WellScoped]
    refine ⟨iha h.1, ?_⟩
    have hb := ihb (c := c + 1) (k := k) h.2
    rwa [show d + 1 + k = d + k + 1 from by omega] at hb
  | letE a v b iha ihv ihb =>
    intro d c k h
    simp only [WellScoped] at h
    simp only [lift, WellScoped]
    refine ⟨iha h.1, ihv h.2.1, ?_⟩
    have hb := ihb (c := c + 1) (k := k) h.2.2
    rwa [show d + 1 + k = d + k + 1 from by omega] at hb

/-- Scope preservation for `instantiate`: `e` fitting `j + d + 1` slots —
    `j` inner binders, the `j`-th hole, `d` outer — and the (already
    `j`-lifted) replacement `s` fitting `j + d` slots gives `j + d` slots.
    At the entry `j = 0` this is `ws (D+1) e → ws D s → ws D (inst 0 s e)`. -/
theorem ws_instantiate {e : Expr Nat} : ∀ {j d : Nat} {s : Expr Nat},
    WellScoped (j + d + 1) e → WellScoped (j + d) s →
    WellScoped (j + d) (instantiate j s e) := by
  induction e with
  | bvar i =>
    intro j d s hi hs
    simp only [WellScoped] at hi
    simp only [instantiate]
    split
    · exact hs
    · split <;> simp only [WellScoped] <;> omega
  | sort l => intro _ _ _ _ _; trivial
  | const r ls => intro _ _ _ _ _; trivial
  | lit t => intro _ _ _ _ _; trivial
  | app f x ihf ihx =>
    intro j d s h hs
    simp only [WellScoped] at h
    simp only [instantiate, WellScoped]
    exact ⟨ihf h.1 hs, ihx h.2 hs⟩
  | lam a b iha ihb =>
    intro j d s h hs
    simp only [WellScoped] at h
    simp only [instantiate, WellScoped]
    refine ⟨iha h.1 hs, ?_⟩
    have hb : WellScoped (j + 1 + d + 1) b := by
      rw [show j + 1 + d + 1 = j + d + 1 + 1 from by omega]; exact h.2
    have hs' : WellScoped (j + 1 + d) (lift 0 1 s) := by
      have := ws_lift hs (c := 0) (k := 1)
      rwa [show j + d + 1 = j + 1 + d from by omega] at this
    have res := ihb (j := j + 1) (d := d) hb hs'
    rwa [show j + 1 + d = j + d + 1 from by omega] at res
  | pi a b iha ihb =>
    intro j d s h hs
    simp only [WellScoped] at h
    simp only [instantiate, WellScoped]
    refine ⟨iha h.1 hs, ?_⟩
    have hb : WellScoped (j + 1 + d + 1) b := by
      rw [show j + 1 + d + 1 = j + d + 1 + 1 from by omega]; exact h.2
    have hs' : WellScoped (j + 1 + d) (lift 0 1 s) := by
      have := ws_lift hs (c := 0) (k := 1)
      rwa [show j + d + 1 = j + 1 + d from by omega] at this
    have res := ihb (j := j + 1) (d := d) hb hs'
    rwa [show j + 1 + d = j + d + 1 from by omega] at res
  | letE a v b iha ihv ihb =>
    intro j d s h hs
    simp only [WellScoped] at h
    simp only [instantiate, WellScoped]
    refine ⟨iha h.1 hs, ihv h.2.1 hs, ?_⟩
    have hb : WellScoped (j + 1 + d + 1) b := by
      rw [show j + 1 + d + 1 = j + d + 1 + 1 from by omega]; exact h.2.2
    have hs' : WellScoped (j + 1 + d) (lift 0 1 s) := by
      have := ws_lift hs (c := 0) (k := 1)
      rwa [show j + d + 1 = j + 1 + d from by omega] at this
    have res := ihb (j := j + 1) (d := d) hb hs'
    rwa [show j + 1 + d = j + d + 1 from by omega] at res

/-- 07 §22's scope leg at the entry: substitution at index 0 sends
    `D + 1`–scoped and `D`–scoped to `D`–scoped. -/
theorem ws_instantiate0 {e r : Expr Nat} {D : Nat}
    (he : WellScoped (D + 1) e) (hr : WellScoped D r) :
    WellScoped D (instantiate0 r e) := by
  have := ws_instantiate (j := 0) (d := D) (s := r) (e := e)
    (by simpa using he) (by simpa using hr)
  simpa [instantiate0] using this

/-! ## The V1 contract statement -/

/-- `PreV1` (E-07CompactInstantiate, reworked): `decodeInputV1` — the
    contract's syntactic front door — decodes the input to a depth `D` and
    two terms `e, r` (which pins the input to the canonical record
    `inputV D (encToksU e) (encToksU r)` and puts `e, r` in the
    representation domain — `decodeInputV1_sound`); `e` is well scoped at
    `D + 1`, `r` at `D`; and the total token count `N_e := (encToksU e).length`
    (ENTER/EXIT markers included) is strictly below `M = 2^63 − 1`
    (`i64Max`). `N_e < M` is a premise, not implied by decode success, and
    it is a token-count bound only — it does not make `81 · N_e + 30` fit
    i64 (see `costBoundI64`). The depth check `D + 1` is arithmetic on
    `Nat`, not executed `i64` addition. -/
def PreV1 (input : Val) : Prop :=
  ∃ (D : Nat) (e r : Expr Nat),
    decodeInputV1 input = some (D, e, r) ∧
    WellScoped (D + 1) e ∧ WellScoped D r ∧ ((encToksU e).length : Int) < i64Max

/-- V1 total correctness (CT-023's instantiate row for this contract):
    under `PreV1` the entry runs to the compact output `{repl = tr,
    skel = skelOf 0 e}` within `81 · N_e + 30` transitions; the compact
    output expands — through `expandCompact`, which reads only `repl` and
    `skel` — to the encoding of `instantiate0 r e`, which is well scoped at
    `D`. `ResidueRow = ∅` is discharged at `#guard` above (the derived entry
    row is empty); `Evals` is the no-residue run. -/
theorem instV1_total (input : Val) (h : PreV1 input) :
    ∃ (D : Int) (e r : Expr Nat) (te tr : List Val) (n : Nat),
      input = inputV D te tr ∧ n ≤ 81 * te.length + 30 ∧
      Evals instProg [input, unitRaw] MAIN (.p (outV tr (skelOf 0 e)) unitRaw) n ∧
      expandCompact (outV tr (skelOf 0 e)) =
        some (.l (encToksU (instantiate0 r e))) ∧
      WellScoped D.toNat (instantiate0 r e) := by
  obtain ⟨D, e, r, hdec, hwe, hwr, hcap⟩ := h
  obtain ⟨hinput, _hDM, he, hr⟩ := decodeInputV1_sound hdec
  subst hinput
  obtain ⟨n, hn, hev⟩ := evals_main (D : Int) e (encToksU e) (encToksU r) he hcap
  exact ⟨(D : Int), e, r, encToksU e, encToksU r, n, rfl, hn, hev,
    expandCompact_out r e (encToksU r) hr, ws_instantiate0 hwe hwr⟩

/-! ## Named contract invariants (E-07 rework)

The seven named facts the reworked contract needs beyond `instV1_total`:
canonical streams have `markerBal` balance `0`, never dip below `0`, and
reach depth `≥ 1` at every EXIT — so the fold body's `d` counter cannot go
negative and the `.handle OV` residue is not entered for the depth step;
bvar tokens in a canonical stream carry checked `repN` payloads; the
`signed_overflow` residue is eliminated by the derived run itself; the
cost claim is `Nat`-valued (`N_e < M` alone does not fit `81 · N_e + 30`
into i64); and the wire layer's `1024` list bound is a theorem of
`ScmWire`'s decode, not an axiom about `decodeInputV1`. -/

/-- The per-token contribution to the running binder depth the fold body
    maintains: `+1` on ENTER (`k = 8`), `−1` on EXIT (`k = 9`), `0` on
    every other token. -/
def markerStep (t : Val) : Int :=
  match tokKL t with
  | some (k, _, _) => if k = 8 then 1 else if k = 9 then -1 else 0
  | none => 0

/-- The running binder depth after a token list — the accumulator's `d`
    field is exactly this value along a canonical stream. -/
def markerBal : List Val → Int
  | [] => 0
  | t :: ts => markerStep t + markerBal ts

theorem markerStep_tok (k : Int) (l : String) (n : Int) :
    markerStep (tokV k l n) = (if k = 8 then 1 else if k = 9 then -1 else 0 : Int) := rfl

theorem markerBal_cons (t : Val) (ts : List Val) :
    markerBal (t :: ts) = markerStep t + markerBal ts := rfl

theorem markerBal_append (xs ys : List Val) :
    markerBal (xs ++ ys) = markerBal xs + markerBal ys := by
  induction xs with
  | nil => simp [markerBal]
  | cons x xs ih => simp [markerBal, ih]; omega

/-- `s` either ends inside `a` or extends past it — `s ++ t = a ++ b`
    decomposed. -/
theorem prefix_append_split {s t a b : List Val} (h : s ++ t = a ++ b) :
    (∃ u, a = s ++ u ∧ t = u ++ b) ∨ (∃ u, s = a ++ u ∧ b = u ++ t) :=
  List.append_eq_append_iff.mp h

/-- A single-element append forces its split. -/
theorem append_singleton_inv {xs ys : List Val} {y z : Val}
    (h : xs ++ y :: ys = [z]) : xs = [] ∧ y = z ∧ ys = [] := by
  cases xs with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at h
    exact ⟨rfl, h.1, h.2⟩
  | cons x xs' =>
    simp only [List.cons_append, List.cons.injEq] at h
    have hnil : xs' ++ y :: ys = [] := h.2
    exact absurd hnil (by simp)

/-- `enterT` and `exitT` are distinct tokens. -/
theorem enter_ne_exit : enterT ≠ exitT := by
  intro h
  have h' : tokV 8 "" 0 = tokV 9 "" 0 := h
  simp only [tokV, Val.r.injEq, List.cons.injEq, Val.i.injEq, Val.s.injEq] at h'
  omega

/-- A token whose kind is not `9` is not `exitT`. -/
theorem tokV_ne_exit {k : Int} (hk : k ≠ 9) (l : String) (n : Int) :
    tokV k l n ≠ exitT := by
  intro h
  have h' : tokV k l n = tokV 9 "" 0 := h
  simp only [tokV, Val.r.injEq, List.cons.injEq, Val.i.injEq, Val.s.injEq] at h'
  omega

/-- The marker invariant a canonical token stream satisfies: total balance
    `0`, every prefix non-negative (the running depth never dips below
    `0`), and depth `≥ 1` at every EXIT position (each EXIT closes a live
    binder — the fold body's `d` never underflows). -/
def markerInv (ts : List Val) : Prop :=
  markerBal ts = 0 ∧
  (∀ s t, s ++ t = ts → 0 ≤ markerBal s) ∧
  (∀ s t, s ++ exitT :: t = ts → 1 ≤ markerBal s)

theorem markerInv_single (k : Int) (hk8 : k ≠ 8) (hk9 : k ≠ 9) (l : String) (n : Int) :
    markerInv [tokV k l n] := by
  have hstep : markerStep (tokV k l n) = 0 := by
    rw [markerStep_tok, if_neg hk8, if_neg hk9]
  refine ⟨by simp [markerBal, hstep], ?_, ?_⟩
  · intro s t h
    cases s with
    | nil => simp [markerBal]
    | cons x xs =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hx, hnil⟩ := h
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil.mp hnil
      subst hx
      simp [markerBal, hstep]
  · intro s t h
    cases s with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      exact absurd h.1.symm (tokV_ne_exit hk9 l n)
    | cons x xs =>
      simp only [List.cons_append, List.cons.injEq] at h
      exact absurd h.2 (by simp)

theorem markerInv_cons {t : Val} {ts : List Val}
    (hstep : markerStep t = 0) (hne : t ≠ exitT) (h : markerInv ts) : markerInv (t :: ts) := by
  obtain ⟨h0, hp, hx⟩ := h
  refine ⟨by simp [markerBal, hstep, h0], ?_, ?_⟩
  · intro s t' hst
    have h' := List.cons_eq_append_iff.mp hst.symm
    rcases h' with ⟨hs, htt⟩ | ⟨s', hs, hstt⟩
    · subst hs; simp [markerBal]
    · subst hs
      rw [markerBal_cons, hstep]
      have := hp s' t' hstt.symm
      omega
  · intro s t' hst
    have h' := List.cons_eq_append_iff.mp hst.symm
    rcases h' with ⟨hs, htt⟩ | ⟨s', hs, hstt⟩
    · subst hs
      exact absurd (List.cons.inj htt).1.symm hne
    · subst hs
      rw [markerBal_cons, hstep]
      have := hx s' t' hstt.symm
      omega

theorem markerInv_append {a b : List Val} (ha : markerInv a) (hb : markerInv b) :
    markerInv (a ++ b) := by
  obtain ⟨ha0, hap, hax⟩ := ha
  obtain ⟨hb0, hbp, hbx⟩ := hb
  refine ⟨by rw [markerBal_append, ha0, hb0]; omega, ?_, ?_⟩
  · intro s t h
    rcases prefix_append_split h with ⟨u, hsu, hut⟩ | ⟨u, hsu, hub⟩
    · exact hap s u hsu.symm
    · subst hsu
      rw [markerBal_append, ha0]
      have := hbp u t hub.symm
      omega
  · intro s t h
    rcases prefix_append_split (s := s) (t := exitT :: t) (a := a) (b := b) h
      with ⟨u, hsu, htu⟩ | ⟨u, hsu, hub⟩
    · -- `a = s ++ u` and `exitT :: t = u ++ b`: the exit sits inside `a`
      -- unless `u` is empty — but then `b` would itself start with EXIT,
      -- which `hb` forbids.
      have h' := List.cons_eq_append_iff.mp htu
      rcases h' with ⟨hu, hbt⟩ | ⟨w, hu, hwt⟩
      · subst hu
        have hb0' : (1 : Int) ≤ 0 := hbx [] t hbt.symm
        exact absurd hb0' (by decide)
      · subst hu
        exact hax s w hsu.symm
    · -- `s = a ++ u` and `b = u ++ exitT :: t`: the exit sits inside `b`.
      subst hsu
      rw [markerBal_append, ha0]
      have := hbx u t hub.symm
      omega

/-- `a ++ ENTER :: (b ++ [EXIT])` — the canonical binder tail — preserves
    the marker invariant. -/
theorem markerInv_binder {a b : List Val} (ha : markerInv a) (hb : markerInv b) :
    markerInv (a ++ enterT :: (b ++ [exitT])) := by
  obtain ⟨ha0, hap, hax⟩ := ha
  obtain ⟨hb0, hbp, hbx⟩ := hb
  have hstepE : markerStep enterT = 1 := by decide
  have hstepX : markerStep exitT = -1 := by decide
  have hbX : markerBal [exitT] = -1 := by decide
  have hbe : markerBal (enterT :: (b ++ [exitT])) = 0 := by
    rw [markerBal_cons, hstepE, markerBal_append, hb0, hbX]; omega
  refine ⟨by rw [markerBal_append, ha0, hbe]; omega, ?_, ?_⟩
  · intro s t h
    rcases prefix_append_split h with ⟨u, hsu, hut⟩ | ⟨u, hsu, hub⟩
    · exact hap s u hsu.symm
    · -- `s = a ++ u`, `enterT :: (b ++ [exitT]) = u ++ t`
      subst hsu
      have h' := List.cons_eq_append_iff.mp hub
      rcases h' with ⟨hu, ht⟩ | ⟨w, hu, hwt⟩
      · subst hu
        rw [markerBal_append, ha0]
        decide
      · subst hu
        rw [markerBal_append, markerBal_cons, hstepE, ha0]
        -- `w ++ t = b ++ [exitT]` (hwt is `b ++ [exitT] = w ++ t`)
        rcases prefix_append_split hwt.symm with ⟨v, hwv, hvt⟩ | ⟨v, hwv, hvb⟩
        · -- `b = w ++ v`: `w` is a prefix of `b`
          have := hbp w v hwv.symm
          omega
        · -- `w = b ++ v`, `[exitT] = v ++ t` → `v = []` or `v = [exitT]`
          have hv : v = [] ∨ v = [exitT] := by
            rcases prefix_append_split (s := v) (t := t) (a := [exitT]) (b := [])
              (by simpa using hvb.symm) with ⟨w2, hw2, ht2⟩ | ⟨w2, hw2, ht2⟩
            · -- `[exitT] = v ++ w2`
              rcases List.cons_eq_append_iff.mp hw2 with ⟨hv1, -⟩ | ⟨v1, hv1, hw2'⟩
              · exact Or.inl hv1
              · -- `v = exitT :: v1`, `[] = v1 ++ w2` → `v1 = []`
                subst hv1
                obtain ⟨rfl, -⟩ := List.append_eq_nil.mp hw2'.symm
                exact Or.inr rfl
            · -- `v = [exitT] ++ w2`, `[] = w2 ++ t` → `w2 = []`
              obtain ⟨rfl, -⟩ := List.append_eq_nil.mp ht2.symm
              exact Or.inr (by simpa using hw2)
          rcases hv with rfl | rfl
          · have hw : w = b := by simpa using hwv
            subst hw
            rw [hb0]
            decide
          · subst hwv
            rw [markerBal_append, hb0, hbX]
            decide
  · intro s t h
    rcases prefix_append_split (s := s) (t := exitT :: t) (a := a)
      (b := enterT :: (b ++ [exitT])) h with ⟨u, hsu, htu⟩ | ⟨u, hsu, hub⟩
    · -- `a = s ++ u`, `exitT :: t = u ++ enterT :: (b ++ [exitT])`
      have h' := List.cons_eq_append_iff.mp htu
      rcases h' with ⟨hu, hbt⟩ | ⟨w, hu, hwt⟩
      · -- `u = []` forces `enterT :: … = exitT :: t`
        subst hu
        exact absurd (List.cons.inj hbt).1 enter_ne_exit
      · subst hu
        exact hax s w hsu.symm
    · -- `s = a ++ u`, `enterT :: (b ++ [exitT]) = u ++ exitT :: t`
      subst hsu
      have h' := List.cons_eq_append_iff.mp hub
      rcases h' with ⟨hu, hbt⟩ | ⟨w, hu, hwt⟩
      · -- `u = []` forces `exitT :: t = enterT :: …`
        subst hu
        have he : exitT = enterT := (List.cons.inj hbt).1
        exact absurd he.symm enter_ne_exit
      · -- `u = enterT :: w`, `b ++ [exitT] = w ++ exitT :: t`
        subst hu
        rw [markerBal_append, markerBal_cons, hstepE, ha0]
        rcases prefix_append_split (s := w) (t := exitT :: t) (a := b) (b := [exitT])
          hwt.symm with ⟨v, hwv, hvt⟩ | ⟨v, hwv, hvb⟩
        · -- `b = w ++ v`, `exitT :: t = v ++ [exitT]`
          have h' := List.cons_eq_append_iff.mp hvt
          rcases h' with ⟨hv, ht⟩ | ⟨v1, hv, htv1⟩
          · -- `v = []`: `b = w` — this is the final EXIT
            subst hv
            have hbw : w = b := by simpa using hwv.symm
            subst hbw
            rw [hb0]
            omega
          · -- `v = exitT :: v1`: the exit sits inside `b`
            subst hv
            have := hbx w v1 hwv.symm
            omega
        · -- `w = b ++ v`, `[exitT] = v ++ exitT :: t` → `v = []`, `t = []`
          obtain ⟨rfl, -, rfl⟩ := append_singleton_inv hvb.symm
          have hw : w = b := by simpa using hwv
          subst hw
          rw [hb0]
          decide

/-- Every canonical encoding satisfies the marker invariant — the
    contract's marker-balance, no-negative-prefix, and EXIT-safety legs. -/
theorem encToksU_markerInv : ∀ e : Expr Nat, markerInv (encToksU e) := by
  intro e
  induction e with
  | bvar i =>
    exact markerInv_single 0 (by decide) (by decide) "" (i : Int)
  | sort l =>
    exact markerInv_single 1 (by decide) (by decide) (encLevel l) 0
  | const r ls =>
    exact markerInv_single 2 (by decide) (by decide) (encLevels ls) (r : Int)
  | lit t =>
    exact markerInv_single 7 (by decide) (by decide) "" (t : Int)
  | app f x ihf ihx =>
    show markerInv ([tokV 3 "" 0] ++ encToksU f ++ encToksU x)
    have hnorm : [tokV 3 "" 0] ++ encToksU f ++ encToksU x =
        tokV 3 "" 0 :: (encToksU f ++ encToksU x) := by
      simp [List.append_assoc]
    rw [hnorm]
    exact markerInv_cons (by decide) (tokV_ne_exit (by decide) "" 0)
      (markerInv_append ihf ihx)
  | lam a b iha ihb =>
    show markerInv ([tokV 4 "" 0] ++ encToksU a ++ [enterT] ++ encToksU b ++ [exitT])
    have hnorm : [tokV 4 "" 0] ++ encToksU a ++ [enterT] ++ encToksU b ++ [exitT] =
        tokV 4 "" 0 :: (encToksU a ++ enterT :: (encToksU b ++ [exitT])) := by
      simp [List.append_assoc]
    rw [hnorm]
    exact markerInv_cons (by decide) (tokV_ne_exit (by decide) "" 0)
      (markerInv_binder iha ihb)
  | pi a b iha ihb =>
    show markerInv ([tokV 5 "" 0] ++ encToksU a ++ [enterT] ++ encToksU b ++ [exitT])
    have hnorm : [tokV 5 "" 0] ++ encToksU a ++ [enterT] ++ encToksU b ++ [exitT] =
        tokV 5 "" 0 :: (encToksU a ++ enterT :: (encToksU b ++ [exitT])) := by
      simp [List.append_assoc]
    rw [hnorm]
    exact markerInv_cons (by decide) (tokV_ne_exit (by decide) "" 0)
      (markerInv_binder iha ihb)
  | letE a v b iha ihv ihb =>
    show markerInv ([tokV 6 "" 0] ++ encToksU a ++ encToksU v ++ [enterT]
        ++ encToksU b ++ [exitT])
    have hnorm : [tokV 6 "" 0] ++ encToksU a ++ encToksU v ++ [enterT]
        ++ encToksU b ++ [exitT] =
        tokV 6 "" 0 :: (encToksU a ++ (encToksU v ++ enterT :: (encToksU b ++ [exitT]))) := by
      simp [List.append_assoc]
    rw [hnorm]
    exact markerInv_cons (by decide) (tokV_ne_exit (by decide) "" 0)
      (markerInv_append iha (markerInv_binder ihv ihb))

/-- Marker balance: a successfully decoded stream has balance `0` — every
    ENTER is closed. -/
theorem decToks_balanced {ts : List Val} {e : Expr Nat} (h : decToks ts = some e) :
    markerBal ts = 0 := by
  obtain ⟨rfl, -⟩ := decToks_sound h
  exact (encToksU_markerInv e).1

/-- Binder-depth non-negativity: no prefix of a decoded stream dips below
    `0` — the fold counter cannot go negative. -/
theorem decToks_prefix_nonneg {ts s t : List Val} {e : Expr Nat}
    (h : decToks ts = some e) (hs : s ++ t = ts) : 0 ≤ markerBal s := by
  obtain ⟨rfl, -⟩ := decToks_sound h
  exact (encToksU_markerInv e).2.1 s t hs

/-- EXIT safety: every EXIT position in a decoded stream has depth `≥ 1`,
    so the fold body's `d - 1` step never underflows. -/
theorem decToks_exit_bound {ts s t : List Val} {e : Expr Nat}
    (h : decToks ts = some e) (hs : s ++ exitT :: t = ts) : 1 ≤ markerBal s := by
  obtain ⟨rfl, -⟩ := decToks_sound h
  exact (encToksU_markerInv e).2.2 s t hs

/-- Bvar bound: a `bvar` token in a canonical stream is the image of a
    `Nat` index — its payload is the checked i64 `repN` of some `.bvar`
    index of the decoded term. -/
theorem encToksU_bvar_bound {e : Expr Nat} {l : String} {n : Int} (hr : repOk e)
    (hm : tokV 0 l n ∈ encToksU e) : l = "" ∧ ∃ i : Nat, n = (i : Int) ∧ repN i := by
  induction e with
  | bvar i =>
    simp only [encToksU, List.mem_singleton] at hm
    have h' : tokV 0 l n = tokV 0 "" (i : Int) := hm
    simp only [tokV, Val.r.injEq, List.cons.injEq, Val.i.injEq, Val.s.injEq] at h'
    obtain ⟨-, hl, hn⟩ := h'
    unfold repOk encToks at hr
    split at hr
    · rename_i hrep
      exact ⟨hl, i, hn.1, hrep⟩
    · simp at hr
  | sort lv =>
    simp only [encToksU, List.mem_singleton] at hm
    have h' : tokV 0 l n = tokV 1 (encLevel lv) 0 := hm
    simp [tokV] at h'
  | const rf ls =>
    simp only [encToksU, List.mem_singleton] at hm
    have h' : tokV 0 l n = tokV 2 (encLevels ls) (rf : Int) := hm
    simp [tokV] at h'
  | lit t =>
    simp only [encToksU, List.mem_singleton] at hm
    have h' : tokV 0 l n = tokV 7 "" (t : Int) := hm
    simp [tokV] at h'
  | app f x ihf ihx =>
    obtain ⟨hf, hx⟩ := repOk_app_inv hr
    have hm' : tokV 0 l n ∈ tokV 3 "" 0 :: encToksU f ++ encToksU x := by
      simpa only [encToksU, List.singleton_append] using hm
    rcases List.mem_cons.mp hm' with htok | hm1
    · simp [tokV] at htok
    rcases List.mem_append.mp hm1 with hf' | hx'
    · exact ihf hf hf'
    · exact ihx hx hx'
  | lam a b iha ihb =>
    obtain ⟨ha, hb⟩ := repOk_lam_inv hr
    have hm' : tokV 0 l n ∈
        tokV 4 "" 0 :: (encToksU a ++ enterT :: (encToksU b ++ [exitT])) := by
      have hnorm : [tokV 4 "" 0] ++ encToksU a ++ [enterT] ++ encToksU b ++ [exitT] =
          tokV 4 "" 0 :: (encToksU a ++ enterT :: (encToksU b ++ [exitT])) := by
        simp [List.append_assoc]
      rw [← hnorm]
      exact hm
    rcases List.mem_cons.mp hm' with htok | hm1
    · simp [tokV] at htok
    rcases List.mem_append.mp hm1 with ha' | hm2
    · exact iha ha ha'
    rcases List.mem_cons.mp hm2 with htok2 | hm3
    · simp [tokV, enterT] at htok2
    rcases List.mem_append.mp hm3 with hb' | hm4
    · exact ihb hb hb'
    obtain htok3 := List.mem_singleton.mp hm4
    simp [tokV, exitT] at htok3
  | pi a b iha ihb =>
    obtain ⟨ha, hb⟩ := repOk_pi_inv hr
    have hm' : tokV 0 l n ∈
        tokV 5 "" 0 :: (encToksU a ++ enterT :: (encToksU b ++ [exitT])) := by
      have hnorm : [tokV 5 "" 0] ++ encToksU a ++ [enterT] ++ encToksU b ++ [exitT] =
          tokV 5 "" 0 :: (encToksU a ++ enterT :: (encToksU b ++ [exitT])) := by
        simp [List.append_assoc]
      rw [← hnorm]
      exact hm
    rcases List.mem_cons.mp hm' with htok | hm1
    · simp [tokV] at htok
    rcases List.mem_append.mp hm1 with ha' | hm2
    · exact iha ha ha'
    rcases List.mem_cons.mp hm2 with htok2 | hm3
    · simp [tokV, enterT] at htok2
    rcases List.mem_append.mp hm3 with hb' | hm4
    · exact ihb hb hb'
    obtain htok3 := List.mem_singleton.mp hm4
    simp [tokV, exitT] at htok3
  | letE a v b iha ihv ihb =>
    obtain ⟨ha, hv, hb⟩ := repOk_letE_inv hr
    have hm' : tokV 0 l n ∈
        tokV 6 "" 0 :: (encToksU a ++ (encToksU v ++ enterT :: (encToksU b ++ [exitT]))) := by
      have hnorm : [tokV 6 "" 0] ++ encToksU a ++ encToksU v ++ [enterT]
          ++ encToksU b ++ [exitT] =
          tokV 6 "" 0 :: (encToksU a ++ (encToksU v ++ enterT :: (encToksU b ++ [exitT]))) := by
        simp [List.append_assoc]
      rw [← hnorm]
      exact hm
    rcases List.mem_cons.mp hm' with htok | hm1
    · simp [tokV] at htok
    rcases List.mem_append.mp hm1 with ha' | hm2
    · exact iha ha ha'
    rcases List.mem_append.mp hm2 with hv' | hm3
    · exact ihv hv hv'
    rcases List.mem_cons.mp hm3 with htok2 | hm4
    · simp [tokV, enterT] at htok2
    rcases List.mem_append.mp hm4 with hb' | hm5
    · exact ihb hb hb'
    obtain htok3 := List.mem_singleton.mp hm5
    simp [tokV, exitT] at htok3

/-- `signed_overflow` is a declared residue of `instProg` — the `handle
    OV` branches in `enterB`/`exitB`/`bvarTok` — not an assumption: on a
    `PreV1` input the derived entry run reaches
    `retC (.p (outV …) unitRaw)`, and `Raw.step` being a function, the same
    run cannot also land in a `raised` config. The residue's non-firing is
    the witnessed derivation, whose i64 bounds (`d ± 1`, `n − 1`) are
    discharged inside `evals_main` by `N_e < M` and the marker invariant;
    the derived entry row is additionally proved empty at the `#guard`
    above. -/
theorem instV1_signed_overflow_free (input : Val) (h : PreV1 input) :
    ∃ (D : Int) (e _r : Expr Nat) (te tr : List Val) (n : Nat),
      input = inputV D te tr ∧
      Evals instProg [input, unitRaw] MAIN (.p (outV tr (skelOf 0 e)) unitRaw) n := by
  obtain ⟨D, e, r, te, tr, n, hinput, -, hev, -, -⟩ := instV1_total input h
  exact ⟨D, e, r, te, tr, n, hinput, hev⟩

/-- The transition bound is a `Nat` claim: `81 · N_e + 30` exceeds
    `i64Max` well below `M` (`N_e = 2^59` already does), so `N_e < M` does
    NOT discharge an i64-typed cost claim. A consumer that needs the cost
    bound as an i64 takes `costBoundI64` as an additional precondition —
    `instV1_total` makes no such claim and does not need one. -/
def costBoundI64 (Ne : Nat) : Prop := ((81 * Ne + 30 : Nat) : Int) ≤ i64Max

theorem tokenBound_lt_not_cost_i64 :
    ∃ N : Nat, (N : Int) < i64Max ∧ ¬ costBoundI64 N :=
  ⟨576460752303423488, by decide, by unfold costBoundI64; decide⟩  -- `2^59`

/-- A successful `Except` bind exposes its intermediate value — the
    `do`-desugared decode chains decompose stepwise. -/
theorem except_bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β}
    {r : β} (h : Bind.bind x f = .ok r) : ∃ v, x = .ok v ∧ f v = .ok r := by
  cases x with
  | error e => exact Except.noConfusion h
  | ok v => exact ⟨v, rfl, h⟩

/-- The wire layer's list bound (E-07's wire assumption): a counted list
    the canonical wire decoder yields — `ScmWire.decElems`, the carrier's
    bounded `fix` — has at most `iters` elements. This is a theorem of the
    wire decode invariant (one element per step), not an axiom and not a
    property of `decodeInputV1` — the Lean decoder accepts any length;
    inputs that arrive over the wire carry `te.length, tr.length ≤ 1024`. -/
theorem wire_decElems_length_le {cs : Array Char} {kind : Nat} {fuel : Int} :
    ∀ {g : Nat} {left : Int} {iters p q : Nat} {xs : List Rcic.Scm.Wire.Item},
      Rcic.Scm.Wire.decElems cs g kind fuel left p iters = .ok (xs, q) →
        xs.length ≤ iters := by
  intro g
  induction g with
  | zero =>
    intro left iters p q xs h
    simp [Rcic.Scm.Wire.decElems] at h
  | succ g ih =>
    intro left iters p q xs h
    unfold Rcic.Scm.Wire.decElems at h
    split at h
    · -- `left ≤ 0`: the loop ends with `[]`
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp
    · split at h
      · -- `iters = 0`: `bound` refusal
        exact Except.noConfusion h
      · rename_i it
        obtain ⟨⟨x, q1⟩, hdec, hf⟩ := except_bind_eq_ok h
        obtain ⟨⟨xs', q'⟩, hrest, hf2⟩ := except_bind_eq_ok hf
        have hf2' : Except.ok (x :: xs', q') = Except.ok (xs, q) := hf2
        simp only [Except.ok.injEq, Prod.mk.injEq] at hf2'
        obtain ⟨rfl, -⟩ := hf2'
        have := ih hrest
        simp only [List.length_cons]
        omega

/-- The wire's `1024`: a list decoded by `ScmWire.decList` — the carrier's
    `scm_wire_dec_list` `fix` — has at most 1024 elements. -/
theorem wire_decList_length_le_1024 {cs : Array Char} {g kind p q : Nat}
    {fuel : Int} {xs : List Rcic.Scm.Wire.Item}
    (h : Rcic.Scm.Wire.decList cs g kind fuel p = .ok (.list xs, q)) :
    xs.length ≤ 1024 := by
  cases g with
  | zero =>
    simp only [Rcic.Scm.Wire.decList] at h
    exact Except.noConfusion h
  | succ g =>
    simp only [Rcic.Scm.Wire.decList] at h
    obtain ⟨⟨n, q1⟩, hd, hf⟩ := except_bind_eq_ok h
    obtain ⟨⟨xs', q'⟩, he, hf2⟩ := except_bind_eq_ok hf
    have hf2' : Except.ok (Rcic.Scm.Wire.Item.list xs', q') =
      Except.ok (.list xs, q) := hf2
    simp only [Except.ok.injEq, Prod.mk.injEq, Rcic.Scm.Wire.Item.list.injEq] at hf2'
    obtain ⟨rfl, -⟩ := hf2'
    exact wire_decElems_length_le he

end Rcic.Scm.Inst

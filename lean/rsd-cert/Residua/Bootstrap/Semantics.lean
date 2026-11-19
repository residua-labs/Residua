import Residua.Bootstrap.IR
import Residua.Bootstrap.EvalBootSeparators
import Residua.SHA256

/-!
# Bootstrap 1a — evalBoot (ADR r4.3/r4.4/r4.5, 整数定律 A, r5-thin pins)

One interpreter core, parameterized by the four mutable arithmetic arms
(`ArithLaws`). `evalBoot = core lawsA`, `evalBoot' = core lawsMutant` —
the discharge instance routes every pin THROUGH BootExpr evaluation
(RED: re-exporting law*/mutant* under new names is not the interpreter).

Laws (A, WP0.5 census `choice_on_mod = A`):
  floor-mod / exact-div / overflow-refuse / comparisons return bool.
Law violations and fuel exhaustion = `none`; first-class residue values
(ok/res) are DISTINCT from none (r4.4). fuel = Call-only (N6c): checked
nonzero at every node, decremented ONLY at `call`.

ContentHash : Bytes → Bytes = sha256(raw bytes) — the SAME function as
the bundle load-bearing q (N3). 32-byte raw digest; hex is display-only
(r5-thin). Pinned below against the RED's `sha256EmptyRaw`.

0 sorry, 0 axiom. closure_claim = 0.
-/

namespace Residua.Bootstrap.Semantics

open Residua.Bootstrap.IR
open Residua.Bootstrap.EvalBootSeparators (i64Min i64Max inI64Range
  lawAdd lawMod lawDiv mutantAdd mutantMod mutantDiv sha256EmptyRaw)

/-- Untyped runtime values (evalLF style; expr side is intrinsically typed). -/
inductive Val where
  | int   (n : Int)
  | bool  (b : Bool)
  | str   (s : String)
  | bytes (bs : List UInt8)
  | list  (vs : List Val)
  | pair  (a b : Val)
  | inj   (i : Nat) (v : Val)
  | recV  (fs : List (String × Val))
  | someV (v : Val)
  | noneV
  | ok    (v : Val)
  | res   (code : Int)

abbrev EnvV := List Val

mutual
/-- Structural value equality (nested inductive: hand-written, derive fails). -/
def valEq : Val → Val → Bool
  | .int a, .int b => a == b
  | .bool a, .bool b => a == b
  | .str a, .str b => a == b
  | .bytes a, .bytes b => a == b
  | .list xs, .list ys => valEqList xs ys
  | .pair a b, .pair c d => valEq a c && valEq b d
  | .inj i v, .inj j w => i == j && valEq v w
  | .recV fs, .recV gs => valEqFields fs gs
  | .someV a, .someV b => valEq a b
  | .noneV, .noneV => true
  | .ok a, .ok b => valEq a b
  | .res a, .res b => a == b
  | _, _ => false
def valEqList : List Val → List Val → Bool
  | [], [] => true
  | x :: xs, y :: ys => valEq x y && valEqList xs ys
  | _, _ => false
def valEqFields : List (String × Val) → List (String × Val) → Bool
  | [], [] => true
  | (n, x) :: xs, (m, y) :: ys => n == m && valEq x y && valEqFields xs ys
  | _, _ => false
end

/-- Bool-level output check (pins use this; Val has no derivable DecidableEq). -/
def outEq (o : Option Val) (v : Val) : Bool :=
  match o with
  | some w => valEq w v
  | none => false

/-- sha256 raw 32-byte digest over raw bytes (N3: same function as the
    bundle q; NOT reifyVal/hex — that arm of evalLF is explicitly not
    inherited). Built from the sealed SHA256 internals. -/
def sha256Raw (msg : List UInt8) : List UInt8 :=
  let padded := Residua.SHA256.pad msg
  let blocks := Residua.SHA256.chunk64 padded
  let hash := Residua.SHA256.processBlocks blocks Residua.SHA256.hInit
  let words :=
    hash.getD 0 0 :: hash.getD 1 0 :: hash.getD 2 0 :: hash.getD 3 0 ::
    hash.getD 4 0 :: hash.getD 5 0 :: hash.getD 6 0 :: hash.getD 7 0 :: []
  words.flatMap (fun w =>
    [ (w >>> (24 : UInt32)).toUInt8, (w >>> (16 : UInt32)).toUInt8
    , (w >>> (8 : UInt32)).toUInt8, w.toUInt8 ])

/-- The four mutable arms. Everything else is fixed law A in the core. -/
structure ArithLaws where
  addF : Int → Int → Option Int
  modF : Int → Int → Option Int
  divF : Int → Int → Option Int
  cmpOut : Bool → Val

/-- Law A bundle = the RED's law functions (copying law* is the contract). -/
def lawsA : ArithLaws :=
  { addF := lawAdd, modF := lawMod, divF := lawDiv, cmpOut := fun b => .bool b }

/-- Mutant bundle = the RED's mutants (trunc/wrap/i64-compare). -/
def lawsMutant : ArithLaws :=
  { addF := mutantAdd, modF := mutantMod, divF := mutantDiv
  , cmpOut := fun b => .int (if b then 1 else 0) }

/-- Law A for the non-mutated arms: overflow-refuse sub/mul/neg. -/
def lawSub (x y : Int) : Option Int :=
  let d := x - y; if inI64Range d then some d else none
def lawMul (x y : Int) : Option Int :=
  let p := x * y; if inI64Range p then some p else none
def lawNeg (x : Int) : Option Int :=
  let n := -x; if inI64Range n then some n else none

/-- Code-point substring: TOTAL Python-clamp (authoritative law,
    SlotSemanticsCore/interp.py: lo = max(0,min(a,n)), hi = max(0,min(b,n)),
    empty when lo ≥ hi). -/
def strSub (s : String) (a b : Int) : String :=
  let cs := s.toList
  let n : Int := cs.length
  let lo := max 0 (min a n)
  let hi := max 0 (min b n)
  if lo ≤ hi then String.mk ((cs.drop lo.toNat).take (hi - lo).toNat) else ""

/-- Sign+digits integer parse (authoritative law, interp.py StrToInt:
    optional leading '-', 1+ ASCII digits, no '+'; non-numeric and i64
    overflow are eval-none — total, never a partial crash). -/
def strToIntI (s : String) : Option Int :=
  let core (ds : List Char) : Option Int :=
    if ds.isEmpty then none
    else if ds.all (fun c => c.isDigit) then
      some (ds.foldl (fun acc c => acc * 10 + ((c.toNat - '0'.toNat : Nat) : Int)) 0)
    else none
  let r :=
    match s.toList with
    | '-' :: rest => (core rest).map (fun n => -n)
    | cs => core cs
  match r with
  | some n => if inI64Range n then some n else none
  | none => none

/-- List Int of 0..255 → bytes; any out-of-range element → none (pack law). -/
def packBytesV (vs : List Val) : Option (List UInt8) :=
  vs.foldr (fun v acc =>
    match v, acc with
    | .int n, some bs =>
        if 0 ≤ n ∧ n ≤ 255 then some ((UInt8.ofNat n.toNat) :: bs) else none
    | _, _ => none) (some [])

/-- Binary i64 arm helper (not recursive). -/
def arith2 (oa ob : Option Val) (law : Int → Int → Option Int) : Option Val :=
  match oa, ob with
  | some (.int x), some (.int y) => (law x y).map .int
  | _, _ => none

/-- Program body lookup by index. -/
def getProg : Programs S T → (i : Fin T.length) → BootExpr S (T.get i).1 (T.get i).2
  | .cons b _, ⟨0, _⟩ => b
  | .cons _ r, ⟨n+1, h⟩ => getProg r ⟨n, Nat.lt_of_succ_lt_succ h⟩

/-- Every BootExpr constructor has positive size (termination leaf fact). -/
theorem bootExprSizePos {S : SigTable} {G : Ctx} {t : BootTy}
    (e : BootExpr S G t) : 0 < sizeOf e := by
  cases e
  case var i => rw [BootExpr.var.sizeOf_spec]; omega
  case field a i => rw [BootExpr.field.sizeOf_spec]; omega
  case call f a => rw [BootExpr.call.sizeOf_spec]; omega
  case inj i a => rw [BootExpr.inj.sizeOf_spec]; omega
  case matchE a bs => rw [BootExpr.matchE.sizeOf_spec]; omega
  all_goals simp_arith

set_option maxHeartbeats 1600000 in
mutual

/-- The interpreter core. fuel checked nonzero at every node; decremented
    ONLY at call (N6c). Law violations / lookup failures / fuel = none. -/
def eval (L : ArithLaws) (progs : Programs S S) :
    (fuel : Nat) → EnvV → BootExpr S G t → Option Val
  | 0, _, _ => none
  | _+1, _,   .litI n => if inI64Range n then some (.int n) else none
  | _+1, _,   .litB b => some (.bool b)
  | _+1, _,   .litS s => some (.str s)
  | _+1, env, .var i => env.get? i.val
  | f+1, env, .letE a b =>
      match eval L progs (f+1) env a with
      | some v => eval L progs (f+1) (v :: env) b
      | none => none
  | f+1, env, .ifE c a b =>
      match eval L progs (f+1) env c with
      | some (.bool true) => eval L progs (f+1) env a
      | some (.bool false) => eval L progs (f+1) env b
      | _ => none
  | f+1, env, .add a b => arith2 (eval L progs (f+1) env a) (eval L progs (f+1) env b) L.addF
  | f+1, env, .sub a b => arith2 (eval L progs (f+1) env a) (eval L progs (f+1) env b) lawSub
  | f+1, env, .mul a b => arith2 (eval L progs (f+1) env a) (eval L progs (f+1) env b) lawMul
  | f+1, env, .neg a =>
      match eval L progs (f+1) env a with
      | some (.int x) => (lawNeg x).map .int
      | _ => none
  | f+1, env, .divE a b => arith2 (eval L progs (f+1) env a) (eval L progs (f+1) env b) L.divF
  | f+1, env, .modE a b => arith2 (eval L progs (f+1) env a) (eval L progs (f+1) env b) L.modF
  | f+1, env, .lt a b =>
      match eval L progs (f+1) env a, eval L progs (f+1) env b with
      | some (.int x), some (.int y) => some (L.cmpOut (decide (x < y)))
      | _, _ => none
  | f+1, env, .gt a b =>
      match eval L progs (f+1) env a, eval L progs (f+1) env b with
      | some (.int x), some (.int y) => some (L.cmpOut (decide (y < x)))
      | _, _ => none
  | f+1, env, .eqE a b =>
      match eval L progs (f+1) env a, eval L progs (f+1) env b with
      | some va, some vb => some (.bool (valEq va vb))
      | _, _ => none
  | f+1, env, .andE a b =>
      match eval L progs (f+1) env a, eval L progs (f+1) env b with
      | some (.bool x), some (.bool y) => some (.bool (x && y))
      | _, _ => none
  | f+1, env, .orE a b =>
      match eval L progs (f+1) env a, eval L progs (f+1) env b with
      | some (.bool x), some (.bool y) => some (.bool (x || y))
      | _, _ => none
  | f+1, env, .notE a =>
      match eval L progs (f+1) env a with
      | some (.bool x) => some (.bool (!x))
      | _ => none
  | f+1, env, .strLen a =>
      match eval L progs (f+1) env a with
      | some (.str s) => some (.int (s.length : Int))
      | _ => none
  | f+1, env, .strSplit a sep =>
      match eval L progs (f+1) env a, eval L progs (f+1) env sep with
      | some (.str s), some (.str p) =>
          if p.isEmpty then none
          else some (.list ((s.splitOn p).map .str))
      | _, _ => none
  | f+1, env, .strSubstring a lo hi =>
      match eval L progs (f+1) env a, eval L progs (f+1) env lo, eval L progs (f+1) env hi with
      | some (.str s), some (.int x), some (.int y) => some (.str (strSub s x y))
      | _, _, _ => none
  | f+1, env, .strToInt a =>
      match eval L progs (f+1) env a with
      | some (.str s) => (strToIntI s).map .int
      | _ => none
  | _+1, _, .emptyList => some (.list [])
  | f+1, env, .listSingleton a => (eval L progs (f+1) env a).map (fun v => .list [v])
  | f+1, env, .listLen a =>
      match eval L progs (f+1) env a with
      | some (.list vs) => some (.int (vs.length : Int))
      | _ => none
  | f+1, env, .listFirst a =>
      match eval L progs (f+1) env a with
      | some (.list []) => some .noneV
      | some (.list (v :: _)) => some (.someV v)
      | _ => none
  | f+1, env, .listAppend a b =>
      match eval L progs (f+1) env a, eval L progs (f+1) env b with
      | some (.list xs), some (.list ys) => some (.list (xs ++ ys))
      | _, _ => none
  | f+1, env, .listDrop n a =>
      match eval L progs (f+1) env n, eval L progs (f+1) env a with
      | some (.int k), some (.list vs) => some (.list (vs.drop k.toNat))
      | _, _ => none
  | f+1, env, .pairE a b =>
      match eval L progs (f+1) env a, eval L progs (f+1) env b with
      | some x, some y => some (.pair x y)
      | _, _ => none
  | f+1, env, .fstE a =>
      match eval L progs (f+1) env a with
      | some (.pair x _) => some x
      | _ => none
  | f+1, env, .sndE a =>
      match eval L progs (f+1) env a with
      | some (.pair _ y) => some y
      | _ => none
  | f+1, env, .inj i a => (eval L progs (f+1) env a).map (.inj i.val)
  | f+1, env, .matchE a bs =>
      match eval L progs (f+1) env a with
      | some (.inj i v) => evalMatch L progs (f+1) env i v bs
      | _ => none
  | _+1, _, .recNil => some (.recV [])
  | f+1, env, .recCons name a rest =>
      match eval L progs (f+1) env a, eval L progs (f+1) env rest with
      | some v, some (.recV fs) => some (.recV ((name, v) :: fs))
      | _, _ => none
  | f+1, env, .field a i =>
      match eval L progs (f+1) env a with
      | some (.recV fs) =>
          match fs.get? i.val with
          | some (_, v) => some v
          | none => none
      | _ => none
  | f+1, env, .someE a => (eval L progs (f+1) env a).map .someV
  | _+1, _, .noneE => some .noneV
  | f+1, env, .isSomeE a =>
      match eval L progs (f+1) env a with
      | some (.someV _) => some (.bool true)
      | some .noneV => some (.bool false)
      | _ => none
  | f+1, env, .unwrapSome a =>
      match eval L progs (f+1) env a with
      | some (.someV v) => some v
      | _ => none
  | f+1, env, .okE a => (eval L progs (f+1) env a).map .ok
  | _+1, _, .residueE c => some (.res c)
  | f+1, env, .isResidueE a =>
      match eval L progs (f+1) env a with
      | some (.res _) => some (.bool true)
      | some (.ok _) => some (.bool false)
      | _ => none
  | f+1, env, .getResidue a =>
      match eval L progs (f+1) env a with
      | some (.res c) => some (.int c)
      | _ => none
  | f+1, env, .getOk a =>
      match eval L progs (f+1) env a with
      | some (.ok v) => some v
      | _ => none
  | f+1, env, .packBytes a =>
      match eval L progs (f+1) env a with
      | some (.list vs) => (packBytesV vs).map .bytes
      | _ => none
  | f+1, env, .bytesLen a =>
      match eval L progs (f+1) env a with
      | some (.bytes bs) => some (.int (bs.length : Int))
      | _ => none
  | f+1, env, .bytesConcat a b =>
      match eval L progs (f+1) env a, eval L progs (f+1) env b with
      | some (.bytes xs), some (.bytes ys) => some (.bytes (xs ++ ys))
      | _, _ => none
  | f+1, env, .bytesSlice a lo hi =>
      match eval L progs (f+1) env a, eval L progs (f+1) env lo, eval L progs (f+1) env hi with
      | some (.bytes bs), some (.int x), some (.int y) =>
          if x < 0 || y < x || y > (bs.length : Int) then none
          else some (.bytes ((bs.drop x.toNat).take (y - x).toNat))
      | _, _, _ => none
  | f+1, env, .contentHash a =>
      match eval L progs (f+1) env a with
      | some (.bytes bs) => some (.bytes (sha256Raw bs))
      | _ => none
  | f+1, env, .foldE xs init body =>
      match eval L progs (f+1) env xs, eval L progs (f+1) env init with
      | some (.list vs), some acc0 => evalFold L progs (f+1) env body vs acc0
      | _, _ => none
  | f+1, env, .fixE stop step init bound =>
      match eval L progs (f+1) env init, eval L progs (f+1) env bound with
      | some s0, some (.int b) =>
          if b < 0 then none else evalFix L progs (f+1) env stop step s0 0 b.toNat
      | _, _ => none
  | f+1, env, .call g args =>
      match evalArgs L progs (f+1) env args with
      | some vs => eval L progs f vs (getProg progs g)
      | none => none
termination_by fuel _ e => (fuel, sizeOf e, 0, 0)
decreasing_by all_goals first
  | decreasing_tactic
  | (simp only [BootExpr.field.sizeOf_spec, BootExpr.fixE.sizeOf_spec,
       BootExpr.foldE.sizeOf_spec, BootExpr.matchE.sizeOf_spec,
       BootExpr.call.sizeOf_spec]
     first
       | decreasing_tactic
       | (apply Prod.Lex.right
          apply Prod.Lex.left
          have h1 := bootExprSizePos init
          omega))

/-- Argument evaluation (left to right). -/
def evalArgs (L : ArithLaws) (progs : Programs S S) :
    (fuel : Nat) → EnvV → Args S G ts → Option (List Val)
  | 0, _, _ => none
  | _+1, _, .nil => some []
  | f+1, env, .cons a rest =>
      match eval L progs (f+1) env a, evalArgs L progs (f+1) env rest with
      | some v, some vs => some (v :: vs)
      | _, _ => none
termination_by fuel _ args => (fuel, sizeOf args, 0, 0)

/-- Branch selection by summand index; binds the payload at index 0. -/
def evalMatch (L : ArithLaws) (progs : Programs S S) :
    (fuel : Nat) → EnvV → Nat → Val → Branches S G ts r → Option Val
  | 0, _, _, _, _ => none
  | _+1, _, _, _, .nil => none
  | f+1, env, 0, v, .cons b _ => eval L progs (f+1) (v :: env) b
  | f+1, env, i+1, v, .cons _ rest => evalMatch L progs (f+1) env i v rest
termination_by fuel _ _ _ bs => (fuel, sizeOf bs, 0, 0)

/-- Host fold shape: body context = elem :: acc :: Γ (var 0 = element). -/
def evalFold (L : ArithLaws) (progs : Programs S S) :
    (fuel : Nat) → EnvV → BootExpr S (a :: b :: G) b → List Val → Val → Option Val
  | 0, _, _, _, _ => none
  | _+1, _, _, [], acc => some acc
  | f+1, env, body, v :: vs, acc =>
      match eval L progs (f+1) (v :: acc :: env) body with
      | some acc' => evalFold L progs (f+1) env body vs acc'
      | none => none
termination_by fuel _ body vs _ => (fuel, sizeOf body, 1, vs.length)

/-- Host fix shape: returns {converged, state, steps}; converged=false =
    bound exhausted without stopPred (census: converged 扰动 5/9 红). -/
def evalFix (L : ArithLaws) (progs : Programs S S) :
    (fuel : Nat) → EnvV → BootExpr S (s :: G) .bool → BootExpr S (s :: G) s →
    Val → Nat → Nat → Option Val
  | 0, _, _, _, _, _, _ => none
  | f+1, env, stop, step, st, steps, bnd =>
      match eval L progs (f+1) (st :: env) stop with
      | some (.bool true) =>
          some (.recV [("converged", .bool true), ("state", st), ("steps", .int steps)])
      | some (.bool false) =>
          match bnd with
          | 0 => some (.recV [("converged", .bool false), ("state", st), ("steps", .int steps)])
          | b+1 =>
              match eval L progs (f+1) (st :: env) step with
              | some st' => evalFix L progs (f+1) env stop step st' (steps+1) b
              | none => none
      | _ => none
termination_by fuel _ stop step _ _ bnd => (fuel, sizeOf stop + sizeOf step + 1, 1, bnd)

end

/-- evalBoot: the law-A interpreter. -/
def evalBoot (progs : Programs S S) (fuel : Nat) (env : EnvV)
    (e : BootExpr S G t) : Option Val :=
  eval lawsA progs fuel env e

/-- evalBoot': the mutant interpreter (same machinery, mutant arms). -/
def evalBoot' (progs : Programs S S) (fuel : Nat) (env : EnvV)
    (e : BootExpr S G t) : Option Val :=
  eval lawsMutant progs fuel env e

/-! ## 1a discharge: every pin routed THROUGH BootExpr evaluation. -/

section Discharge
open Residua.Bootstrap.EvalBootSeparators

/-- Empty table / empty context evaluation of a closed i64 binary op. -/
private def runI (mk : BootExpr ([] : SigTable) [] .i64 → BootExpr [] [] .i64 →
    BootExpr [] [] .i64) (x y : Int) (L : ArithLaws) : Option Int :=
  match eval L .nil 1 [] (mk (.litI x) (.litI y)) with
  | some (.int n) => some n
  | _ => none

private def runCmp (x y : Int) (L : ArithLaws) : CmpResult :=
  match eval L .nil 1 [] (BootExpr.lt (S := []) (G := []) (.litI x) (.litI y)) with
  | some (.bool b) => .bool b
  | some (.int n) => .i64 n
  | _ => .i64 (-777)

instance : EvalBootSeparatorDischarge where
  evalMod x y := runI .modE x y lawsA
  evalDiv x y := runI .divE x y lawsA
  evalAdd x y := runI .add x y lawsA
  evalLt  x y := runCmp x y lawsA
  pin_mod := by native_decide
  pin_div := by native_decide
  pin_add := by native_decide
  pin_div_min := by native_decide
  pin_lt := by native_decide
  evalMod' x y := runI .modE x y lawsMutant
  evalDiv' x y := runI .divE x y lawsMutant
  evalAdd' x y := runI .add x y lawsMutant
  evalLt'  x y := runCmp x y lawsMutant
  mut_mod := by native_decide
  mut_div := by native_decide
  mut_add := by native_decide
  mut_div_min := by native_decide
  mut_lt := by native_decide

end Discharge

/-! ## Pinned equalities (r4.5): one per op family + law points + hash tie. -/

section Pins

private def ev (e : BootExpr ([] : SigTable) [] t) : Option Val :=
  eval lawsA .nil 1 [] e

-- separation points through the interpreter (law side)
theorem pin_boot_mod_7_m3 : outEq (ev (.modE (.litI 7) (.litI (-3)))) (.int (-2)) = true := by native_decide
theorem pin_boot_div_7_m3 : (ev (.divE (.litI 7) (.litI (-3)))).isNone = true := by native_decide
theorem pin_boot_add_min_m1 : (ev (.add (.litI i64Min) (.litI (-1)))).isNone = true := by native_decide
theorem pin_boot_div_min_m1 : (ev (.divE (.litI i64Min) (.litI (-1)))).isNone = true := by native_decide
theorem pin_boot_lt_m1_1 : outEq (ev (.lt (.litI (-1)) (.litI 1))) (.bool true) = true := by native_decide
-- coincident non-tooth acknowledged (RED): floor = trunc here
theorem pin_boot_mod_m7_m3 : outEq (ev (.modE (.litI (-7)) (.litI (-3)))) (.int (-1)) = true := by native_decide

-- op family pins
theorem pin_boot_sub : outEq (ev (.sub (.litI 5) (.litI 9))) (.int (-4)) = true := by native_decide
theorem pin_boot_mul : outEq (ev (.mul (.litI 6) (.litI 7))) (.int 42) = true := by native_decide
theorem pin_boot_mul_ovf : (ev (.mul (.litI 4294967296) (.litI 4294967296))).isNone = true := by native_decide
theorem pin_boot_neg_min : (ev (.neg (.litI i64Min))).isNone = true := by native_decide
theorem pin_boot_let : outEq (ev (.letE (.litI 41) (.add (.var ⟨0, by decide⟩) (.litI 1)))) (.int 42) = true := by native_decide
theorem pin_boot_if : outEq (ev (.ifE (.litB true) (.litI 1) (.litI 2))) (.int 1) = true := by native_decide
theorem pin_boot_gt : outEq (ev (.gt (.litI 3) (.litI 2))) (.bool true) = true := by native_decide
theorem pin_boot_eq : outEq (ev (.eqE (.litS "ab") (.litS "ab"))) (.bool true) = true := by native_decide
theorem pin_boot_and : outEq (ev (.andE (.litB true) (.litB false))) (.bool false) = true := by native_decide
theorem pin_boot_or : outEq (ev (.orE (.litB false) (.litB true))) (.bool true) = true := by native_decide
theorem pin_boot_not : outEq (ev (.notE (.litB false))) (.bool true) = true := by native_decide
theorem pin_boot_strlen : outEq (ev (.strLen (.litS "héé"))) (.int 3) = true := by native_decide
theorem pin_boot_strsplit :
    outEq (ev (.strSplit (.litS "a,b") (.litS ","))) (.list [.str "a", .str "b"]) = true := by native_decide
theorem pin_boot_strsub : outEq (ev (.strSubstring (.litS "hello") (.litI 1) (.litI 3))) (.str "el") = true := by native_decide
theorem pin_boot_str2int : outEq (ev (.strToInt (.litS "-42"))) (.int (-42)) = true := by native_decide
theorem pin_boot_str2int_bad : (ev (.strToInt (.litS "4a"))).isNone = true := by native_decide
theorem pin_boot_strsub_clamp :
    outEq (ev (.strSubstring (.litS "abc") (.litI (-2)) (.litI 99))) (.str "abc") = true := by native_decide
theorem pin_boot_listdrop_neg :
    outEq (ev (.listDrop (.litI (-1)) (.listSingleton (.litI 7)))) (.list [.int 7]) = true := by native_decide
theorem pin_boot_list :
    outEq (ev (.listLen (.listAppend (.listSingleton (.litI 1)) (.listSingleton (.litI 2))))) (.int 2) = true := by native_decide
theorem pin_boot_listfirst_empty :
    outEq (ev (.listFirst (.emptyList (t := .i64)))) .noneV = true := by native_decide
theorem pin_boot_listdrop :
    outEq (ev (.listDrop (.litI 1) (.listAppend (.listSingleton (.litI 1)) (.listSingleton (.litI 2))))) (.list [.int 2]) = true := by native_decide
theorem pin_boot_pair : outEq (ev (.fstE (.pairE (.litI 1) (.litB true)))) (.int 1) = true := by native_decide
theorem pin_boot_snd : outEq (ev (.sndE (.pairE (.litI 1) (.litB true)))) (.bool true) = true := by native_decide
theorem pin_boot_record :
    outEq (ev (.field (.recCons "a" (.litI 7) .recNil) ⟨0, by decide⟩)) (.int 7) = true := by native_decide
theorem pin_boot_option : outEq (ev (.unwrapSome (.someE (.litI 5)))) (.int 5) = true := by native_decide
theorem pin_boot_issome_none : outEq (ev (.isSomeE (.noneE (t := .i64)))) (.bool false) = true := by native_decide
theorem pin_boot_residue :
    outEq (ev (.getResidue (.residueE (t := .i64) 99))) (.int 99) = true := by native_decide
theorem pin_boot_isresidue_ok :
    outEq (ev (.isResidueE (.okE (.litI 1)))) (.bool false) = true := by native_decide
theorem pin_boot_getok : outEq (ev (.getOk (.okE (.litI 8)))) (.int 8) = true := by native_decide
theorem pin_boot_bytes_len :
    outEq (ev (.bytesLen (.packBytes (.listAppend (.listSingleton (.litI 0)) (.listSingleton (.litI 255)))))) (.int 2) = true := by native_decide
theorem pin_boot_pack_reject :
    (ev (.packBytes (.listSingleton (.litI 256)))).isNone = true := by native_decide
theorem pin_boot_bytes_slice :
    outEq (ev (.bytesSlice (.packBytes (.listAppend (.listSingleton (.litI 10)) (.listSingleton (.litI 20))))
        (.litI 1) (.litI 2))) (.bytes [20]) = true := by native_decide
theorem pin_boot_fold :
    outEq (ev (.foldE (.listAppend (.listSingleton (.litI 1)) (.listSingleton (.litI 2)))
        (.litI 0) (.add (.var ⟨0, by decide⟩) (.var ⟨1, by decide⟩)))) (.int 3) = true := by native_decide
theorem pin_boot_fix :
    outEq (ev (.fixE (.gt (.var ⟨0, by decide⟩) (.litI 2)) (.add (.var ⟨0, by decide⟩) (.litI 1))
        (.litI 0) (.litI 10))) (.recV [("converged", .bool true), ("state", .int 3), ("steps", .int 3)]) = true := by native_decide
theorem pin_boot_match :
    outEq (ev (.matchE (.inj (ts := [.i64, .bool]) ⟨0, by decide⟩ (.litI 5))
        (.cons (.add (.var ⟨0, by decide⟩) (.litI 1)) (.cons (.litI 0) .nil)))) (.int 6) = true := by native_decide

/-- N3 tie: ContentHash through the interpreter on empty bytes = the RED's
    frozen 32-byte raw digest — the SAME function as the bundle q. -/
theorem pin_boot_contenthash_empty :
    outEq (ev (.contentHash (.packBytes (.emptyList (t := .i64))))) (.bytes sha256EmptyRaw) = true := by native_decide

/-- Depth costs no fuel (all pins above run at fuel 1); this is the
    call-free half of the Call-only law. The call half is pinned below. -/
theorem pin_boot_nested_nocall_fuel1 :
    outEq (ev (.add (.add (.litI 1) (.litI 2)) (.add (.litI 3) (.litI 4)))) (.int 10) = true := by
  native_decide

/-! ### call / Programs pins (grok #3562 F1: C0 is a call graph — the
    call path must be load-bearing in the pins, not only in the
    interpreter definition). -/

def sig42 : SigTable := [([], .i64)]
def prog42 : Programs sig42 sig42 := .cons (.litI 42) .nil

/-- call works: fuel 2 (call consumes one, body runs at fuel 1). -/
theorem pin_boot_call :
    outEq (eval lawsA prog42 2 [] (.call ⟨0, by decide⟩ .nil : BootExpr sig42 [] .i64)) (.int 42) = true := by
  native_decide

/-- Call-only fuel decrement, call half: at fuel 1 the body runs at
    fuel 0 and refuses — call is exactly what fuel meters. -/
theorem pin_boot_call_fuel1 :
    (eval lawsA prog42 1 [] (.call ⟨0, by decide⟩ .nil : BootExpr sig42 [] .i64)).isNone = true := by
  native_decide

/-- call with an argument: program 0 = add 1 to its parameter. -/
def sigInc : SigTable := [([.i64], .i64)]
def progInc : Programs sigInc sigInc :=
  .cons (.add (.var ⟨0, by decide⟩) (.litI 1)) .nil

theorem pin_boot_call_arg :
    outEq (eval lawsA progInc 2 []
      (.call ⟨0, by decide⟩ (.cons (.litI 41) .nil) : BootExpr sigInc [] .i64))
      (.int 42) = true := by
  native_decide

/-- Frozen separators contract q (RED file tie; bytes live in
    lean/Residua/Bootstrap/separators_contract_v1.json). -/
example : Residua.Bootstrap.EvalBootSeparators.separatorsContractV1Q =
    "84c06f8c6bd099a35fab94f18c90b96a654b05f4f9233dc490a70e2119633656" := rfl

/-- fuel 0 = none. -/
theorem pin_boot_fuel_zero :
    (eval lawsA .nil 0 [] (.litI 1 : BootExpr [] [] .i64)).isNone = true := by native_decide

end Pins

end Residua.Bootstrap.Semantics

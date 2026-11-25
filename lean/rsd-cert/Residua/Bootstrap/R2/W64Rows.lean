import Residua.Bootstrap.R2.SCM

/-!
# UINT64-0 rows: the width-64 word operators of S4 revision 2 against stock Lean's `UInt64`

Every row evaluates one operator of `Residua.Bootstrap.R2.SCM.evalSCM` on literals at and around 2^32, 2^63 and 2^64 and
compares the value with Lean 4.14's own `UInt64` function of the same operands (`+ - * / % < ≤ &&& ||| ^^^ ~~~ <<< >>>`,
Lean's `x / 0 = 0`, `x % 0 = x`, shift count mod 64). `lean --run W64Rows.lean` prints `w64rows ok=<n>/<n>` and exits 1 on
any difference; the planted mutants (reports/uint64/MUTANTS.tsv) must make it exit 1. `closure_claim = 0`.
-/

namespace Residua.Bootstrap.R2.SCM

def ev (e : SCMExpr [] [] .i64) : Option SCMVal := evalSCM (.nil : SCMPrograms [] []) 2 [] e
def evB (e : SCMExpr [] [] .bool) : Option SCMVal := evalSCM (.nil : SCMPrograms [] []) 2 [] e
def evL (e : SCMExpr [] [] (.list .i64)) : Option SCMVal := evalSCM (.nil : SCMPrograms [] []) 2 [] e
def evN (e : SCMExpr [] [] natMagTy) : Option SCMVal := evalSCM (.nil : SCMPrograms [] []) 2 [] e

def wvals : List UInt64 :=
  [0, 1, 2, 0xFFFFFFFF, 0x100000000, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0x8000000000000001,
   0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF]
def wcounts : List UInt64 := [0, 1, 31, 32, 63, 64, 65, 127, 128, 0xFFFFFFFFFFFFFFFF]

def isW (o : Option SCMVal) (x : UInt64) : Bool := scmOutEq o (.int (x.toNat : Int))
def isB (o : Option SCMVal) (b : Bool) : Bool := scmOutEq o (.bool b)

def rowsBin : List Bool :=
  wvals.flatMap fun a => wvals.flatMap fun b =>
    [ isW (ev (.wAdd (.litW a) (.litW b))) (a + b),
      isW (ev (.wSub (.litW a) (.litW b))) (a - b),
      isW (ev (.wMul (.litW a) (.litW b))) (a * b),
      isW (ev (.wDiv (.litW a) (.litW b))) (a / b),
      isW (ev (.wMod (.litW a) (.litW b))) (a % b),
      isB (evB (.wLt (.litW a) (.litW b))) (decide (a < b)),
      isB (evB (.wLe (.litW a) (.litW b))) (decide (a ≤ b)),
      isW (ev (.wAnd (.litW a) (.litW b))) (a &&& b),
      isW (ev (.wOr (.litW a) (.litW b))) (a ||| b),
      isW (ev (.wXor (.litW a) (.litW b))) (a ^^^ b) ]

def rowsNot : List Bool := wvals.map fun a => isW (ev (.wNot (.litW a))) (~~~a)

def rowsShift : List Bool :=
  wvals.flatMap fun a => wcounts.flatMap fun n =>
    [ isW (ev (.wShl (.litW a) (.litW n))) (a <<< n),
      isW (ev (.wShr (.litW a) (.litW n))) (a >>> n) ]

/-- Operands outside `[0, 2^64)` are refused (`none`), the word domain is closed. -/
def rowsDomain : List Bool :=
  [ (ev (.wAdd (.litI (-1)) (.litW 1))).isNone, (ev (.wMul (.litW 1) (.litI (-5)))).isNone,
    (ev (.wNot (.litI (-1)))).isNone, (evB (.wLt (.litI (-3)) (.litW 1))).isNone,
    isW (ev (.wAdd (.litI 5) (.litW 7))) 12 ]

/-- One node program through `let`: a nested row (two operators, a bound variable). -/
def rowsNested : List Bool :=
  [ isW (ev (.let1 (.wMul (.litW 0x8000000000000001) (.litW 2)) (.wAdd (.var ⟨0, by decide⟩) (.litW 0xFFFFFFFFFFFFFFFF)))) 0x0
      |> fun _ => isW (ev (.let1 (.wMul (.litW 0x8000000000000001) (.litW 2))
          (.wAdd (.var ⟨0, by decide⟩) (.litW 0xFFFFFFFFFFFFFFFF))))
          ((0x8000000000000001 * 2 : UInt64) + 0xFFFFFFFFFFFFFFFF) ]

/-- FLOAT64-0 rows (17 operators, tags 78..94). -/
def rowsF64 : List Bool :=
  [ scmOutEq (ev (.fAdd (.litW 0x3FF8000000000000) (.litW 0x4004000000000000))) (.int 0x4010000000000000),
    scmOutEq (ev (.fSub (.litW 0x400C000000000000) (.litW 0x3FF8000000000000))) (.int 0x4000000000000000),
    scmOutEq (ev (.fMul (.litW 0x3FF8000000000000) (.litW 0x4000000000000000))) (.int 0x4008000000000000),
    scmOutEq (ev (.fDiv (.litW 0x4008000000000000) (.litW 0x4000000000000000))) (.int 0x3FF8000000000000),
    scmOutEq (ev (.fDiv (.litW 0x3FF0000000000000) (.litW 0x0000000000000000))) (.int 0x7FF0000000000000),
    scmOutEq (evB (.fLt (.litW 0x3FF8000000000000) (.litW 0x4000000000000000))) (.bool true),
    scmOutEq (evB (.fLt (.litW 0x7FF8000000000000) (.litW 0x3FF0000000000000))) (.bool false),
    scmOutEq (evB (.fLe (.litW 0x4000000000000000) (.litW 0x4000000000000000))) (.bool true),
    scmOutEq (evB (.fLe (.litW 0x7FF8000000000000) (.litW 0x4000000000000000))) (.bool false),
    scmOutEq (evB (.fEq (.litW 0x0000000000000000) (.litW 0x8000000000000000))) (.bool true),
    scmOutEq (evB (.fEq (.litW 0x7FF8000000000000) (.litW 0x7FF8000000000000))) (.bool false),
    scmOutEq (ev (.fNeg (.litW 0x3FF8000000000000))) (.int 0xBFF8000000000000),
    scmOutEq (ev (.fNeg (.litW 0x0000000000000000))) (.int 0x8000000000000000),
    scmOutEq (ev (.fAbs (.litW 0xBFF8000000000000))) (.int 0x3FF8000000000000),
    scmOutEq (ev (.fAbs (.litW 0x8000000000000000))) (.int 0x0000000000000000),
    scmOutEq (ev (.fSqrt (.litW 0x4010000000000000))) (.int 0x4000000000000000),
    scmOutEq (ev (.fSqrt (.litW 0xBFF8000000000000))) (.int 0x7FF8000000000000),
    scmOutEq (ev (.fSqrt (.litW 4842126294296133448))) (.int 4724639673638920813),
    scmOutEq (ev (.fFloor (.litW 0x3FF8000000000000))) (.int 0x3FF0000000000000),
    scmOutEq (ev (.fFloor (.litW 0xBFF8000000000000))) (.int 0xC000000000000000),
    scmOutEq (ev (.fCeil (.litW 0x3FF8000000000000))) (.int 0x4000000000000000),
    scmOutEq (ev (.fCeil (.litW 0xBFF8000000000000))) (.int 0xBFF0000000000000),
    scmOutEq (ev (.fRound (.litW 0x4004000000000000))) (.int 0x4008000000000000),
    scmOutEq (ev (.fRound (.litW 0xC004000000000000))) (.int 0xC008000000000000),
    scmOutEq (ev (.fRound (.litW 0x3FD999999999999A))) (.int 0x0000000000000000),
    scmOutEq (ev (.fOfW (.litW 3))) (.int 0x4008000000000000),
    scmOutEq (ev (.fOfW (.litW 0xFFFFFFFFFFFFFFFF))) (.int 0x43F0000000000000),
    scmOutEq (ev (.fOfI (.litI (-3)))) (.int 0xC008000000000000),
    scmOutEq (ev (.fOfI (.litI 0))) (.int 0x0000000000000000),
    scmOutEq (ev (.fToW (.litW 0x400C000000000000))) (.int 3),
    scmOutEq (ev (.fToW (.litW 0xBFF8000000000000))) (.int 0),
    scmOutEq (ev (.fToW (.litW 0x7FF8000000000000))) (.int 0),
    scmOutEq (ev (.fToW (.litW 0x7FF0000000000000))) (.int 18446744073709551615),
    scmOutEq (ev (.fBits (.litW 0x7FF0000000000001))) (.int 0x7FF8000000000000),
    scmOutEq (ev (.fBits (.litW 0xFFF8000000000042))) (.int 0x7FF8000000000000),
    scmOutEq (ev (.fBits (.litW 0x8000000000000000))) (.int 0x8000000000000000),
    scmOutEq (ev (.fBits (.litW 0x3FF8000000000000))) (.int 0x3FF8000000000000) ]

/-- ARRAY-0 rows (13 operators, tags 55..63, 95..98). -/
def rowsArr : List Bool :=
  [ scmOutEq (evL (.aEmpty (.litW 16))) (.list []),
    scmOutEq (evL (.aEmpty (.wToN (.litW 16) : SCMExpr [] [] natMagTy))) (.list []),
    scmOutEq (evL (.aMk (.litW 3) (.litW 7))) (.list [.int 7, .int 7, .int 7]),
    scmOutEq (evL (.aMk (.wToN (.litW 2) : SCMExpr [] [] natMagTy) (.litW 9))) (.list [.int 9, .int 9]),
    scmOutEq (evL (.aOfList (.listAppend (.listSingleton (.litW 10)) (.listSingleton (.litW 20))))) (.list [.int 10, .int 20]),
    scmOutEq (evL (.aToList (.aMk (.litW 2) (.litW 5)))) (.list [.int 5, .int 5]),
    scmOutEq (ev (.aUSize (.aMk (.litW 4) (.litW 9)))) (.int 4),
    scmOutEq (evN (.wToN (.litW 0))) (.record [(natMagKey, .list [])]),
    scmOutEq (evN (.wToN (.litW 258))) (.record [(natMagKey, .list [.int 2, .int 1])]),
    scmOutEq (ev (.wToN (.litW 258))) (.int 258),
    scmOutEq (evN (.aSize (.aMk (.litW 3) (.litW 7)))) (.record [(natMagKey, .list [.int 3])]),
    scmOutEq (ev (.aSize (.aMk (.litW 3) (.litW 7)))) (.int 3),
    scmOutEq (evL (.aPush (.aPush (.aEmpty (.litW 0)) (.litW 11)) (.litW 22))) (.list [.int 11, .int 22]),
    scmOutEq (evL (.aPop (.aPush (.aPush (.aEmpty (.litW 0)) (.litW 11)) (.litW 22)))) (.list [.int 11]),
    scmOutEq (evL (.aPop (.aEmpty (.litW 0)))) (.list []),
    scmOutEq (ev (.aGet (.aPush (.aPush (.aEmpty (.litW 0)) (.litW 11)) (.litW 22)) (.litW 1))) (.int 22),
    scmOutEq (ev (.aGet (.aPush (.aPush (.aEmpty (.litW 0)) (.litW 11)) (.litW 22)) (.wToN (.litW 0) : SCMExpr [] [] natMagTy))) (.int 11),
    (ev (.aGet (.aMk (.litW 2) (.litW 11)) (.litW 2))).isNone,
    (ev (.aGet (.aMk (.litW 2) (.litW 11)) (.wToN (.litW 5) : SCMExpr [] [] natMagTy))).isNone,
    scmOutEq (evL (.aSet (.aPush (.aPush (.aEmpty (.litW 0)) (.litW 11)) (.litW 22)) (.litW 0) (.litW 99))) (.list [.int 99, .int 22]),
    scmOutEq (evL (.aSet (.aPush (.aPush (.aEmpty (.litW 0)) (.litW 11)) (.litW 22)) (.wToN (.litW 1) : SCMExpr [] [] natMagTy) (.litW 88))) (.list [.int 11, .int 88]),
    (evL (.aSet (.aMk (.litW 2) (.litW 11)) (.litW 2) (.litW 99))).isNone,
    scmOutEq (evL (.aSlice (.aPush (.aPush (.aPush (.aEmpty (.litW 0)) (.litW 10)) (.litW 20)) (.litW 30)) (.litW 1) (.litW 2))) (.list [.int 20]),
    scmOutEq (evL (.aSlice (.aPush (.aPush (.aPush (.aEmpty (.litW 0)) (.litW 10)) (.litW 20)) (.litW 30)) (.litW 1) (.litW 3))) (.list [.int 20, .int 30]),
    scmOutEq (evL (.aSlice (.aPush (.aPush (.aEmpty (.litW 0)) (.litW 10)) (.litW 20)) (.litW 1) (.litW 99))) (.list [.int 20]),
    scmOutEq (evL (.aSlice (.aPush (.aPush (.aEmpty (.litW 0)) (.litW 10)) (.litW 20)) (.litW 2) (.litW 1))) (.list []),
    scmOutEq (evL (.aAppend (.aMk (.litW 2) (.litW 1)) (.aMk (.litW 1) (.litW 2)))) (.list [.int 1, .int 1, .int 2]) ]

def allRows : List Bool := rowsBin ++ rowsNot ++ rowsShift ++ rowsDomain ++ rowsNested ++ rowsF64 ++ rowsArr

end Residua.Bootstrap.R2.SCM

open Residua.Bootstrap.R2.SCM in
def main : IO UInt32 := do
  let ok := allRows.filter id |>.length
  IO.println s!"w64rows ok={ok}/{allRows.length}"
  return (if ok == allRows.length then 0 else 1)

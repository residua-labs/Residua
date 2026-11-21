import Residua.Bootstrap.R2.SCM

/-!
# UINT64-0 rows: the width-64 word operators of S4 revision 2 against stock Lean's `UInt64`

Every row evaluates one operator of `Residua.Bootstrap.R2.SCM.evalSCM` on literals at and around 2^32, 2^63 and 2^64 and
compares the value with Lean 4.14's own `UInt64` function of the same operands (`+ - * / % < ≤ &&& ||| ^^^ ~~~ <<< >>>`,
Lean's `x / 0 = 0`, `x % 0 = x`, shift count mod 64). `lean --run W64Rows.lean` prints `w64rows ok=<n>/<n>` and exits 1 on
any difference; the planted mutants (reports/uint64/MUTANTS.tsv) must make it exit 1. `closure_claim = 0`.
-/

namespace Residua.Bootstrap.R2.SCM

def ev (e : SCMExpr [] [] .i64) : Option SCMVal := evalSCM (.nil : SCMPrograms [] []) 1 [] e
def evB (e : SCMExpr [] [] .bool) : Option SCMVal := evalSCM (.nil : SCMPrograms [] []) 1 [] e

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

def allRows : List Bool := rowsBin ++ rowsNot ++ rowsShift ++ rowsDomain ++ rowsNested

end Residua.Bootstrap.R2.SCM

open Residua.Bootstrap.R2.SCM in
def main : IO UInt32 := do
  let ok := allRows.filter id |>.length
  IO.println s!"w64rows ok={ok}/{allRows.length}"
  return (if ok == allRows.length then 0 else 1)

import rcic.ScmSrcGroups
import rcic.ScmSrcGroupsKernelRfl

/-! Real input for the R-NoFunRec work: the four function-recursive constructors of the K3c table, with their field shapes and the canonical ι right-hand sides that a function-recursive ι rule must reproduce.

Provenance: hand-transcribed (no generator) from `devin/k3c-groups` @ `cefd14e16e`; every literal is tied by `kernel_rfl` to the judgment's own `equationDoms` / `iotaSchemaAt` / `iotaLhsType` in `ScmSrcGroupsFunRecEntryCheck`, which also re-exposes their existing typings. This module imports only `rcic.ScmSrcGroups` and `rcic.ScmSrcGroupsKernelRfl`. It is admission-side data only. It states no verdict of main's ι (field kinds, witnesses, reduction), so it compiles before and after a fix of R-NoFunRec (#6151).

`ctorTypeLitVaR`/`mVaR` (slot 142) carries the stage-1a hand correction: the `BLC vs xb` premise added and the value count tied to the field count `n` — see `ScmSrcGroups.lean`'s header for the correction it transcribes (slot 102 `mCctP`'s `CCT rb tb` fix is the other one; it does not appear in this file).

* `cctSum` 103 and `cctRec` 104: family `CCT` 96, constructors 6 and 7 of 8, recursor 105.
* `vaList` 139 and `vaR` 142: family `ValueAt` 133, constructors 5 and 8 of 9, recursor 143.
* Each has exactly one function-recursive field. Its inner telescope ends in a family application whose first index is compound.

`.lit` bytes are atoms here, not the machine's `xMem` expansion. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG.FunRecEntry

def ctorTypeLitCctSum : Expr Nat :=
  .pi (
.const 34 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 77 []) (
.bvar 6)) (
.bvar 4)) (
.pi (
.app (
.app (
.const 69 []) (
.bvar 7)) (
.bvar 6)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 83)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5)) (
.pi (
.pi (
.const 0 []) (
.const 8 [])) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 15)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 3) (
.bvar 2))) (
.bvar 1))))) (
.app (
.app (
.const 96 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 8))) (
.bvar 9))))))))))))))))

kernel_rfl_theorem memberCctSum_eq :
  mCctSum = ⟨.constructorM, 0, ctorTypeLitCctSum, none⟩

def domsLitCctSum : List (Expr Nat) :=
  [
.const 34 [],
.const 0 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
.app (
.app (
.const 77 []) (
.bvar 6)) (
.bvar 4),
.app (
.app (
.const 69 []) (
.bvar 7)) (
.bvar 6),
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5),
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 83)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5),
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5),
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5),
.pi (
.const 0 []) (
.const 8 []),
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 15)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 3) (
.bvar 2))) (
.bvar 1))))
]

def resLitCctSum : Expr Nat :=
  .app (
.app (
.const 96 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 8))) (
.bvar 9)

kernel_rfl_theorem peelCctSum :
  peelPis 15 mCctSum.mtype = some (domsLitCctSum, resLitCctSum)

def resIdxLitCctSum : List (Expr Nat) :=
  [
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 8),
.bvar 9
]

kernel_rfl_theorem resIdxCctSum : familyIdx 0 resLitCctSum = resIdxLitCctSum

abbrev funFieldPosCctSum : Nat := 14

def funFieldLitCctSum : Expr Nat :=
  .pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 15)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 3) (
.bvar 2))) (
.bvar 1))))

kernel_rfl_theorem funFieldCctSum :
  domsLitCctSum[funFieldPosCctSum]? = some funFieldLitCctSum

def innerDomsLitCctSum : List (Expr Nat) :=
  [
.const 0 [],
.const 4 [],
.app (
.app (
.app (
.const 88 []) (
.bvar 15)) (
.bvar 1)) (
.bvar 0)
]

def innerResLitCctSum : Expr Nat :=
  .app (
.app (
.const 96 []) (
.app (
.bvar 3) (
.bvar 2))) (
.bvar 1)

kernel_rfl_theorem innerPeelCctSum :
  peelPis 3 funFieldLitCctSum = some (innerDomsLitCctSum, innerResLitCctSum)

def innerIdxLitCctSum : List (Expr Nat) :=
  [
.app (
.bvar 3) (
.bvar 2),
.bvar 1
]

kernel_rfl_theorem innerIdxCctSum :
  familyIdx 0 innerResLitCctSum = innerIdxLitCctSum

def shapesLitCctSum : List FieldShape :=
  [.nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .recursive 3]

kernel_rfl_theorem shapesCctSum_eq : shapesCctSum = shapesLitCctSum

def minorLitCctSum : Expr Nat :=
  .pi (
.const 34 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 77 []) (
.bvar 6)) (
.bvar 4)) (
.pi (
.app (
.app (
.const 69 []) (
.bvar 7)) (
.bvar 6)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 83)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5)) (
.pi (
.pi (
.const 0 []) (
.const 8 [])) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 15)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 3) (
.bvar 2))) (
.bvar 1))))) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 16)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 24) (
.app (
.bvar 4) (
.bvar 2))) (
.bvar 1)) (
.app (
.app (
.app (
.bvar 3) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)))))) (
.app (
.app (
.app (
.bvar 22) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 9))) (
.bvar 10)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 103 []) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1))))))))))))))))))

kernel_rfl_theorem minorCctSum_eq : minorCctSum = minorLitCctSum

def eqDomsLitCctSum : List (Expr Nat) :=
  [
.pi (
.const 8 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 1)) (
.bvar 0)) (
.sort (.zero)))),
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.const 11 [])) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 2) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 1))) (
.const 11 [])) (
.app (
.app (
.const 97 []) (
.bvar 1)) (
.bvar 0)))),
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.const 12 [])) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 3) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 1))) (
.const 12 [])) (
.app (
.app (
.const 98 []) (
.bvar 1)) (
.bvar 0)))),
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.const 13 [])) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 4) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 1))) (
.const 13 [])) (
.app (
.app (
.const 99 []) (
.bvar 1)) (
.bvar 0)))),
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.const 14 [])) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 5) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 1))) (
.const 14 [])) (
.app (
.app (
.const 100 []) (
.bvar 1)) (
.bvar 0)))),
.pi (
.const 8 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 76)) (
.const 5 []))) (
.bvar 2)) (
.bvar 1)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 2)) (
.bvar 1)) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 5)) (
.bvar 4)) (
.pi (
.app (
.app (
.app (
.bvar 11) (
.bvar 6)) (
.bvar 5)) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 12) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 4))) (
.bvar 5)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 101 []) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)))))))))),
.pi (
.const 8 []) (
.pi (
.const 8 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 80)) (
.const 5 []))) (
.bvar 4)) (
.bvar 2)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 3)) (
.bvar 4)) (
.bvar 2)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 3)) (
.bvar 2)) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 9)) (
.bvar 7)) (
.pi (
.app (
.app (
.app (
.bvar 16) (
.bvar 10)) (
.bvar 8)) (
.bvar 0)) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 10)) (
.bvar 8)) (
.pi (
.app (
.app (
.app (
.bvar 18) (
.bvar 11)) (
.bvar 9)) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 19) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 7))) (
.bvar 8)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 102 []) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 1)))))))))))))))),
.pi (
.const 34 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 77 []) (
.bvar 6)) (
.bvar 4)) (
.pi (
.app (
.app (
.const 69 []) (
.bvar 7)) (
.bvar 6)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 83)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5)) (
.pi (
.pi (
.const 0 []) (
.const 8 [])) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 15)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 3) (
.bvar 2))) (
.bvar 1))))) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 16)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 24) (
.app (
.bvar 4) (
.bvar 2))) (
.bvar 1)) (
.app (
.app (
.app (
.bvar 3) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)))))) (
.app (
.app (
.app (
.bvar 22) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 9))) (
.bvar 10)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 103 []) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)))))))))))))))))),
.pi (
.const 38 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 84 []) (
.bvar 6)) (
.bvar 4)) (
.pi (
.app (
.app (
.const 73 []) (
.bvar 7)) (
.bvar 6)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5)) (
.pi (
.pi (
.const 0 []) (
.const 8 [])) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 16)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 4) (
.bvar 3))) (
.bvar 1)))))) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 17)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 26) (
.app (
.bvar 5) (
.bvar 3))) (
.bvar 1)) (
.app (
.app (
.app (
.app (
.bvar 4) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))) (
.app (
.app (
.app (
.bvar 23) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 9))) (
.bvar 10)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 104 []) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)))))))))))))))))),
.const 8 [],
.const 4 [],
.const 34 [],
.const 0 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
.app (
.app (
.const 77 []) (
.bvar 6)) (
.bvar 4),
.app (
.app (
.const 69 []) (
.bvar 7)) (
.bvar 6),
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5),
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 83)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5),
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5),
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5),
.pi (
.const 0 []) (
.const 8 []),
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 15)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 3) (
.bvar 2))) (
.bvar 1))))
]

def rhsLitCctSum : Expr Nat :=
  .app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.bvar 18) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.lam (
.const 0 []) (
.lam (
.const 4 []) (
.lam (
.app (
.app (
.app (
.const 88 []) (
.bvar 16)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 105 []) (
.bvar 28)) (
.bvar 27)) (
.bvar 26)) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.bvar 20)) (
.app (
.bvar 4) (
.bvar 2))) (
.bvar 1)) (
.app (
.app (
.app (
.bvar 3) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))

def lhsLitCctSum : Expr Nat :=
  .app (
.app (
.app (
.bvar 25) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 8))) (
.bvar 9)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 103 []) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))

def ctorTypeLitCctRec : Expr Nat :=
  .pi (
.const 38 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 84 []) (
.bvar 6)) (
.bvar 4)) (
.pi (
.app (
.app (
.const 73 []) (
.bvar 7)) (
.bvar 6)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5)) (
.pi (
.pi (
.const 0 []) (
.const 8 [])) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 16)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 4) (
.bvar 3))) (
.bvar 1)))))) (
.app (
.app (
.const 96 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 8))) (
.bvar 9))))))))))))))))

kernel_rfl_theorem memberCctRec_eq :
  mCctRec = ⟨.constructorM, 0, ctorTypeLitCctRec, none⟩

def domsLitCctRec : List (Expr Nat) :=
  [
.const 38 [],
.const 0 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
.app (
.app (
.const 84 []) (
.bvar 6)) (
.bvar 4),
.app (
.app (
.const 73 []) (
.bvar 7)) (
.bvar 6),
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5),
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5),
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5),
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5),
.pi (
.const 0 []) (
.const 8 []),
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 16)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 4) (
.bvar 3))) (
.bvar 1)))))
]

def resLitCctRec : Expr Nat :=
  .app (
.app (
.const 96 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 8))) (
.bvar 9)

kernel_rfl_theorem peelCctRec :
  peelPis 15 mCctRec.mtype = some (domsLitCctRec, resLitCctRec)

def resIdxLitCctRec : List (Expr Nat) :=
  [
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 8),
.bvar 9
]

kernel_rfl_theorem resIdxCctRec : familyIdx 0 resLitCctRec = resIdxLitCctRec

abbrev funFieldPosCctRec : Nat := 14

def funFieldLitCctRec : Expr Nat :=
  .pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 16)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 4) (
.bvar 3))) (
.bvar 1)))))

kernel_rfl_theorem funFieldCctRec :
  domsLitCctRec[funFieldPosCctRec]? = some funFieldLitCctRec

def innerDomsLitCctRec : List (Expr Nat) :=
  [
.const 0 [],
.const 4 [],
.const 4 [],
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 16)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)
]

def innerResLitCctRec : Expr Nat :=
  .app (
.app (
.const 96 []) (
.app (
.bvar 4) (
.bvar 3))) (
.bvar 1)

kernel_rfl_theorem innerPeelCctRec :
  peelPis 4 funFieldLitCctRec = some (innerDomsLitCctRec, innerResLitCctRec)

def innerIdxLitCctRec : List (Expr Nat) :=
  [
.app (
.bvar 4) (
.bvar 3),
.bvar 1
]

kernel_rfl_theorem innerIdxCctRec :
  familyIdx 0 innerResLitCctRec = innerIdxLitCctRec

def shapesLitCctRec : List FieldShape :=
  [.nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .recursive 4]

kernel_rfl_theorem shapesCctRec_eq : shapesCctRec = shapesLitCctRec

def minorLitCctRec : Expr Nat :=
  .pi (
.const 38 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 84 []) (
.bvar 6)) (
.bvar 4)) (
.pi (
.app (
.app (
.const 73 []) (
.bvar 7)) (
.bvar 6)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5)) (
.pi (
.pi (
.const 0 []) (
.const 8 [])) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 16)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 4) (
.bvar 3))) (
.bvar 1)))))) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 17)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 26) (
.app (
.bvar 5) (
.bvar 3))) (
.bvar 1)) (
.app (
.app (
.app (
.app (
.bvar 4) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))) (
.app (
.app (
.app (
.bvar 23) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 9))) (
.bvar 10)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 104 []) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1))))))))))))))))))

kernel_rfl_theorem minorCctRec_eq : minorCctRec = minorLitCctRec

def eqDomsLitCctRec : List (Expr Nat) :=
  [
.pi (
.const 8 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 1)) (
.bvar 0)) (
.sort (.zero)))),
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.const 11 [])) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 2) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 1))) (
.const 11 [])) (
.app (
.app (
.const 97 []) (
.bvar 1)) (
.bvar 0)))),
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.const 12 [])) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 3) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 1))) (
.const 12 [])) (
.app (
.app (
.const 98 []) (
.bvar 1)) (
.bvar 0)))),
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.const 13 [])) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 4) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 1))) (
.const 13 [])) (
.app (
.app (
.const 99 []) (
.bvar 1)) (
.bvar 0)))),
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.const 14 [])) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 5) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 1))) (
.const 14 [])) (
.app (
.app (
.const 100 []) (
.bvar 1)) (
.bvar 0)))),
.pi (
.const 8 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 76)) (
.const 5 []))) (
.bvar 2)) (
.bvar 1)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 2)) (
.bvar 1)) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 5)) (
.bvar 4)) (
.pi (
.app (
.app (
.app (
.bvar 11) (
.bvar 6)) (
.bvar 5)) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 12) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 4))) (
.bvar 5)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 101 []) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)))))))))),
.pi (
.const 8 []) (
.pi (
.const 8 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 80)) (
.const 5 []))) (
.bvar 4)) (
.bvar 2)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 3)) (
.bvar 4)) (
.bvar 2)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 3)) (
.bvar 2)) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 9)) (
.bvar 7)) (
.pi (
.app (
.app (
.app (
.bvar 16) (
.bvar 10)) (
.bvar 8)) (
.bvar 0)) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 10)) (
.bvar 8)) (
.pi (
.app (
.app (
.app (
.bvar 18) (
.bvar 11)) (
.bvar 9)) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 19) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 7))) (
.bvar 8)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 102 []) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 1)))))))))))))))),
.pi (
.const 34 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 77 []) (
.bvar 6)) (
.bvar 4)) (
.pi (
.app (
.app (
.const 69 []) (
.bvar 7)) (
.bvar 6)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 83)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5)) (
.pi (
.pi (
.const 0 []) (
.const 8 [])) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 15)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 3) (
.bvar 2))) (
.bvar 1))))) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 16)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 24) (
.app (
.bvar 4) (
.bvar 2))) (
.bvar 1)) (
.app (
.app (
.app (
.bvar 3) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)))))) (
.app (
.app (
.app (
.bvar 22) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 9))) (
.bvar 10)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 103 []) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)))))))))))))))))),
.pi (
.const 38 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 84 []) (
.bvar 6)) (
.bvar 4)) (
.pi (
.app (
.app (
.const 73 []) (
.bvar 7)) (
.bvar 6)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5)) (
.pi (
.pi (
.const 0 []) (
.const 8 [])) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 16)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 4) (
.bvar 3))) (
.bvar 1)))))) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 17)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 26) (
.app (
.bvar 5) (
.bvar 3))) (
.bvar 1)) (
.app (
.app (
.app (
.app (
.bvar 4) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))) (
.app (
.app (
.app (
.bvar 23) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 9))) (
.bvar 10)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 104 []) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)))))))))))))))))),
.const 8 [],
.const 4 [],
.const 38 [],
.const 0 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
.app (
.app (
.const 84 []) (
.bvar 6)) (
.bvar 4),
.app (
.app (
.const 73 []) (
.bvar 7)) (
.bvar 6),
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5),
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5),
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5),
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5),
.pi (
.const 0 []) (
.const 8 []),
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 16)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 4) (
.bvar 3))) (
.bvar 1)))))
]

def rhsLitCctRec : Expr Nat :=
  .app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.bvar 17) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.lam (
.const 0 []) (
.lam (
.const 4 []) (
.lam (
.const 4 []) (
.lam (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 17)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 105 []) (
.bvar 29)) (
.bvar 28)) (
.bvar 27)) (
.bvar 26)) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.app (
.bvar 5) (
.bvar 3))) (
.bvar 1)) (
.app (
.app (
.app (
.app (
.bvar 4) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)))))))

def lhsLitCctRec : Expr Nat :=
  .app (
.app (
.app (
.bvar 25) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 8))) (
.bvar 9)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 104 []) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))

def ctorTypeLitVaList : Expr Nat :=
  .pi (
.const 8 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 34 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 76)) (
.const 5 []))) (
.bvar 8)) (
.bvar 7)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 8)) (
.bvar 7)) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 11)) (
.bvar 10)) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 10)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.bvar 15)) (
.bvar 14)) (
.bvar 3))) (
.bvar 1))))) (
.pi (
.app (
.app (
.const 69 []) (
.bvar 9)) (
.bvar 8)) (
.pi (
.app (
.app (
.const 77 []) (
.bvar 10)) (
.bvar 6)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 10)) (
.bvar 8)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 76)) (
.const 5 []))) (
.bvar 9)) (
.bvar 10)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 11)) (
.bvar 9)) (
.bvar 8)) (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 15))) (
.bvar 16)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 101 []) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)))) (
.bvar 9))))))))))))))))))))

kernel_rfl_theorem memberVaList_eq :
  mVaList = ⟨.constructorM, 0, ctorTypeLitVaList, none⟩

def domsLitVaList : List (Expr Nat) :=
  [
.const 8 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 34 [],
.const 0 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 76)) (
.const 5 []))) (
.bvar 8)) (
.bvar 7),
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 8)) (
.bvar 7),
.app (
.app (
.const 96 []) (
.bvar 11)) (
.bvar 10),
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 10)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.bvar 15)) (
.bvar 14)) (
.bvar 3))) (
.bvar 1)))),
.app (
.app (
.const 69 []) (
.bvar 9)) (
.bvar 8),
.app (
.app (
.const 77 []) (
.bvar 10)) (
.bvar 6),
.app (
.app (
.const 58 []) (
.bvar 10)) (
.bvar 8),
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 76)) (
.const 5 []))) (
.bvar 9)) (
.bvar 10),
.app (
.app (
.app (
.const 46 []) (
.bvar 11)) (
.bvar 9)) (
.bvar 8)
]

def resLitVaList : Expr Nat :=
  .app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 15))) (
.bvar 16)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 101 []) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)))) (
.bvar 9)

kernel_rfl_theorem peelVaList :
  peelPis 19 mVaList.mtype = some (domsLitVaList, resLitVaList)

def resIdxLitVaList : List (Expr Nat) :=
  [
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 15))) (
.bvar 16)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 101 []) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)),
.bvar 9
]

kernel_rfl_theorem resIdxVaList : familyIdx 0 resLitVaList = resIdxLitVaList

abbrev funFieldPosVaList : Nat := 13

def funFieldLitVaList : Expr Nat :=
  .pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 10)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.bvar 15)) (
.bvar 14)) (
.bvar 3))) (
.bvar 1))))

kernel_rfl_theorem funFieldVaList :
  domsLitVaList[funFieldPosVaList]? = some funFieldLitVaList

def innerDomsLitVaList : List (Expr Nat) :=
  [
.const 0 [],
.const 4 [],
.app (
.app (
.app (
.const 88 []) (
.bvar 10)) (
.bvar 1)) (
.bvar 0)
]

def innerResLitVaList : Expr Nat :=
  .app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.bvar 15)) (
.bvar 14)) (
.bvar 3))) (
.bvar 1)

kernel_rfl_theorem innerPeelVaList :
  peelPis 3 funFieldLitVaList = some (innerDomsLitVaList, innerResLitVaList)

def innerIdxLitVaList : List (Expr Nat) :=
  [
.app (
.app (
.app (
.const 107 []) (
.bvar 15)) (
.bvar 14)) (
.bvar 3),
.bvar 1
]

kernel_rfl_theorem innerIdxVaList :
  familyIdx 0 innerResLitVaList = innerIdxLitVaList

def shapesLitVaList : List FieldShape :=
  [.nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .recursive 3, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive]

kernel_rfl_theorem shapesVaList_eq : shapesVaList = shapesLitVaList

def minorLitVaList : Expr Nat :=
  .pi (
.const 8 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 34 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 76)) (
.const 5 []))) (
.bvar 8)) (
.bvar 7)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 8)) (
.bvar 7)) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 11)) (
.bvar 10)) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 10)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.bvar 15)) (
.bvar 14)) (
.bvar 3))) (
.bvar 1))))) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 11)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 22) (
.app (
.app (
.app (
.const 107 []) (
.bvar 16)) (
.bvar 15)) (
.bvar 4))) (
.bvar 1)) (
.app (
.app (
.app (
.bvar 3) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)))))) (
.pi (
.app (
.app (
.const 69 []) (
.bvar 10)) (
.bvar 9)) (
.pi (
.app (
.app (
.const 77 []) (
.bvar 11)) (
.bvar 7)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 11)) (
.bvar 9)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 76)) (
.const 5 []))) (
.bvar 10)) (
.bvar 11)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 12)) (
.bvar 10)) (
.bvar 9)) (
.app (
.app (
.app (
.bvar 25) (
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 16))) (
.bvar 17)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 101 []) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)))) (
.bvar 10)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 139 []) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))))))))))))))))))

kernel_rfl_theorem minorVaList_eq : minorVaList = minorLitVaList

def eqDomsLitVaList : List (Expr Nat) :=
  [
.pi (
.const 106 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 133 []) (
.bvar 1)) (
.bvar 0)) (
.sort (.zero)))),
.pi (
.const 8 []) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 0)) (
.const 12 [])) (
.app (
.app (
.app (
.bvar 2) (
.app (
.app (
.app (
.const 107 []) (
.bvar 1)) (
.const 12 [])) (
.bvar 0))) (
.const 15 [])) (
.app (
.app (
.const 134 []) (
.bvar 1)) (
.bvar 0)))),
.pi (
.const 8 []) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 0)) (
.const 12 [])) (
.app (
.app (
.app (
.bvar 3) (
.app (
.app (
.app (
.const 107 []) (
.bvar 1)) (
.const 12 [])) (
.bvar 0))) (
.const 16 [])) (
.app (
.app (
.const 135 []) (
.bvar 1)) (
.bvar 0)))),
.pi (
.const 8 []) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 0)) (
.const 11 [])) (
.pi (
.const 30 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 61 []) (
.bvar 2)) (
.bvar 1)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 73)) (
.const 5 []))) (
.bvar 2)) (
.bvar 1)) (
.app (
.app (
.app (
.bvar 9) (
.app (
.app (
.app (
.const 107 []) (
.bvar 6)) (
.const 11 [])) (
.bvar 5))) (
.bvar 2)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 136 []) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))))),
.pi (
.const 8 []) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 0)) (
.const 13 [])) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 81 []) (
.bvar 2)) (
.bvar 1)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 84)) (
.const 5 []))) (
.bvar 2)) (
.bvar 1)) (
.app (
.app (
.app (
.bvar 10) (
.app (
.app (
.app (
.const 107 []) (
.bvar 6)) (
.const 13 [])) (
.bvar 5))) (
.bvar 2)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 137 []) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))))),
.pi (
.const 8 []) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 0)) (
.const 14 [])) (
.pi (
.const 4 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 65 []) (
.bvar 5)) (
.bvar 4)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 5)) (
.bvar 3)) (
.pi (
.app (
.app (
.const 125 []) (
.bvar 7)) (
.bvar 3)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 89)) (
.const 5 []))) (
.bvar 5)) (
.bvar 6)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 7)) (
.bvar 5)) (
.bvar 4)) (
.app (
.app (
.app (
.bvar 17) (
.app (
.app (
.app (
.const 107 []) (
.bvar 12)) (
.const 14 [])) (
.bvar 11))) (
.bvar 5)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 138 []) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))))))))))),
.pi (
.const 8 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 34 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 76)) (
.const 5 []))) (
.bvar 8)) (
.bvar 7)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 8)) (
.bvar 7)) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 11)) (
.bvar 10)) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 10)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.bvar 15)) (
.bvar 14)) (
.bvar 3))) (
.bvar 1))))) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 11)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 22) (
.app (
.app (
.app (
.const 107 []) (
.bvar 16)) (
.bvar 15)) (
.bvar 4))) (
.bvar 1)) (
.app (
.app (
.app (
.bvar 3) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)))))) (
.pi (
.app (
.app (
.const 69 []) (
.bvar 10)) (
.bvar 9)) (
.pi (
.app (
.app (
.const 77 []) (
.bvar 11)) (
.bvar 7)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 11)) (
.bvar 9)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 76)) (
.const 5 []))) (
.bvar 10)) (
.bvar 11)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 12)) (
.bvar 10)) (
.bvar 9)) (
.app (
.app (
.app (
.bvar 25) (
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 16))) (
.bvar 17)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 101 []) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)))) (
.bvar 10)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 139 []) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)))))))))))))))))))))),
.pi (
.const 8 []) (
.pi (
.const 8 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 80)) (
.const 5 []))) (
.bvar 8)) (
.bvar 6)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 7)) (
.bvar 8)) (
.bvar 6)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 7)) (
.bvar 6)) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 13)) (
.bvar 11)) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 13)) (
.bvar 11)) (
.pi (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.bvar 15)) (
.bvar 13)) (
.bvar 1))) (
.bvar 8)) (
.pi (
.app (
.app (
.app (
.bvar 23) (
.app (
.app (
.app (
.const 107 []) (
.bvar 16)) (
.bvar 14)) (
.bvar 2))) (
.bvar 9)) (
.bvar 0)) (
.pi (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.bvar 16)) (
.bvar 14)) (
.bvar 2))) (
.bvar 9)) (
.pi (
.app (
.app (
.app (
.bvar 25) (
.app (
.app (
.app (
.const 107 []) (
.bvar 17)) (
.bvar 15)) (
.bvar 3))) (
.bvar 10)) (
.bvar 0)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 80)) (
.const 5 []))) (
.bvar 12)) (
.bvar 10)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 11)) (
.bvar 12)) (
.bvar 10)) (
.app (
.app (
.app (
.bvar 28) (
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 15))) (
.bvar 16)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 102 []) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)))) (
.bvar 11)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 140 []) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 3)) (
.bvar 1)) (
.bvar 0)))))))))))))))))))))))),
.pi (
.const 34 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 77 []) (
.bvar 6)) (
.bvar 4)) (
.pi (
.app (
.app (
.const 69 []) (
.bvar 7)) (
.bvar 6)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 83)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5)) (
.pi (
.pi (
.const 0 []) (
.const 8 [])) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 15)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 3) (
.bvar 2))) (
.bvar 1))))) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 106 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 129 []) (
.bvar 20)) (
.bvar 5)) (
.bvar 3)) (
.pi (
.app (
.app (
.const 133 []) (
.bvar 4)) (
.bvar 3)) (
.pi (
.app (
.app (
.app (
.bvar 30) (
.bvar 5)) (
.bvar 4)) (
.bvar 0)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 8)) (
.bvar 7)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 74)) (
.const 5 []))) (
.bvar 8)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 7)) (
.bvar 5)) (
.app (
.app (
.app (
.bvar 34) (
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 20))) (
.bvar 21)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 103 []) (
.bvar 26)) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)))) (
.bvar 6)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 141 []) (
.bvar 26)) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))))))))))))))))))))))))),
.pi (
.const 38 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 84 []) (
.bvar 6)) (
.bvar 4)) (
.pi (
.app (
.app (
.const 73 []) (
.bvar 7)) (
.bvar 6)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5)) (
.pi (
.pi (
.const 0 []) (
.const 8 [])) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 16)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 4) (
.bvar 3))) (
.bvar 1)))))) (
.pi (
.const 34 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 22)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 9)) (
.bvar 4)) (
.bvar 0)) (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.app (
.bvar 12) (
.bvar 5))) (
.bvar 3)) (
.app (
.app (
.app (
.app (
.bvar 11) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)))) (
.bvar 1)))))))) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 23)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 10)) (
.bvar 4)) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 35) (
.app (
.app (
.app (
.const 107 []) (
.app (
.bvar 13) (
.bvar 5))) (
.bvar 3)) (
.app (
.app (
.app (
.app (
.bvar 12) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)))) (
.bvar 1)) (
.app (
.app (
.app (
.app (
.app (
.app (
.bvar 6) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))))) (
.pi (
.app (
.app (
.const 69 []) (
.bvar 6)) (
.bvar 20)) (
.pi (
.app (
.app (
.const 77 []) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 22)) (
.bvar 7)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 8)) (
.bvar 6)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 7)) (
.bvar 8)) (
.bvar 6)) (
.app (
.app (
.app (
.bvar 35) (
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 20))) (
.bvar 21)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 104 []) (
.bvar 26)) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)))) (
.bvar 7)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 142 []) (
.bvar 26)) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))))))))))))))))))))))))),
.const 106 [],
.const 4 [],
.const 8 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 34 [],
.const 0 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 76)) (
.const 5 []))) (
.bvar 8)) (
.bvar 7),
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 8)) (
.bvar 7),
.app (
.app (
.const 96 []) (
.bvar 11)) (
.bvar 10),
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 10)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.bvar 15)) (
.bvar 14)) (
.bvar 3))) (
.bvar 1)))),
.app (
.app (
.const 69 []) (
.bvar 9)) (
.bvar 8),
.app (
.app (
.const 77 []) (
.bvar 10)) (
.bvar 6),
.app (
.app (
.const 58 []) (
.bvar 10)) (
.bvar 8),
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 76)) (
.const 5 []))) (
.bvar 9)) (
.bvar 10),
.app (
.app (
.app (
.const 46 []) (
.bvar 11)) (
.bvar 9)) (
.bvar 8)
]

def rhsLitVaList : Expr Nat :=
  .app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.bvar 24) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.lam (
.const 0 []) (
.lam (
.const 4 []) (
.lam (
.app (
.app (
.app (
.const 88 []) (
.bvar 16)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 143 []) (
.bvar 33)) (
.bvar 32)) (
.bvar 31)) (
.bvar 30)) (
.bvar 29)) (
.bvar 28)) (
.bvar 27)) (
.bvar 26)) (
.bvar 25)) (
.bvar 24)) (
.app (
.app (
.app (
.const 107 []) (
.bvar 21)) (
.bvar 20)) (
.bvar 9))) (
.bvar 1)) (
.app (
.app (
.app (
.bvar 8) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)

def lhsLitVaList : Expr Nat :=
  .app (
.app (
.app (
.bvar 30) (
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 15))) (
.bvar 16)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 101 []) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)))) (
.bvar 9)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 139 []) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))

def ctorTypeLitVaR : Expr Nat :=
  .pi (
.const 38 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 84 []) (
.bvar 6)) (
.bvar 4)) (
.pi (
.app (
.app (
.const 73 []) (
.bvar 7)) (
.bvar 6)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5)) (
.pi (
.pi (
.const 0 []) (
.const 8 [])) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 16)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 4) (
.bvar 3))) (
.bvar 1)))))) (
.pi (
.const 34 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 22)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 9)) (
.bvar 4)) (
.bvar 0)) (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.app (
.bvar 12) (
.bvar 5))) (
.bvar 3)) (
.app (
.app (
.app (
.app (
.bvar 11) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)))) (
.bvar 1)))))))) (
.pi (
.app (
.app (
.const 69 []) (
.bvar 5)) (
.bvar 19)) (
.pi (
.app (
.app (
.const 77 []) (
.bvar 6)) (
.bvar 4)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 21)) (
.bvar 6)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 7)) (
.bvar 5)) (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 19))) (
.bvar 20)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 104 []) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)))) (
.bvar 6)))))))))))))))))))))))))))

kernel_rfl_theorem memberVaR_eq :
  mVaR = ⟨.constructorM, 0, ctorTypeLitVaR, none⟩

def domsLitVaR : List (Expr Nat) :=
  [
.const 38 [],
.const 0 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
.app (
.app (
.const 84 []) (
.bvar 6)) (
.bvar 4),
.app (
.app (
.const 73 []) (
.bvar 7)) (
.bvar 6),
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5),
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5),
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5),
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5),
.pi (
.const 0 []) (
.const 8 []),
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 16)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 4) (
.bvar 3))) (
.bvar 1))))),
.const 34 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 22)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 9)) (
.bvar 4)) (
.bvar 0)) (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.app (
.bvar 12) (
.bvar 5))) (
.bvar 3)) (
.app (
.app (
.app (
.app (
.bvar 11) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)))) (
.bvar 1))))))),
.app (
.app (
.const 69 []) (
.bvar 5)) (
.bvar 19),
.app (
.app (
.const 77 []) (
.bvar 6)) (
.bvar 4),
.app (
.app (
.const 58 []) (
.bvar 21)) (
.bvar 6),
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 7)) (
.bvar 5),
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 7)) (
.bvar 5)
]

def resLitVaR : Expr Nat :=
  .app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 19))) (
.bvar 20)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 104 []) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)))) (
.bvar 6)

kernel_rfl_theorem peelVaR :
  peelPis 26 mVaR.mtype = some (domsLitVaR, resLitVaR)

def resIdxLitVaR : List (Expr Nat) :=
  [
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 19))) (
.bvar 20)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 104 []) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)),
.bvar 6
]

kernel_rfl_theorem resIdxVaR : familyIdx 0 resLitVaR = resIdxLitVaR

abbrev funFieldPosVaR : Nat := 20

def funFieldLitVaR : Expr Nat :=
  .pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 22)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 9)) (
.bvar 4)) (
.bvar 0)) (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.app (
.bvar 12) (
.bvar 5))) (
.bvar 3)) (
.app (
.app (
.app (
.app (
.bvar 11) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)))) (
.bvar 1)))))))

kernel_rfl_theorem funFieldVaR :
  domsLitVaR[funFieldPosVaR]? = some funFieldLitVaR

def innerDomsLitVaR : List (Expr Nat) :=
  [
.const 0 [],
.const 4 [],
.const 4 [],
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 22)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0),
.const 4 [],
.app (
.app (
.app (
.const 88 []) (
.bvar 9)) (
.bvar 4)) (
.bvar 0)
]

def innerResLitVaR : Expr Nat :=
  .app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.app (
.bvar 12) (
.bvar 5))) (
.bvar 3)) (
.app (
.app (
.app (
.app (
.bvar 11) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)))) (
.bvar 1)

kernel_rfl_theorem innerPeelVaR :
  peelPis 6 funFieldLitVaR = some (innerDomsLitVaR, innerResLitVaR)

def innerIdxLitVaR : List (Expr Nat) :=
  [
.app (
.app (
.app (
.const 107 []) (
.app (
.bvar 12) (
.bvar 5))) (
.bvar 3)) (
.app (
.app (
.app (
.app (
.bvar 11) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)),
.bvar 1
]

kernel_rfl_theorem innerIdxVaR :
  familyIdx 0 innerResLitVaR = innerIdxLitVaR

def shapesLitVaR : List FieldShape :=
  [.nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .recursive 6, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive, .nonrecursive]

kernel_rfl_theorem shapesVaR_eq : shapesVaR = shapesLitVaR

def minorLitVaR : Expr Nat :=
  .pi (
.const 38 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 84 []) (
.bvar 6)) (
.bvar 4)) (
.pi (
.app (
.app (
.const 73 []) (
.bvar 7)) (
.bvar 6)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5)) (
.pi (
.pi (
.const 0 []) (
.const 8 [])) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 16)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 4) (
.bvar 3))) (
.bvar 1)))))) (
.pi (
.const 34 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 22)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 9)) (
.bvar 4)) (
.bvar 0)) (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.app (
.bvar 12) (
.bvar 5))) (
.bvar 3)) (
.app (
.app (
.app (
.app (
.bvar 11) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)))) (
.bvar 1)))))))) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 23)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 10)) (
.bvar 4)) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 35) (
.app (
.app (
.app (
.const 107 []) (
.app (
.bvar 13) (
.bvar 5))) (
.bvar 3)) (
.app (
.app (
.app (
.app (
.bvar 12) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)))) (
.bvar 1)) (
.app (
.app (
.app (
.app (
.app (
.app (
.bvar 6) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))))) (
.pi (
.app (
.app (
.const 69 []) (
.bvar 6)) (
.bvar 20)) (
.pi (
.app (
.app (
.const 77 []) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 22)) (
.bvar 7)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 8)) (
.bvar 6)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 7)) (
.bvar 8)) (
.bvar 6)) (
.app (
.app (
.app (
.bvar 35) (
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 20))) (
.bvar 21)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 104 []) (
.bvar 26)) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)))) (
.bvar 7)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 142 []) (
.bvar 26)) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)))))))))))))))))))))))))))))

kernel_rfl_theorem minorVaR_eq : minorVaR = minorLitVaR

def eqDomsLitVaR : List (Expr Nat) :=
  [
.pi (
.const 106 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 133 []) (
.bvar 1)) (
.bvar 0)) (
.sort (.zero)))),
.pi (
.const 8 []) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 0)) (
.const 12 [])) (
.app (
.app (
.app (
.bvar 2) (
.app (
.app (
.app (
.const 107 []) (
.bvar 1)) (
.const 12 [])) (
.bvar 0))) (
.const 15 [])) (
.app (
.app (
.const 134 []) (
.bvar 1)) (
.bvar 0)))),
.pi (
.const 8 []) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 0)) (
.const 12 [])) (
.app (
.app (
.app (
.bvar 3) (
.app (
.app (
.app (
.const 107 []) (
.bvar 1)) (
.const 12 [])) (
.bvar 0))) (
.const 16 [])) (
.app (
.app (
.const 135 []) (
.bvar 1)) (
.bvar 0)))),
.pi (
.const 8 []) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 0)) (
.const 11 [])) (
.pi (
.const 30 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 61 []) (
.bvar 2)) (
.bvar 1)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 73)) (
.const 5 []))) (
.bvar 2)) (
.bvar 1)) (
.app (
.app (
.app (
.bvar 9) (
.app (
.app (
.app (
.const 107 []) (
.bvar 6)) (
.const 11 [])) (
.bvar 5))) (
.bvar 2)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 136 []) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))))),
.pi (
.const 8 []) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 0)) (
.const 13 [])) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 81 []) (
.bvar 2)) (
.bvar 1)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 84)) (
.const 5 []))) (
.bvar 2)) (
.bvar 1)) (
.app (
.app (
.app (
.bvar 10) (
.app (
.app (
.app (
.const 107 []) (
.bvar 6)) (
.const 13 [])) (
.bvar 5))) (
.bvar 2)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 137 []) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))))),
.pi (
.const 8 []) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 0)) (
.const 14 [])) (
.pi (
.const 4 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 65 []) (
.bvar 5)) (
.bvar 4)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 5)) (
.bvar 3)) (
.pi (
.app (
.app (
.const 125 []) (
.bvar 7)) (
.bvar 3)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 89)) (
.const 5 []))) (
.bvar 5)) (
.bvar 6)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 7)) (
.bvar 5)) (
.bvar 4)) (
.app (
.app (
.app (
.bvar 17) (
.app (
.app (
.app (
.const 107 []) (
.bvar 12)) (
.const 14 [])) (
.bvar 11))) (
.bvar 5)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 138 []) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))))))))))),
.pi (
.const 8 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 34 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 76)) (
.const 5 []))) (
.bvar 8)) (
.bvar 7)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 8)) (
.bvar 7)) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 11)) (
.bvar 10)) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 10)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.bvar 15)) (
.bvar 14)) (
.bvar 3))) (
.bvar 1))))) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 11)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 22) (
.app (
.app (
.app (
.const 107 []) (
.bvar 16)) (
.bvar 15)) (
.bvar 4))) (
.bvar 1)) (
.app (
.app (
.app (
.bvar 3) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)))))) (
.pi (
.app (
.app (
.const 69 []) (
.bvar 10)) (
.bvar 9)) (
.pi (
.app (
.app (
.const 77 []) (
.bvar 11)) (
.bvar 7)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 11)) (
.bvar 9)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 76)) (
.const 5 []))) (
.bvar 10)) (
.bvar 11)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 12)) (
.bvar 10)) (
.bvar 9)) (
.app (
.app (
.app (
.bvar 25) (
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 16))) (
.bvar 17)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 101 []) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)))) (
.bvar 10)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 139 []) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)))))))))))))))))))))),
.pi (
.const 8 []) (
.pi (
.const 8 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 80)) (
.const 5 []))) (
.bvar 8)) (
.bvar 6)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 7)) (
.bvar 8)) (
.bvar 6)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 7)) (
.bvar 6)) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 13)) (
.bvar 11)) (
.pi (
.app (
.app (
.const 96 []) (
.bvar 13)) (
.bvar 11)) (
.pi (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.bvar 15)) (
.bvar 13)) (
.bvar 1))) (
.bvar 8)) (
.pi (
.app (
.app (
.app (
.bvar 23) (
.app (
.app (
.app (
.const 107 []) (
.bvar 16)) (
.bvar 14)) (
.bvar 2))) (
.bvar 9)) (
.bvar 0)) (
.pi (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.bvar 16)) (
.bvar 14)) (
.bvar 2))) (
.bvar 9)) (
.pi (
.app (
.app (
.app (
.bvar 25) (
.app (
.app (
.app (
.const 107 []) (
.bvar 17)) (
.bvar 15)) (
.bvar 3))) (
.bvar 10)) (
.bvar 0)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 80)) (
.const 5 []))) (
.bvar 12)) (
.bvar 10)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 11)) (
.bvar 12)) (
.bvar 10)) (
.app (
.app (
.app (
.bvar 28) (
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 15))) (
.bvar 16)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 102 []) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)))) (
.bvar 11)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 140 []) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 3)) (
.bvar 1)) (
.bvar 0)))))))))))))))))))))))),
.pi (
.const 34 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 77 []) (
.bvar 6)) (
.bvar 4)) (
.pi (
.app (
.app (
.const 69 []) (
.bvar 7)) (
.bvar 6)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 83)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5)) (
.pi (
.pi (
.const 0 []) (
.const 8 [])) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 15)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 3) (
.bvar 2))) (
.bvar 1))))) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 106 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 129 []) (
.bvar 20)) (
.bvar 5)) (
.bvar 3)) (
.pi (
.app (
.app (
.const 133 []) (
.bvar 4)) (
.bvar 3)) (
.pi (
.app (
.app (
.app (
.bvar 30) (
.bvar 5)) (
.bvar 4)) (
.bvar 0)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 8)) (
.bvar 7)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 74)) (
.const 5 []))) (
.bvar 8)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 7)) (
.bvar 5)) (
.app (
.app (
.app (
.bvar 34) (
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 20))) (
.bvar 21)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 103 []) (
.bvar 26)) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)))) (
.bvar 6)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 141 []) (
.bvar 26)) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))))))))))))))))))))))))),
.pi (
.const 38 []) (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.const 84 []) (
.bvar 6)) (
.bvar 4)) (
.pi (
.app (
.app (
.const 73 []) (
.bvar 7)) (
.bvar 6)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5)) (
.pi (
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5)) (
.pi (
.pi (
.const 0 []) (
.const 8 [])) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 16)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 4) (
.bvar 3))) (
.bvar 1)))))) (
.pi (
.const 34 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 22)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 9)) (
.bvar 4)) (
.bvar 0)) (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.app (
.bvar 12) (
.bvar 5))) (
.bvar 3)) (
.app (
.app (
.app (
.app (
.bvar 11) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)))) (
.bvar 1)))))))) (
.pi (
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 23)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 10)) (
.bvar 4)) (
.bvar 0)) (
.app (
.app (
.app (
.bvar 35) (
.app (
.app (
.app (
.const 107 []) (
.app (
.bvar 13) (
.bvar 5))) (
.bvar 3)) (
.app (
.app (
.app (
.app (
.bvar 12) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)))) (
.bvar 1)) (
.app (
.app (
.app (
.app (
.app (
.app (
.bvar 6) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))))) (
.pi (
.app (
.app (
.const 69 []) (
.bvar 6)) (
.bvar 20)) (
.pi (
.app (
.app (
.const 77 []) (
.bvar 7)) (
.bvar 5)) (
.pi (
.app (
.app (
.const 58 []) (
.bvar 22)) (
.bvar 7)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 8)) (
.bvar 6)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 7)) (
.bvar 8)) (
.bvar 6)) (
.app (
.app (
.app (
.bvar 35) (
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 20))) (
.bvar 21)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 104 []) (
.bvar 26)) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)))) (
.bvar 7)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 142 []) (
.bvar 26)) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))))))))))))))))))))))))),
.const 106 [],
.const 4 [],
.const 38 [],
.const 0 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
.app (
.app (
.const 84 []) (
.bvar 6)) (
.bvar 4),
.app (
.app (
.const 73 []) (
.bvar 7)) (
.bvar 6),
.app (
.app (
.const 58 []) (
.bvar 7)) (
.bvar 5),
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 6)) (
.bvar 5),
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 8)) (
.bvar 5),
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 6)) (
.bvar 5),
.pi (
.const 0 []) (
.const 8 []),
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 16)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.app (
.app (
.const 96 []) (
.app (
.bvar 4) (
.bvar 3))) (
.bvar 1))))),
.const 34 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
.pi (
.const 0 []) (
.pi (
.const 4 []) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 22)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.pi (
.const 4 []) (
.pi (
.app (
.app (
.app (
.const 88 []) (
.bvar 9)) (
.bvar 4)) (
.bvar 0)) (
.app (
.app (
.const 133 []) (
.app (
.app (
.app (
.const 107 []) (
.app (
.bvar 12) (
.bvar 5))) (
.bvar 3)) (
.app (
.app (
.app (
.app (
.bvar 11) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)))) (
.bvar 1))))))),
.app (
.app (
.const 69 []) (
.bvar 5)) (
.bvar 19),
.app (
.app (
.const 77 []) (
.bvar 6)) (
.bvar 4),
.app (
.app (
.const 58 []) (
.bvar 21)) (
.bvar 6),
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 82)) (
.const 5 []))) (
.bvar 7)) (
.bvar 5),
.app (
.app (
.app (
.const 46 []) (
.bvar 6)) (
.bvar 7)) (
.bvar 5)
]

def rhsLitVaR : Expr Nat :=
  .app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.bvar 28) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.lam (
.const 0 []) (
.lam (
.const 4 []) (
.lam (
.const 4 []) (
.lam (
.app (
.app (
.app (
.app (
.const 92 []) (
.bvar 28)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)) (
.lam (
.const 4 []) (
.lam (
.app (
.app (
.app (
.const 88 []) (
.bvar 15)) (
.bvar 4)) (
.bvar 0)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 143 []) (
.bvar 43)) (
.bvar 42)) (
.bvar 41)) (
.bvar 40)) (
.bvar 39)) (
.bvar 38)) (
.bvar 37)) (
.bvar 36)) (
.bvar 35)) (
.bvar 34)) (
.app (
.app (
.app (
.const 107 []) (
.app (
.bvar 18) (
.bvar 5))) (
.bvar 3)) (
.app (
.app (
.app (
.app (
.bvar 17) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)))) (
.bvar 1)) (
.app (
.app (
.app (
.app (
.app (
.app (
.bvar 11) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)))))))))) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)

def lhsLitVaR : Expr Nat :=
  .app (
.app (
.app (
.bvar 37) (
.app (
.app (
.app (
.const 107 []) (
.app (
.app (
.app (
.const 9 []) (
.lit 3)) (
.lit 16)) (
.bvar 19))) (
.bvar 20)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 104 []) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)))) (
.bvar 6)) (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.app (
.const 142 []) (
.bvar 25)) (
.bvar 24)) (
.bvar 23)) (
.bvar 22)) (
.bvar 21)) (
.bvar 20)) (
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 12)) (
.bvar 11)) (
.bvar 10)) (
.bvar 9)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)) (
.bvar 3)) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))

#print axioms memberCctSum_eq
#print axioms peelCctSum
#print axioms resIdxCctSum
#print axioms funFieldCctSum
#print axioms innerPeelCctSum
#print axioms innerIdxCctSum
#print axioms shapesCctSum_eq
#print axioms minorCctSum_eq
#print axioms memberCctRec_eq
#print axioms peelCctRec
#print axioms resIdxCctRec
#print axioms funFieldCctRec
#print axioms innerPeelCctRec
#print axioms innerIdxCctRec
#print axioms shapesCctRec_eq
#print axioms minorCctRec_eq
#print axioms memberVaList_eq
#print axioms peelVaList
#print axioms resIdxVaList
#print axioms funFieldVaList
#print axioms innerPeelVaList
#print axioms innerIdxVaList
#print axioms shapesVaList_eq
#print axioms minorVaList_eq
#print axioms memberVaR_eq
#print axioms peelVaR
#print axioms resIdxVaR
#print axioms funFieldVaR
#print axioms innerPeelVaR
#print axioms innerIdxVaR
#print axioms shapesVaR_eq
#print axioms minorVaR_eq

end Rcic.Scm.SrcG.FunRecEntry

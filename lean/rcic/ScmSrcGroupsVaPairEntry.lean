import rcic.ScmSrcGroups
import rcic.ScmSrcGroupsKernelRfl

/-! Real input for the idxwalk work: ValueAt's `vaPair` at slot 140, exactly as `idxValueAt_false` used it.

Base: `devin/k3c-groups` @ `cefd14e16e`. This module imports only `rcic.ScmSrcGroups` (the 168-slot table, which brings `ScmSrcGroupsOld`, `RcicSrcEnvV1` and main's kernel) and `rcic.ScmSrcGroupsKernelRfl`. It states no walk or admission verdict, so it compiles with or without the idxwalk change. By `rfl`, its environments coincide with `envPre 143` and `extendEnv (envPre 143) 143 recValueAt` (`ScmSrcGroupsVaPairEntryCheck`).

* The group: family `ValueAt` at 133 (no parameters, two indices), constructors 134–142, `vaPair` = constructor 6 at 140 (20 fields), recursor `recValueAt` at 143 (motive, 9 minors, 2 indices, major).
* Literal unfoldings of the three members against their real definitions (`renameMember πmap Old.mVaPair`, `renameMember πmap SrcTV.mVA`, `policyRecursorType famViewValueAt …`), with their peeled telescopes.
* `vaPair`'s two direct recursive fields, 16 and 17, with their index lists. The first index is the compound `mkBound …` that defect 2 is about.
* `mkWit` is `idxValueAt_false`'s witness constructor (`ScmSrcGroupsLK1Pin.lean` lines 11–74 at `cefd14e16e`), verbatim except that `fields` and `preMajor` are parameters. `junkWitness?` is the instance `idxValueAt_false` used: 20 `sort 0` fields and 12 `sort 0` pre-major entries.

`.lit` bytes are atoms here: these are the declarative objects, not the machine's `xMem` expansion. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG.VaPairEntry

abbrev famRef : Nat := 133
abbrev ctorRef : Nat := 140
abbrev recRef : Nat := 143
abbrev ctorIdx : Nat := 6
abbrev nparams : Nat := 0
abbrev nindices : Nat := 2
abbrev nMinors : Nat := 9
abbrev nfields : Nat := 20

def famTypeLit : Expr Nat :=
  .pi (
.const 106 []) (
.pi (
.const 4 []) (
.sort (.zero)))

def ctorTypeLit : Expr Nat :=
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
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 80)) (
.const 5 []))) (
.bvar 10)) (
.bvar 8)) (
.pi (
.app (
.app (
.app (
.const 46 []) (
.bvar 9)) (
.bvar 10)) (
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
.bvar 13))) (
.bvar 14)) (
.app (
.app (
.app (
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
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)))) (
.bvar 9)))))))))))))))))))))

def recTypeLit : Expr Nat :=
  .pi (
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
.sort (.zero))))) (
.pi (
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
.bvar 0))))) (
.pi (
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
.bvar 0))))) (
.pi (
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
.bvar 0)))))))))) (
.pi (
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
.bvar 0)))))))))) (
.pi (
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
.bvar 0)))))))))))))))) (
.pi (
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
.bvar 0))))))))))))))))))))))) (
.pi (
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
.bvar 0))))))))))))))))))))))))) (
.pi (
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
.bvar 0)))))))))))))))))))))))))))))) (
.pi (
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
.bvar 0)))))))))))))))))))))))))))))) (
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
.app (
.app (
.app (
.bvar 12) (
.bvar 2)) (
.bvar 1)) (
.bvar 0))))))))))))))

kernel_rfl_theorem famMember_eq :
  mValueAt = ⟨.inductiveM, 0, famTypeLit, none⟩
kernel_rfl_theorem ctorMember_eq :
  mVaPair = ⟨.constructorM, 0, ctorTypeLit, none⟩
kernel_rfl_theorem recMember_eq :
  recValueAt = ⟨.recursorM, 0, recTypeLit, none⟩

def famDomsLit : List (Expr Nat) :=
  [
.const 106 [],
.const 4 []
]

def famResLit : Expr Nat :=
  .sort (.zero)

kernel_rfl_theorem fam_peel :
  peelPis 2 mValueAt.mtype = some (famDomsLit, famResLit)

def ctorDomsLit : List (Expr Nat) :=
  [
.const 8 [],
.const 8 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
.const 4 [],
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
.lit 80)) (
.const 5 []))) (
.bvar 8)) (
.bvar 6),
.app (
.app (
.app (
.const 46 []) (
.bvar 7)) (
.bvar 8)) (
.bvar 6),
.app (
.app (
.app (
.app (
.const 23 []) (
.lit 3)) (
.lit 16)) (
.bvar 7)) (
.bvar 6),
.app (
.app (
.const 96 []) (
.bvar 13)) (
.bvar 11),
.app (
.app (
.const 96 []) (
.bvar 13)) (
.bvar 11),
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
.bvar 8),
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
.bvar 8),
.app (
.app (
.app (
.const 46 []) (
.app (
.app (
.const 6 []) (
.lit 80)) (
.const 5 []))) (
.bvar 10)) (
.bvar 8),
.app (
.app (
.app (
.const 46 []) (
.bvar 9)) (
.bvar 10)) (
.bvar 8)
]

def ctorResLit : Expr Nat :=
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
.bvar 13))) (
.bvar 14)) (
.app (
.app (
.app (
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
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)))) (
.bvar 9)

kernel_rfl_theorem ctor_peel :
  peelPis 20 mVaPair.mtype = some (ctorDomsLit, ctorResLit)

def recDomsLit : List (Expr Nat) :=
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
.app (
.app (
.const 133 []) (
.bvar 1)) (
.bvar 0)
]

def recBodyLit : Expr Nat :=
  .app (
.app (
.app (
.bvar 12) (
.bvar 2)) (
.bvar 1)) (
.bvar 0)

kernel_rfl_theorem rec_peel :
  peelPis 13 recValueAt.mtype = some (recDomsLit, recBodyLit)

theorem piCounts :
  piCount mValueAt.mtype = 2 ∧ piCount mVaPair.mtype = 20 ∧
    piCount recValueAt.mtype = 13 := by decide

def ctorKindsLit : List RecKind :=
  [.plain, .plain, .plain, .plain, .plain, .plain, .plain, .plain, .plain, .plain, .plain, .plain, .plain, .plain, .plain, .plain, .directRec, .directRec, .plain, .plain]

def recField16IdxLit : List (Expr Nat) :=
  [
.app (
.app (
.app (
.const 107 []) (
.bvar 15)) (
.bvar 13)) (
.bvar 1),
.bvar 8
]

def recField17IdxLit : List (Expr Nat) :=
  [
.app (
.app (
.app (
.const 107 []) (
.bvar 15)) (
.bvar 13)) (
.bvar 1),
.bvar 8
]

def ctorResIdxLit : List (Expr Nat) :=
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
.bvar 13))) (
.bvar 14)) (
.app (
.app (
.app (
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
.bvar 19)) (
.bvar 18)) (
.bvar 17)) (
.bvar 16)) (
.bvar 15)) (
.bvar 14)) (
.bvar 13)) (
.bvar 8)) (
.bvar 7)) (
.bvar 6)) (
.bvar 5)) (
.bvar 4)),
.bvar 9
]

kernel_rfl_theorem ctor_kinds :
  analyzeFields 133 ctorDomsLit = some ctorKindsLit

theorem recField_idx :
  familyIdx 0 (ctorDomsLit.getD 16 (.sort .zero)) = recField16IdxLit ∧
    familyIdx 0 (ctorDomsLit.getD 17 (.sort .zero)) = recField17IdxLit := by decide

kernel_rfl_theorem ctorRes_idx : familyIdx 0 ctorResLit = ctorResIdxLit
kernel_rfl_theorem ctor_instLevels :
  instantiateLevels [] mVaPair.mtype = mVaPair.mtype
kernel_rfl_theorem ctor_closed : lift 0 1 mVaPair.mtype = mVaPair.mtype
kernel_rfl_theorem rec_closed : lift 0 1 recValueAt.mtype = recValueAt.mtype

def prefixEnv : ResolvedEnv :=
  (srcMembersG.take 143).foldl (fun E (r, m) => extendEnv E r m) emptyEnv

def extEnv : ResolvedEnv := extendEnv prefixEnv 143 recValueAt

kernel_rfl_theorem prefix_fam : prefixEnv.members 133 = some mValueAt
kernel_rfl_theorem prefix_ctor : prefixEnv.members 140 = some mVaPair
kernel_rfl_theorem prefix_fresh : prefixEnv.members 143 = none
kernel_rfl_theorem ext_fam : extEnv.members 133 = some mValueAt
kernel_rfl_theorem ext_ctor : extEnv.members 140 = some mVaPair
kernel_rfl_theorem ext_rec : extEnv.members 143 = some recValueAt

theorem ext_extends :
    ∀ r m, prefixEnv.members r = some m → extEnv.members r = some m := by
  intro r m hmem
  by_cases h143 : r = 143
  · subst h143
    have hn := prefix_fresh
    rw [hn] at hmem
    nomatch hmem
  · show (if r = 143 then some recValueAt else prefixEnv.members r) = some m
    rw [if_neg h143]
    exact hmem

def mkWit (E : ResolvedEnv) (cm fm : CheckedMember)
    (hrec : E.members 143 = some recValueAt)
    (hctor : E.members 140 = some cm) (hctorK : cm.mclass = .constructorM)
    (hfam : E.members 133 = some fm) (hfamK : fm.mclass = .inductiveM)
    (hcl : lift 0 1 cm.mtype = cm.mtype)
    (hrcl : lift 0 1 recValueAt.mtype = recValueAt.mtype)
    (fields preMajor : List (Expr Nat)) :
    Option {w : IotaWitness E // w.recRef = 143 ∧ w.recMember = recValueAt} :=
  match hp : peelPis (0 + fields.length) cm.mtype with
  | none => none
  | some ⟨cd, cr⟩ =>
  match hk : analyzeFields 133 (cd.drop 0) with
  | none => none
  | some kinds =>
  match hr : peelPis (0 + 1 + 9 + 2 + 1) recValueAt.mtype with
  | none => none
  | some ⟨rd, rb⟩ =>
  match hm : preMajor[0 + 1 + 6]? with
  | none => none
  | some minor =>
  match hca : applyTel (preMajor.take 0) (instantiateLevels [] cm.mtype) with
  | none => none
  | some ctap =>
      if h : (0 + fields.length = piCount cm.mtype)
          ∧ (0 + 2 = piCount fm.mtype)
          ∧ (0 + 1 + 9 + 2 + 1 = piCount recValueAt.mtype)
          ∧ kinds.length = fields.length
          ∧ isFamilyApp 133 cr = true
          ∧ rb = foldApps (.bvar (9 + 2 + 1))
              ((List.range 2).reverse.map (fun i => Expr.bvar (i + 1)) ++
                [Expr.bvar 0])
          ∧ rd[0 + 1 + 9 + 2]? = some
              (foldApps (.const 133 ((List.range fm.arity).map Level.param))
                ((List.range 0).reverse.map
                  (fun i => Expr.bvar (i + 2 + 9 + 1)) ++
                 (List.range 2).reverse.map (fun i => Expr.bvar i)))
          ∧ ([] : List Level).length = recValueAt.arity
          ∧ isPiTel kinds.length ctap = true
          ∧ directRecConstHead kinds ctap = true
          ∧ resultConstHead kinds ctap = true
          ∧ preMajor.length = 0 + 1 + 9 + 2
          ∧ 6 < 9 ∧ 140 = 133 + 1 + 6 ∧ 143 = 133 + 1 + 9 then
        let ⟨hnpar, hnidx, hnmin, hlen, hfa, hrb, hmaj, hls, hct, hfm,
            hrt, hpre, hidx, hci, hri⟩ := h
        let w : IotaWitness E :=
          { recRef := 143, ctorRef := 140, ls := [], lsC := [],
                 recMember := recValueAt, ctorMember := cm,
                 hrec, hctor, hrecK := rfl, hctorK,
                 preMajor, fields, ctorParams := [], kinds, minor,
                 hlen, familyRef := 133, famMember := fm, hfam, hfamK,
                 nparams := 0, nindices := 2, nMinors := 9, ctorIdx := 6,
                 hctorParams := rfl, hnpar, hnidx, hnmin, hidx,
                 hctorIdx := hci, hrecIdx := hri, hpre, hminor := hm,
                 ctorDoms := cd, ctorResult := cr, hpeel := hp,
                 hfamApp := hfa, hkinds := hk,
                 recDoms := rd, recBody := rb, hpeelRec := hr,
                 hrecBody := hrb, hmajorTy := hmaj,
                 hrecClosed := hrcl, hctorClosed := hcl,
                 hlsLen := hls, ctorAfterParams := ctap,
                 hctorAfter := hca, hctorTel := hct,
                 hfamTel := hfm, hresTel := hrt }
        some ⟨w, rfl, rfl⟩
      else none

def junkFields : List (Expr Nat) := List.replicate 20 (.sort .zero)
def junkPreMajor : List (Expr Nat) := List.replicate 12 (.sort .zero)

def junkWitness? :=
  mkWit extEnv mVaPair mValueAt ext_rec ext_ctor rfl ext_fam rfl ctor_closed rec_closed
    junkFields junkPreMajor

kernel_rfl_theorem junkWitness_isSome : junkWitness?.isSome = true
kernel_rfl_theorem junkWitness_data :
  junkWitness?.map (fun p => (p.1.fields, p.1.preMajor, p.1.kinds, p.1.ctorDoms,
      p.1.ctorResult, p.1.ctorAfterParams, p.1.recDoms, p.1.recBody, p.1.minor)) =
    some (junkFields, junkPreMajor, ctorKindsLit, ctorDomsLit, ctorResLit, ctorTypeLit,
      recDomsLit, recBodyLit, .sort .zero)

#print axioms famMember_eq
#print axioms ctorMember_eq
#print axioms recMember_eq
#print axioms fam_peel
#print axioms ctor_peel
#print axioms rec_peel
#print axioms piCounts
#print axioms ctor_kinds
#print axioms recField_idx
#print axioms ctorRes_idx
#print axioms ctor_instLevels
#print axioms ctor_closed
#print axioms rec_closed
#print axioms prefix_fam
#print axioms prefix_ctor
#print axioms prefix_fresh
#print axioms ext_fam
#print axioms ext_ctor
#print axioms ext_rec
#print axioms ext_extends
#print axioms junkWitness_isSome
#print axioms junkWitness_data

end Rcic.Scm.SrcG.VaPairEntry

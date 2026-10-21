/-
RCIC 07 §3 — G2-S1: `EnvWfT` admission of the support blocks
(`RcicG2Objects`), each block admitted on its own at a concrete base.

`blockEnv E ms` extends `E` by the block's members in list order — exactly
`EnvWfT.group`'s `(f, fm) :: ctors ++ [(rr, rm)]` admission order. Four of
the eight support blocks ARE already-admitted fixtures, member for member
(each coincidence is `rfl`, so a drift in either side breaks it):

* `trueMembersAt 0`  = `trueEnvU`'s members  (`RcicTypedGroupPins`)
* `falseMembersAt 0` = `falseEnvU`'s members (`RcicTypedGroupPins`)
* `andMembersAt 0`   = `andEnvU`'s members   (`RcicTypedGroupPins`)
* `eqMembersAt 63`   = `eqEnvT`'s members    (`RcicPinEqEraseWf`)

so their admission is the fixture's `EnvWfT`, transported. `Bool`, `Or`,
`Pos`, `BNat` and the `SV<d>` blocks are admitted in their own modules.
Admission at the refined env's symbolic base (`supBase`) is G2-S3.
-/
import rcic.RcicG2Objects
import rcic.RcicTypedGroupPins
import rcic.RcicPinEqEraseWf

namespace Rcic.G2
open Rcic.Declarative

/-- `E` extended by `ms` in list order. -/
def blockEnv (E : ResolvedEnv) (ms : List (Nat × CheckedMember)) : ResolvedEnv :=
  ms.foldl (fun E rm => extendEnv E rm.1 rm.2) E

theorem trueMembersAt_fixture :
    trueMembersAt 0 = [(0, trueFamMember), (1, trueIntroMember), (2, trueRecMemberU)] := rfl

theorem falseMembersAt_fixture :
    falseMembersAt 0 = [(0, falseFamMember), (1, falseRecMemberU)] := rfl

theorem andMembersAt_fixture :
    andMembersAt 0 = [(0, andFamMember), (1, andIntroMember), (2, andRecMemberU)] := rfl

theorem eqMembersAt_fixture :
    eqMembersAt 63 = [(63, eqFamT), (64, eqReflT), (65, eqRecT)] := rfl

theorem trueBlockEnv_eq : blockEnv emptyEnv (trueMembersAt 0) = trueEnvU := rfl
theorem falseBlockEnv_eq : blockEnv emptyEnv (falseMembersAt 0) = falseEnvU := rfl
theorem andBlockEnv_eq : blockEnv emptyEnv (andMembersAt 0) = andEnvU := rfl
theorem eqBlockEnv_eq : blockEnv emptyEnv (eqMembersAt 63) = eqEnvT := rfl

/-- `True`'s block admits. -/
def trueBlockWfT : EnvWfT (blockEnv emptyEnv (trueMembersAt 0)) := trueEnvUWfT

/-- `False`'s block admits. -/
def falseBlockWfT : EnvWfT (blockEnv emptyEnv (falseMembersAt 0)) := falseEnvUWfT

/-- `And`'s block admits. -/
def andBlockWfT : EnvWfT (blockEnv emptyEnv (andMembersAt 0)) := andEnvUWfT

/-- `Eq`'s block admits. -/
def eqBlockWfT : EnvWfT (blockEnv emptyEnv (eqMembersAt 63)) := pinEqGroupWfT

end Rcic.G2

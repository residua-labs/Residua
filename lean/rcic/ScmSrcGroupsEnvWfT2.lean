import rcic.ScmSrcGroupsEnvWfT1

/-! `EnvWfT` for srcEnvG slots in this file's range. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

kernel_rfl_theorem tyB11 : (sortTyAtC (envPre 11) mBytesI.arity 96 [] mBytesI.mtype).isSome = true
def tyT11 : Σ u, HasTyT (envPre 11) mBytesI.arity [] mBytesI.mtype (.sort u) :=
  (sortTyAtC (envPre 11) mBytesI.arity 96 [] mBytesI.mtype).get tyB11
kernel_rfl_theorem bdB11 : (tyAtC (envPre 11) mBytesI.arity 96 [] (mBytesI.body.getD (.sort .zero)) mBytesI.mtype).isSome = true
def bdT11 : HasTyT (envPre 11) mBytesI.arity [] (mBytesI.body.getD (.sort .zero)) mBytesI.mtype :=
  (tyAtC (envPre 11) mBytesI.arity 96 [] (mBytesI.body.getD (.sort .zero)) mBytesI.mtype).get bdB11
def wft12 : EnvWfT (envPre 12) :=
  wfTOfExtend (r := 11) (m := mBytesI) (by decide) rfl
    (.definition (envPre 11) 11 mBytesI.mtype (mBytesI.body.getD (.sort .zero)) _ wft11 rfl
      tyT11.2 bdT11 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB12 : (sortTyAtC (envPre 12) mBytesB.arity 96 [] mBytesB.mtype).isSome = true
def tyT12 : Σ u, HasTyT (envPre 12) mBytesB.arity [] mBytesB.mtype (.sort u) :=
  (sortTyAtC (envPre 12) mBytesB.arity 96 [] mBytesB.mtype).get tyB12
kernel_rfl_theorem bdB12 : (tyAtC (envPre 12) mBytesB.arity 96 [] (mBytesB.body.getD (.sort .zero)) mBytesB.mtype).isSome = true
def bdT12 : HasTyT (envPre 12) mBytesB.arity [] (mBytesB.body.getD (.sort .zero)) mBytesB.mtype :=
  (tyAtC (envPre 12) mBytesB.arity 96 [] (mBytesB.body.getD (.sort .zero)) mBytesB.mtype).get bdB12
def wft13 : EnvWfT (envPre 13) :=
  wfTOfExtend (r := 12) (m := mBytesB) (by decide) rfl
    (.definition (envPre 12) 12 mBytesB.mtype (mBytesB.body.getD (.sort .zero)) _ wft12 rfl
      tyT12.2 bdT12 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB13 : (sortTyAtC (envPre 13) mBytesS.arity 96 [] mBytesS.mtype).isSome = true
def tyT13 : Σ u, HasTyT (envPre 13) mBytesS.arity [] mBytesS.mtype (.sort u) :=
  (sortTyAtC (envPre 13) mBytesS.arity 96 [] mBytesS.mtype).get tyB13
kernel_rfl_theorem bdB13 : (tyAtC (envPre 13) mBytesS.arity 96 [] (mBytesS.body.getD (.sort .zero)) mBytesS.mtype).isSome = true
def bdT13 : HasTyT (envPre 13) mBytesS.arity [] (mBytesS.body.getD (.sort .zero)) mBytesS.mtype :=
  (tyAtC (envPre 13) mBytesS.arity 96 [] (mBytesS.body.getD (.sort .zero)) mBytesS.mtype).get bdB13
def wft14 : EnvWfT (envPre 14) :=
  wfTOfExtend (r := 13) (m := mBytesS) (by decide) rfl
    (.definition (envPre 13) 13 mBytesS.mtype (mBytesS.body.getD (.sort .zero)) _ wft13 rfl
      tyT13.2 bdT13 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB14 : (sortTyAtC (envPre 14) mBytesY.arity 96 [] mBytesY.mtype).isSome = true
def tyT14 : Σ u, HasTyT (envPre 14) mBytesY.arity [] mBytesY.mtype (.sort u) :=
  (sortTyAtC (envPre 14) mBytesY.arity 96 [] mBytesY.mtype).get tyB14
kernel_rfl_theorem bdB14 : (tyAtC (envPre 14) mBytesY.arity 96 [] (mBytesY.body.getD (.sort .zero)) mBytesY.mtype).isSome = true
def bdT14 : HasTyT (envPre 14) mBytesY.arity [] (mBytesY.body.getD (.sort .zero)) mBytesY.mtype :=
  (tyAtC (envPre 14) mBytesY.arity 96 [] (mBytesY.body.getD (.sort .zero)) mBytesY.mtype).get bdB14
def wft15 : EnvWfT (envPre 15) :=
  wfTOfExtend (r := 14) (m := mBytesY) (by decide) rfl
    (.definition (envPre 14) 14 mBytesY.mtype (mBytesY.body.getD (.sort .zero)) _ wft14 rfl
      tyT14.2 bdT14 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB15 : (sortTyAtC (envPre 15) mBytesB0.arity 96 [] mBytesB0.mtype).isSome = true
def tyT15 : Σ u, HasTyT (envPre 15) mBytesB0.arity [] mBytesB0.mtype (.sort u) :=
  (sortTyAtC (envPre 15) mBytesB0.arity 96 [] mBytesB0.mtype).get tyB15
kernel_rfl_theorem bdB15 : (tyAtC (envPre 15) mBytesB0.arity 96 [] (mBytesB0.body.getD (.sort .zero)) mBytesB0.mtype).isSome = true
def bdT15 : HasTyT (envPre 15) mBytesB0.arity [] (mBytesB0.body.getD (.sort .zero)) mBytesB0.mtype :=
  (tyAtC (envPre 15) mBytesB0.arity 96 [] (mBytesB0.body.getD (.sort .zero)) mBytesB0.mtype).get bdB15
def wft16 : EnvWfT (envPre 16) :=
  wfTOfExtend (r := 15) (m := mBytesB0) (by decide) rfl
    (.definition (envPre 15) 15 mBytesB0.mtype (mBytesB0.body.getD (.sort .zero)) _ wft15 rfl
      tyT15.2 bdT15 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB16 : (sortTyAtC (envPre 16) mBytesB1.arity 96 [] mBytesB1.mtype).isSome = true
def tyT16 : Σ u, HasTyT (envPre 16) mBytesB1.arity [] mBytesB1.mtype (.sort u) :=
  (sortTyAtC (envPre 16) mBytesB1.arity 96 [] mBytesB1.mtype).get tyB16
kernel_rfl_theorem bdB16 : (tyAtC (envPre 16) mBytesB1.arity 96 [] (mBytesB1.body.getD (.sort .zero)) mBytesB1.mtype).isSome = true
def bdT16 : HasTyT (envPre 16) mBytesB1.arity [] (mBytesB1.body.getD (.sort .zero)) mBytesB1.mtype :=
  (tyAtC (envPre 16) mBytesB1.arity 96 [] (mBytesB1.body.getD (.sort .zero)) mBytesB1.mtype).get bdB16
def wft17 : EnvWfT (envPre 17) :=
  wfTOfExtend (r := 16) (m := mBytesB1) (by decide) rfl
    (.definition (envPre 16) 16 mBytesB1.mtype (mBytesB1.body.getD (.sort .zero)) _ wft16 rfl
      tyT16.2 bdT16 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB17 : (sortTyAtC (envPre 17) mDigestI.arity 96 [] mDigestI.mtype).isSome = true
def tyT17 : Σ u, HasTyT (envPre 17) mDigestI.arity [] mDigestI.mtype (.sort u) :=
  (sortTyAtC (envPre 17) mDigestI.arity 96 [] mDigestI.mtype).get tyB17
kernel_rfl_theorem bdB17 : (tyAtC (envPre 17) mDigestI.arity 96 [] (mDigestI.body.getD (.sort .zero)) mDigestI.mtype).isSome = true
def bdT17 : HasTyT (envPre 17) mDigestI.arity [] (mDigestI.body.getD (.sort .zero)) mDigestI.mtype :=
  (tyAtC (envPre 17) mDigestI.arity 96 [] (mDigestI.body.getD (.sort .zero)) mDigestI.mtype).get bdB17
def wft18 : EnvWfT (envPre 18) :=
  wfTOfExtend (r := 17) (m := mDigestI) (by decide) rfl
    (.definition (envPre 17) 17 mDigestI.mtype (mDigestI.body.getD (.sort .zero)) _ wft17 rfl
      tyT17.2 bdT17 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB18 : (sortTyAtC (envPre 18) mDigestB.arity 96 [] mDigestB.mtype).isSome = true
def tyT18 : Σ u, HasTyT (envPre 18) mDigestB.arity [] mDigestB.mtype (.sort u) :=
  (sortTyAtC (envPre 18) mDigestB.arity 96 [] mDigestB.mtype).get tyB18
kernel_rfl_theorem bdB18 : (tyAtC (envPre 18) mDigestB.arity 96 [] (mDigestB.body.getD (.sort .zero)) mDigestB.mtype).isSome = true
def bdT18 : HasTyT (envPre 18) mDigestB.arity [] (mDigestB.body.getD (.sort .zero)) mDigestB.mtype :=
  (tyAtC (envPre 18) mDigestB.arity 96 [] (mDigestB.body.getD (.sort .zero)) mDigestB.mtype).get bdB18
def wft19 : EnvWfT (envPre 19) :=
  wfTOfExtend (r := 18) (m := mDigestB) (by decide) rfl
    (.definition (envPre 18) 18 mDigestB.mtype (mDigestB.body.getD (.sort .zero)) _ wft18 rfl
      tyT18.2 bdT18 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB19 : (sortTyAtC (envPre 19) mDigestS.arity 96 [] mDigestS.mtype).isSome = true
def tyT19 : Σ u, HasTyT (envPre 19) mDigestS.arity [] mDigestS.mtype (.sort u) :=
  (sortTyAtC (envPre 19) mDigestS.arity 96 [] mDigestS.mtype).get tyB19
kernel_rfl_theorem bdB19 : (tyAtC (envPre 19) mDigestS.arity 96 [] (mDigestS.body.getD (.sort .zero)) mDigestS.mtype).isSome = true
def bdT19 : HasTyT (envPre 19) mDigestS.arity [] (mDigestS.body.getD (.sort .zero)) mDigestS.mtype :=
  (tyAtC (envPre 19) mDigestS.arity 96 [] (mDigestS.body.getD (.sort .zero)) mDigestS.mtype).get bdB19
def wft20 : EnvWfT (envPre 20) :=
  wfTOfExtend (r := 19) (m := mDigestS) (by decide) rfl
    (.definition (envPre 19) 19 mDigestS.mtype (mDigestS.body.getD (.sort .zero)) _ wft19 rfl
      tyT19.2 bdT19 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB20 : (sortTyAtC (envPre 20) mDigestY.arity 96 [] mDigestY.mtype).isSome = true
def tyT20 : Σ u, HasTyT (envPre 20) mDigestY.arity [] mDigestY.mtype (.sort u) :=
  (sortTyAtC (envPre 20) mDigestY.arity 96 [] mDigestY.mtype).get tyB20
kernel_rfl_theorem bdB20 : (tyAtC (envPre 20) mDigestY.arity 96 [] (mDigestY.body.getD (.sort .zero)) mDigestY.mtype).isSome = true
def bdT20 : HasTyT (envPre 20) mDigestY.arity [] (mDigestY.body.getD (.sort .zero)) mDigestY.mtype :=
  (tyAtC (envPre 20) mDigestY.arity 96 [] (mDigestY.body.getD (.sort .zero)) mDigestY.mtype).get bdB20
def wft21 : EnvWfT (envPre 21) :=
  wfTOfExtend (r := 20) (m := mDigestY) (by decide) rfl
    (.definition (envPre 20) 20 mDigestY.mtype (mDigestY.body.getD (.sort .zero)) _ wft20 rfl
      tyT20.2 bdT20 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB21 : (sortTyAtC (envPre 21) mBytesLB.arity 96 [] mBytesLB.mtype).isSome = true
def tyT21 : Σ u, HasTyT (envPre 21) mBytesLB.arity [] mBytesLB.mtype (.sort u) :=
  (sortTyAtC (envPre 21) mBytesLB.arity 96 [] mBytesLB.mtype).get tyB21
kernel_rfl_theorem bdB21 : (tyAtC (envPre 21) mBytesLB.arity 96 [] (mBytesLB.body.getD (.sort .zero)) mBytesLB.mtype).isSome = true
def bdT21 : HasTyT (envPre 21) mBytesLB.arity [] (mBytesLB.body.getD (.sort .zero)) mBytesLB.mtype :=
  (tyAtC (envPre 21) mBytesLB.arity 96 [] (mBytesLB.body.getD (.sort .zero)) mBytesLB.mtype).get bdB21
def wft22 : EnvWfT (envPre 22) :=
  wfTOfExtend (r := 21) (m := mBytesLB) (by decide) rfl
    (.definition (envPre 21) 21 mBytesLB.mtype (mBytesLB.body.getD (.sort .zero)) _ wft21 rfl
      tyT21.2 bdT21 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB22 : (sortTyAtC (envPre 22) mDigestLB.arity 96 [] mDigestLB.mtype).isSome = true
def tyT22 : Σ u, HasTyT (envPre 22) mDigestLB.arity [] mDigestLB.mtype (.sort u) :=
  (sortTyAtC (envPre 22) mDigestLB.arity 96 [] mDigestLB.mtype).get tyB22
kernel_rfl_theorem bdB22 : (tyAtC (envPre 22) mDigestLB.arity 96 [] (mDigestLB.body.getD (.sort .zero)) mDigestLB.mtype).isSome = true
def bdT22 : HasTyT (envPre 22) mDigestLB.arity [] (mDigestLB.body.getD (.sort .zero)) mDigestLB.mtype :=
  (tyAtC (envPre 22) mDigestLB.arity 96 [] (mDigestLB.body.getD (.sort .zero)) mDigestLB.mtype).get bdB22
def wft23 : EnvWfT (envPre 23) :=
  wfTOfExtend (r := 22) (m := mDigestLB) (by decide) rfl
    (.definition (envPre 22) 22 mDigestLB.mtype (mDigestLB.body.getD (.sort .zero)) _ wft22 rfl
      tyT22.2 bdT22 (fun _ => rfl) (fun _ => rfl) rfl rfl)

end Rcic.Scm.SrcG

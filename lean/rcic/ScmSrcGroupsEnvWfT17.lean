import rcic.ScmSrcGroupsEnvWfT16

/-! `EnvWfT` for srcEnvG slots in this file's range. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

kernel_rfl_theorem tyB159 : (tyAtC (envPre 159) mNthBNilVa.arity 96 [] mNthBNilVa.mtype (.sort .zero)).isSome = true
def tyT159 : HasTyT (envPre 159) mNthBNilVa.arity [] mNthBNilVa.mtype (.sort .zero) :=
  (tyAtC (envPre 159) mNthBNilVa.arity 96 [] mNthBNilVa.mtype (.sort .zero)).get tyB159
/- DEFERRED COMPOSITION (slot 159 `srcNthBTyT`): this is the chain's only
   open premise — a `HasTyT (envPre 159) 0 [] …` hypothesis of exactly the
   type `Rcic.Declarative.srcNthBTyT` proves in PR #6205, and it is closed
   downstream in one line as PR #6225's `envWfT_srcEnvG`. Not a wall:
   `convAt?` carries an ι arm (#6205's shared `iotaBetaStep?` selector —
   `iotaStepWith?` on a recursor-on-constructor redex, else `betaStepWith?`
   on a λ-headed application; on `none` it falls through to the
   application-congruence and literal arms), so the checker never refuses
   here. The measured residual is a kernel whnf recursion bound on
   extracting the conversion derivation (RcicTypedConvIotaPins,
   KERNEL-SHAPE HONESTY) — which is why the premise rides as a hypothesis
   rather than being recomputed in-file. -/
def wft160 (srcNthBTyT : HasTyT (envPre 159) 0 [] (mNthBNilVa.body.getD (.sort .zero)) mNthBNilVa.mtype) : EnvWfT (envPre 160) :=
  wfTOfExtend (r := 159) (m := mNthBNilVa) (by decide) rfl
    (.thm (envPre 159) 159 mNthBNilVa.mtype (mNthBNilVa.body.getD (.sort .zero)) wft159 rfl
      tyT159 srcNthBTyT (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB160 : (tyAtC (envPre 160) mVLBNil.arity 96 [] mVLBNil.mtype (.sort .zero)).isSome = true
def tyT160 : HasTyT (envPre 160) mVLBNil.arity [] mVLBNil.mtype (.sort .zero) :=
  (tyAtC (envPre 160) mVLBNil.arity 96 [] mVLBNil.mtype (.sort .zero)).get tyB160
kernel_rfl_theorem bdB160 : (tyAtC (envPre 160) mVLBNil.arity 96 [] (mVLBNil.body.getD (.sort .zero)) mVLBNil.mtype).isSome = true
def bdT160 : HasTyT (envPre 160) mVLBNil.arity [] (mVLBNil.body.getD (.sort .zero)) mVLBNil.mtype :=
  (tyAtC (envPre 160) mVLBNil.arity 96 [] (mVLBNil.body.getD (.sort .zero)) mVLBNil.mtype).get bdB160
def wft161 (srcNthBTyT : HasTyT (envPre 159) 0 [] (mNthBNilVa.body.getD (.sort .zero)) mNthBNilVa.mtype) : EnvWfT (envPre 161) :=
  wfTOfExtend (r := 160) (m := mVLBNil) (by decide) rfl
    (.thm (envPre 160) 160 mVLBNil.mtype (mVLBNil.body.getD (.sort .zero)) (wft160 srcNthBTyT) rfl
      tyT160 bdT160 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB161 : (tyAtC (envPre 161) mLt510.arity 96 [] mLt510.mtype (.sort .zero)).isSome = true
def tyT161 : HasTyT (envPre 161) mLt510.arity [] mLt510.mtype (.sort .zero) :=
  (tyAtC (envPre 161) mLt510.arity 96 [] mLt510.mtype (.sort .zero)).get tyB161
kernel_rfl_theorem bdB161 : (tyAtC (envPre 161) mLt510.arity 96 [] (mLt510.body.getD (.sort .zero)) mLt510.mtype).isSome = true
def bdT161 : HasTyT (envPre 161) mLt510.arity [] (mLt510.body.getD (.sort .zero)) mLt510.mtype :=
  (tyAtC (envPre 161) mLt510.arity 96 [] (mLt510.body.getD (.sort .zero)) mLt510.mtype).get bdB161
def wft162 (srcNthBTyT : HasTyT (envPre 159) 0 [] (mNthBNilVa.body.getD (.sort .zero)) mNthBNilVa.mtype) : EnvWfT (envPre 162) :=
  wfTOfExtend (r := 161) (m := mLt510) (by decide) rfl
    (.thm (envPre 161) 161 mLt510.mtype (mLt510.body.getD (.sort .zero)) (wft161 srcNthBTyT) rfl
      tyT161 bdT161 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB162 : (tyAtC (envPre 162) mNd5.arity 96 [] mNd5.mtype (.sort .zero)).isSome = true
def tyT162 : HasTyT (envPre 162) mNd5.arity [] mNd5.mtype (.sort .zero) :=
  (tyAtC (envPre 162) mNd5.arity 96 [] mNd5.mtype (.sort .zero)).get tyB162
kernel_rfl_theorem bdB162 : (tyAtC (envPre 162) mNd5.arity 96 [] (mNd5.body.getD (.sort .zero)) mNd5.mtype).isSome = true
def bdT162 : HasTyT (envPre 162) mNd5.arity [] (mNd5.body.getD (.sort .zero)) mNd5.mtype :=
  (tyAtC (envPre 162) mNd5.arity 96 [] (mNd5.body.getD (.sort .zero)) mNd5.mtype).get bdB162
def wft163 (srcNthBTyT : HasTyT (envPre 159) 0 [] (mNthBNilVa.body.getD (.sort .zero)) mNthBNilVa.mtype) : EnvWfT (envPre 163) :=
  wfTOfExtend (r := 162) (m := mNd5) (by decide) rfl
    (.thm (envPre 162) 162 mNd5.mtype (mNd5.body.getD (.sort .zero)) (wft162 srcNthBTyT) rfl
      tyT162 bdT162 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB163 : (tyAtC (envPre 163) mBc53S.arity 96 [] mBc53S.mtype (.sort .zero)).isSome = true
def tyT163 : HasTyT (envPre 163) mBc53S.arity [] mBc53S.mtype (.sort .zero) :=
  (tyAtC (envPre 163) mBc53S.arity 96 [] mBc53S.mtype (.sort .zero)).get tyB163
kernel_rfl_theorem bdB163 : (tyAtC (envPre 163) mBc53S.arity 96 [] (mBc53S.body.getD (.sort .zero)) mBc53S.mtype).isSome = true
def bdT163 : HasTyT (envPre 163) mBc53S.arity [] (mBc53S.body.getD (.sort .zero)) mBc53S.mtype :=
  (tyAtC (envPre 163) mBc53S.arity 96 [] (mBc53S.body.getD (.sort .zero)) mBc53S.mtype).get bdB163
def wft164 (srcNthBTyT : HasTyT (envPre 159) 0 [] (mNthBNilVa.body.getD (.sort .zero)) mNthBNilVa.mtype) : EnvWfT (envPre 164) :=
  wfTOfExtend (r := 163) (m := mBc53S) (by decide) rfl
    (.thm (envPre 163) 163 mBc53S.mtype (mBc53S.body.getD (.sort .zero)) (wft163 srcNthBTyT) rfl
      tyT163 bdT163 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB164 : (tyAtC (envPre 164) mNea5.arity 96 [] mNea5.mtype (.sort .zero)).isSome = true
def tyT164 : HasTyT (envPre 164) mNea5.arity [] mNea5.mtype (.sort .zero) :=
  (tyAtC (envPre 164) mNea5.arity 96 [] mNea5.mtype (.sort .zero)).get tyB164
kernel_rfl_theorem bdB164 : (tyAtC (envPre 164) mNea5.arity 96 [] (mNea5.body.getD (.sort .zero)) mNea5.mtype).isSome = true
def bdT164 : HasTyT (envPre 164) mNea5.arity [] (mNea5.body.getD (.sort .zero)) mNea5.mtype :=
  (tyAtC (envPre 164) mNea5.arity 96 [] (mNea5.body.getD (.sort .zero)) mNea5.mtype).get bdB164
def wft165 (srcNthBTyT : HasTyT (envPre 159) 0 [] (mNthBNilVa.body.getD (.sort .zero)) mNthBNilVa.mtype) : EnvWfT (envPre 165) :=
  wfTOfExtend (r := 164) (m := mNea5) (by decide) rfl
    (.thm (envPre 164) 164 mNea5.mtype (mNea5.body.getD (.sort .zero)) (wft164 srcNthBTyT) rfl
      tyT164 bdT164 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB165 : (tyAtC (envPre 165) mIeaP5.arity 96 [] mIeaP5.mtype (.sort .zero)).isSome = true
def tyT165 : HasTyT (envPre 165) mIeaP5.arity [] mIeaP5.mtype (.sort .zero) :=
  (tyAtC (envPre 165) mIeaP5.arity 96 [] mIeaP5.mtype (.sort .zero)).get tyB165
kernel_rfl_theorem bdB165 : (tyAtC (envPre 165) mIeaP5.arity 96 [] (mIeaP5.body.getD (.sort .zero)) mIeaP5.mtype).isSome = true
def bdT165 : HasTyT (envPre 165) mIeaP5.arity [] (mIeaP5.body.getD (.sort .zero)) mIeaP5.mtype :=
  (tyAtC (envPre 165) mIeaP5.arity 96 [] (mIeaP5.body.getD (.sort .zero)) mIeaP5.mtype).get bdB165
def wft166 (srcNthBTyT : HasTyT (envPre 159) 0 [] (mNthBNilVa.body.getD (.sort .zero)) mNthBNilVa.mtype) : EnvWfT (envPre 166) :=
  wfTOfExtend (r := 165) (m := mIeaP5) (by decide) rfl
    (.thm (envPre 165) 165 mIeaP5.mtype (mIeaP5.body.getD (.sort .zero)) (wft165 srcNthBTyT) rfl
      tyT165 bdT165 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB166 : (tyAtC (envPre 166) mBcI5.arity 96 [] mBcI5.mtype (.sort .zero)).isSome = true
def tyT166 : HasTyT (envPre 166) mBcI5.arity [] mBcI5.mtype (.sort .zero) :=
  (tyAtC (envPre 166) mBcI5.arity 96 [] mBcI5.mtype (.sort .zero)).get tyB166
kernel_rfl_theorem bdB166 : (tyAtC (envPre 166) mBcI5.arity 96 [] (mBcI5.body.getD (.sort .zero)) mBcI5.mtype).isSome = true
def bdT166 : HasTyT (envPre 166) mBcI5.arity [] (mBcI5.body.getD (.sort .zero)) mBcI5.mtype :=
  (tyAtC (envPre 166) mBcI5.arity 96 [] (mBcI5.body.getD (.sort .zero)) mBcI5.mtype).get bdB166
def wft167 (srcNthBTyT : HasTyT (envPre 159) 0 [] (mNthBNilVa.body.getD (.sort .zero)) mNthBNilVa.mtype) : EnvWfT (envPre 167) :=
  wfTOfExtend (r := 166) (m := mBcI5) (by decide) rfl
    (.thm (envPre 166) 166 mBcI5.mtype (mBcI5.body.getD (.sort .zero)) (wft166 srcNthBTyT) rfl
      tyT166 bdT166 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB167 : (tyAtC (envPre 167) mVI5.arity 96 [] mVI5.mtype (.sort .zero)).isSome = true
def tyT167 : HasTyT (envPre 167) mVI5.arity [] mVI5.mtype (.sort .zero) :=
  (tyAtC (envPre 167) mVI5.arity 96 [] mVI5.mtype (.sort .zero)).get tyB167
kernel_rfl_theorem bdB167 : (tyAtC (envPre 167) mVI5.arity 96 [] (mVI5.body.getD (.sort .zero)) mVI5.mtype).isSome = true
def bdT167 : HasTyT (envPre 167) mVI5.arity [] (mVI5.body.getD (.sort .zero)) mVI5.mtype :=
  (tyAtC (envPre 167) mVI5.arity 96 [] (mVI5.body.getD (.sort .zero)) mVI5.mtype).get bdB167
def wft168 (srcNthBTyT : HasTyT (envPre 159) 0 [] (mNthBNilVa.body.getD (.sort .zero)) mNthBNilVa.mtype) : EnvWfT (envPre 168) :=
  wfTOfExtend (r := 167) (m := mVI5) (by decide) rfl
    (.thm (envPre 167) 167 mVI5.mtype (mVI5.body.getD (.sort .zero)) (wft167 srcNthBTyT) rfl
      tyT167 bdT167 (fun _ => rfl) (fun _ => rfl) rfl rfl)

end Rcic.Scm.SrcG

import rcic.ScmSrcGroupsEnvWfT12

/-! `EnvWfT` for srcEnvG slots in this file's range. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

kernel_rfl_theorem tyB109 : (sortTyAtC (envPre 109) mI64Ref.arity 96 [] mI64Ref.mtype).isSome = true
def tyT109 : Σ u, HasTyT (envPre 109) mI64Ref.arity [] mI64Ref.mtype (.sort u) :=
  (sortTyAtC (envPre 109) mI64Ref.arity 96 [] mI64Ref.mtype).get tyB109
kernel_rfl_theorem bdB109 : (tyAtC (envPre 109) mI64Ref.arity 96 [] (mI64Ref.body.getD (.sort .zero)) mI64Ref.mtype).isSome = true
def bdT109 : HasTyT (envPre 109) mI64Ref.arity [] (mI64Ref.body.getD (.sort .zero)) mI64Ref.mtype :=
  (tyAtC (envPre 109) mI64Ref.arity 96 [] (mI64Ref.body.getD (.sort .zero)) mI64Ref.mtype).get bdB109
def wft110 : EnvWfT (envPre 110) :=
  wfTOfExtend (r := 109) (m := mI64Ref) (by decide) rfl
    (.definition (envPre 109) 109 mI64Ref.mtype (mI64Ref.body.getD (.sort .zero)) _ wft109 rfl
      tyT109.2 bdT109 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB110 : (sortTyAtC (envPre 110) mBoolRef.arity 96 [] mBoolRef.mtype).isSome = true
def tyT110 : Σ u, HasTyT (envPre 110) mBoolRef.arity [] mBoolRef.mtype (.sort u) :=
  (sortTyAtC (envPre 110) mBoolRef.arity 96 [] mBoolRef.mtype).get tyB110
kernel_rfl_theorem bdB110 : (tyAtC (envPre 110) mBoolRef.arity 96 [] (mBoolRef.body.getD (.sort .zero)) mBoolRef.mtype).isSome = true
def bdT110 : HasTyT (envPre 110) mBoolRef.arity [] (mBoolRef.body.getD (.sort .zero)) mBoolRef.mtype :=
  (tyAtC (envPre 110) mBoolRef.arity 96 [] (mBoolRef.body.getD (.sort .zero)) mBoolRef.mtype).get bdB110
def wft111 : EnvWfT (envPre 111) :=
  wfTOfExtend (r := 110) (m := mBoolRef) (by decide) rfl
    (.definition (envPre 110) 110 mBoolRef.mtype (mBoolRef.body.getD (.sort .zero)) _ wft110 rfl
      tyT110.2 bdT110 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB111 : (sortTyAtC (envPre 111) mStrRef.arity 96 [] mStrRef.mtype).isSome = true
def tyT111 : Σ u, HasTyT (envPre 111) mStrRef.arity [] mStrRef.mtype (.sort u) :=
  (sortTyAtC (envPre 111) mStrRef.arity 96 [] mStrRef.mtype).get tyB111
kernel_rfl_theorem bdB111 : (tyAtC (envPre 111) mStrRef.arity 96 [] (mStrRef.body.getD (.sort .zero)) mStrRef.mtype).isSome = true
def bdT111 : HasTyT (envPre 111) mStrRef.arity [] (mStrRef.body.getD (.sort .zero)) mStrRef.mtype :=
  (tyAtC (envPre 111) mStrRef.arity 96 [] (mStrRef.body.getD (.sort .zero)) mStrRef.mtype).get bdB111
def wft112 : EnvWfT (envPre 112) :=
  wfTOfExtend (r := 111) (m := mStrRef) (by decide) rfl
    (.definition (envPre 111) 111 mStrRef.mtype (mStrRef.body.getD (.sort .zero)) _ wft111 rfl
      tyT111.2 bdT111 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB112 : (sortTyAtC (envPre 112) mBytesRef.arity 96 [] mBytesRef.mtype).isSome = true
def tyT112 : Σ u, HasTyT (envPre 112) mBytesRef.arity [] mBytesRef.mtype (.sort u) :=
  (sortTyAtC (envPre 112) mBytesRef.arity 96 [] mBytesRef.mtype).get tyB112
kernel_rfl_theorem bdB112 : (tyAtC (envPre 112) mBytesRef.arity 96 [] (mBytesRef.body.getD (.sort .zero)) mBytesRef.mtype).isSome = true
def bdT112 : HasTyT (envPre 112) mBytesRef.arity [] (mBytesRef.body.getD (.sort .zero)) mBytesRef.mtype :=
  (tyAtC (envPre 112) mBytesRef.arity 96 [] (mBytesRef.body.getD (.sort .zero)) mBytesRef.mtype).get bdB112
def wft113 : EnvWfT (envPre 113) :=
  wfTOfExtend (r := 112) (m := mBytesRef) (by decide) rfl
    (.definition (envPre 112) 112 mBytesRef.mtype (mBytesRef.body.getD (.sort .zero)) _ wft112 rfl
      tyT112.2 bdT112 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB113 : (tyAtC (envPre 113) mCctI64Pf.arity 96 [] mCctI64Pf.mtype (.sort .zero)).isSome = true
def tyT113 : HasTyT (envPre 113) mCctI64Pf.arity [] mCctI64Pf.mtype (.sort .zero) :=
  (tyAtC (envPre 113) mCctI64Pf.arity 96 [] mCctI64Pf.mtype (.sort .zero)).get tyB113
kernel_rfl_theorem bdB113 : (tyAtC (envPre 113) mCctI64Pf.arity 96 [] (mCctI64Pf.body.getD (.sort .zero)) mCctI64Pf.mtype).isSome = true
def bdT113 : HasTyT (envPre 113) mCctI64Pf.arity [] (mCctI64Pf.body.getD (.sort .zero)) mCctI64Pf.mtype :=
  (tyAtC (envPre 113) mCctI64Pf.arity 96 [] (mCctI64Pf.body.getD (.sort .zero)) mCctI64Pf.mtype).get bdB113
def wft114 : EnvWfT (envPre 114) :=
  wfTOfExtend (r := 113) (m := mCctI64Pf) (by decide) rfl
    (.thm (envPre 113) 113 mCctI64Pf.mtype (mCctI64Pf.body.getD (.sort .zero)) wft113 rfl
      tyT113 bdT113 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB114 : (tyAtC (envPre 114) mCctBoolPf.arity 96 [] mCctBoolPf.mtype (.sort .zero)).isSome = true
def tyT114 : HasTyT (envPre 114) mCctBoolPf.arity [] mCctBoolPf.mtype (.sort .zero) :=
  (tyAtC (envPre 114) mCctBoolPf.arity 96 [] mCctBoolPf.mtype (.sort .zero)).get tyB114
kernel_rfl_theorem bdB114 : (tyAtC (envPre 114) mCctBoolPf.arity 96 [] (mCctBoolPf.body.getD (.sort .zero)) mCctBoolPf.mtype).isSome = true
def bdT114 : HasTyT (envPre 114) mCctBoolPf.arity [] (mCctBoolPf.body.getD (.sort .zero)) mCctBoolPf.mtype :=
  (tyAtC (envPre 114) mCctBoolPf.arity 96 [] (mCctBoolPf.body.getD (.sort .zero)) mCctBoolPf.mtype).get bdB114
def wft115 : EnvWfT (envPre 115) :=
  wfTOfExtend (r := 114) (m := mCctBoolPf) (by decide) rfl
    (.thm (envPre 114) 114 mCctBoolPf.mtype (mCctBoolPf.body.getD (.sort .zero)) wft114 rfl
      tyT114 bdT114 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB115 : (tyAtC (envPre 115) mCctStrPf.arity 96 [] mCctStrPf.mtype (.sort .zero)).isSome = true
def tyT115 : HasTyT (envPre 115) mCctStrPf.arity [] mCctStrPf.mtype (.sort .zero) :=
  (tyAtC (envPre 115) mCctStrPf.arity 96 [] mCctStrPf.mtype (.sort .zero)).get tyB115
kernel_rfl_theorem bdB115 : (tyAtC (envPre 115) mCctStrPf.arity 96 [] (mCctStrPf.body.getD (.sort .zero)) mCctStrPf.mtype).isSome = true
def bdT115 : HasTyT (envPre 115) mCctStrPf.arity [] (mCctStrPf.body.getD (.sort .zero)) mCctStrPf.mtype :=
  (tyAtC (envPre 115) mCctStrPf.arity 96 [] (mCctStrPf.body.getD (.sort .zero)) mCctStrPf.mtype).get bdB115
def wft116 : EnvWfT (envPre 116) :=
  wfTOfExtend (r := 115) (m := mCctStrPf) (by decide) rfl
    (.thm (envPre 115) 115 mCctStrPf.mtype (mCctStrPf.body.getD (.sort .zero)) wft115 rfl
      tyT115 bdT115 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB116 : (tyAtC (envPre 116) mCctBytesPf.arity 96 [] mCctBytesPf.mtype (.sort .zero)).isSome = true
def tyT116 : HasTyT (envPre 116) mCctBytesPf.arity [] mCctBytesPf.mtype (.sort .zero) :=
  (tyAtC (envPre 116) mCctBytesPf.arity 96 [] mCctBytesPf.mtype (.sort .zero)).get tyB116
kernel_rfl_theorem bdB116 : (tyAtC (envPre 116) mCctBytesPf.arity 96 [] (mCctBytesPf.body.getD (.sort .zero)) mCctBytesPf.mtype).isSome = true
def bdT116 : HasTyT (envPre 116) mCctBytesPf.arity [] (mCctBytesPf.body.getD (.sort .zero)) mCctBytesPf.mtype :=
  (tyAtC (envPre 116) mCctBytesPf.arity 96 [] (mCctBytesPf.body.getD (.sort .zero)) mCctBytesPf.mtype).get bdB116
def wft117 : EnvWfT (envPre 117) :=
  wfTOfExtend (r := 116) (m := mCctBytesPf) (by decide) rfl
    (.thm (envPre 116) 116 mCctBytesPf.mtype (mCctBytesPf.body.getD (.sort .zero)) wft116 rfl
      tyT116 bdT116 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB117 : (sortTyAtC (envPre 117) mBoundI64.arity 96 [] mBoundI64.mtype).isSome = true
def tyT117 : Σ u, HasTyT (envPre 117) mBoundI64.arity [] mBoundI64.mtype (.sort u) :=
  (sortTyAtC (envPre 117) mBoundI64.arity 96 [] mBoundI64.mtype).get tyB117
kernel_rfl_theorem bdB117 : (tyAtC (envPre 117) mBoundI64.arity 96 [] (mBoundI64.body.getD (.sort .zero)) mBoundI64.mtype).isSome = true
def bdT117 : HasTyT (envPre 117) mBoundI64.arity [] (mBoundI64.body.getD (.sort .zero)) mBoundI64.mtype :=
  (tyAtC (envPre 117) mBoundI64.arity 96 [] (mBoundI64.body.getD (.sort .zero)) mBoundI64.mtype).get bdB117
def wft118 : EnvWfT (envPre 118) :=
  wfTOfExtend (r := 117) (m := mBoundI64) (by decide) rfl
    (.definition (envPre 117) 117 mBoundI64.mtype (mBoundI64.body.getD (.sort .zero)) _ wft117 rfl
      tyT117.2 bdT117 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB118 : (sortTyAtC (envPre 118) mBoundBool.arity 96 [] mBoundBool.mtype).isSome = true
def tyT118 : Σ u, HasTyT (envPre 118) mBoundBool.arity [] mBoundBool.mtype (.sort u) :=
  (sortTyAtC (envPre 118) mBoundBool.arity 96 [] mBoundBool.mtype).get tyB118
kernel_rfl_theorem bdB118 : (tyAtC (envPre 118) mBoundBool.arity 96 [] (mBoundBool.body.getD (.sort .zero)) mBoundBool.mtype).isSome = true
def bdT118 : HasTyT (envPre 118) mBoundBool.arity [] (mBoundBool.body.getD (.sort .zero)) mBoundBool.mtype :=
  (tyAtC (envPre 118) mBoundBool.arity 96 [] (mBoundBool.body.getD (.sort .zero)) mBoundBool.mtype).get bdB118
def wft119 : EnvWfT (envPre 119) :=
  wfTOfExtend (r := 118) (m := mBoundBool) (by decide) rfl
    (.definition (envPre 118) 118 mBoundBool.mtype (mBoundBool.body.getD (.sort .zero)) _ wft118 rfl
      tyT118.2 bdT118 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB119 : (sortTyAtC (envPre 119) mBoundStr.arity 96 [] mBoundStr.mtype).isSome = true
def tyT119 : Σ u, HasTyT (envPre 119) mBoundStr.arity [] mBoundStr.mtype (.sort u) :=
  (sortTyAtC (envPre 119) mBoundStr.arity 96 [] mBoundStr.mtype).get tyB119
kernel_rfl_theorem bdB119 : (tyAtC (envPre 119) mBoundStr.arity 96 [] (mBoundStr.body.getD (.sort .zero)) mBoundStr.mtype).isSome = true
def bdT119 : HasTyT (envPre 119) mBoundStr.arity [] (mBoundStr.body.getD (.sort .zero)) mBoundStr.mtype :=
  (tyAtC (envPre 119) mBoundStr.arity 96 [] (mBoundStr.body.getD (.sort .zero)) mBoundStr.mtype).get bdB119
def wft120 : EnvWfT (envPre 120) :=
  wfTOfExtend (r := 119) (m := mBoundStr) (by decide) rfl
    (.definition (envPre 119) 119 mBoundStr.mtype (mBoundStr.body.getD (.sort .zero)) _ wft119 rfl
      tyT119.2 bdT119 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB120 : (sortTyAtC (envPre 120) mBoundBytes.arity 96 [] mBoundBytes.mtype).isSome = true
def tyT120 : Σ u, HasTyT (envPre 120) mBoundBytes.arity [] mBoundBytes.mtype (.sort u) :=
  (sortTyAtC (envPre 120) mBoundBytes.arity 96 [] mBoundBytes.mtype).get tyB120
kernel_rfl_theorem bdB120 : (tyAtC (envPre 120) mBoundBytes.arity 96 [] (mBoundBytes.body.getD (.sort .zero)) mBoundBytes.mtype).isSome = true
def bdT120 : HasTyT (envPre 120) mBoundBytes.arity [] (mBoundBytes.body.getD (.sort .zero)) mBoundBytes.mtype :=
  (tyAtC (envPre 120) mBoundBytes.arity 96 [] (mBoundBytes.body.getD (.sort .zero)) mBoundBytes.mtype).get bdB120
def wft121 : EnvWfT (envPre 121) :=
  wfTOfExtend (r := 120) (m := mBoundBytes) (by decide) rfl
    (.definition (envPre 120) 120 mBoundBytes.mtype (mBoundBytes.body.getD (.sort .zero)) _ wft120 rfl
      tyT120.2 bdT120 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB121 : (tyAtC (envPre 121) mBcLB.arity 96 [] mBcLB.mtype (.sort .zero)).isSome = true
def tyT121 : HasTyT (envPre 121) mBcLB.arity [] mBcLB.mtype (.sort .zero) :=
  (tyAtC (envPre 121) mBcLB.arity 96 [] mBcLB.mtype (.sort .zero)).get tyB121
kernel_rfl_theorem bdB121 : (tyAtC (envPre 121) mBcLB.arity 96 [] (mBcLB.body.getD (.sort .zero)) mBcLB.mtype).isSome = true
def bdT121 : HasTyT (envPre 121) mBcLB.arity [] (mBcLB.body.getD (.sort .zero)) mBcLB.mtype :=
  (tyAtC (envPre 121) mBcLB.arity 96 [] (mBcLB.body.getD (.sort .zero)) mBcLB.mtype).get bdB121
def wft122 : EnvWfT (envPre 122) :=
  wfTOfExtend (r := 121) (m := mBcLB) (by decide) rfl
    (.thm (envPre 121) 121 mBcLB.mtype (mBcLB.body.getD (.sort .zero)) wft121 rfl
      tyT121 bdT121 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB122 : (sortTyAtC (envPre 122) mLbRef.arity 96 [] mLbRef.mtype).isSome = true
def tyT122 : Σ u, HasTyT (envPre 122) mLbRef.arity [] mLbRef.mtype (.sort u) :=
  (sortTyAtC (envPre 122) mLbRef.arity 96 [] mLbRef.mtype).get tyB122
kernel_rfl_theorem bdB122 : (tyAtC (envPre 122) mLbRef.arity 96 [] (mLbRef.body.getD (.sort .zero)) mLbRef.mtype).isSome = true
def bdT122 : HasTyT (envPre 122) mLbRef.arity [] (mLbRef.body.getD (.sort .zero)) mLbRef.mtype :=
  (tyAtC (envPre 122) mLbRef.arity 96 [] (mLbRef.body.getD (.sort .zero)) mLbRef.mtype).get bdB122
def wft123 : EnvWfT (envPre 123) :=
  wfTOfExtend (r := 122) (m := mLbRef) (by decide) rfl
    (.definition (envPre 122) 122 mLbRef.mtype (mLbRef.body.getD (.sort .zero)) _ wft122 rfl
      tyT122.2 bdT122 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB123 : (tyAtC (envPre 123) mCctLbPf.arity 96 [] mCctLbPf.mtype (.sort .zero)).isSome = true
def tyT123 : HasTyT (envPre 123) mCctLbPf.arity [] mCctLbPf.mtype (.sort .zero) :=
  (tyAtC (envPre 123) mCctLbPf.arity 96 [] mCctLbPf.mtype (.sort .zero)).get tyB123
kernel_rfl_theorem bdB123 : (tyAtC (envPre 123) mCctLbPf.arity 96 [] (mCctLbPf.body.getD (.sort .zero)) mCctLbPf.mtype).isSome = true
def bdT123 : HasTyT (envPre 123) mCctLbPf.arity [] (mCctLbPf.body.getD (.sort .zero)) mCctLbPf.mtype :=
  (tyAtC (envPre 123) mCctLbPf.arity 96 [] (mCctLbPf.body.getD (.sort .zero)) mCctLbPf.mtype).get bdB123
def wft124 : EnvWfT (envPre 124) :=
  wfTOfExtend (r := 123) (m := mCctLbPf) (by decide) rfl
    (.thm (envPre 123) 123 mCctLbPf.mtype (mCctLbPf.body.getD (.sort .zero)) wft123 rfl
      tyT123 bdT123 (fun _ => rfl) (fun _ => rfl) rfl rfl)
kernel_rfl_theorem tyB124 : (sortTyAtC (envPre 124) mBoundListBool.arity 96 [] mBoundListBool.mtype).isSome = true
def tyT124 : Σ u, HasTyT (envPre 124) mBoundListBool.arity [] mBoundListBool.mtype (.sort u) :=
  (sortTyAtC (envPre 124) mBoundListBool.arity 96 [] mBoundListBool.mtype).get tyB124
kernel_rfl_theorem bdB124 : (tyAtC (envPre 124) mBoundListBool.arity 96 [] (mBoundListBool.body.getD (.sort .zero)) mBoundListBool.mtype).isSome = true
def bdT124 : HasTyT (envPre 124) mBoundListBool.arity [] (mBoundListBool.body.getD (.sort .zero)) mBoundListBool.mtype :=
  (tyAtC (envPre 124) mBoundListBool.arity 96 [] (mBoundListBool.body.getD (.sort .zero)) mBoundListBool.mtype).get bdB124
def wft125 : EnvWfT (envPre 125) :=
  wfTOfExtend (r := 124) (m := mBoundListBool) (by decide) rfl
    (.definition (envPre 124) 124 mBoundListBool.mtype (mBoundListBool.body.getD (.sort .zero)) _ wft124 rfl
      tyT124.2 bdT124 (fun _ => rfl) (fun _ => rfl) rfl rfl)

end Rcic.Scm.SrcG

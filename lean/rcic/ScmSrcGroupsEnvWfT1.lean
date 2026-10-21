import rcic.ScmSrcGroupsEnvWfT0

/-! `EnvWfT` for srcEnvG slots in this file's range. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/- slots 4–7: family mBytes, recursor recBytes -/
kernel_rfl_theorem tyB4 : (sortTyAtC (envPre 4) mBytes.arity 96 [] mBytes.mtype).isSome = true
def tyT4 : Σ u, HasTyT (envPre 4) mBytes.arity [] mBytes.mtype (.sort u) :=
  (sortTyAtC (envPre 4) mBytes.arity 96 [] mBytes.mtype).get tyB4
kernel_rfl_theorem tyB5 : (sortTyAtC (envPre 5) mBnil.arity 96 [] mBnil.mtype).isSome = true
def tyT5 : Σ u, HasTyT (envPre 5) mBnil.arity [] mBnil.mtype (.sort u) :=
  (sortTyAtC (envPre 5) mBnil.arity 96 [] mBnil.mtype).get tyB5
kernel_rfl_theorem tyS5 : (sortTyAtC (extendEnv (envPre 4) 4 mBytes) mBnil.arity 96 [] mBnil.mtype).isSome = true
kernel_rfl_theorem tyB6 : (sortTyAtC (envPre 6) mBcons.arity 96 [] mBcons.mtype).isSome = true
def tyT6 : Σ u, HasTyT (envPre 6) mBcons.arity [] mBcons.mtype (.sort u) :=
  (sortTyAtC (envPre 6) mBcons.arity 96 [] mBcons.mtype).get tyB6
kernel_rfl_theorem tyS6 : (sortTyAtC (extendEnv (envPre 4) 4 mBytes) mBcons.arity 96 [] mBcons.mtype).isSome = true
kernel_rfl_theorem tyB7 : (sortTyAtC (envPre 7) recBytes.arity 96 [] recBytes.mtype).isSome = true
def tyT7 : Σ u, HasTyT (envPre 7) recBytes.arity [] recBytes.mtype (.sort u) :=
  (sortTyAtC (envPre 7) recBytes.arity 96 [] recBytes.mtype).get tyB7
def dFam4 := (admFamView? admFamBytes).get rfl
def dCtor5 := (admCtorViews? admCtorBnil).get rfl
def dCtor6 := (admCtorViews? admCtorBcons).get rfl
def dRec7 := (admRecData admRecBytes).get rfl
kernel_rfl_theorem famB4 : famTypedB (extendEnv (envPre 4) 4 mBytes) 96 dFam4 = true
kernel_rfl_theorem famB5 : famTypedB (envPre 5) 96 dCtor5.1 = true
kernel_rfl_theorem ctorB5 : ctorTypedB 96 dCtor5.2.2 = true
kernel_rfl_theorem famB6 : famTypedB (envPre 6) 96 dCtor6.1 = true
kernel_rfl_theorem ctorB6 : ctorTypedB 96 dCtor6.2.2 = true
kernel_rfl_theorem famB7 : famTypedB (envPre 7) 96 dRec7.1.family = true
kernel_rfl_theorem ctorB7 : ctorTypedAllB 96 dRec7.1 = true
kernel_rfl_theorem idxB7 : recIdxAdmittedTB dRec7.1 dRec7.2 = true
kernel_rfl_theorem iotaB7_0 : iotaEqB (a := dRec7.1) (h14 := dRec7.2) (synCheck (extendEnv (envPre 7) 7 recBytes) recBytes.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB7_1 : iotaEqB (a := dRec7.1) (h14 := dRec7.2) (synCheck (extendEnv (envPre 7) 7 recBytes) recBytes.arity) 1 (by decide) = true
def typedFam4 : IndGroupTypedT admFamBytes := famTypedT_of (fuel := 96) dFam4 famB4
def typedCtor5 : IndGroupTypedT admCtorBnil :=
  ⟨famTypedT_of (fuel := 96) dCtor5.1 famB5, ctorTypedT_of (fuel := 96) ctorB5⟩
def typedCtor6 : IndGroupTypedT admCtorBcons :=
  ⟨famTypedT_of (fuel := 96) dCtor6.1 famB6, ctorTypedT_of (fuel := 96) ctorB6⟩
theorem iotaAllB7 : finAllB dRec7.1.constructors.length
    (iotaEqB (a := dRec7.1) (h14 := dRec7.2) (synCheck (extendEnv (envPre 7) 7 recBytes) recBytes.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB7_0
    | 1 => iotaB7_1
    | k+2 => absurd hi (by have : dRec7.1.constructors.length = 2 := rfl; omega)
def iotaT7 : ∀ i, IotaEquationTypedT dRec7.1 i (dRec7.2.fuelAt i) (dRec7.2.shapesAt i) :=
  iotaEqsT_of iotaAllB7
def idxT7 : IdxAdmittedT admRecBytes := idxT_of admRecBytes idxB7
def typedRec7 : IndGroupTypedT admRecBytes :=
  ⟨famTypedT_of (fuel := 96) dRec7.1.family famB7,
   ctorTypedAll_of ctorB7,
   iotaT7⟩
def mem4 : GroupMembersT (extendEnv (envPre 4) 4 mBytes) (envPre 4)
    [(4, mBytes), (5, mBnil), (6, mBcons), (7, recBytes)] (extendEnv (envPre 7) 7 recBytes) :=
  (GroupMembersT.cons _ 4 mBytes _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamBytes PUnit.unit _ tyT4.2 (fun h => absurd h (by decide)) typedFam4
    (GroupMembersT.cons _ 5 mBnil _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorBnil PUnit.unit _ tyT5.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS5).2⟩) typedCtor5
    (GroupMembersT.cons _ 6 mBcons _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorBcons PUnit.unit _ tyT6.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS6).2⟩) typedCtor6
    (GroupMembersT.cons _ 7 recBytes _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecBytes idxT7 _ tyT7.2 (fun h => absurd h (by decide)) typedRec7
    (.nil _)))))
def wft8 : EnvWfT (envPre 8) :=
  wfTOfExtend (r := 7) (m := recBytes) (by decide) rfl
    (.group (envPre 4) 4 mBytes [(5, mBnil), (6, mBcons)] 7 recBytes _ wft4 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem4)
/- slots 8–10: family mRefT, recursor recRefT -/
kernel_rfl_theorem tyB8 : (sortTyAtC (envPre 8) mRefT.arity 96 [] mRefT.mtype).isSome = true
def tyT8 : Σ u, HasTyT (envPre 8) mRefT.arity [] mRefT.mtype (.sort u) :=
  (sortTyAtC (envPre 8) mRefT.arity 96 [] mRefT.mtype).get tyB8
kernel_rfl_theorem tyB9 : (sortTyAtC (envPre 9) mMkRef.arity 96 [] mMkRef.mtype).isSome = true
def tyT9 : Σ u, HasTyT (envPre 9) mMkRef.arity [] mMkRef.mtype (.sort u) :=
  (sortTyAtC (envPre 9) mMkRef.arity 96 [] mMkRef.mtype).get tyB9
kernel_rfl_theorem tyS9 : (sortTyAtC (extendEnv (envPre 8) 8 mRefT) mMkRef.arity 96 [] mMkRef.mtype).isSome = true
kernel_rfl_theorem tyB10 : (sortTyAtC (envPre 10) recRefT.arity 96 [] recRefT.mtype).isSome = true
def tyT10 : Σ u, HasTyT (envPre 10) recRefT.arity [] recRefT.mtype (.sort u) :=
  (sortTyAtC (envPre 10) recRefT.arity 96 [] recRefT.mtype).get tyB10
def dFam8 := (admFamView? admFamRefT).get rfl
def dCtor9 := (admCtorViews? admCtorMkRef).get rfl
def dRec10 := (admRecData admRecRefT).get rfl
kernel_rfl_theorem famB8 : famTypedB (extendEnv (envPre 8) 8 mRefT) 96 dFam8 = true
kernel_rfl_theorem famB9 : famTypedB (envPre 9) 96 dCtor9.1 = true
kernel_rfl_theorem ctorB9 : ctorTypedB 96 dCtor9.2.2 = true
kernel_rfl_theorem famB10 : famTypedB (envPre 10) 96 dRec10.1.family = true
kernel_rfl_theorem ctorB10 : ctorTypedAllB 96 dRec10.1 = true
kernel_rfl_theorem idxB10 : recIdxAdmittedTB dRec10.1 dRec10.2 = true
kernel_rfl_theorem iotaB10_0 : iotaEqB (a := dRec10.1) (h14 := dRec10.2) (synCheck (extendEnv (envPre 10) 10 recRefT) recRefT.arity) 0 (by decide) = true
def typedFam8 : IndGroupTypedT admFamRefT := famTypedT_of (fuel := 96) dFam8 famB8
def typedCtor9 : IndGroupTypedT admCtorMkRef :=
  ⟨famTypedT_of (fuel := 96) dCtor9.1 famB9, ctorTypedT_of (fuel := 96) ctorB9⟩
theorem iotaAllB10 : finAllB dRec10.1.constructors.length
    (iotaEqB (a := dRec10.1) (h14 := dRec10.2) (synCheck (extendEnv (envPre 10) 10 recRefT) recRefT.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB10_0
    | k+1 => absurd hi (by have : dRec10.1.constructors.length = 1 := rfl; omega)
def iotaT10 : ∀ i, IotaEquationTypedT dRec10.1 i (dRec10.2.fuelAt i) (dRec10.2.shapesAt i) :=
  iotaEqsT_of iotaAllB10
def idxT10 : IdxAdmittedT admRecRefT := idxT_of admRecRefT idxB10
def typedRec10 : IndGroupTypedT admRecRefT :=
  ⟨famTypedT_of (fuel := 96) dRec10.1.family famB10,
   ctorTypedAll_of ctorB10,
   iotaT10⟩
def mem8 : GroupMembersT (extendEnv (envPre 8) 8 mRefT) (envPre 8)
    [(8, mRefT), (9, mMkRef), (10, recRefT)] (extendEnv (envPre 10) 10 recRefT) :=
  (GroupMembersT.cons _ 8 mRefT _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamRefT PUnit.unit _ tyT8.2 (fun h => absurd h (by decide)) typedFam8
    (GroupMembersT.cons _ 9 mMkRef _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorMkRef PUnit.unit _ tyT9.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS9).2⟩) typedCtor9
    (GroupMembersT.cons _ 10 recRefT _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecRefT idxT10 _ tyT10.2 (fun h => absurd h (by decide)) typedRec10
    (.nil _))))
def wft11 : EnvWfT (envPre 11) :=
  wfTOfExtend (r := 10) (m := recRefT) (by decide) rfl
    (.group (envPre 8) 8 mRefT [(9, mMkRef)] 10 recRefT _ wft8 rfl
      (fun c hc => by simp at hc; rcases hc with rfl <;> rfl) rfl mem8)

end Rcic.Scm.SrcG

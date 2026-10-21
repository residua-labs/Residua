import rcic.ScmSrcGroupsEnvWfT11

/-! `EnvWfT` for srcEnvG slots in this file's range. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/- slots 106–108: family mBCT, recursor recBCT -/
kernel_rfl_theorem tyB106 : (sortTyAtC (envPre 106) mBCT.arity 96 [] mBCT.mtype).isSome = true
def tyT106 : Σ u, HasTyT (envPre 106) mBCT.arity [] mBCT.mtype (.sort u) :=
  (sortTyAtC (envPre 106) mBCT.arity 96 [] mBCT.mtype).get tyB106
kernel_rfl_theorem tyB107 : (sortTyAtC (envPre 107) mMkBound.arity 96 [] mMkBound.mtype).isSome = true
def tyT107 : Σ u, HasTyT (envPre 107) mMkBound.arity [] mMkBound.mtype (.sort u) :=
  (sortTyAtC (envPre 107) mMkBound.arity 96 [] mMkBound.mtype).get tyB107
kernel_rfl_theorem tyS107 : (sortTyAtC (extendEnv (envPre 106) 106 mBCT) mMkBound.arity 96 [] mMkBound.mtype).isSome = true
kernel_rfl_theorem tyB108 : (sortTyAtC (envPre 108) recBCT.arity 96 [] recBCT.mtype).isSome = true
def tyT108 : Σ u, HasTyT (envPre 108) recBCT.arity [] recBCT.mtype (.sort u) :=
  (sortTyAtC (envPre 108) recBCT.arity 96 [] recBCT.mtype).get tyB108
def dFam106 := (admFamView? admFamBCT).get rfl
def dCtor107 := (admCtorViews? admCtorMkBound).get rfl
def dRec108 := (admRecData admRecBCT).get rfl
kernel_rfl_theorem famB106 : famTypedB (extendEnv (envPre 106) 106 mBCT) 96 dFam106 = true
kernel_rfl_theorem famB107 : famTypedB (envPre 107) 96 dCtor107.1 = true
kernel_rfl_theorem ctorB107 : ctorTypedB 96 dCtor107.2.2 = true
kernel_rfl_theorem famB108 : famTypedB (envPre 108) 96 dRec108.1.family = true
kernel_rfl_theorem ctorB108 : ctorTypedAllB 96 dRec108.1 = true
kernel_rfl_theorem idxB108 : recIdxAdmittedTB dRec108.1 dRec108.2 = true
kernel_rfl_theorem iotaB108_0 : iotaEqB (a := dRec108.1) (h14 := dRec108.2) (synCheck (extendEnv (envPre 108) 108 recBCT) recBCT.arity) 0 (by decide) = true
def typedFam106 : IndGroupTypedT admFamBCT := famTypedT_of (fuel := 96) dFam106 famB106
def typedCtor107 : IndGroupTypedT admCtorMkBound :=
  ⟨famTypedT_of (fuel := 96) dCtor107.1 famB107, ctorTypedT_of (fuel := 96) ctorB107⟩
theorem iotaAllB108 : finAllB dRec108.1.constructors.length
    (iotaEqB (a := dRec108.1) (h14 := dRec108.2) (synCheck (extendEnv (envPre 108) 108 recBCT) recBCT.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB108_0
    | k+1 => absurd hi (by have : dRec108.1.constructors.length = 1 := rfl; omega)
def iotaT108 : ∀ i, IotaEquationTypedT dRec108.1 i (dRec108.2.fuelAt i) (dRec108.2.shapesAt i) :=
  iotaEqsT_of iotaAllB108
def idxT108 : IdxAdmittedT admRecBCT := idxT_of admRecBCT idxB108
def typedRec108 : IndGroupTypedT admRecBCT :=
  ⟨famTypedT_of (fuel := 96) dRec108.1.family famB108,
   ctorTypedAll_of ctorB108,
   iotaT108⟩
def mem106 : GroupMembersT (extendEnv (envPre 106) 106 mBCT) (envPre 106)
    [(106, mBCT), (107, mMkBound), (108, recBCT)] (extendEnv (envPre 108) 108 recBCT) :=
  (GroupMembersT.cons _ 106 mBCT _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamBCT PUnit.unit _ tyT106.2 (fun h => absurd h (by decide)) typedFam106
    (GroupMembersT.cons _ 107 mMkBound _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorMkBound PUnit.unit _ tyT107.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS107).2⟩) typedCtor107
    (GroupMembersT.cons _ 108 recBCT _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecBCT idxT108 _ tyT108.2 (fun h => absurd h (by decide)) typedRec108
    (.nil _))))
def wft109 : EnvWfT (envPre 109) :=
  wfTOfExtend (r := 108) (m := recBCT) (by decide) rfl
    (.group (envPre 106) 106 mBCT [(107, mMkBound)] 108 recBCT _ wft106 rfl
      (fun c hc => by simp at hc; rcases hc with rfl <;> rfl) rfl mem106)

end Rcic.Scm.SrcG

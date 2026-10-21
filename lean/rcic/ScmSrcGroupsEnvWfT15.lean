import rcic.ScmSrcGroupsEnvWfT14
import rcic.ScmSrcGroupsFunRecTypedEq

/-! `EnvWfT` for srcEnvG slots in this file's range. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/- slots 133–143: family mValueAt, recursor recValueAt -/
kernel_rfl_theorem tyB133 : (sortTyAtC (envPre 133) mValueAt.arity 96 [] mValueAt.mtype).isSome = true
def tyT133 : Σ u, HasTyT (envPre 133) mValueAt.arity [] mValueAt.mtype (.sort u) :=
  (sortTyAtC (envPre 133) mValueAt.arity 96 [] mValueAt.mtype).get tyB133
kernel_rfl_theorem tyB134 : (sortTyAtC (envPre 134) mVaB0.arity 96 [] mVaB0.mtype).isSome = true
def tyT134 : Σ u, HasTyT (envPre 134) mVaB0.arity [] mVaB0.mtype (.sort u) :=
  (sortTyAtC (envPre 134) mVaB0.arity 96 [] mVaB0.mtype).get tyB134
kernel_rfl_theorem tyS134 : (sortTyAtC (extendEnv (envPre 133) 133 mValueAt) mVaB0.arity 96 [] mVaB0.mtype).isSome = true
kernel_rfl_theorem tyB135 : (sortTyAtC (envPre 135) mVaB1.arity 96 [] mVaB1.mtype).isSome = true
def tyT135 : Σ u, HasTyT (envPre 135) mVaB1.arity [] mVaB1.mtype (.sort u) :=
  (sortTyAtC (envPre 135) mVaB1.arity 96 [] mVaB1.mtype).get tyB135
kernel_rfl_theorem tyS135 : (sortTyAtC (extendEnv (envPre 133) 133 mValueAt) mVaB1.arity 96 [] mVaB1.mtype).isSome = true
kernel_rfl_theorem tyB136 : (sortTyAtC (envPre 136) mVaI64.arity 96 [] mVaI64.mtype).isSome = true
def tyT136 : Σ u, HasTyT (envPre 136) mVaI64.arity [] mVaI64.mtype (.sort u) :=
  (sortTyAtC (envPre 136) mVaI64.arity 96 [] mVaI64.mtype).get tyB136
kernel_rfl_theorem tyS136 : (sortTyAtC (extendEnv (envPre 133) 133 mValueAt) mVaI64.arity 96 [] mVaI64.mtype).isSome = true
kernel_rfl_theorem tyB137 : (sortTyAtC (envPre 137) mVaStr.arity 96 [] mVaStr.mtype).isSome = true
def tyT137 : Σ u, HasTyT (envPre 137) mVaStr.arity [] mVaStr.mtype (.sort u) :=
  (sortTyAtC (envPre 137) mVaStr.arity 96 [] mVaStr.mtype).get tyB137
kernel_rfl_theorem tyS137 : (sortTyAtC (extendEnv (envPre 133) 133 mValueAt) mVaStr.arity 96 [] mVaStr.mtype).isSome = true
kernel_rfl_theorem tyB138 : (sortTyAtC (envPre 138) mVaY.arity 96 [] mVaY.mtype).isSome = true
def tyT138 : Σ u, HasTyT (envPre 138) mVaY.arity [] mVaY.mtype (.sort u) :=
  (sortTyAtC (envPre 138) mVaY.arity 96 [] mVaY.mtype).get tyB138
kernel_rfl_theorem tyS138 : (sortTyAtC (extendEnv (envPre 133) 133 mValueAt) mVaY.arity 96 [] mVaY.mtype).isSome = true
kernel_rfl_theorem tyB139 : (sortTyAtC (envPre 139) mVaList.arity 96 [] mVaList.mtype).isSome = true
def tyT139 : Σ u, HasTyT (envPre 139) mVaList.arity [] mVaList.mtype (.sort u) :=
  (sortTyAtC (envPre 139) mVaList.arity 96 [] mVaList.mtype).get tyB139
kernel_rfl_theorem tyS139 : (sortTyAtC (extendEnv (envPre 133) 133 mValueAt) mVaList.arity 96 [] mVaList.mtype).isSome = true
kernel_rfl_theorem tyB140 : (sortTyAtC (envPre 140) mVaPair.arity 96 [] mVaPair.mtype).isSome = true
def tyT140 : Σ u, HasTyT (envPre 140) mVaPair.arity [] mVaPair.mtype (.sort u) :=
  (sortTyAtC (envPre 140) mVaPair.arity 96 [] mVaPair.mtype).get tyB140
kernel_rfl_theorem tyS140 : (sortTyAtC (extendEnv (envPre 133) 133 mValueAt) mVaPair.arity 96 [] mVaPair.mtype).isSome = true
kernel_rfl_theorem tyB141 : (sortTyAtC (envPre 141) mVaJ.arity 96 [] mVaJ.mtype).isSome = true
def tyT141 : Σ u, HasTyT (envPre 141) mVaJ.arity [] mVaJ.mtype (.sort u) :=
  (sortTyAtC (envPre 141) mVaJ.arity 96 [] mVaJ.mtype).get tyB141
kernel_rfl_theorem tyS141 : (sortTyAtC (extendEnv (envPre 133) 133 mValueAt) mVaJ.arity 96 [] mVaJ.mtype).isSome = true
kernel_rfl_theorem tyB142 : (sortTyAtC (envPre 142) mVaR.arity 96 [] mVaR.mtype).isSome = true
def tyT142 : Σ u, HasTyT (envPre 142) mVaR.arity [] mVaR.mtype (.sort u) :=
  (sortTyAtC (envPre 142) mVaR.arity 96 [] mVaR.mtype).get tyB142
kernel_rfl_theorem tyS142 : (sortTyAtC (extendEnv (envPre 133) 133 mValueAt) mVaR.arity 96 [] mVaR.mtype).isSome = true
kernel_rfl_theorem tyB143 : (sortTyAtC (envPre 143) recValueAt.arity 96 [] recValueAt.mtype).isSome = true
def tyT143 : Σ u, HasTyT (envPre 143) recValueAt.arity [] recValueAt.mtype (.sort u) :=
  (sortTyAtC (envPre 143) recValueAt.arity 96 [] recValueAt.mtype).get tyB143
def dFam133 := (admFamView? admFamValueAt).get rfl
def dCtor134 := (admCtorViews? admCtorVaB0).get rfl
def dCtor135 := (admCtorViews? admCtorVaB1).get rfl
def dCtor136 := (admCtorViews? admCtorVaI64).get rfl
def dCtor137 := (admCtorViews? admCtorVaStr).get rfl
def dCtor138 := (admCtorViews? admCtorVaY).get rfl
def dCtor139 := (admCtorViews? admCtorVaList).get rfl
def dCtor140 := (admCtorViews? admCtorVaPair).get rfl
def dCtor141 := (admCtorViews? admCtorVaJ).get rfl
def dCtor142 := (admCtorViews? admCtorVaR).get rfl
def dRec143 := (admRecData admRecValueAt).get rfl
kernel_rfl_theorem famB133 : famTypedB (extendEnv (envPre 133) 133 mValueAt) 96 dFam133 = true
kernel_rfl_theorem famB134 : famTypedB (envPre 134) 96 dCtor134.1 = true
kernel_rfl_theorem ctorB134 : ctorTypedB 96 dCtor134.2.2 = true
kernel_rfl_theorem famB135 : famTypedB (envPre 135) 96 dCtor135.1 = true
kernel_rfl_theorem ctorB135 : ctorTypedB 96 dCtor135.2.2 = true
kernel_rfl_theorem famB136 : famTypedB (envPre 136) 96 dCtor136.1 = true
kernel_rfl_theorem ctorB136 : ctorTypedB 96 dCtor136.2.2 = true
kernel_rfl_theorem famB137 : famTypedB (envPre 137) 96 dCtor137.1 = true
kernel_rfl_theorem ctorB137 : ctorTypedB 96 dCtor137.2.2 = true
kernel_rfl_theorem famB138 : famTypedB (envPre 138) 96 dCtor138.1 = true
kernel_rfl_theorem ctorB138 : ctorTypedB 96 dCtor138.2.2 = true
kernel_rfl_theorem famB139 : famTypedB (envPre 139) 96 dCtor139.1 = true
kernel_rfl_theorem ctorB139 : ctorTypedB 96 dCtor139.2.2 = true
kernel_rfl_theorem famB140 : famTypedB (envPre 140) 96 dCtor140.1 = true
kernel_rfl_theorem ctorB140 : ctorTypedB 96 dCtor140.2.2 = true
kernel_rfl_theorem famB141 : famTypedB (envPre 141) 96 dCtor141.1 = true
kernel_rfl_theorem ctorB141 : ctorTypedB 96 dCtor141.2.2 = true
kernel_rfl_theorem famB142 : famTypedB (envPre 142) 96 dCtor142.1 = true
kernel_rfl_theorem ctorB142 : ctorTypedB 96 dCtor142.2.2 = true
kernel_rfl_theorem famB143 : famTypedB (envPre 143) 96 dRec143.1.family = true
kernel_rfl_theorem ctorB143 : ctorTypedAllB 96 dRec143.1 = true
theorem idxB143 : recIdxAdmittedTB dRec143.1 dRec143.2 = true := FunRecTyped.vaRecIdxAdmittedB
kernel_rfl_theorem iotaB143_0 : iotaEqB (a := dRec143.1) (h14 := dRec143.2) (synCheck (extendEnv (envPre 143) 143 recValueAt) recValueAt.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB143_1 : iotaEqB (a := dRec143.1) (h14 := dRec143.2) (synCheck (extendEnv (envPre 143) 143 recValueAt) recValueAt.arity) 1 (by decide) = true
kernel_rfl_theorem iotaB143_2 : iotaEqB (a := dRec143.1) (h14 := dRec143.2) (synCheck (extendEnv (envPre 143) 143 recValueAt) recValueAt.arity) 2 (by decide) = true
kernel_rfl_theorem iotaB143_3 : iotaEqB (a := dRec143.1) (h14 := dRec143.2) (synCheck (extendEnv (envPre 143) 143 recValueAt) recValueAt.arity) 3 (by decide) = true
kernel_rfl_theorem iotaB143_4 : iotaEqB (a := dRec143.1) (h14 := dRec143.2) (synCheck (extendEnv (envPre 143) 143 recValueAt) recValueAt.arity) 4 (by decide) = true
kernel_rfl_theorem iotaB143_5 : iotaEqB (a := dRec143.1) (h14 := dRec143.2) (synCheck (extendEnv (envPre 143) 143 recValueAt) recValueAt.arity) 5 (by decide) = true
kernel_rfl_theorem iotaB143_6 : iotaEqB (a := dRec143.1) (h14 := dRec143.2) (synCheck (extendEnv (envPre 143) 143 recValueAt) recValueAt.arity) 6 (by decide) = true
kernel_rfl_theorem iotaB143_7 : iotaEqB (a := dRec143.1) (h14 := dRec143.2) (synCheck (extendEnv (envPre 143) 143 recValueAt) recValueAt.arity) 7 (by decide) = true
kernel_rfl_theorem iotaB143_8 : iotaEqB (a := dRec143.1) (h14 := dRec143.2) (synCheck (extendEnv (envPre 143) 143 recValueAt) recValueAt.arity) 8 (by decide) = true
def typedFam133 : IndGroupTypedT admFamValueAt := famTypedT_of (fuel := 96) dFam133 famB133
def typedCtor134 : IndGroupTypedT admCtorVaB0 :=
  ⟨famTypedT_of (fuel := 96) dCtor134.1 famB134, ctorTypedT_of (fuel := 96) ctorB134⟩
def typedCtor135 : IndGroupTypedT admCtorVaB1 :=
  ⟨famTypedT_of (fuel := 96) dCtor135.1 famB135, ctorTypedT_of (fuel := 96) ctorB135⟩
def typedCtor136 : IndGroupTypedT admCtorVaI64 :=
  ⟨famTypedT_of (fuel := 96) dCtor136.1 famB136, ctorTypedT_of (fuel := 96) ctorB136⟩
def typedCtor137 : IndGroupTypedT admCtorVaStr :=
  ⟨famTypedT_of (fuel := 96) dCtor137.1 famB137, ctorTypedT_of (fuel := 96) ctorB137⟩
def typedCtor138 : IndGroupTypedT admCtorVaY :=
  ⟨famTypedT_of (fuel := 96) dCtor138.1 famB138, ctorTypedT_of (fuel := 96) ctorB138⟩
def typedCtor139 : IndGroupTypedT admCtorVaList :=
  ⟨famTypedT_of (fuel := 96) dCtor139.1 famB139, ctorTypedT_of (fuel := 96) ctorB139⟩
def typedCtor140 : IndGroupTypedT admCtorVaPair :=
  ⟨famTypedT_of (fuel := 96) dCtor140.1 famB140, ctorTypedT_of (fuel := 96) ctorB140⟩
def typedCtor141 : IndGroupTypedT admCtorVaJ :=
  ⟨famTypedT_of (fuel := 96) dCtor141.1 famB141, ctorTypedT_of (fuel := 96) ctorB141⟩
def typedCtor142 : IndGroupTypedT admCtorVaR :=
  ⟨famTypedT_of (fuel := 96) dCtor142.1 famB142, ctorTypedT_of (fuel := 96) ctorB142⟩
theorem iotaAllB143 : finAllB dRec143.1.constructors.length
    (iotaEqB (a := dRec143.1) (h14 := dRec143.2) (synCheck (extendEnv (envPre 143) 143 recValueAt) recValueAt.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB143_0
    | 1 => iotaB143_1
    | 2 => iotaB143_2
    | 3 => iotaB143_3
    | 4 => iotaB143_4
    | 5 => iotaB143_5
    | 6 => iotaB143_6
    | 7 => iotaB143_7
    | 8 => iotaB143_8
    | k+9 => absurd hi (by have : dRec143.1.constructors.length = 9 := rfl; omega)
def iotaT143 : ∀ i, IotaEquationTypedT dRec143.1 i (dRec143.2.fuelAt i) (dRec143.2.shapesAt i) :=
  iotaEqsT_of iotaAllB143
def idxT143 : IdxAdmittedT admRecValueAt := FunRecTyped.vaRecIdxAdmittedT
def typedRec143 : IndGroupTypedT admRecValueAt :=
  ⟨famTypedT_of (fuel := 96) dRec143.1.family famB143,
   ctorTypedAll_of ctorB143,
   iotaT143⟩
def mem133 : GroupMembersT (extendEnv (envPre 133) 133 mValueAt) (envPre 133)
    [(133, mValueAt), (134, mVaB0), (135, mVaB1), (136, mVaI64), (137, mVaStr), (138, mVaY), (139, mVaList), (140, mVaPair), (141, mVaJ), (142, mVaR), (143, recValueAt)] (extendEnv (envPre 143) 143 recValueAt) :=
  (GroupMembersT.cons _ 133 mValueAt _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamValueAt PUnit.unit _ tyT133.2 (fun h => absurd h (by decide)) typedFam133
    (GroupMembersT.cons _ 134 mVaB0 _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorVaB0 PUnit.unit _ tyT134.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS134).2⟩) typedCtor134
    (GroupMembersT.cons _ 135 mVaB1 _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorVaB1 PUnit.unit _ tyT135.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS135).2⟩) typedCtor135
    (GroupMembersT.cons _ 136 mVaI64 _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorVaI64 PUnit.unit _ tyT136.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS136).2⟩) typedCtor136
    (GroupMembersT.cons _ 137 mVaStr _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorVaStr PUnit.unit _ tyT137.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS137).2⟩) typedCtor137
    (GroupMembersT.cons _ 138 mVaY _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorVaY PUnit.unit _ tyT138.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS138).2⟩) typedCtor138
    (GroupMembersT.cons _ 139 mVaList _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorVaList PUnit.unit _ tyT139.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS139).2⟩) typedCtor139
    (GroupMembersT.cons _ 140 mVaPair _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorVaPair PUnit.unit _ tyT140.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS140).2⟩) typedCtor140
    (GroupMembersT.cons _ 141 mVaJ _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorVaJ PUnit.unit _ tyT141.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS141).2⟩) typedCtor141
    (GroupMembersT.cons _ 142 mVaR _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorVaR PUnit.unit _ tyT142.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS142).2⟩) typedCtor142
    (GroupMembersT.cons _ 143 recValueAt _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecValueAt idxT143 _ tyT143.2 (fun h => absurd h (by decide)) typedRec143
    (.nil _))))))))))))
def wft144 : EnvWfT (envPre 144) :=
  wfTOfExtend (r := 143) (m := recValueAt) (by decide) rfl
    (.group (envPre 133) 133 mValueAt [(134, mVaB0), (135, mVaB1), (136, mVaI64), (137, mVaStr), (138, mVaY), (139, mVaList), (140, mVaPair), (141, mVaJ), (142, mVaR)] 143 recValueAt _ wft133 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) rfl mem133)

end Rcic.Scm.SrcG

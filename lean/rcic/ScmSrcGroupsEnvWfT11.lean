import rcic.ScmSrcGroupsEnvWfT10
import rcic.ScmSrcGroupsFunRecTypedEq

/-! `EnvWfT` for srcEnvG slots in this file's range. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/- slots 96–105: family mCCT, recursor recCCT -/
kernel_rfl_theorem tyB96 : (sortTyAtC (envPre 96) mCCT.arity 96 [] mCCT.mtype).isSome = true
def tyT96 : Σ u, HasTyT (envPre 96) mCCT.arity [] mCCT.mtype (.sort u) :=
  (sortTyAtC (envPre 96) mCCT.arity 96 [] mCCT.mtype).get tyB96
kernel_rfl_theorem tyB97 : (sortTyAtC (envPre 97) mCctI.arity 96 [] mCctI.mtype).isSome = true
def tyT97 : Σ u, HasTyT (envPre 97) mCctI.arity [] mCctI.mtype (.sort u) :=
  (sortTyAtC (envPre 97) mCctI.arity 96 [] mCctI.mtype).get tyB97
kernel_rfl_theorem tyS97 : (sortTyAtC (extendEnv (envPre 96) 96 mCCT) mCctI.arity 96 [] mCctI.mtype).isSome = true
kernel_rfl_theorem tyB98 : (sortTyAtC (envPre 98) mCctB.arity 96 [] mCctB.mtype).isSome = true
def tyT98 : Σ u, HasTyT (envPre 98) mCctB.arity [] mCctB.mtype (.sort u) :=
  (sortTyAtC (envPre 98) mCctB.arity 96 [] mCctB.mtype).get tyB98
kernel_rfl_theorem tyS98 : (sortTyAtC (extendEnv (envPre 96) 96 mCCT) mCctB.arity 96 [] mCctB.mtype).isSome = true
kernel_rfl_theorem tyB99 : (sortTyAtC (envPre 99) mCctStr.arity 96 [] mCctStr.mtype).isSome = true
def tyT99 : Σ u, HasTyT (envPre 99) mCctStr.arity [] mCctStr.mtype (.sort u) :=
  (sortTyAtC (envPre 99) mCctStr.arity 96 [] mCctStr.mtype).get tyB99
kernel_rfl_theorem tyS99 : (sortTyAtC (extendEnv (envPre 96) 96 mCCT) mCctStr.arity 96 [] mCctStr.mtype).isSome = true
kernel_rfl_theorem tyB100 : (sortTyAtC (envPre 100) mCctY.arity 96 [] mCctY.mtype).isSome = true
def tyT100 : Σ u, HasTyT (envPre 100) mCctY.arity [] mCctY.mtype (.sort u) :=
  (sortTyAtC (envPre 100) mCctY.arity 96 [] mCctY.mtype).get tyB100
kernel_rfl_theorem tyS100 : (sortTyAtC (extendEnv (envPre 96) 96 mCCT) mCctY.arity 96 [] mCctY.mtype).isSome = true
kernel_rfl_theorem tyB101 : (sortTyAtC (envPre 101) mCctL.arity 96 [] mCctL.mtype).isSome = true
def tyT101 : Σ u, HasTyT (envPre 101) mCctL.arity [] mCctL.mtype (.sort u) :=
  (sortTyAtC (envPre 101) mCctL.arity 96 [] mCctL.mtype).get tyB101
kernel_rfl_theorem tyS101 : (sortTyAtC (extendEnv (envPre 96) 96 mCCT) mCctL.arity 96 [] mCctL.mtype).isSome = true
kernel_rfl_theorem tyB102 : (sortTyAtC (envPre 102) mCctP.arity 96 [] mCctP.mtype).isSome = true
def tyT102 : Σ u, HasTyT (envPre 102) mCctP.arity [] mCctP.mtype (.sort u) :=
  (sortTyAtC (envPre 102) mCctP.arity 96 [] mCctP.mtype).get tyB102
kernel_rfl_theorem tyS102 : (sortTyAtC (extendEnv (envPre 96) 96 mCCT) mCctP.arity 96 [] mCctP.mtype).isSome = true
kernel_rfl_theorem tyB103 : (sortTyAtC (envPre 103) mCctSum.arity 96 [] mCctSum.mtype).isSome = true
def tyT103 : Σ u, HasTyT (envPre 103) mCctSum.arity [] mCctSum.mtype (.sort u) :=
  (sortTyAtC (envPre 103) mCctSum.arity 96 [] mCctSum.mtype).get tyB103
kernel_rfl_theorem tyS103 : (sortTyAtC (extendEnv (envPre 96) 96 mCCT) mCctSum.arity 96 [] mCctSum.mtype).isSome = true
kernel_rfl_theorem tyB104 : (sortTyAtC (envPre 104) mCctRec.arity 96 [] mCctRec.mtype).isSome = true
def tyT104 : Σ u, HasTyT (envPre 104) mCctRec.arity [] mCctRec.mtype (.sort u) :=
  (sortTyAtC (envPre 104) mCctRec.arity 96 [] mCctRec.mtype).get tyB104
kernel_rfl_theorem tyS104 : (sortTyAtC (extendEnv (envPre 96) 96 mCCT) mCctRec.arity 96 [] mCctRec.mtype).isSome = true
kernel_rfl_theorem tyB105 : (sortTyAtC (envPre 105) recCCT.arity 96 [] recCCT.mtype).isSome = true
def tyT105 : Σ u, HasTyT (envPre 105) recCCT.arity [] recCCT.mtype (.sort u) :=
  (sortTyAtC (envPre 105) recCCT.arity 96 [] recCCT.mtype).get tyB105
def dFam96 := (admFamView? admFamCCT).get rfl
def dCtor97 := (admCtorViews? admCtorCctI).get rfl
def dCtor98 := (admCtorViews? admCtorCctB).get rfl
def dCtor99 := (admCtorViews? admCtorCctStr).get rfl
def dCtor100 := (admCtorViews? admCtorCctY).get rfl
def dCtor101 := (admCtorViews? admCtorCctL).get rfl
def dCtor102 := (admCtorViews? admCtorCctP).get rfl
def dCtor103 := (admCtorViews? admCtorCctSum).get rfl
def dCtor104 := (admCtorViews? admCtorCctRec).get rfl
def dRec105 := (admRecData admRecCCT).get rfl
kernel_rfl_theorem famB96 : famTypedB (extendEnv (envPre 96) 96 mCCT) 96 dFam96 = true
kernel_rfl_theorem famB97 : famTypedB (envPre 97) 96 dCtor97.1 = true
kernel_rfl_theorem ctorB97 : ctorTypedB 96 dCtor97.2.2 = true
kernel_rfl_theorem famB98 : famTypedB (envPre 98) 96 dCtor98.1 = true
kernel_rfl_theorem ctorB98 : ctorTypedB 96 dCtor98.2.2 = true
kernel_rfl_theorem famB99 : famTypedB (envPre 99) 96 dCtor99.1 = true
kernel_rfl_theorem ctorB99 : ctorTypedB 96 dCtor99.2.2 = true
kernel_rfl_theorem famB100 : famTypedB (envPre 100) 96 dCtor100.1 = true
kernel_rfl_theorem ctorB100 : ctorTypedB 96 dCtor100.2.2 = true
kernel_rfl_theorem famB101 : famTypedB (envPre 101) 96 dCtor101.1 = true
kernel_rfl_theorem ctorB101 : ctorTypedB 96 dCtor101.2.2 = true
kernel_rfl_theorem famB102 : famTypedB (envPre 102) 96 dCtor102.1 = true
kernel_rfl_theorem ctorB102 : ctorTypedB 96 dCtor102.2.2 = true
kernel_rfl_theorem famB103 : famTypedB (envPre 103) 96 dCtor103.1 = true
kernel_rfl_theorem ctorB103 : ctorTypedB 96 dCtor103.2.2 = true
kernel_rfl_theorem famB104 : famTypedB (envPre 104) 96 dCtor104.1 = true
kernel_rfl_theorem ctorB104 : ctorTypedB 96 dCtor104.2.2 = true
kernel_rfl_theorem famB105 : famTypedB (envPre 105) 96 dRec105.1.family = true
kernel_rfl_theorem ctorB105 : ctorTypedAllB 96 dRec105.1 = true
theorem idxB105 : recIdxAdmittedTB dRec105.1 dRec105.2 = true := FunRecTyped.cctRecIdxAdmittedB
kernel_rfl_theorem iotaB105_0 : iotaEqB (a := dRec105.1) (h14 := dRec105.2) (synCheck (extendEnv (envPre 105) 105 recCCT) recCCT.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB105_1 : iotaEqB (a := dRec105.1) (h14 := dRec105.2) (synCheck (extendEnv (envPre 105) 105 recCCT) recCCT.arity) 1 (by decide) = true
kernel_rfl_theorem iotaB105_2 : iotaEqB (a := dRec105.1) (h14 := dRec105.2) (synCheck (extendEnv (envPre 105) 105 recCCT) recCCT.arity) 2 (by decide) = true
kernel_rfl_theorem iotaB105_3 : iotaEqB (a := dRec105.1) (h14 := dRec105.2) (synCheck (extendEnv (envPre 105) 105 recCCT) recCCT.arity) 3 (by decide) = true
kernel_rfl_theorem iotaB105_4 : iotaEqB (a := dRec105.1) (h14 := dRec105.2) (synCheck (extendEnv (envPre 105) 105 recCCT) recCCT.arity) 4 (by decide) = true
kernel_rfl_theorem iotaB105_5 : iotaEqB (a := dRec105.1) (h14 := dRec105.2) (synCheck (extendEnv (envPre 105) 105 recCCT) recCCT.arity) 5 (by decide) = true
kernel_rfl_theorem iotaB105_6 : iotaEqB (a := dRec105.1) (h14 := dRec105.2) (synCheck (extendEnv (envPre 105) 105 recCCT) recCCT.arity) 6 (by decide) = true
kernel_rfl_theorem iotaB105_7 : iotaEqB (a := dRec105.1) (h14 := dRec105.2) (synCheck (extendEnv (envPre 105) 105 recCCT) recCCT.arity) 7 (by decide) = true
def typedFam96 : IndGroupTypedT admFamCCT := famTypedT_of (fuel := 96) dFam96 famB96
def typedCtor97 : IndGroupTypedT admCtorCctI :=
  ⟨famTypedT_of (fuel := 96) dCtor97.1 famB97, ctorTypedT_of (fuel := 96) ctorB97⟩
def typedCtor98 : IndGroupTypedT admCtorCctB :=
  ⟨famTypedT_of (fuel := 96) dCtor98.1 famB98, ctorTypedT_of (fuel := 96) ctorB98⟩
def typedCtor99 : IndGroupTypedT admCtorCctStr :=
  ⟨famTypedT_of (fuel := 96) dCtor99.1 famB99, ctorTypedT_of (fuel := 96) ctorB99⟩
def typedCtor100 : IndGroupTypedT admCtorCctY :=
  ⟨famTypedT_of (fuel := 96) dCtor100.1 famB100, ctorTypedT_of (fuel := 96) ctorB100⟩
def typedCtor101 : IndGroupTypedT admCtorCctL :=
  ⟨famTypedT_of (fuel := 96) dCtor101.1 famB101, ctorTypedT_of (fuel := 96) ctorB101⟩
def typedCtor102 : IndGroupTypedT admCtorCctP :=
  ⟨famTypedT_of (fuel := 96) dCtor102.1 famB102, ctorTypedT_of (fuel := 96) ctorB102⟩
def typedCtor103 : IndGroupTypedT admCtorCctSum :=
  ⟨famTypedT_of (fuel := 96) dCtor103.1 famB103, ctorTypedT_of (fuel := 96) ctorB103⟩
def typedCtor104 : IndGroupTypedT admCtorCctRec :=
  ⟨famTypedT_of (fuel := 96) dCtor104.1 famB104, ctorTypedT_of (fuel := 96) ctorB104⟩
theorem iotaAllB105 : finAllB dRec105.1.constructors.length
    (iotaEqB (a := dRec105.1) (h14 := dRec105.2) (synCheck (extendEnv (envPre 105) 105 recCCT) recCCT.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB105_0
    | 1 => iotaB105_1
    | 2 => iotaB105_2
    | 3 => iotaB105_3
    | 4 => iotaB105_4
    | 5 => iotaB105_5
    | 6 => iotaB105_6
    | 7 => iotaB105_7
    | k+8 => absurd hi (by have : dRec105.1.constructors.length = 8 := rfl; omega)
def iotaT105 : ∀ i, IotaEquationTypedT dRec105.1 i (dRec105.2.fuelAt i) (dRec105.2.shapesAt i) :=
  iotaEqsT_of iotaAllB105
def idxT105 : IdxAdmittedT admRecCCT := FunRecTyped.cctRecIdxAdmittedT
def typedRec105 : IndGroupTypedT admRecCCT :=
  ⟨famTypedT_of (fuel := 96) dRec105.1.family famB105,
   ctorTypedAll_of ctorB105,
   iotaT105⟩
def mem96 : GroupMembersT (extendEnv (envPre 96) 96 mCCT) (envPre 96)
    [(96, mCCT), (97, mCctI), (98, mCctB), (99, mCctStr), (100, mCctY), (101, mCctL), (102, mCctP), (103, mCctSum), (104, mCctRec), (105, recCCT)] (extendEnv (envPre 105) 105 recCCT) :=
  (GroupMembersT.cons _ 96 mCCT _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamCCT PUnit.unit _ tyT96.2 (fun h => absurd h (by decide)) typedFam96
    (GroupMembersT.cons _ 97 mCctI _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorCctI PUnit.unit _ tyT97.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS97).2⟩) typedCtor97
    (GroupMembersT.cons _ 98 mCctB _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorCctB PUnit.unit _ tyT98.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS98).2⟩) typedCtor98
    (GroupMembersT.cons _ 99 mCctStr _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorCctStr PUnit.unit _ tyT99.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS99).2⟩) typedCtor99
    (GroupMembersT.cons _ 100 mCctY _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorCctY PUnit.unit _ tyT100.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS100).2⟩) typedCtor100
    (GroupMembersT.cons _ 101 mCctL _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorCctL PUnit.unit _ tyT101.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS101).2⟩) typedCtor101
    (GroupMembersT.cons _ 102 mCctP _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorCctP PUnit.unit _ tyT102.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS102).2⟩) typedCtor102
    (GroupMembersT.cons _ 103 mCctSum _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorCctSum PUnit.unit _ tyT103.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS103).2⟩) typedCtor103
    (GroupMembersT.cons _ 104 mCctRec _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorCctRec PUnit.unit _ tyT104.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS104).2⟩) typedCtor104
    (GroupMembersT.cons _ 105 recCCT _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecCCT idxT105 _ tyT105.2 (fun h => absurd h (by decide)) typedRec105
    (.nil _)))))))))))
def wft106 : EnvWfT (envPre 106) :=
  wfTOfExtend (r := 105) (m := recCCT) (by decide) rfl
    (.group (envPre 96) 96 mCCT [(97, mCctI), (98, mCctB), (99, mCctStr), (100, mCctY), (101, mCctL), (102, mCctP), (103, mCctSum), (104, mCctRec)] 105 recCCT _ wft96 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) rfl mem96)

end Rcic.Scm.SrcG

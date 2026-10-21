import rcic.ScmSrcGroupsEnvWfT3

/-! `EnvWfT` for srcEnvG slots in this file's range. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/- slots 30–33: family mI, recursor recI -/
kernel_rfl_theorem tyB30 : (sortTyAtC (envPre 30) mI.arity 96 [] mI.mtype).isSome = true
def tyT30 : Σ u, HasTyT (envPre 30) mI.arity [] mI.mtype (.sort u) :=
  (sortTyAtC (envPre 30) mI.arity 96 [] mI.mtype).get tyB30
kernel_rfl_theorem tyB31 : (sortTyAtC (envPre 31) mIPos.arity 96 [] mIPos.mtype).isSome = true
def tyT31 : Σ u, HasTyT (envPre 31) mIPos.arity [] mIPos.mtype (.sort u) :=
  (sortTyAtC (envPre 31) mIPos.arity 96 [] mIPos.mtype).get tyB31
kernel_rfl_theorem tyS31 : (sortTyAtC (extendEnv (envPre 30) 30 mI) mIPos.arity 96 [] mIPos.mtype).isSome = true
kernel_rfl_theorem tyB32 : (sortTyAtC (envPre 32) mINegS.arity 96 [] mINegS.mtype).isSome = true
def tyT32 : Σ u, HasTyT (envPre 32) mINegS.arity [] mINegS.mtype (.sort u) :=
  (sortTyAtC (envPre 32) mINegS.arity 96 [] mINegS.mtype).get tyB32
kernel_rfl_theorem tyS32 : (sortTyAtC (extendEnv (envPre 30) 30 mI) mINegS.arity 96 [] mINegS.mtype).isSome = true
kernel_rfl_theorem tyB33 : (sortTyAtC (envPre 33) recI.arity 96 [] recI.mtype).isSome = true
def tyT33 : Σ u, HasTyT (envPre 33) recI.arity [] recI.mtype (.sort u) :=
  (sortTyAtC (envPre 33) recI.arity 96 [] recI.mtype).get tyB33
def dFam30 := (admFamView? admFamI).get rfl
def dCtor31 := (admCtorViews? admCtorIPos).get rfl
def dCtor32 := (admCtorViews? admCtorINegS).get rfl
def dRec33 := (admRecData admRecI).get rfl
kernel_rfl_theorem famB30 : famTypedB (extendEnv (envPre 30) 30 mI) 96 dFam30 = true
kernel_rfl_theorem famB31 : famTypedB (envPre 31) 96 dCtor31.1 = true
kernel_rfl_theorem ctorB31 : ctorTypedB 96 dCtor31.2.2 = true
kernel_rfl_theorem famB32 : famTypedB (envPre 32) 96 dCtor32.1 = true
kernel_rfl_theorem ctorB32 : ctorTypedB 96 dCtor32.2.2 = true
kernel_rfl_theorem famB33 : famTypedB (envPre 33) 96 dRec33.1.family = true
kernel_rfl_theorem ctorB33 : ctorTypedAllB 96 dRec33.1 = true
kernel_rfl_theorem idxB33 : recIdxAdmittedTB dRec33.1 dRec33.2 = true
kernel_rfl_theorem iotaB33_0 : iotaEqB (a := dRec33.1) (h14 := dRec33.2) (synCheck (extendEnv (envPre 33) 33 recI) recI.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB33_1 : iotaEqB (a := dRec33.1) (h14 := dRec33.2) (synCheck (extendEnv (envPre 33) 33 recI) recI.arity) 1 (by decide) = true
def typedFam30 : IndGroupTypedT admFamI := famTypedT_of (fuel := 96) dFam30 famB30
def typedCtor31 : IndGroupTypedT admCtorIPos :=
  ⟨famTypedT_of (fuel := 96) dCtor31.1 famB31, ctorTypedT_of (fuel := 96) ctorB31⟩
def typedCtor32 : IndGroupTypedT admCtorINegS :=
  ⟨famTypedT_of (fuel := 96) dCtor32.1 famB32, ctorTypedT_of (fuel := 96) ctorB32⟩
theorem iotaAllB33 : finAllB dRec33.1.constructors.length
    (iotaEqB (a := dRec33.1) (h14 := dRec33.2) (synCheck (extendEnv (envPre 33) 33 recI) recI.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB33_0
    | 1 => iotaB33_1
    | k+2 => absurd hi (by have : dRec33.1.constructors.length = 2 := rfl; omega)
def iotaT33 : ∀ i, IotaEquationTypedT dRec33.1 i (dRec33.2.fuelAt i) (dRec33.2.shapesAt i) :=
  iotaEqsT_of iotaAllB33
def idxT33 : IdxAdmittedT admRecI := idxT_of admRecI idxB33
def typedRec33 : IndGroupTypedT admRecI :=
  ⟨famTypedT_of (fuel := 96) dRec33.1.family famB33,
   ctorTypedAll_of ctorB33,
   iotaT33⟩
def mem30 : GroupMembersT (extendEnv (envPre 30) 30 mI) (envPre 30)
    [(30, mI), (31, mIPos), (32, mINegS), (33, recI)] (extendEnv (envPre 33) 33 recI) :=
  (GroupMembersT.cons _ 30 mI _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamI PUnit.unit _ tyT30.2 (fun h => absurd h (by decide)) typedFam30
    (GroupMembersT.cons _ 31 mIPos _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorIPos PUnit.unit _ tyT31.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS31).2⟩) typedCtor31
    (GroupMembersT.cons _ 32 mINegS _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorINegS PUnit.unit _ tyT32.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS32).2⟩) typedCtor32
    (GroupMembersT.cons _ 33 recI _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecI idxT33 _ tyT33.2 (fun h => absurd h (by decide)) typedRec33
    (.nil _)))))
def wft34 : EnvWfT (envPre 34) :=
  wfTOfExtend (r := 33) (m := recI) (by decide) rfl
    (.group (envPre 30) 30 mI [(31, mIPos), (32, mINegS)] 33 recI _ wft30 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem30)
/- slots 34–37: family mBL, recursor recBL -/
kernel_rfl_theorem tyB34 : (sortTyAtC (envPre 34) mBL.arity 96 [] mBL.mtype).isSome = true
def tyT34 : Σ u, HasTyT (envPre 34) mBL.arity [] mBL.mtype (.sort u) :=
  (sortTyAtC (envPre 34) mBL.arity 96 [] mBL.mtype).get tyB34
kernel_rfl_theorem tyB35 : (sortTyAtC (envPre 35) mBlNil.arity 96 [] mBlNil.mtype).isSome = true
def tyT35 : Σ u, HasTyT (envPre 35) mBlNil.arity [] mBlNil.mtype (.sort u) :=
  (sortTyAtC (envPre 35) mBlNil.arity 96 [] mBlNil.mtype).get tyB35
kernel_rfl_theorem tyS35 : (sortTyAtC (extendEnv (envPre 34) 34 mBL) mBlNil.arity 96 [] mBlNil.mtype).isSome = true
kernel_rfl_theorem tyB36 : (sortTyAtC (envPre 36) mBlCons.arity 96 [] mBlCons.mtype).isSome = true
def tyT36 : Σ u, HasTyT (envPre 36) mBlCons.arity [] mBlCons.mtype (.sort u) :=
  (sortTyAtC (envPre 36) mBlCons.arity 96 [] mBlCons.mtype).get tyB36
kernel_rfl_theorem tyS36 : (sortTyAtC (extendEnv (envPre 34) 34 mBL) mBlCons.arity 96 [] mBlCons.mtype).isSome = true
kernel_rfl_theorem tyB37 : (sortTyAtC (envPre 37) recBL.arity 96 [] recBL.mtype).isSome = true
def tyT37 : Σ u, HasTyT (envPre 37) recBL.arity [] recBL.mtype (.sort u) :=
  (sortTyAtC (envPre 37) recBL.arity 96 [] recBL.mtype).get tyB37
def dFam34 := (admFamView? admFamBL).get rfl
def dCtor35 := (admCtorViews? admCtorBlNil).get rfl
def dCtor36 := (admCtorViews? admCtorBlCons).get rfl
def dRec37 := (admRecData admRecBL).get rfl
kernel_rfl_theorem famB34 : famTypedB (extendEnv (envPre 34) 34 mBL) 96 dFam34 = true
kernel_rfl_theorem famB35 : famTypedB (envPre 35) 96 dCtor35.1 = true
kernel_rfl_theorem ctorB35 : ctorTypedB 96 dCtor35.2.2 = true
kernel_rfl_theorem famB36 : famTypedB (envPre 36) 96 dCtor36.1 = true
kernel_rfl_theorem ctorB36 : ctorTypedB 96 dCtor36.2.2 = true
kernel_rfl_theorem famB37 : famTypedB (envPre 37) 96 dRec37.1.family = true
kernel_rfl_theorem ctorB37 : ctorTypedAllB 96 dRec37.1 = true
kernel_rfl_theorem idxB37 : recIdxAdmittedTB dRec37.1 dRec37.2 = true
kernel_rfl_theorem iotaB37_0 : iotaEqB (a := dRec37.1) (h14 := dRec37.2) (synCheck (extendEnv (envPre 37) 37 recBL) recBL.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB37_1 : iotaEqB (a := dRec37.1) (h14 := dRec37.2) (synCheck (extendEnv (envPre 37) 37 recBL) recBL.arity) 1 (by decide) = true
def typedFam34 : IndGroupTypedT admFamBL := famTypedT_of (fuel := 96) dFam34 famB34
def typedCtor35 : IndGroupTypedT admCtorBlNil :=
  ⟨famTypedT_of (fuel := 96) dCtor35.1 famB35, ctorTypedT_of (fuel := 96) ctorB35⟩
def typedCtor36 : IndGroupTypedT admCtorBlCons :=
  ⟨famTypedT_of (fuel := 96) dCtor36.1 famB36, ctorTypedT_of (fuel := 96) ctorB36⟩
theorem iotaAllB37 : finAllB dRec37.1.constructors.length
    (iotaEqB (a := dRec37.1) (h14 := dRec37.2) (synCheck (extendEnv (envPre 37) 37 recBL) recBL.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB37_0
    | 1 => iotaB37_1
    | k+2 => absurd hi (by have : dRec37.1.constructors.length = 2 := rfl; omega)
def iotaT37 : ∀ i, IotaEquationTypedT dRec37.1 i (dRec37.2.fuelAt i) (dRec37.2.shapesAt i) :=
  iotaEqsT_of iotaAllB37
def idxT37 : IdxAdmittedT admRecBL := idxT_of admRecBL idxB37
def typedRec37 : IndGroupTypedT admRecBL :=
  ⟨famTypedT_of (fuel := 96) dRec37.1.family famB37,
   ctorTypedAll_of ctorB37,
   iotaT37⟩
def mem34 : GroupMembersT (extendEnv (envPre 34) 34 mBL) (envPre 34)
    [(34, mBL), (35, mBlNil), (36, mBlCons), (37, recBL)] (extendEnv (envPre 37) 37 recBL) :=
  (GroupMembersT.cons _ 34 mBL _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamBL PUnit.unit _ tyT34.2 (fun h => absurd h (by decide)) typedFam34
    (GroupMembersT.cons _ 35 mBlNil _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorBlNil PUnit.unit _ tyT35.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS35).2⟩) typedCtor35
    (GroupMembersT.cons _ 36 mBlCons _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorBlCons PUnit.unit _ tyT36.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS36).2⟩) typedCtor36
    (GroupMembersT.cons _ 37 recBL _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecBL idxT37 _ tyT37.2 (fun h => absurd h (by decide)) typedRec37
    (.nil _)))))
def wft38 : EnvWfT (envPre 38) :=
  wfTOfExtend (r := 37) (m := recBL) (by decide) rfl
    (.group (envPre 34) 34 mBL [(35, mBlNil), (36, mBlCons)] 37 recBL _ wft34 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem34)

end Rcic.Scm.SrcG

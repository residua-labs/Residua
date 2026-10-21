import rcic.ScmSrcGroupsEnvWfT4

/-! `EnvWfT` for srcEnvG slots in this file's range. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/- slots 38–41: family mFT, recursor recFT -/
kernel_rfl_theorem tyB38 : (sortTyAtC (envPre 38) mFT.arity 96 [] mFT.mtype).isSome = true
def tyT38 : Σ u, HasTyT (envPre 38) mFT.arity [] mFT.mtype (.sort u) :=
  (sortTyAtC (envPre 38) mFT.arity 96 [] mFT.mtype).get tyB38
kernel_rfl_theorem tyB39 : (sortTyAtC (envPre 39) mFtNil.arity 96 [] mFtNil.mtype).isSome = true
def tyT39 : Σ u, HasTyT (envPre 39) mFtNil.arity [] mFtNil.mtype (.sort u) :=
  (sortTyAtC (envPre 39) mFtNil.arity 96 [] mFtNil.mtype).get tyB39
kernel_rfl_theorem tyS39 : (sortTyAtC (extendEnv (envPre 38) 38 mFT) mFtNil.arity 96 [] mFtNil.mtype).isSome = true
kernel_rfl_theorem tyB40 : (sortTyAtC (envPre 40) mFtCons.arity 96 [] mFtCons.mtype).isSome = true
def tyT40 : Σ u, HasTyT (envPre 40) mFtCons.arity [] mFtCons.mtype (.sort u) :=
  (sortTyAtC (envPre 40) mFtCons.arity 96 [] mFtCons.mtype).get tyB40
kernel_rfl_theorem tyS40 : (sortTyAtC (extendEnv (envPre 38) 38 mFT) mFtCons.arity 96 [] mFtCons.mtype).isSome = true
kernel_rfl_theorem tyB41 : (sortTyAtC (envPre 41) recFT.arity 96 [] recFT.mtype).isSome = true
def tyT41 : Σ u, HasTyT (envPre 41) recFT.arity [] recFT.mtype (.sort u) :=
  (sortTyAtC (envPre 41) recFT.arity 96 [] recFT.mtype).get tyB41
def dFam38 := (admFamView? admFamFT).get rfl
def dCtor39 := (admCtorViews? admCtorFtNil).get rfl
def dCtor40 := (admCtorViews? admCtorFtCons).get rfl
def dRec41 := (admRecData admRecFT).get rfl
kernel_rfl_theorem famB38 : famTypedB (extendEnv (envPre 38) 38 mFT) 96 dFam38 = true
kernel_rfl_theorem famB39 : famTypedB (envPre 39) 96 dCtor39.1 = true
kernel_rfl_theorem ctorB39 : ctorTypedB 96 dCtor39.2.2 = true
kernel_rfl_theorem famB40 : famTypedB (envPre 40) 96 dCtor40.1 = true
kernel_rfl_theorem ctorB40 : ctorTypedB 96 dCtor40.2.2 = true
kernel_rfl_theorem famB41 : famTypedB (envPre 41) 96 dRec41.1.family = true
kernel_rfl_theorem ctorB41 : ctorTypedAllB 96 dRec41.1 = true
kernel_rfl_theorem idxB41 : recIdxAdmittedTB dRec41.1 dRec41.2 = true
kernel_rfl_theorem iotaB41_0 : iotaEqB (a := dRec41.1) (h14 := dRec41.2) (synCheck (extendEnv (envPre 41) 41 recFT) recFT.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB41_1 : iotaEqB (a := dRec41.1) (h14 := dRec41.2) (synCheck (extendEnv (envPre 41) 41 recFT) recFT.arity) 1 (by decide) = true
def typedFam38 : IndGroupTypedT admFamFT := famTypedT_of (fuel := 96) dFam38 famB38
def typedCtor39 : IndGroupTypedT admCtorFtNil :=
  ⟨famTypedT_of (fuel := 96) dCtor39.1 famB39, ctorTypedT_of (fuel := 96) ctorB39⟩
def typedCtor40 : IndGroupTypedT admCtorFtCons :=
  ⟨famTypedT_of (fuel := 96) dCtor40.1 famB40, ctorTypedT_of (fuel := 96) ctorB40⟩
theorem iotaAllB41 : finAllB dRec41.1.constructors.length
    (iotaEqB (a := dRec41.1) (h14 := dRec41.2) (synCheck (extendEnv (envPre 41) 41 recFT) recFT.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB41_0
    | 1 => iotaB41_1
    | k+2 => absurd hi (by have : dRec41.1.constructors.length = 2 := rfl; omega)
def iotaT41 : ∀ i, IotaEquationTypedT dRec41.1 i (dRec41.2.fuelAt i) (dRec41.2.shapesAt i) :=
  iotaEqsT_of iotaAllB41
def idxT41 : IdxAdmittedT admRecFT := idxT_of admRecFT idxB41
def typedRec41 : IndGroupTypedT admRecFT :=
  ⟨famTypedT_of (fuel := 96) dRec41.1.family famB41,
   ctorTypedAll_of ctorB41,
   iotaT41⟩
def mem38 : GroupMembersT (extendEnv (envPre 38) 38 mFT) (envPre 38)
    [(38, mFT), (39, mFtNil), (40, mFtCons), (41, recFT)] (extendEnv (envPre 41) 41 recFT) :=
  (GroupMembersT.cons _ 38 mFT _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamFT PUnit.unit _ tyT38.2 (fun h => absurd h (by decide)) typedFam38
    (GroupMembersT.cons _ 39 mFtNil _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorFtNil PUnit.unit _ tyT39.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS39).2⟩) typedCtor39
    (GroupMembersT.cons _ 40 mFtCons _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorFtCons PUnit.unit _ tyT40.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS40).2⟩) typedCtor40
    (GroupMembersT.cons _ 41 recFT _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecFT idxT41 _ tyT41.2 (fun h => absurd h (by decide)) typedRec41
    (.nil _)))))
def wft42 : EnvWfT (envPre 42) :=
  wfTOfExtend (r := 41) (m := recFT) (by decide) rfl
    (.group (envPre 38) 38 mFT [(39, mFtNil), (40, mFtCons)] 41 recFT _ wft38 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem38)
/- slots 42–45: family mLt, recursor recLt -/
kernel_rfl_theorem tyB42 : (sortTyAtC (envPre 42) mLt.arity 96 [] mLt.mtype).isSome = true
def tyT42 : Σ u, HasTyT (envPre 42) mLt.arity [] mLt.mtype (.sort u) :=
  (sortTyAtC (envPre 42) mLt.arity 96 [] mLt.mtype).get tyB42
kernel_rfl_theorem tyB43 : (sortTyAtC (envPre 43) mLtBase.arity 96 [] mLtBase.mtype).isSome = true
def tyT43 : Σ u, HasTyT (envPre 43) mLtBase.arity [] mLtBase.mtype (.sort u) :=
  (sortTyAtC (envPre 43) mLtBase.arity 96 [] mLtBase.mtype).get tyB43
kernel_rfl_theorem tyS43 : (sortTyAtC (extendEnv (envPre 42) 42 mLt) mLtBase.arity 96 [] mLtBase.mtype).isSome = true
kernel_rfl_theorem tyB44 : (sortTyAtC (envPre 44) mLtStep.arity 96 [] mLtStep.mtype).isSome = true
def tyT44 : Σ u, HasTyT (envPre 44) mLtStep.arity [] mLtStep.mtype (.sort u) :=
  (sortTyAtC (envPre 44) mLtStep.arity 96 [] mLtStep.mtype).get tyB44
kernel_rfl_theorem tyS44 : (sortTyAtC (extendEnv (envPre 42) 42 mLt) mLtStep.arity 96 [] mLtStep.mtype).isSome = true
kernel_rfl_theorem tyB45 : (sortTyAtC (envPre 45) recLt.arity 96 [] recLt.mtype).isSome = true
def tyT45 : Σ u, HasTyT (envPre 45) recLt.arity [] recLt.mtype (.sort u) :=
  (sortTyAtC (envPre 45) recLt.arity 96 [] recLt.mtype).get tyB45
def dFam42 := (admFamView? admFamLt).get rfl
def dCtor43 := (admCtorViews? admCtorLtBase).get rfl
def dCtor44 := (admCtorViews? admCtorLtStep).get rfl
def dRec45 := (admRecData admRecLt).get rfl
kernel_rfl_theorem famB42 : famTypedB (extendEnv (envPre 42) 42 mLt) 96 dFam42 = true
kernel_rfl_theorem famB43 : famTypedB (envPre 43) 96 dCtor43.1 = true
kernel_rfl_theorem ctorB43 : ctorTypedB 96 dCtor43.2.2 = true
kernel_rfl_theorem famB44 : famTypedB (envPre 44) 96 dCtor44.1 = true
kernel_rfl_theorem ctorB44 : ctorTypedB 96 dCtor44.2.2 = true
kernel_rfl_theorem famB45 : famTypedB (envPre 45) 96 dRec45.1.family = true
kernel_rfl_theorem ctorB45 : ctorTypedAllB 96 dRec45.1 = true
kernel_rfl_theorem freshB45 : ((envPre 45).members 45).isNone = true
theorem classB45 : (match recLt.mclass with | .recursorM => true | _ => false) = true := rfl
kernel_rfl_theorem mtB45 : Rcic.Declarative.exprClosedAt 0 recLt.mtype = true
theorem famX45 : (extendEnv (envPre 45) 45 recLt).members dRec45.1.family.ref = some dRec45.1.family.member := by
  rw [extendEnv_members_ne (by decide : dRec45.1.family.ref ≠ 45)]
  exact dRec45.1.family.present
kernel_rfl_theorem ixC45_0 : Rcic.Declarative.exprClosedAt 0 (dRec45.1.constructors[0]'(by decide)).mtype = true
kernel_rfl_theorem ixF45_0E : (dRec45.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (envPre 45) (dRec45.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR45_0E0 : constsMemberFuel (envPre 45) (dRec45.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec45.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR45_0E1 : constsMemberFuel (envPre 45) (dRec45.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec45.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri45_0E : (dRec45.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (envPre 45) (dRec45.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR45_0E0
    | 1 => ixR45_0E1
    | k+2 => absurd hk (by have : (dRec45.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF45_0X : (dRec45.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 45) 45 recLt) (dRec45.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR45_0X0 : constsMemberFuel (extendEnv (envPre 45) 45 recLt) (dRec45.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec45.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR45_0X1 : constsMemberFuel (extendEnv (envPre 45) 45 recLt) (dRec45.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec45.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri45_0X : (dRec45.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 45) 45 recLt) (dRec45.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR45_0X0
    | 1 => ixR45_0X1
    | k+2 => absurd hk (by have : (dRec45.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc45_0 : Rcic.Declarative.exprClosedAt (dRec45.1.family.parameters.length + 1 + dRec45.1.constructors.length + dRec45.1.family.indices.length + (dRec45.1.constructorViews ⟨0, by decide⟩).fields.length) (descriptorSchema dRec45.1 dRec45.2 ⟨0, by decide⟩) = true
theorem ctorChk45_0 : recCtorCheckB dRec45.1 dRec45.2 ⟨0, by decide⟩ = true :=
  recCtorCheckB_of ixC45_0 ixF45_0E ri45_0E ixF45_0X ri45_0X famX45 ixSc45_0
kernel_rfl_theorem ixC45_1 : Rcic.Declarative.exprClosedAt 0 (dRec45.1.constructors[1]'(by decide)).mtype = true
kernel_rfl_theorem ixF45_1E : (dRec45.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (envPre 45) (dRec45.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR45_1E0 : constsMemberFuel (envPre 45) (dRec45.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec45.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR45_1E1 : constsMemberFuel (envPre 45) (dRec45.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec45.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri45_1E : (dRec45.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (envPre 45) (dRec45.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR45_1E0
    | 1 => ixR45_1E1
    | k+2 => absurd hk (by have : (dRec45.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF45_1X : (dRec45.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 45) 45 recLt) (dRec45.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR45_1X0 : constsMemberFuel (extendEnv (envPre 45) 45 recLt) (dRec45.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec45.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR45_1X1 : constsMemberFuel (extendEnv (envPre 45) 45 recLt) (dRec45.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec45.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri45_1X : (dRec45.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 45) 45 recLt) (dRec45.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR45_1X0
    | 1 => ixR45_1X1
    | k+2 => absurd hk (by have : (dRec45.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc45_1 : Rcic.Declarative.exprClosedAt (dRec45.1.family.parameters.length + 1 + dRec45.1.constructors.length + dRec45.1.family.indices.length + (dRec45.1.constructorViews ⟨1, by decide⟩).fields.length) (descriptorSchema dRec45.1 dRec45.2 ⟨1, by decide⟩) = true
theorem ctorChk45_1 : recCtorCheckB dRec45.1 dRec45.2 ⟨1, by decide⟩ = true :=
  recCtorCheckB_of ixC45_1 ixF45_1E ri45_1E ixF45_1X ri45_1X famX45 ixSc45_1
theorem idxB45 : recIdxAdmittedTB dRec45.1 dRec45.2 = true :=
  recIdxAdmittedB_of freshB45 classB45 mtB45 fun ⟨i, hi⟩ =>
    match i with
    | 0 => ctorChk45_0
    | 1 => ctorChk45_1
    | k+2 => absurd hi (by have : dRec45.1.constructors.length = 2 := rfl; omega)
kernel_rfl_theorem iotaB45_0 : iotaEqB (a := dRec45.1) (h14 := dRec45.2) (synCheck (extendEnv (envPre 45) 45 recLt) recLt.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB45_1 : iotaEqB (a := dRec45.1) (h14 := dRec45.2) (synCheck (extendEnv (envPre 45) 45 recLt) recLt.arity) 1 (by decide) = true
def typedFam42 : IndGroupTypedT admFamLt := famTypedT_of (fuel := 96) dFam42 famB42
def typedCtor43 : IndGroupTypedT admCtorLtBase :=
  ⟨famTypedT_of (fuel := 96) dCtor43.1 famB43, ctorTypedT_of (fuel := 96) ctorB43⟩
def typedCtor44 : IndGroupTypedT admCtorLtStep :=
  ⟨famTypedT_of (fuel := 96) dCtor44.1 famB44, ctorTypedT_of (fuel := 96) ctorB44⟩
theorem iotaAllB45 : finAllB dRec45.1.constructors.length
    (iotaEqB (a := dRec45.1) (h14 := dRec45.2) (synCheck (extendEnv (envPre 45) 45 recLt) recLt.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB45_0
    | 1 => iotaB45_1
    | k+2 => absurd hi (by have : dRec45.1.constructors.length = 2 := rfl; omega)
def iotaT45 : ∀ i, IotaEquationTypedT dRec45.1 i (dRec45.2.fuelAt i) (dRec45.2.shapesAt i) :=
  iotaEqsT_of iotaAllB45
def idxT45 : IdxAdmittedT admRecLt := idxT_of admRecLt idxB45
def typedRec45 : IndGroupTypedT admRecLt :=
  ⟨famTypedT_of (fuel := 96) dRec45.1.family famB45,
   ctorTypedAll_of ctorB45,
   iotaT45⟩
def mem42 : GroupMembersT (extendEnv (envPre 42) 42 mLt) (envPre 42)
    [(42, mLt), (43, mLtBase), (44, mLtStep), (45, recLt)] (extendEnv (envPre 45) 45 recLt) :=
  (GroupMembersT.cons _ 42 mLt _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamLt PUnit.unit _ tyT42.2 (fun h => absurd h (by decide)) typedFam42
    (GroupMembersT.cons _ 43 mLtBase _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorLtBase PUnit.unit _ tyT43.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS43).2⟩) typedCtor43
    (GroupMembersT.cons _ 44 mLtStep _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorLtStep PUnit.unit _ tyT44.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS44).2⟩) typedCtor44
    (GroupMembersT.cons _ 45 recLt _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecLt idxT45 _ tyT45.2 (fun h => absurd h (by decide)) typedRec45
    (.nil _)))))
def wft46 : EnvWfT (envPre 46) :=
  wfTOfExtend (r := 45) (m := recLt) (by decide) rfl
    (.group (envPre 42) 42 mLt [(43, mLtBase), (44, mLtStep)] 45 recLt _ wft42 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem42)

end Rcic.Scm.SrcG

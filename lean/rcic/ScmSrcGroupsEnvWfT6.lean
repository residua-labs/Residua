import rcic.ScmSrcGroupsEnvWfT5

/-! `EnvWfT` for srcEnvG slots in this file's range. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/- slots 46–49: family mBC, recursor recBC -/
kernel_rfl_theorem tyB46 : (sortTyAtC (envPre 46) mBC.arity 96 [] mBC.mtype).isSome = true
def tyT46 : Σ u, HasTyT (envPre 46) mBC.arity [] mBC.mtype (.sort u) :=
  (sortTyAtC (envPre 46) mBC.arity 96 [] mBC.mtype).get tyB46
kernel_rfl_theorem tyB47 : (sortTyAtC (envPre 47) mCatNil.arity 96 [] mCatNil.mtype).isSome = true
def tyT47 : Σ u, HasTyT (envPre 47) mCatNil.arity [] mCatNil.mtype (.sort u) :=
  (sortTyAtC (envPre 47) mCatNil.arity 96 [] mCatNil.mtype).get tyB47
kernel_rfl_theorem tyS47 : (sortTyAtC (extendEnv (envPre 46) 46 mBC) mCatNil.arity 96 [] mCatNil.mtype).isSome = true
kernel_rfl_theorem tyB48 : (sortTyAtC (envPre 48) mCatCons.arity 96 [] mCatCons.mtype).isSome = true
def tyT48 : Σ u, HasTyT (envPre 48) mCatCons.arity [] mCatCons.mtype (.sort u) :=
  (sortTyAtC (envPre 48) mCatCons.arity 96 [] mCatCons.mtype).get tyB48
kernel_rfl_theorem tyS48 : (sortTyAtC (extendEnv (envPre 46) 46 mBC) mCatCons.arity 96 [] mCatCons.mtype).isSome = true
kernel_rfl_theorem tyB49 : (sortTyAtC (envPre 49) recBC.arity 96 [] recBC.mtype).isSome = true
def tyT49 : Σ u, HasTyT (envPre 49) recBC.arity [] recBC.mtype (.sort u) :=
  (sortTyAtC (envPre 49) recBC.arity 96 [] recBC.mtype).get tyB49
def dFam46 := (admFamView? admFamBC).get rfl
def dCtor47 := (admCtorViews? admCtorCatNil).get rfl
def dCtor48 := (admCtorViews? admCtorCatCons).get rfl
def dRec49 := (admRecData admRecBC).get rfl
kernel_rfl_theorem famB46 : famTypedB (extendEnv (envPre 46) 46 mBC) 96 dFam46 = true
kernel_rfl_theorem famB47 : famTypedB (envPre 47) 96 dCtor47.1 = true
kernel_rfl_theorem ctorB47 : ctorTypedB 96 dCtor47.2.2 = true
kernel_rfl_theorem famB48 : famTypedB (envPre 48) 96 dCtor48.1 = true
kernel_rfl_theorem ctorB48 : ctorTypedB 96 dCtor48.2.2 = true
kernel_rfl_theorem famB49 : famTypedB (envPre 49) 96 dRec49.1.family = true
kernel_rfl_theorem ctorB49 : ctorTypedAllB 96 dRec49.1 = true
kernel_rfl_theorem freshB49 : ((envPre 49).members 49).isNone = true
theorem classB49 : (match recBC.mclass with | .recursorM => true | _ => false) = true := rfl
kernel_rfl_theorem mtB49 : Rcic.Declarative.exprClosedAt 0 recBC.mtype = true
theorem famX49 : (extendEnv (envPre 49) 49 recBC).members dRec49.1.family.ref = some dRec49.1.family.member := by
  rw [extendEnv_members_ne (by decide : dRec49.1.family.ref ≠ 49)]
  exact dRec49.1.family.present
kernel_rfl_theorem ixC49_0 : Rcic.Declarative.exprClosedAt 0 (dRec49.1.constructors[0]'(by decide)).mtype = true
kernel_rfl_theorem ixF49_0E : (dRec49.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (envPre 49) (dRec49.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR49_0E0 : constsMemberFuel (envPre 49) (dRec49.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec49.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR49_0E1 : constsMemberFuel (envPre 49) (dRec49.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec49.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR49_0E2 : constsMemberFuel (envPre 49) (dRec49.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec49.1.constructorViews ⟨0, by decide⟩).resultIndices[2]'(by decide)) = true
theorem ri49_0E : (dRec49.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (envPre 49) (dRec49.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR49_0E0
    | 1 => ixR49_0E1
    | 2 => ixR49_0E2
    | k+3 => absurd hk (by have : (dRec49.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 3 := rfl; omega)
kernel_rfl_theorem ixF49_0X : (dRec49.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 49) 49 recBC) (dRec49.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR49_0X0 : constsMemberFuel (extendEnv (envPre 49) 49 recBC) (dRec49.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec49.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR49_0X1 : constsMemberFuel (extendEnv (envPre 49) 49 recBC) (dRec49.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec49.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR49_0X2 : constsMemberFuel (extendEnv (envPre 49) 49 recBC) (dRec49.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec49.1.constructorViews ⟨0, by decide⟩).resultIndices[2]'(by decide)) = true
theorem ri49_0X : (dRec49.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 49) 49 recBC) (dRec49.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR49_0X0
    | 1 => ixR49_0X1
    | 2 => ixR49_0X2
    | k+3 => absurd hk (by have : (dRec49.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 3 := rfl; omega)
kernel_rfl_theorem ixSc49_0 : Rcic.Declarative.exprClosedAt (dRec49.1.family.parameters.length + 1 + dRec49.1.constructors.length + dRec49.1.family.indices.length + (dRec49.1.constructorViews ⟨0, by decide⟩).fields.length) (descriptorSchema dRec49.1 dRec49.2 ⟨0, by decide⟩) = true
theorem ctorChk49_0 : recCtorCheckB dRec49.1 dRec49.2 ⟨0, by decide⟩ = true :=
  recCtorCheckB_of ixC49_0 ixF49_0E ri49_0E ixF49_0X ri49_0X famX49 ixSc49_0
kernel_rfl_theorem ixC49_1 : Rcic.Declarative.exprClosedAt 0 (dRec49.1.constructors[1]'(by decide)).mtype = true
kernel_rfl_theorem ixF49_1E : (dRec49.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (envPre 49) (dRec49.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR49_1E0 : constsMemberFuel (envPre 49) (dRec49.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec49.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR49_1E1 : constsMemberFuel (envPre 49) (dRec49.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec49.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR49_1E2 : constsMemberFuel (envPre 49) (dRec49.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec49.1.constructorViews ⟨1, by decide⟩).resultIndices[2]'(by decide)) = true
theorem ri49_1E : (dRec49.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (envPre 49) (dRec49.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR49_1E0
    | 1 => ixR49_1E1
    | 2 => ixR49_1E2
    | k+3 => absurd hk (by have : (dRec49.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 3 := rfl; omega)
kernel_rfl_theorem ixF49_1X : (dRec49.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 49) 49 recBC) (dRec49.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR49_1X0 : constsMemberFuel (extendEnv (envPre 49) 49 recBC) (dRec49.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec49.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR49_1X1 : constsMemberFuel (extendEnv (envPre 49) 49 recBC) (dRec49.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec49.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR49_1X2 : constsMemberFuel (extendEnv (envPre 49) 49 recBC) (dRec49.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec49.1.constructorViews ⟨1, by decide⟩).resultIndices[2]'(by decide)) = true
theorem ri49_1X : (dRec49.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 49) 49 recBC) (dRec49.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR49_1X0
    | 1 => ixR49_1X1
    | 2 => ixR49_1X2
    | k+3 => absurd hk (by have : (dRec49.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 3 := rfl; omega)
kernel_rfl_theorem ixSc49_1 : Rcic.Declarative.exprClosedAt (dRec49.1.family.parameters.length + 1 + dRec49.1.constructors.length + dRec49.1.family.indices.length + (dRec49.1.constructorViews ⟨1, by decide⟩).fields.length) (descriptorSchema dRec49.1 dRec49.2 ⟨1, by decide⟩) = true
theorem ctorChk49_1 : recCtorCheckB dRec49.1 dRec49.2 ⟨1, by decide⟩ = true :=
  recCtorCheckB_of ixC49_1 ixF49_1E ri49_1E ixF49_1X ri49_1X famX49 ixSc49_1
theorem idxB49 : recIdxAdmittedTB dRec49.1 dRec49.2 = true :=
  recIdxAdmittedB_of freshB49 classB49 mtB49 fun ⟨i, hi⟩ =>
    match i with
    | 0 => ctorChk49_0
    | 1 => ctorChk49_1
    | k+2 => absurd hi (by have : dRec49.1.constructors.length = 2 := rfl; omega)
kernel_rfl_theorem iotaB49_0 : iotaEqB (a := dRec49.1) (h14 := dRec49.2) (synCheck (extendEnv (envPre 49) 49 recBC) recBC.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB49_1 : iotaEqB (a := dRec49.1) (h14 := dRec49.2) (synCheck (extendEnv (envPre 49) 49 recBC) recBC.arity) 1 (by decide) = true
def typedFam46 : IndGroupTypedT admFamBC := famTypedT_of (fuel := 96) dFam46 famB46
def typedCtor47 : IndGroupTypedT admCtorCatNil :=
  ⟨famTypedT_of (fuel := 96) dCtor47.1 famB47, ctorTypedT_of (fuel := 96) ctorB47⟩
def typedCtor48 : IndGroupTypedT admCtorCatCons :=
  ⟨famTypedT_of (fuel := 96) dCtor48.1 famB48, ctorTypedT_of (fuel := 96) ctorB48⟩
theorem iotaAllB49 : finAllB dRec49.1.constructors.length
    (iotaEqB (a := dRec49.1) (h14 := dRec49.2) (synCheck (extendEnv (envPre 49) 49 recBC) recBC.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB49_0
    | 1 => iotaB49_1
    | k+2 => absurd hi (by have : dRec49.1.constructors.length = 2 := rfl; omega)
def iotaT49 : ∀ i, IotaEquationTypedT dRec49.1 i (dRec49.2.fuelAt i) (dRec49.2.shapesAt i) :=
  iotaEqsT_of iotaAllB49
def idxT49 : IdxAdmittedT admRecBC := idxT_of admRecBC idxB49
def typedRec49 : IndGroupTypedT admRecBC :=
  ⟨famTypedT_of (fuel := 96) dRec49.1.family famB49,
   ctorTypedAll_of ctorB49,
   iotaT49⟩
def mem46 : GroupMembersT (extendEnv (envPre 46) 46 mBC) (envPre 46)
    [(46, mBC), (47, mCatNil), (48, mCatCons), (49, recBC)] (extendEnv (envPre 49) 49 recBC) :=
  (GroupMembersT.cons _ 46 mBC _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamBC PUnit.unit _ tyT46.2 (fun h => absurd h (by decide)) typedFam46
    (GroupMembersT.cons _ 47 mCatNil _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorCatNil PUnit.unit _ tyT47.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS47).2⟩) typedCtor47
    (GroupMembersT.cons _ 48 mCatCons _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorCatCons PUnit.unit _ tyT48.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS48).2⟩) typedCtor48
    (GroupMembersT.cons _ 49 recBC _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecBC idxT49 _ tyT49.2 (fun h => absurd h (by decide)) typedRec49
    (.nil _)))))
def wft50 : EnvWfT (envPre 50) :=
  wfTOfExtend (r := 49) (m := recBC) (by decide) rfl
    (.group (envPre 46) 46 mBC [(47, mCatNil), (48, mCatCons)] 49 recBC _ wft46 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem46)
/- slots 50–53: family mDM10, recursor recDM10 -/
kernel_rfl_theorem tyB50 : (sortTyAtC (envPre 50) mDM10.arity 96 [] mDM10.mtype).isSome = true
def tyT50 : Σ u, HasTyT (envPre 50) mDM10.arity [] mDM10.mtype (.sort u) :=
  (sortTyAtC (envPre 50) mDM10.arity 96 [] mDM10.mtype).get tyB50
kernel_rfl_theorem tyB51 : (sortTyAtC (envPre 51) mDmBase.arity 96 [] mDmBase.mtype).isSome = true
def tyT51 : Σ u, HasTyT (envPre 51) mDmBase.arity [] mDmBase.mtype (.sort u) :=
  (sortTyAtC (envPre 51) mDmBase.arity 96 [] mDmBase.mtype).get tyB51
kernel_rfl_theorem tyS51 : (sortTyAtC (extendEnv (envPre 50) 50 mDM10) mDmBase.arity 96 [] mDmBase.mtype).isSome = true
kernel_rfl_theorem tyB52 : (sortTyAtC (envPre 52) mDmStep.arity 96 [] mDmStep.mtype).isSome = true
def tyT52 : Σ u, HasTyT (envPre 52) mDmStep.arity [] mDmStep.mtype (.sort u) :=
  (sortTyAtC (envPre 52) mDmStep.arity 96 [] mDmStep.mtype).get tyB52
kernel_rfl_theorem tyS52 : (sortTyAtC (extendEnv (envPre 50) 50 mDM10) mDmStep.arity 96 [] mDmStep.mtype).isSome = true
kernel_rfl_theorem tyB53 : (sortTyAtC (envPre 53) recDM10.arity 96 [] recDM10.mtype).isSome = true
def tyT53 : Σ u, HasTyT (envPre 53) recDM10.arity [] recDM10.mtype (.sort u) :=
  (sortTyAtC (envPre 53) recDM10.arity 96 [] recDM10.mtype).get tyB53
def dFam50 := (admFamView? admFamDM10).get rfl
def dCtor51 := (admCtorViews? admCtorDmBase).get rfl
def dCtor52 := (admCtorViews? admCtorDmStep).get rfl
def dRec53 := (admRecData admRecDM10).get rfl
kernel_rfl_theorem famB50 : famTypedB (extendEnv (envPre 50) 50 mDM10) 96 dFam50 = true
kernel_rfl_theorem famB51 : famTypedB (envPre 51) 96 dCtor51.1 = true
kernel_rfl_theorem ctorB51 : ctorTypedB 96 dCtor51.2.2 = true
kernel_rfl_theorem famB52 : famTypedB (envPre 52) 96 dCtor52.1 = true
kernel_rfl_theorem ctorB52 : ctorTypedB 96 dCtor52.2.2 = true
kernel_rfl_theorem famB53 : famTypedB (envPre 53) 96 dRec53.1.family = true
kernel_rfl_theorem ctorB53 : ctorTypedAllB 96 dRec53.1 = true
kernel_rfl_theorem freshB53 : ((envPre 53).members 53).isNone = true
theorem classB53 : (match recDM10.mclass with | .recursorM => true | _ => false) = true := rfl
kernel_rfl_theorem mtB53 : Rcic.Declarative.exprClosedAt 0 recDM10.mtype = true
theorem famX53 : (extendEnv (envPre 53) 53 recDM10).members dRec53.1.family.ref = some dRec53.1.family.member := by
  rw [extendEnv_members_ne (by decide : dRec53.1.family.ref ≠ 53)]
  exact dRec53.1.family.present
kernel_rfl_theorem ixC53_0 : Rcic.Declarative.exprClosedAt 0 (dRec53.1.constructors[0]'(by decide)).mtype = true
kernel_rfl_theorem ixF53_0E : (dRec53.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (envPre 53) (dRec53.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR53_0E0 : constsMemberFuel (envPre 53) (dRec53.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec53.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR53_0E1 : constsMemberFuel (envPre 53) (dRec53.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec53.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR53_0E2 : constsMemberFuel (envPre 53) (dRec53.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec53.1.constructorViews ⟨0, by decide⟩).resultIndices[2]'(by decide)) = true
theorem ri53_0E : (dRec53.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (envPre 53) (dRec53.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR53_0E0
    | 1 => ixR53_0E1
    | 2 => ixR53_0E2
    | k+3 => absurd hk (by have : (dRec53.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 3 := rfl; omega)
kernel_rfl_theorem ixF53_0X : (dRec53.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 53) 53 recDM10) (dRec53.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR53_0X0 : constsMemberFuel (extendEnv (envPre 53) 53 recDM10) (dRec53.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec53.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR53_0X1 : constsMemberFuel (extendEnv (envPre 53) 53 recDM10) (dRec53.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec53.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR53_0X2 : constsMemberFuel (extendEnv (envPre 53) 53 recDM10) (dRec53.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec53.1.constructorViews ⟨0, by decide⟩).resultIndices[2]'(by decide)) = true
theorem ri53_0X : (dRec53.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 53) 53 recDM10) (dRec53.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR53_0X0
    | 1 => ixR53_0X1
    | 2 => ixR53_0X2
    | k+3 => absurd hk (by have : (dRec53.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 3 := rfl; omega)
kernel_rfl_theorem ixSc53_0 : Rcic.Declarative.exprClosedAt (dRec53.1.family.parameters.length + 1 + dRec53.1.constructors.length + dRec53.1.family.indices.length + (dRec53.1.constructorViews ⟨0, by decide⟩).fields.length) (descriptorSchema dRec53.1 dRec53.2 ⟨0, by decide⟩) = true
theorem ctorChk53_0 : recCtorCheckB dRec53.1 dRec53.2 ⟨0, by decide⟩ = true :=
  recCtorCheckB_of ixC53_0 ixF53_0E ri53_0E ixF53_0X ri53_0X famX53 ixSc53_0
kernel_rfl_theorem ixC53_1 : Rcic.Declarative.exprClosedAt 0 (dRec53.1.constructors[1]'(by decide)).mtype = true
kernel_rfl_theorem ixF53_1E : (dRec53.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (envPre 53) (dRec53.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR53_1E0 : constsMemberFuel (envPre 53) (dRec53.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec53.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR53_1E1 : constsMemberFuel (envPre 53) (dRec53.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec53.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR53_1E2 : constsMemberFuel (envPre 53) (dRec53.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec53.1.constructorViews ⟨1, by decide⟩).resultIndices[2]'(by decide)) = true
theorem ri53_1E : (dRec53.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (envPre 53) (dRec53.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR53_1E0
    | 1 => ixR53_1E1
    | 2 => ixR53_1E2
    | k+3 => absurd hk (by have : (dRec53.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 3 := rfl; omega)
kernel_rfl_theorem ixF53_1X : (dRec53.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 53) 53 recDM10) (dRec53.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR53_1X0 : constsMemberFuel (extendEnv (envPre 53) 53 recDM10) (dRec53.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec53.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR53_1X1 : constsMemberFuel (extendEnv (envPre 53) 53 recDM10) (dRec53.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec53.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR53_1X2 : constsMemberFuel (extendEnv (envPre 53) 53 recDM10) (dRec53.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec53.1.constructorViews ⟨1, by decide⟩).resultIndices[2]'(by decide)) = true
theorem ri53_1X : (dRec53.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 53) 53 recDM10) (dRec53.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR53_1X0
    | 1 => ixR53_1X1
    | 2 => ixR53_1X2
    | k+3 => absurd hk (by have : (dRec53.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 3 := rfl; omega)
kernel_rfl_theorem ixSc53_1 : Rcic.Declarative.exprClosedAt (dRec53.1.family.parameters.length + 1 + dRec53.1.constructors.length + dRec53.1.family.indices.length + (dRec53.1.constructorViews ⟨1, by decide⟩).fields.length) (descriptorSchema dRec53.1 dRec53.2 ⟨1, by decide⟩) = true
theorem ctorChk53_1 : recCtorCheckB dRec53.1 dRec53.2 ⟨1, by decide⟩ = true :=
  recCtorCheckB_of ixC53_1 ixF53_1E ri53_1E ixF53_1X ri53_1X famX53 ixSc53_1
theorem idxB53 : recIdxAdmittedTB dRec53.1 dRec53.2 = true :=
  recIdxAdmittedB_of freshB53 classB53 mtB53 fun ⟨i, hi⟩ =>
    match i with
    | 0 => ctorChk53_0
    | 1 => ctorChk53_1
    | k+2 => absurd hi (by have : dRec53.1.constructors.length = 2 := rfl; omega)
kernel_rfl_theorem iotaB53_0 : iotaEqB (a := dRec53.1) (h14 := dRec53.2) (synCheck (extendEnv (envPre 53) 53 recDM10) recDM10.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB53_1 : iotaEqB (a := dRec53.1) (h14 := dRec53.2) (synCheck (extendEnv (envPre 53) 53 recDM10) recDM10.arity) 1 (by decide) = true
def typedFam50 : IndGroupTypedT admFamDM10 := famTypedT_of (fuel := 96) dFam50 famB50
def typedCtor51 : IndGroupTypedT admCtorDmBase :=
  ⟨famTypedT_of (fuel := 96) dCtor51.1 famB51, ctorTypedT_of (fuel := 96) ctorB51⟩
def typedCtor52 : IndGroupTypedT admCtorDmStep :=
  ⟨famTypedT_of (fuel := 96) dCtor52.1 famB52, ctorTypedT_of (fuel := 96) ctorB52⟩
theorem iotaAllB53 : finAllB dRec53.1.constructors.length
    (iotaEqB (a := dRec53.1) (h14 := dRec53.2) (synCheck (extendEnv (envPre 53) 53 recDM10) recDM10.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB53_0
    | 1 => iotaB53_1
    | k+2 => absurd hi (by have : dRec53.1.constructors.length = 2 := rfl; omega)
def iotaT53 : ∀ i, IotaEquationTypedT dRec53.1 i (dRec53.2.fuelAt i) (dRec53.2.shapesAt i) :=
  iotaEqsT_of iotaAllB53
def idxT53 : IdxAdmittedT admRecDM10 := idxT_of admRecDM10 idxB53
def typedRec53 : IndGroupTypedT admRecDM10 :=
  ⟨famTypedT_of (fuel := 96) dRec53.1.family famB53,
   ctorTypedAll_of ctorB53,
   iotaT53⟩
def mem50 : GroupMembersT (extendEnv (envPre 50) 50 mDM10) (envPre 50)
    [(50, mDM10), (51, mDmBase), (52, mDmStep), (53, recDM10)] (extendEnv (envPre 53) 53 recDM10) :=
  (GroupMembersT.cons _ 50 mDM10 _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamDM10 PUnit.unit _ tyT50.2 (fun h => absurd h (by decide)) typedFam50
    (GroupMembersT.cons _ 51 mDmBase _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorDmBase PUnit.unit _ tyT51.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS51).2⟩) typedCtor51
    (GroupMembersT.cons _ 52 mDmStep _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorDmStep PUnit.unit _ tyT52.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS52).2⟩) typedCtor52
    (GroupMembersT.cons _ 53 recDM10 _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecDM10 idxT53 _ tyT53.2 (fun h => absurd h (by decide)) typedRec53
    (.nil _)))))
def wft54 : EnvWfT (envPre 54) :=
  wfTOfExtend (r := 53) (m := recDM10) (by decide) rfl
    (.group (envPre 50) 50 mDM10 [(51, mDmBase), (52, mDmStep)] 53 recDM10 _ wft50 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem50)

end Rcic.Scm.SrcG

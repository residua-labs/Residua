import rcic.ScmSrcGroupsEnvWfT6

/-! `EnvWfT` for srcEnvG slots in this file's range. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/- slots 54–57: family mND, recursor recND -/
kernel_rfl_theorem tyB54 : (sortTyAtC (envPre 54) mND.arity 96 [] mND.mtype).isSome = true
def tyT54 : Σ u, HasTyT (envPre 54) mND.arity [] mND.mtype (.sort u) :=
  (sortTyAtC (envPre 54) mND.arity 96 [] mND.mtype).get tyB54
kernel_rfl_theorem tyB55 : (sortTyAtC (envPre 55) mNdBase.arity 96 [] mNdBase.mtype).isSome = true
def tyT55 : Σ u, HasTyT (envPre 55) mNdBase.arity [] mNdBase.mtype (.sort u) :=
  (sortTyAtC (envPre 55) mNdBase.arity 96 [] mNdBase.mtype).get tyB55
kernel_rfl_theorem tyS55 : (sortTyAtC (extendEnv (envPre 54) 54 mND) mNdBase.arity 96 [] mNdBase.mtype).isSome = true
kernel_rfl_theorem tyB56 : (sortTyAtC (envPre 56) mNdStep.arity 96 [] mNdStep.mtype).isSome = true
def tyT56 : Σ u, HasTyT (envPre 56) mNdStep.arity [] mNdStep.mtype (.sort u) :=
  (sortTyAtC (envPre 56) mNdStep.arity 96 [] mNdStep.mtype).get tyB56
kernel_rfl_theorem tyS56 : (sortTyAtC (extendEnv (envPre 54) 54 mND) mNdStep.arity 96 [] mNdStep.mtype).isSome = true
kernel_rfl_theorem tyB57 : (sortTyAtC (envPre 57) recND.arity 96 [] recND.mtype).isSome = true
def tyT57 : Σ u, HasTyT (envPre 57) recND.arity [] recND.mtype (.sort u) :=
  (sortTyAtC (envPre 57) recND.arity 96 [] recND.mtype).get tyB57
def dFam54 := (admFamView? admFamND).get rfl
def dCtor55 := (admCtorViews? admCtorNdBase).get rfl
def dCtor56 := (admCtorViews? admCtorNdStep).get rfl
def dRec57 := (admRecData admRecND).get rfl
kernel_rfl_theorem famB54 : famTypedB (extendEnv (envPre 54) 54 mND) 96 dFam54 = true
kernel_rfl_theorem famB55 : famTypedB (envPre 55) 96 dCtor55.1 = true
kernel_rfl_theorem ctorB55 : ctorTypedB 96 dCtor55.2.2 = true
kernel_rfl_theorem famB56 : famTypedB (envPre 56) 96 dCtor56.1 = true
kernel_rfl_theorem ctorB56 : ctorTypedB 96 dCtor56.2.2 = true
kernel_rfl_theorem famB57 : famTypedB (envPre 57) 96 dRec57.1.family = true
kernel_rfl_theorem ctorB57 : ctorTypedAllB 96 dRec57.1 = true
kernel_rfl_theorem freshB57 : ((envPre 57).members 57).isNone = true
theorem classB57 : (match recND.mclass with | .recursorM => true | _ => false) = true := rfl
kernel_rfl_theorem mtB57 : Rcic.Declarative.exprClosedAt 0 recND.mtype = true
theorem famX57 : (extendEnv (envPre 57) 57 recND).members dRec57.1.family.ref = some dRec57.1.family.member := by
  rw [extendEnv_members_ne (by decide : dRec57.1.family.ref ≠ 57)]
  exact dRec57.1.family.present
kernel_rfl_theorem ixC57_0 : Rcic.Declarative.exprClosedAt 0 (dRec57.1.constructors[0]'(by decide)).mtype = true
kernel_rfl_theorem ixF57_0E : (dRec57.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (envPre 57) (dRec57.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR57_0E0 : constsMemberFuel (envPre 57) (dRec57.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec57.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR57_0E1 : constsMemberFuel (envPre 57) (dRec57.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec57.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri57_0E : (dRec57.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (envPre 57) (dRec57.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR57_0E0
    | 1 => ixR57_0E1
    | k+2 => absurd hk (by have : (dRec57.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF57_0X : (dRec57.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 57) 57 recND) (dRec57.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR57_0X0 : constsMemberFuel (extendEnv (envPre 57) 57 recND) (dRec57.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec57.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR57_0X1 : constsMemberFuel (extendEnv (envPre 57) 57 recND) (dRec57.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec57.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri57_0X : (dRec57.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 57) 57 recND) (dRec57.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR57_0X0
    | 1 => ixR57_0X1
    | k+2 => absurd hk (by have : (dRec57.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc57_0 : Rcic.Declarative.exprClosedAt (dRec57.1.family.parameters.length + 1 + dRec57.1.constructors.length + dRec57.1.family.indices.length + (dRec57.1.constructorViews ⟨0, by decide⟩).fields.length) (descriptorSchema dRec57.1 dRec57.2 ⟨0, by decide⟩) = true
theorem ctorChk57_0 : recCtorCheckB dRec57.1 dRec57.2 ⟨0, by decide⟩ = true :=
  recCtorCheckB_of ixC57_0 ixF57_0E ri57_0E ixF57_0X ri57_0X famX57 ixSc57_0
kernel_rfl_theorem ixC57_1 : Rcic.Declarative.exprClosedAt 0 (dRec57.1.constructors[1]'(by decide)).mtype = true
kernel_rfl_theorem ixF57_1E : (dRec57.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (envPre 57) (dRec57.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR57_1E0 : constsMemberFuel (envPre 57) (dRec57.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec57.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR57_1E1 : constsMemberFuel (envPre 57) (dRec57.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec57.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri57_1E : (dRec57.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (envPre 57) (dRec57.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR57_1E0
    | 1 => ixR57_1E1
    | k+2 => absurd hk (by have : (dRec57.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF57_1X : (dRec57.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 57) 57 recND) (dRec57.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR57_1X0 : constsMemberFuel (extendEnv (envPre 57) 57 recND) (dRec57.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec57.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR57_1X1 : constsMemberFuel (extendEnv (envPre 57) 57 recND) (dRec57.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec57.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri57_1X : (dRec57.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 57) 57 recND) (dRec57.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR57_1X0
    | 1 => ixR57_1X1
    | k+2 => absurd hk (by have : (dRec57.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc57_1 : Rcic.Declarative.exprClosedAt (dRec57.1.family.parameters.length + 1 + dRec57.1.constructors.length + dRec57.1.family.indices.length + (dRec57.1.constructorViews ⟨1, by decide⟩).fields.length) (descriptorSchema dRec57.1 dRec57.2 ⟨1, by decide⟩) = true
theorem ctorChk57_1 : recCtorCheckB dRec57.1 dRec57.2 ⟨1, by decide⟩ = true :=
  recCtorCheckB_of ixC57_1 ixF57_1E ri57_1E ixF57_1X ri57_1X famX57 ixSc57_1
theorem idxB57 : recIdxAdmittedTB dRec57.1 dRec57.2 = true :=
  recIdxAdmittedB_of freshB57 classB57 mtB57 fun ⟨i, hi⟩ =>
    match i with
    | 0 => ctorChk57_0
    | 1 => ctorChk57_1
    | k+2 => absurd hi (by have : dRec57.1.constructors.length = 2 := rfl; omega)
kernel_rfl_theorem iotaB57_0 : iotaEqB (a := dRec57.1) (h14 := dRec57.2) (synCheck (extendEnv (envPre 57) 57 recND) recND.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB57_1 : iotaEqB (a := dRec57.1) (h14 := dRec57.2) (synCheck (extendEnv (envPre 57) 57 recND) recND.arity) 1 (by decide) = true
def typedFam54 : IndGroupTypedT admFamND := famTypedT_of (fuel := 96) dFam54 famB54
def typedCtor55 : IndGroupTypedT admCtorNdBase :=
  ⟨famTypedT_of (fuel := 96) dCtor55.1 famB55, ctorTypedT_of (fuel := 96) ctorB55⟩
def typedCtor56 : IndGroupTypedT admCtorNdStep :=
  ⟨famTypedT_of (fuel := 96) dCtor56.1 famB56, ctorTypedT_of (fuel := 96) ctorB56⟩
theorem iotaAllB57 : finAllB dRec57.1.constructors.length
    (iotaEqB (a := dRec57.1) (h14 := dRec57.2) (synCheck (extendEnv (envPre 57) 57 recND) recND.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB57_0
    | 1 => iotaB57_1
    | k+2 => absurd hi (by have : dRec57.1.constructors.length = 2 := rfl; omega)
def iotaT57 : ∀ i, IotaEquationTypedT dRec57.1 i (dRec57.2.fuelAt i) (dRec57.2.shapesAt i) :=
  iotaEqsT_of iotaAllB57
def idxT57 : IdxAdmittedT admRecND := idxT_of admRecND idxB57
def typedRec57 : IndGroupTypedT admRecND :=
  ⟨famTypedT_of (fuel := 96) dRec57.1.family famB57,
   ctorTypedAll_of ctorB57,
   iotaT57⟩
def mem54 : GroupMembersT (extendEnv (envPre 54) 54 mND) (envPre 54)
    [(54, mND), (55, mNdBase), (56, mNdStep), (57, recND)] (extendEnv (envPre 57) 57 recND) :=
  (GroupMembersT.cons _ 54 mND _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamND PUnit.unit _ tyT54.2 (fun h => absurd h (by decide)) typedFam54
    (GroupMembersT.cons _ 55 mNdBase _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorNdBase PUnit.unit _ tyT55.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS55).2⟩) typedCtor55
    (GroupMembersT.cons _ 56 mNdStep _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorNdStep PUnit.unit _ tyT56.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS56).2⟩) typedCtor56
    (GroupMembersT.cons _ 57 recND _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecND idxT57 _ tyT57.2 (fun h => absurd h (by decide)) typedRec57
    (.nil _)))))
def wft58 : EnvWfT (envPre 58) :=
  wfTOfExtend (r := 57) (m := recND) (by decide) rfl
    (.group (envPre 54) 54 mND [(55, mNdBase), (56, mNdStep)] 57 recND _ wft54 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem54)
/- slots 58–60: family mNEA, recursor recNEA -/
kernel_rfl_theorem tyB58 : (sortTyAtC (envPre 58) mNEA.arity 96 [] mNEA.mtype).isSome = true
def tyT58 : Σ u, HasTyT (envPre 58) mNEA.arity [] mNEA.mtype (.sort u) :=
  (sortTyAtC (envPre 58) mNEA.arity 96 [] mNEA.mtype).get tyB58
kernel_rfl_theorem tyB59 : (sortTyAtC (envPre 59) mNeIntro.arity 96 [] mNeIntro.mtype).isSome = true
def tyT59 : Σ u, HasTyT (envPre 59) mNeIntro.arity [] mNeIntro.mtype (.sort u) :=
  (sortTyAtC (envPre 59) mNeIntro.arity 96 [] mNeIntro.mtype).get tyB59
kernel_rfl_theorem tyS59 : (sortTyAtC (extendEnv (envPre 58) 58 mNEA) mNeIntro.arity 96 [] mNeIntro.mtype).isSome = true
kernel_rfl_theorem tyB60 : (sortTyAtC (envPre 60) recNEA.arity 96 [] recNEA.mtype).isSome = true
def tyT60 : Σ u, HasTyT (envPre 60) recNEA.arity [] recNEA.mtype (.sort u) :=
  (sortTyAtC (envPre 60) recNEA.arity 96 [] recNEA.mtype).get tyB60
def dFam58 := (admFamView? admFamNEA).get rfl
def dCtor59 := (admCtorViews? admCtorNeIntro).get rfl
def dRec60 := (admRecData admRecNEA).get rfl
kernel_rfl_theorem famB58 : famTypedB (extendEnv (envPre 58) 58 mNEA) 96 dFam58 = true
kernel_rfl_theorem famB59 : famTypedB (envPre 59) 96 dCtor59.1 = true
kernel_rfl_theorem ctorB59 : ctorTypedB 96 dCtor59.2.2 = true
kernel_rfl_theorem famB60 : famTypedB (envPre 60) 96 dRec60.1.family = true
kernel_rfl_theorem ctorB60 : ctorTypedAllB 96 dRec60.1 = true
kernel_rfl_theorem freshB60 : ((envPre 60).members 60).isNone = true
theorem classB60 : (match recNEA.mclass with | .recursorM => true | _ => false) = true := rfl
kernel_rfl_theorem mtB60 : Rcic.Declarative.exprClosedAt 0 recNEA.mtype = true
theorem famX60 : (extendEnv (envPre 60) 60 recNEA).members dRec60.1.family.ref = some dRec60.1.family.member := by
  rw [extendEnv_members_ne (by decide : dRec60.1.family.ref ≠ 60)]
  exact dRec60.1.family.present
kernel_rfl_theorem ixC60_0 : Rcic.Declarative.exprClosedAt 0 (dRec60.1.constructors[0]'(by decide)).mtype = true
kernel_rfl_theorem ixF60_0E : (dRec60.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (envPre 60) (dRec60.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR60_0E0 : constsMemberFuel (envPre 60) (dRec60.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec60.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR60_0E1 : constsMemberFuel (envPre 60) (dRec60.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec60.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri60_0E : (dRec60.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (envPre 60) (dRec60.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR60_0E0
    | 1 => ixR60_0E1
    | k+2 => absurd hk (by have : (dRec60.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF60_0X : (dRec60.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 60) 60 recNEA) (dRec60.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR60_0X0 : constsMemberFuel (extendEnv (envPre 60) 60 recNEA) (dRec60.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec60.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR60_0X1 : constsMemberFuel (extendEnv (envPre 60) 60 recNEA) (dRec60.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec60.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri60_0X : (dRec60.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 60) 60 recNEA) (dRec60.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR60_0X0
    | 1 => ixR60_0X1
    | k+2 => absurd hk (by have : (dRec60.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc60_0 : Rcic.Declarative.exprClosedAt (dRec60.1.family.parameters.length + 1 + dRec60.1.constructors.length + dRec60.1.family.indices.length + (dRec60.1.constructorViews ⟨0, by decide⟩).fields.length) (descriptorSchema dRec60.1 dRec60.2 ⟨0, by decide⟩) = true
theorem ctorChk60_0 : recCtorCheckB dRec60.1 dRec60.2 ⟨0, by decide⟩ = true :=
  recCtorCheckB_of ixC60_0 ixF60_0E ri60_0E ixF60_0X ri60_0X famX60 ixSc60_0
theorem idxB60 : recIdxAdmittedTB dRec60.1 dRec60.2 = true :=
  recIdxAdmittedB_of freshB60 classB60 mtB60 fun ⟨i, hi⟩ =>
    match i with
    | 0 => ctorChk60_0
    | k+1 => absurd hi (by have : dRec60.1.constructors.length = 1 := rfl; omega)
kernel_rfl_theorem iotaB60_0 : iotaEqB (a := dRec60.1) (h14 := dRec60.2) (synCheck (extendEnv (envPre 60) 60 recNEA) recNEA.arity) 0 (by decide) = true
def typedFam58 : IndGroupTypedT admFamNEA := famTypedT_of (fuel := 96) dFam58 famB58
def typedCtor59 : IndGroupTypedT admCtorNeIntro :=
  ⟨famTypedT_of (fuel := 96) dCtor59.1 famB59, ctorTypedT_of (fuel := 96) ctorB59⟩
theorem iotaAllB60 : finAllB dRec60.1.constructors.length
    (iotaEqB (a := dRec60.1) (h14 := dRec60.2) (synCheck (extendEnv (envPre 60) 60 recNEA) recNEA.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB60_0
    | k+1 => absurd hi (by have : dRec60.1.constructors.length = 1 := rfl; omega)
def iotaT60 : ∀ i, IotaEquationTypedT dRec60.1 i (dRec60.2.fuelAt i) (dRec60.2.shapesAt i) :=
  iotaEqsT_of iotaAllB60
def idxT60 : IdxAdmittedT admRecNEA := idxT_of admRecNEA idxB60
def typedRec60 : IndGroupTypedT admRecNEA :=
  ⟨famTypedT_of (fuel := 96) dRec60.1.family famB60,
   ctorTypedAll_of ctorB60,
   iotaT60⟩
def mem58 : GroupMembersT (extendEnv (envPre 58) 58 mNEA) (envPre 58)
    [(58, mNEA), (59, mNeIntro), (60, recNEA)] (extendEnv (envPre 60) 60 recNEA) :=
  (GroupMembersT.cons _ 58 mNEA _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamNEA PUnit.unit _ tyT58.2 (fun h => absurd h (by decide)) typedFam58
    (GroupMembersT.cons _ 59 mNeIntro _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorNeIntro PUnit.unit _ tyT59.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS59).2⟩) typedCtor59
    (GroupMembersT.cons _ 60 recNEA _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecNEA idxT60 _ tyT60.2 (fun h => absurd h (by decide)) typedRec60
    (.nil _))))
def wft61 : EnvWfT (envPre 61) :=
  wfTOfExtend (r := 60) (m := recNEA) (by decide) rfl
    (.group (envPre 58) 58 mNEA [(59, mNeIntro)] 60 recNEA _ wft58 rfl
      (fun c hc => by simp at hc; rcases hc with rfl <;> rfl) rfl mem58)
/- slots 61–64: family mIEA, recursor recIEA -/
kernel_rfl_theorem tyB61 : (sortTyAtC (envPre 61) mIEA.arity 96 [] mIEA.mtype).isSome = true
def tyT61 : Σ u, HasTyT (envPre 61) mIEA.arity [] mIEA.mtype (.sort u) :=
  (sortTyAtC (envPre 61) mIEA.arity 96 [] mIEA.mtype).get tyB61
kernel_rfl_theorem tyB62 : (sortTyAtC (envPre 62) mIePos.arity 96 [] mIePos.mtype).isSome = true
def tyT62 : Σ u, HasTyT (envPre 62) mIePos.arity [] mIePos.mtype (.sort u) :=
  (sortTyAtC (envPre 62) mIePos.arity 96 [] mIePos.mtype).get tyB62
kernel_rfl_theorem tyS62 : (sortTyAtC (extendEnv (envPre 61) 61 mIEA) mIePos.arity 96 [] mIePos.mtype).isSome = true
kernel_rfl_theorem tyB63 : (sortTyAtC (envPre 63) mIeNeg.arity 96 [] mIeNeg.mtype).isSome = true
def tyT63 : Σ u, HasTyT (envPre 63) mIeNeg.arity [] mIeNeg.mtype (.sort u) :=
  (sortTyAtC (envPre 63) mIeNeg.arity 96 [] mIeNeg.mtype).get tyB63
kernel_rfl_theorem tyS63 : (sortTyAtC (extendEnv (envPre 61) 61 mIEA) mIeNeg.arity 96 [] mIeNeg.mtype).isSome = true
kernel_rfl_theorem tyB64 : (sortTyAtC (envPre 64) recIEA.arity 96 [] recIEA.mtype).isSome = true
def tyT64 : Σ u, HasTyT (envPre 64) recIEA.arity [] recIEA.mtype (.sort u) :=
  (sortTyAtC (envPre 64) recIEA.arity 96 [] recIEA.mtype).get tyB64
def dFam61 := (admFamView? admFamIEA).get rfl
def dCtor62 := (admCtorViews? admCtorIePos).get rfl
def dCtor63 := (admCtorViews? admCtorIeNeg).get rfl
def dRec64 := (admRecData admRecIEA).get rfl
kernel_rfl_theorem famB61 : famTypedB (extendEnv (envPre 61) 61 mIEA) 96 dFam61 = true
kernel_rfl_theorem famB62 : famTypedB (envPre 62) 96 dCtor62.1 = true
kernel_rfl_theorem ctorB62 : ctorTypedB 96 dCtor62.2.2 = true
kernel_rfl_theorem famB63 : famTypedB (envPre 63) 96 dCtor63.1 = true
kernel_rfl_theorem ctorB63 : ctorTypedB 96 dCtor63.2.2 = true
kernel_rfl_theorem famB64 : famTypedB (envPre 64) 96 dRec64.1.family = true
kernel_rfl_theorem ctorB64 : ctorTypedAllB 96 dRec64.1 = true
kernel_rfl_theorem freshB64 : ((envPre 64).members 64).isNone = true
theorem classB64 : (match recIEA.mclass with | .recursorM => true | _ => false) = true := rfl
kernel_rfl_theorem mtB64 : Rcic.Declarative.exprClosedAt 0 recIEA.mtype = true
theorem famX64 : (extendEnv (envPre 64) 64 recIEA).members dRec64.1.family.ref = some dRec64.1.family.member := by
  rw [extendEnv_members_ne (by decide : dRec64.1.family.ref ≠ 64)]
  exact dRec64.1.family.present
kernel_rfl_theorem ixC64_0 : Rcic.Declarative.exprClosedAt 0 (dRec64.1.constructors[0]'(by decide)).mtype = true
kernel_rfl_theorem ixF64_0E : (dRec64.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (envPre 64) (dRec64.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR64_0E0 : constsMemberFuel (envPre 64) (dRec64.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec64.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR64_0E1 : constsMemberFuel (envPre 64) (dRec64.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec64.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri64_0E : (dRec64.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (envPre 64) (dRec64.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR64_0E0
    | 1 => ixR64_0E1
    | k+2 => absurd hk (by have : (dRec64.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF64_0X : (dRec64.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 64) 64 recIEA) (dRec64.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR64_0X0 : constsMemberFuel (extendEnv (envPre 64) 64 recIEA) (dRec64.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec64.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR64_0X1 : constsMemberFuel (extendEnv (envPre 64) 64 recIEA) (dRec64.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec64.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri64_0X : (dRec64.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 64) 64 recIEA) (dRec64.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR64_0X0
    | 1 => ixR64_0X1
    | k+2 => absurd hk (by have : (dRec64.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc64_0 : Rcic.Declarative.exprClosedAt (dRec64.1.family.parameters.length + 1 + dRec64.1.constructors.length + dRec64.1.family.indices.length + (dRec64.1.constructorViews ⟨0, by decide⟩).fields.length) (descriptorSchema dRec64.1 dRec64.2 ⟨0, by decide⟩) = true
theorem ctorChk64_0 : recCtorCheckB dRec64.1 dRec64.2 ⟨0, by decide⟩ = true :=
  recCtorCheckB_of ixC64_0 ixF64_0E ri64_0E ixF64_0X ri64_0X famX64 ixSc64_0
kernel_rfl_theorem ixC64_1 : Rcic.Declarative.exprClosedAt 0 (dRec64.1.constructors[1]'(by decide)).mtype = true
kernel_rfl_theorem ixF64_1E : (dRec64.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (envPre 64) (dRec64.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR64_1E0 : constsMemberFuel (envPre 64) (dRec64.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec64.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR64_1E1 : constsMemberFuel (envPre 64) (dRec64.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec64.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri64_1E : (dRec64.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (envPre 64) (dRec64.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR64_1E0
    | 1 => ixR64_1E1
    | k+2 => absurd hk (by have : (dRec64.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF64_1X : (dRec64.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 64) 64 recIEA) (dRec64.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR64_1X0 : constsMemberFuel (extendEnv (envPre 64) 64 recIEA) (dRec64.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec64.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR64_1X1 : constsMemberFuel (extendEnv (envPre 64) 64 recIEA) (dRec64.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec64.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri64_1X : (dRec64.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 64) 64 recIEA) (dRec64.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR64_1X0
    | 1 => ixR64_1X1
    | k+2 => absurd hk (by have : (dRec64.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc64_1 : Rcic.Declarative.exprClosedAt (dRec64.1.family.parameters.length + 1 + dRec64.1.constructors.length + dRec64.1.family.indices.length + (dRec64.1.constructorViews ⟨1, by decide⟩).fields.length) (descriptorSchema dRec64.1 dRec64.2 ⟨1, by decide⟩) = true
theorem ctorChk64_1 : recCtorCheckB dRec64.1 dRec64.2 ⟨1, by decide⟩ = true :=
  recCtorCheckB_of ixC64_1 ixF64_1E ri64_1E ixF64_1X ri64_1X famX64 ixSc64_1
theorem idxB64 : recIdxAdmittedTB dRec64.1 dRec64.2 = true :=
  recIdxAdmittedB_of freshB64 classB64 mtB64 fun ⟨i, hi⟩ =>
    match i with
    | 0 => ctorChk64_0
    | 1 => ctorChk64_1
    | k+2 => absurd hi (by have : dRec64.1.constructors.length = 2 := rfl; omega)
kernel_rfl_theorem iotaB64_0 : iotaEqB (a := dRec64.1) (h14 := dRec64.2) (synCheck (extendEnv (envPre 64) 64 recIEA) recIEA.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB64_1 : iotaEqB (a := dRec64.1) (h14 := dRec64.2) (synCheck (extendEnv (envPre 64) 64 recIEA) recIEA.arity) 1 (by decide) = true
def typedFam61 : IndGroupTypedT admFamIEA := famTypedT_of (fuel := 96) dFam61 famB61
def typedCtor62 : IndGroupTypedT admCtorIePos :=
  ⟨famTypedT_of (fuel := 96) dCtor62.1 famB62, ctorTypedT_of (fuel := 96) ctorB62⟩
def typedCtor63 : IndGroupTypedT admCtorIeNeg :=
  ⟨famTypedT_of (fuel := 96) dCtor63.1 famB63, ctorTypedT_of (fuel := 96) ctorB63⟩
theorem iotaAllB64 : finAllB dRec64.1.constructors.length
    (iotaEqB (a := dRec64.1) (h14 := dRec64.2) (synCheck (extendEnv (envPre 64) 64 recIEA) recIEA.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB64_0
    | 1 => iotaB64_1
    | k+2 => absurd hi (by have : dRec64.1.constructors.length = 2 := rfl; omega)
def iotaT64 : ∀ i, IotaEquationTypedT dRec64.1 i (dRec64.2.fuelAt i) (dRec64.2.shapesAt i) :=
  iotaEqsT_of iotaAllB64
def idxT64 : IdxAdmittedT admRecIEA := idxT_of admRecIEA idxB64
def typedRec64 : IndGroupTypedT admRecIEA :=
  ⟨famTypedT_of (fuel := 96) dRec64.1.family famB64,
   ctorTypedAll_of ctorB64,
   iotaT64⟩
def mem61 : GroupMembersT (extendEnv (envPre 61) 61 mIEA) (envPre 61)
    [(61, mIEA), (62, mIePos), (63, mIeNeg), (64, recIEA)] (extendEnv (envPre 64) 64 recIEA) :=
  (GroupMembersT.cons _ 61 mIEA _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamIEA PUnit.unit _ tyT61.2 (fun h => absurd h (by decide)) typedFam61
    (GroupMembersT.cons _ 62 mIePos _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorIePos PUnit.unit _ tyT62.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS62).2⟩) typedCtor62
    (GroupMembersT.cons _ 63 mIeNeg _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorIeNeg PUnit.unit _ tyT63.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS63).2⟩) typedCtor63
    (GroupMembersT.cons _ 64 recIEA _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecIEA idxT64 _ tyT64.2 (fun h => absurd h (by decide)) typedRec64
    (.nil _)))))
def wft65 : EnvWfT (envPre 65) :=
  wfTOfExtend (r := 64) (m := recIEA) (by decide) rfl
    (.group (envPre 61) 61 mIEA [(62, mIePos), (63, mIeNeg)] 64 recIEA _ wft61 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem61)

end Rcic.Scm.SrcG

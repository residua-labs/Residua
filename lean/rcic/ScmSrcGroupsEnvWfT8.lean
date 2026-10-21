import rcic.ScmSrcGroupsEnvWfT7

/-! `EnvWfT` for srcEnvG slots in this file's range. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/- slots 65–68: family mSL, recursor recSL -/
kernel_rfl_theorem tyB65 : (sortTyAtC (envPre 65) mSL.arity 96 [] mSL.mtype).isSome = true
def tyT65 : Σ u, HasTyT (envPre 65) mSL.arity [] mSL.mtype (.sort u) :=
  (sortTyAtC (envPre 65) mSL.arity 96 [] mSL.mtype).get tyB65
kernel_rfl_theorem tyB66 : (sortTyAtC (envPre 66) mSlNil.arity 96 [] mSlNil.mtype).isSome = true
def tyT66 : Σ u, HasTyT (envPre 66) mSlNil.arity [] mSlNil.mtype (.sort u) :=
  (sortTyAtC (envPre 66) mSlNil.arity 96 [] mSlNil.mtype).get tyB66
kernel_rfl_theorem tyS66 : (sortTyAtC (extendEnv (envPre 65) 65 mSL) mSlNil.arity 96 [] mSlNil.mtype).isSome = true
kernel_rfl_theorem tyB67 : (sortTyAtC (envPre 67) mSlCons.arity 96 [] mSlCons.mtype).isSome = true
def tyT67 : Σ u, HasTyT (envPre 67) mSlCons.arity [] mSlCons.mtype (.sort u) :=
  (sortTyAtC (envPre 67) mSlCons.arity 96 [] mSlCons.mtype).get tyB67
kernel_rfl_theorem tyS67 : (sortTyAtC (extendEnv (envPre 65) 65 mSL) mSlCons.arity 96 [] mSlCons.mtype).isSome = true
kernel_rfl_theorem tyB68 : (sortTyAtC (envPre 68) recSL.arity 96 [] recSL.mtype).isSome = true
def tyT68 : Σ u, HasTyT (envPre 68) recSL.arity [] recSL.mtype (.sort u) :=
  (sortTyAtC (envPre 68) recSL.arity 96 [] recSL.mtype).get tyB68
def dFam65 := (admFamView? admFamSL).get rfl
def dCtor66 := (admCtorViews? admCtorSlNil).get rfl
def dCtor67 := (admCtorViews? admCtorSlCons).get rfl
def dRec68 := (admRecData admRecSL).get rfl
kernel_rfl_theorem famB65 : famTypedB (extendEnv (envPre 65) 65 mSL) 96 dFam65 = true
kernel_rfl_theorem famB66 : famTypedB (envPre 66) 96 dCtor66.1 = true
kernel_rfl_theorem ctorB66 : ctorTypedB 96 dCtor66.2.2 = true
kernel_rfl_theorem famB67 : famTypedB (envPre 67) 96 dCtor67.1 = true
kernel_rfl_theorem ctorB67 : ctorTypedB 96 dCtor67.2.2 = true
kernel_rfl_theorem famB68 : famTypedB (envPre 68) 96 dRec68.1.family = true
kernel_rfl_theorem ctorB68 : ctorTypedAllB 96 dRec68.1 = true
kernel_rfl_theorem freshB68 : ((envPre 68).members 68).isNone = true
theorem classB68 : (match recSL.mclass with | .recursorM => true | _ => false) = true := rfl
kernel_rfl_theorem mtB68 : Rcic.Declarative.exprClosedAt 0 recSL.mtype = true
theorem famX68 : (extendEnv (envPre 68) 68 recSL).members dRec68.1.family.ref = some dRec68.1.family.member := by
  rw [extendEnv_members_ne (by decide : dRec68.1.family.ref ≠ 68)]
  exact dRec68.1.family.present
kernel_rfl_theorem ixC68_0 : Rcic.Declarative.exprClosedAt 0 (dRec68.1.constructors[0]'(by decide)).mtype = true
kernel_rfl_theorem ixF68_0E : (dRec68.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (envPre 68) (dRec68.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR68_0E0 : constsMemberFuel (envPre 68) (dRec68.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec68.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR68_0E1 : constsMemberFuel (envPre 68) (dRec68.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec68.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri68_0E : (dRec68.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (envPre 68) (dRec68.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR68_0E0
    | 1 => ixR68_0E1
    | k+2 => absurd hk (by have : (dRec68.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF68_0X : (dRec68.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 68) 68 recSL) (dRec68.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR68_0X0 : constsMemberFuel (extendEnv (envPre 68) 68 recSL) (dRec68.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec68.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR68_0X1 : constsMemberFuel (extendEnv (envPre 68) 68 recSL) (dRec68.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec68.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri68_0X : (dRec68.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 68) 68 recSL) (dRec68.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR68_0X0
    | 1 => ixR68_0X1
    | k+2 => absurd hk (by have : (dRec68.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc68_0 : Rcic.Declarative.exprClosedAt (dRec68.1.family.parameters.length + 1 + dRec68.1.constructors.length + dRec68.1.family.indices.length + (dRec68.1.constructorViews ⟨0, by decide⟩).fields.length) (descriptorSchema dRec68.1 dRec68.2 ⟨0, by decide⟩) = true
theorem ctorChk68_0 : recCtorCheckB dRec68.1 dRec68.2 ⟨0, by decide⟩ = true :=
  recCtorCheckB_of ixC68_0 ixF68_0E ri68_0E ixF68_0X ri68_0X famX68 ixSc68_0
kernel_rfl_theorem ixC68_1 : Rcic.Declarative.exprClosedAt 0 (dRec68.1.constructors[1]'(by decide)).mtype = true
kernel_rfl_theorem ixF68_1E : (dRec68.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (envPre 68) (dRec68.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR68_1E0 : constsMemberFuel (envPre 68) (dRec68.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec68.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR68_1E1 : constsMemberFuel (envPre 68) (dRec68.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec68.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri68_1E : (dRec68.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (envPre 68) (dRec68.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR68_1E0
    | 1 => ixR68_1E1
    | k+2 => absurd hk (by have : (dRec68.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF68_1X : (dRec68.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 68) 68 recSL) (dRec68.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR68_1X0 : constsMemberFuel (extendEnv (envPre 68) 68 recSL) (dRec68.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec68.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR68_1X1 : constsMemberFuel (extendEnv (envPre 68) 68 recSL) (dRec68.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec68.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri68_1X : (dRec68.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 68) 68 recSL) (dRec68.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR68_1X0
    | 1 => ixR68_1X1
    | k+2 => absurd hk (by have : (dRec68.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc68_1 : Rcic.Declarative.exprClosedAt (dRec68.1.family.parameters.length + 1 + dRec68.1.constructors.length + dRec68.1.family.indices.length + (dRec68.1.constructorViews ⟨1, by decide⟩).fields.length) (descriptorSchema dRec68.1 dRec68.2 ⟨1, by decide⟩) = true
theorem ctorChk68_1 : recCtorCheckB dRec68.1 dRec68.2 ⟨1, by decide⟩ = true :=
  recCtorCheckB_of ixC68_1 ixF68_1E ri68_1E ixF68_1X ri68_1X famX68 ixSc68_1
theorem idxB68 : recIdxAdmittedTB dRec68.1 dRec68.2 = true :=
  recIdxAdmittedB_of freshB68 classB68 mtB68 fun ⟨i, hi⟩ =>
    match i with
    | 0 => ctorChk68_0
    | 1 => ctorChk68_1
    | k+2 => absurd hi (by have : dRec68.1.constructors.length = 2 := rfl; omega)
kernel_rfl_theorem iotaB68_0 : iotaEqB (a := dRec68.1) (h14 := dRec68.2) (synCheck (extendEnv (envPre 68) 68 recSL) recSL.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB68_1 : iotaEqB (a := dRec68.1) (h14 := dRec68.2) (synCheck (extendEnv (envPre 68) 68 recSL) recSL.arity) 1 (by decide) = true
def typedFam65 : IndGroupTypedT admFamSL := famTypedT_of (fuel := 96) dFam65 famB65
def typedCtor66 : IndGroupTypedT admCtorSlNil :=
  ⟨famTypedT_of (fuel := 96) dCtor66.1 famB66, ctorTypedT_of (fuel := 96) ctorB66⟩
def typedCtor67 : IndGroupTypedT admCtorSlCons :=
  ⟨famTypedT_of (fuel := 96) dCtor67.1 famB67, ctorTypedT_of (fuel := 96) ctorB67⟩
theorem iotaAllB68 : finAllB dRec68.1.constructors.length
    (iotaEqB (a := dRec68.1) (h14 := dRec68.2) (synCheck (extendEnv (envPre 68) 68 recSL) recSL.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB68_0
    | 1 => iotaB68_1
    | k+2 => absurd hi (by have : dRec68.1.constructors.length = 2 := rfl; omega)
def iotaT68 : ∀ i, IotaEquationTypedT dRec68.1 i (dRec68.2.fuelAt i) (dRec68.2.shapesAt i) :=
  iotaEqsT_of iotaAllB68
def idxT68 : IdxAdmittedT admRecSL := idxT_of admRecSL idxB68
def typedRec68 : IndGroupTypedT admRecSL :=
  ⟨famTypedT_of (fuel := 96) dRec68.1.family famB68,
   ctorTypedAll_of ctorB68,
   iotaT68⟩
def mem65 : GroupMembersT (extendEnv (envPre 65) 65 mSL) (envPre 65)
    [(65, mSL), (66, mSlNil), (67, mSlCons), (68, recSL)] (extendEnv (envPre 68) 68 recSL) :=
  (GroupMembersT.cons _ 65 mSL _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamSL PUnit.unit _ tyT65.2 (fun h => absurd h (by decide)) typedFam65
    (GroupMembersT.cons _ 66 mSlNil _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorSlNil PUnit.unit _ tyT66.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS66).2⟩) typedCtor66
    (GroupMembersT.cons _ 67 mSlCons _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorSlCons PUnit.unit _ tyT67.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS67).2⟩) typedCtor67
    (GroupMembersT.cons _ 68 recSL _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecSL idxT68 _ tyT68.2 (fun h => absurd h (by decide)) typedRec68
    (.nil _)))))
def wft69 : EnvWfT (envPre 69) :=
  wfTOfExtend (r := 68) (m := recSL) (by decide) rfl
    (.group (envPre 65) 65 mSL [(66, mSlNil), (67, mSlCons)] 68 recSL _ wft65 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem65)
/- slots 69–72: family mBLL, recursor recBLL -/
kernel_rfl_theorem tyB69 : (sortTyAtC (envPre 69) mBLL.arity 96 [] mBLL.mtype).isSome = true
def tyT69 : Σ u, HasTyT (envPre 69) mBLL.arity [] mBLL.mtype (.sort u) :=
  (sortTyAtC (envPre 69) mBLL.arity 96 [] mBLL.mtype).get tyB69
kernel_rfl_theorem tyB70 : (sortTyAtC (envPre 70) mBllNil.arity 96 [] mBllNil.mtype).isSome = true
def tyT70 : Σ u, HasTyT (envPre 70) mBllNil.arity [] mBllNil.mtype (.sort u) :=
  (sortTyAtC (envPre 70) mBllNil.arity 96 [] mBllNil.mtype).get tyB70
kernel_rfl_theorem tyS70 : (sortTyAtC (extendEnv (envPre 69) 69 mBLL) mBllNil.arity 96 [] mBllNil.mtype).isSome = true
kernel_rfl_theorem tyB71 : (sortTyAtC (envPre 71) mBllCons.arity 96 [] mBllCons.mtype).isSome = true
def tyT71 : Σ u, HasTyT (envPre 71) mBllCons.arity [] mBllCons.mtype (.sort u) :=
  (sortTyAtC (envPre 71) mBllCons.arity 96 [] mBllCons.mtype).get tyB71
kernel_rfl_theorem tyS71 : (sortTyAtC (extendEnv (envPre 69) 69 mBLL) mBllCons.arity 96 [] mBllCons.mtype).isSome = true
kernel_rfl_theorem tyB72 : (sortTyAtC (envPre 72) recBLL.arity 96 [] recBLL.mtype).isSome = true
def tyT72 : Σ u, HasTyT (envPre 72) recBLL.arity [] recBLL.mtype (.sort u) :=
  (sortTyAtC (envPre 72) recBLL.arity 96 [] recBLL.mtype).get tyB72
def dFam69 := (admFamView? admFamBLL).get rfl
def dCtor70 := (admCtorViews? admCtorBllNil).get rfl
def dCtor71 := (admCtorViews? admCtorBllCons).get rfl
def dRec72 := (admRecData admRecBLL).get rfl
kernel_rfl_theorem famB69 : famTypedB (extendEnv (envPre 69) 69 mBLL) 96 dFam69 = true
kernel_rfl_theorem famB70 : famTypedB (envPre 70) 96 dCtor70.1 = true
kernel_rfl_theorem ctorB70 : ctorTypedB 96 dCtor70.2.2 = true
kernel_rfl_theorem famB71 : famTypedB (envPre 71) 96 dCtor71.1 = true
kernel_rfl_theorem ctorB71 : ctorTypedB 96 dCtor71.2.2 = true
kernel_rfl_theorem famB72 : famTypedB (envPre 72) 96 dRec72.1.family = true
kernel_rfl_theorem ctorB72 : ctorTypedAllB 96 dRec72.1 = true
kernel_rfl_theorem freshB72 : ((envPre 72).members 72).isNone = true
theorem classB72 : (match recBLL.mclass with | .recursorM => true | _ => false) = true := rfl
kernel_rfl_theorem mtB72 : Rcic.Declarative.exprClosedAt 0 recBLL.mtype = true
theorem famX72 : (extendEnv (envPre 72) 72 recBLL).members dRec72.1.family.ref = some dRec72.1.family.member := by
  rw [extendEnv_members_ne (by decide : dRec72.1.family.ref ≠ 72)]
  exact dRec72.1.family.present
kernel_rfl_theorem ixC72_0 : Rcic.Declarative.exprClosedAt 0 (dRec72.1.constructors[0]'(by decide)).mtype = true
kernel_rfl_theorem ixF72_0E : (dRec72.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (envPre 72) (dRec72.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR72_0E0 : constsMemberFuel (envPre 72) (dRec72.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec72.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR72_0E1 : constsMemberFuel (envPre 72) (dRec72.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec72.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri72_0E : (dRec72.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (envPre 72) (dRec72.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR72_0E0
    | 1 => ixR72_0E1
    | k+2 => absurd hk (by have : (dRec72.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF72_0X : (dRec72.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 72) 72 recBLL) (dRec72.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR72_0X0 : constsMemberFuel (extendEnv (envPre 72) 72 recBLL) (dRec72.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec72.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR72_0X1 : constsMemberFuel (extendEnv (envPre 72) 72 recBLL) (dRec72.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec72.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri72_0X : (dRec72.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 72) 72 recBLL) (dRec72.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR72_0X0
    | 1 => ixR72_0X1
    | k+2 => absurd hk (by have : (dRec72.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc72_0 : Rcic.Declarative.exprClosedAt (dRec72.1.family.parameters.length + 1 + dRec72.1.constructors.length + dRec72.1.family.indices.length + (dRec72.1.constructorViews ⟨0, by decide⟩).fields.length) (descriptorSchema dRec72.1 dRec72.2 ⟨0, by decide⟩) = true
theorem ctorChk72_0 : recCtorCheckB dRec72.1 dRec72.2 ⟨0, by decide⟩ = true :=
  recCtorCheckB_of ixC72_0 ixF72_0E ri72_0E ixF72_0X ri72_0X famX72 ixSc72_0
kernel_rfl_theorem ixC72_1 : Rcic.Declarative.exprClosedAt 0 (dRec72.1.constructors[1]'(by decide)).mtype = true
kernel_rfl_theorem ixF72_1E : (dRec72.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (envPre 72) (dRec72.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR72_1E0 : constsMemberFuel (envPre 72) (dRec72.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec72.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR72_1E1 : constsMemberFuel (envPre 72) (dRec72.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec72.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri72_1E : (dRec72.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (envPre 72) (dRec72.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR72_1E0
    | 1 => ixR72_1E1
    | k+2 => absurd hk (by have : (dRec72.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF72_1X : (dRec72.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 72) 72 recBLL) (dRec72.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR72_1X0 : constsMemberFuel (extendEnv (envPre 72) 72 recBLL) (dRec72.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec72.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR72_1X1 : constsMemberFuel (extendEnv (envPre 72) 72 recBLL) (dRec72.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec72.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri72_1X : (dRec72.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 72) 72 recBLL) (dRec72.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR72_1X0
    | 1 => ixR72_1X1
    | k+2 => absurd hk (by have : (dRec72.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc72_1 : Rcic.Declarative.exprClosedAt (dRec72.1.family.parameters.length + 1 + dRec72.1.constructors.length + dRec72.1.family.indices.length + (dRec72.1.constructorViews ⟨1, by decide⟩).fields.length) (descriptorSchema dRec72.1 dRec72.2 ⟨1, by decide⟩) = true
theorem ctorChk72_1 : recCtorCheckB dRec72.1 dRec72.2 ⟨1, by decide⟩ = true :=
  recCtorCheckB_of ixC72_1 ixF72_1E ri72_1E ixF72_1X ri72_1X famX72 ixSc72_1
theorem idxB72 : recIdxAdmittedTB dRec72.1 dRec72.2 = true :=
  recIdxAdmittedB_of freshB72 classB72 mtB72 fun ⟨i, hi⟩ =>
    match i with
    | 0 => ctorChk72_0
    | 1 => ctorChk72_1
    | k+2 => absurd hi (by have : dRec72.1.constructors.length = 2 := rfl; omega)
kernel_rfl_theorem iotaB72_0 : iotaEqB (a := dRec72.1) (h14 := dRec72.2) (synCheck (extendEnv (envPre 72) 72 recBLL) recBLL.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB72_1 : iotaEqB (a := dRec72.1) (h14 := dRec72.2) (synCheck (extendEnv (envPre 72) 72 recBLL) recBLL.arity) 1 (by decide) = true
def typedFam69 : IndGroupTypedT admFamBLL := famTypedT_of (fuel := 96) dFam69 famB69
def typedCtor70 : IndGroupTypedT admCtorBllNil :=
  ⟨famTypedT_of (fuel := 96) dCtor70.1 famB70, ctorTypedT_of (fuel := 96) ctorB70⟩
def typedCtor71 : IndGroupTypedT admCtorBllCons :=
  ⟨famTypedT_of (fuel := 96) dCtor71.1 famB71, ctorTypedT_of (fuel := 96) ctorB71⟩
theorem iotaAllB72 : finAllB dRec72.1.constructors.length
    (iotaEqB (a := dRec72.1) (h14 := dRec72.2) (synCheck (extendEnv (envPre 72) 72 recBLL) recBLL.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB72_0
    | 1 => iotaB72_1
    | k+2 => absurd hi (by have : dRec72.1.constructors.length = 2 := rfl; omega)
def iotaT72 : ∀ i, IotaEquationTypedT dRec72.1 i (dRec72.2.fuelAt i) (dRec72.2.shapesAt i) :=
  iotaEqsT_of iotaAllB72
def idxT72 : IdxAdmittedT admRecBLL := idxT_of admRecBLL idxB72
def typedRec72 : IndGroupTypedT admRecBLL :=
  ⟨famTypedT_of (fuel := 96) dRec72.1.family famB72,
   ctorTypedAll_of ctorB72,
   iotaT72⟩
def mem69 : GroupMembersT (extendEnv (envPre 69) 69 mBLL) (envPre 69)
    [(69, mBLL), (70, mBllNil), (71, mBllCons), (72, recBLL)] (extendEnv (envPre 72) 72 recBLL) :=
  (GroupMembersT.cons _ 69 mBLL _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamBLL PUnit.unit _ tyT69.2 (fun h => absurd h (by decide)) typedFam69
    (GroupMembersT.cons _ 70 mBllNil _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorBllNil PUnit.unit _ tyT70.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS70).2⟩) typedCtor70
    (GroupMembersT.cons _ 71 mBllCons _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorBllCons PUnit.unit _ tyT71.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS71).2⟩) typedCtor71
    (GroupMembersT.cons _ 72 recBLL _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecBLL idxT72 _ tyT72.2 (fun h => absurd h (by decide)) typedRec72
    (.nil _)))))
def wft73 : EnvWfT (envPre 73) :=
  wfTOfExtend (r := 72) (m := recBLL) (by decide) rfl
    (.group (envPre 69) 69 mBLL [(70, mBllNil), (71, mBllCons)] 72 recBLL _ wft69 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem69)
/- slots 73–76: family mFTL, recursor recFTL -/
kernel_rfl_theorem tyB73 : (sortTyAtC (envPre 73) mFTL.arity 96 [] mFTL.mtype).isSome = true
def tyT73 : Σ u, HasTyT (envPre 73) mFTL.arity [] mFTL.mtype (.sort u) :=
  (sortTyAtC (envPre 73) mFTL.arity 96 [] mFTL.mtype).get tyB73
kernel_rfl_theorem tyB74 : (sortTyAtC (envPre 74) mFtlNil.arity 96 [] mFtlNil.mtype).isSome = true
def tyT74 : Σ u, HasTyT (envPre 74) mFtlNil.arity [] mFtlNil.mtype (.sort u) :=
  (sortTyAtC (envPre 74) mFtlNil.arity 96 [] mFtlNil.mtype).get tyB74
kernel_rfl_theorem tyS74 : (sortTyAtC (extendEnv (envPre 73) 73 mFTL) mFtlNil.arity 96 [] mFtlNil.mtype).isSome = true
kernel_rfl_theorem tyB75 : (sortTyAtC (envPre 75) mFtlCons.arity 96 [] mFtlCons.mtype).isSome = true
def tyT75 : Σ u, HasTyT (envPre 75) mFtlCons.arity [] mFtlCons.mtype (.sort u) :=
  (sortTyAtC (envPre 75) mFtlCons.arity 96 [] mFtlCons.mtype).get tyB75
kernel_rfl_theorem tyS75 : (sortTyAtC (extendEnv (envPre 73) 73 mFTL) mFtlCons.arity 96 [] mFtlCons.mtype).isSome = true
kernel_rfl_theorem tyB76 : (sortTyAtC (envPre 76) recFTL.arity 96 [] recFTL.mtype).isSome = true
def tyT76 : Σ u, HasTyT (envPre 76) recFTL.arity [] recFTL.mtype (.sort u) :=
  (sortTyAtC (envPre 76) recFTL.arity 96 [] recFTL.mtype).get tyB76
def dFam73 := (admFamView? admFamFTL).get rfl
def dCtor74 := (admCtorViews? admCtorFtlNil).get rfl
def dCtor75 := (admCtorViews? admCtorFtlCons).get rfl
def dRec76 := (admRecData admRecFTL).get rfl
kernel_rfl_theorem famB73 : famTypedB (extendEnv (envPre 73) 73 mFTL) 96 dFam73 = true
kernel_rfl_theorem famB74 : famTypedB (envPre 74) 96 dCtor74.1 = true
kernel_rfl_theorem ctorB74 : ctorTypedB 96 dCtor74.2.2 = true
kernel_rfl_theorem famB75 : famTypedB (envPre 75) 96 dCtor75.1 = true
kernel_rfl_theorem ctorB75 : ctorTypedB 96 dCtor75.2.2 = true
kernel_rfl_theorem famB76 : famTypedB (envPre 76) 96 dRec76.1.family = true
kernel_rfl_theorem ctorB76 : ctorTypedAllB 96 dRec76.1 = true
kernel_rfl_theorem freshB76 : ((envPre 76).members 76).isNone = true
theorem classB76 : (match recFTL.mclass with | .recursorM => true | _ => false) = true := rfl
kernel_rfl_theorem mtB76 : Rcic.Declarative.exprClosedAt 0 recFTL.mtype = true
theorem famX76 : (extendEnv (envPre 76) 76 recFTL).members dRec76.1.family.ref = some dRec76.1.family.member := by
  rw [extendEnv_members_ne (by decide : dRec76.1.family.ref ≠ 76)]
  exact dRec76.1.family.present
kernel_rfl_theorem ixC76_0 : Rcic.Declarative.exprClosedAt 0 (dRec76.1.constructors[0]'(by decide)).mtype = true
kernel_rfl_theorem ixF76_0E : (dRec76.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (envPre 76) (dRec76.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR76_0E0 : constsMemberFuel (envPre 76) (dRec76.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec76.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR76_0E1 : constsMemberFuel (envPre 76) (dRec76.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec76.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri76_0E : (dRec76.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (envPre 76) (dRec76.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR76_0E0
    | 1 => ixR76_0E1
    | k+2 => absurd hk (by have : (dRec76.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF76_0X : (dRec76.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 76) 76 recFTL) (dRec76.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR76_0X0 : constsMemberFuel (extendEnv (envPre 76) 76 recFTL) (dRec76.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec76.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR76_0X1 : constsMemberFuel (extendEnv (envPre 76) 76 recFTL) (dRec76.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec76.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri76_0X : (dRec76.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 76) 76 recFTL) (dRec76.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR76_0X0
    | 1 => ixR76_0X1
    | k+2 => absurd hk (by have : (dRec76.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc76_0 : Rcic.Declarative.exprClosedAt (dRec76.1.family.parameters.length + 1 + dRec76.1.constructors.length + dRec76.1.family.indices.length + (dRec76.1.constructorViews ⟨0, by decide⟩).fields.length) (descriptorSchema dRec76.1 dRec76.2 ⟨0, by decide⟩) = true
theorem ctorChk76_0 : recCtorCheckB dRec76.1 dRec76.2 ⟨0, by decide⟩ = true :=
  recCtorCheckB_of ixC76_0 ixF76_0E ri76_0E ixF76_0X ri76_0X famX76 ixSc76_0
kernel_rfl_theorem ixC76_1 : Rcic.Declarative.exprClosedAt 0 (dRec76.1.constructors[1]'(by decide)).mtype = true
kernel_rfl_theorem ixF76_1E : (dRec76.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (envPre 76) (dRec76.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR76_1E0 : constsMemberFuel (envPre 76) (dRec76.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec76.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR76_1E1 : constsMemberFuel (envPre 76) (dRec76.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec76.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri76_1E : (dRec76.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (envPre 76) (dRec76.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR76_1E0
    | 1 => ixR76_1E1
    | k+2 => absurd hk (by have : (dRec76.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF76_1X : (dRec76.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 76) 76 recFTL) (dRec76.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR76_1X0 : constsMemberFuel (extendEnv (envPre 76) 76 recFTL) (dRec76.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec76.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR76_1X1 : constsMemberFuel (extendEnv (envPre 76) 76 recFTL) (dRec76.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec76.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri76_1X : (dRec76.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 76) 76 recFTL) (dRec76.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR76_1X0
    | 1 => ixR76_1X1
    | k+2 => absurd hk (by have : (dRec76.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc76_1 : Rcic.Declarative.exprClosedAt (dRec76.1.family.parameters.length + 1 + dRec76.1.constructors.length + dRec76.1.family.indices.length + (dRec76.1.constructorViews ⟨1, by decide⟩).fields.length) (descriptorSchema dRec76.1 dRec76.2 ⟨1, by decide⟩) = true
theorem ctorChk76_1 : recCtorCheckB dRec76.1 dRec76.2 ⟨1, by decide⟩ = true :=
  recCtorCheckB_of ixC76_1 ixF76_1E ri76_1E ixF76_1X ri76_1X famX76 ixSc76_1
theorem idxB76 : recIdxAdmittedTB dRec76.1 dRec76.2 = true :=
  recIdxAdmittedB_of freshB76 classB76 mtB76 fun ⟨i, hi⟩ =>
    match i with
    | 0 => ctorChk76_0
    | 1 => ctorChk76_1
    | k+2 => absurd hi (by have : dRec76.1.constructors.length = 2 := rfl; omega)
kernel_rfl_theorem iotaB76_0 : iotaEqB (a := dRec76.1) (h14 := dRec76.2) (synCheck (extendEnv (envPre 76) 76 recFTL) recFTL.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB76_1 : iotaEqB (a := dRec76.1) (h14 := dRec76.2) (synCheck (extendEnv (envPre 76) 76 recFTL) recFTL.arity) 1 (by decide) = true
def typedFam73 : IndGroupTypedT admFamFTL := famTypedT_of (fuel := 96) dFam73 famB73
def typedCtor74 : IndGroupTypedT admCtorFtlNil :=
  ⟨famTypedT_of (fuel := 96) dCtor74.1 famB74, ctorTypedT_of (fuel := 96) ctorB74⟩
def typedCtor75 : IndGroupTypedT admCtorFtlCons :=
  ⟨famTypedT_of (fuel := 96) dCtor75.1 famB75, ctorTypedT_of (fuel := 96) ctorB75⟩
theorem iotaAllB76 : finAllB dRec76.1.constructors.length
    (iotaEqB (a := dRec76.1) (h14 := dRec76.2) (synCheck (extendEnv (envPre 76) 76 recFTL) recFTL.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB76_0
    | 1 => iotaB76_1
    | k+2 => absurd hi (by have : dRec76.1.constructors.length = 2 := rfl; omega)
def iotaT76 : ∀ i, IotaEquationTypedT dRec76.1 i (dRec76.2.fuelAt i) (dRec76.2.shapesAt i) :=
  iotaEqsT_of iotaAllB76
def idxT76 : IdxAdmittedT admRecFTL := idxT_of admRecFTL idxB76
def typedRec76 : IndGroupTypedT admRecFTL :=
  ⟨famTypedT_of (fuel := 96) dRec76.1.family famB76,
   ctorTypedAll_of ctorB76,
   iotaT76⟩
def mem73 : GroupMembersT (extendEnv (envPre 73) 73 mFTL) (envPre 73)
    [(73, mFTL), (74, mFtlNil), (75, mFtlCons), (76, recFTL)] (extendEnv (envPre 76) 76 recFTL) :=
  (GroupMembersT.cons _ 73 mFTL _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamFTL PUnit.unit _ tyT73.2 (fun h => absurd h (by decide)) typedFam73
    (GroupMembersT.cons _ 74 mFtlNil _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorFtlNil PUnit.unit _ tyT74.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS74).2⟩) typedCtor74
    (GroupMembersT.cons _ 75 mFtlCons _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorFtlCons PUnit.unit _ tyT75.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS75).2⟩) typedCtor75
    (GroupMembersT.cons _ 76 recFTL _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecFTL idxT76 _ tyT76.2 (fun h => absurd h (by decide)) typedRec76
    (.nil _)))))
def wft77 : EnvWfT (envPre 77) :=
  wfTOfExtend (r := 76) (m := recFTL) (by decide) rfl
    (.group (envPre 73) 73 mFTL [(74, mFtlNil), (75, mFtlCons)] 76 recFTL _ wft73 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem73)

end Rcic.Scm.SrcG

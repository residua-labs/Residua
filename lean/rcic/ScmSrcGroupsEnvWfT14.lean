import rcic.ScmSrcGroupsEnvWfT13

/-! `EnvWfT` for srcEnvG slots in this file's range. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/- slots 125–128: family mNEL, recursor recNEL -/
kernel_rfl_theorem tyB125 : (sortTyAtC (envPre 125) mNEL.arity 96 [] mNEL.mtype).isSome = true
def tyT125 : Σ u, HasTyT (envPre 125) mNEL.arity [] mNEL.mtype (.sort u) :=
  (sortTyAtC (envPre 125) mNEL.arity 96 [] mNEL.mtype).get tyB125
kernel_rfl_theorem tyB126 : (sortTyAtC (envPre 126) mNelNil.arity 96 [] mNelNil.mtype).isSome = true
def tyT126 : Σ u, HasTyT (envPre 126) mNelNil.arity [] mNelNil.mtype (.sort u) :=
  (sortTyAtC (envPre 126) mNelNil.arity 96 [] mNelNil.mtype).get tyB126
kernel_rfl_theorem tyS126 : (sortTyAtC (extendEnv (envPre 125) 125 mNEL) mNelNil.arity 96 [] mNelNil.mtype).isSome = true
kernel_rfl_theorem tyB127 : (sortTyAtC (envPre 127) mNelCons.arity 96 [] mNelCons.mtype).isSome = true
def tyT127 : Σ u, HasTyT (envPre 127) mNelCons.arity [] mNelCons.mtype (.sort u) :=
  (sortTyAtC (envPre 127) mNelCons.arity 96 [] mNelCons.mtype).get tyB127
kernel_rfl_theorem tyS127 : (sortTyAtC (extendEnv (envPre 125) 125 mNEL) mNelCons.arity 96 [] mNelCons.mtype).isSome = true
kernel_rfl_theorem tyB128 : (sortTyAtC (envPre 128) recNEL.arity 96 [] recNEL.mtype).isSome = true
def tyT128 : Σ u, HasTyT (envPre 128) recNEL.arity [] recNEL.mtype (.sort u) :=
  (sortTyAtC (envPre 128) recNEL.arity 96 [] recNEL.mtype).get tyB128
def dFam125 := (admFamView? admFamNEL).get rfl
def dCtor126 := (admCtorViews? admCtorNelNil).get rfl
def dCtor127 := (admCtorViews? admCtorNelCons).get rfl
def dRec128 := (admRecData admRecNEL).get rfl
kernel_rfl_theorem famB125 : famTypedB (extendEnv (envPre 125) 125 mNEL) 96 dFam125 = true
kernel_rfl_theorem famB126 : famTypedB (envPre 126) 96 dCtor126.1 = true
kernel_rfl_theorem ctorB126 : ctorTypedB 96 dCtor126.2.2 = true
kernel_rfl_theorem famB127 : famTypedB (envPre 127) 96 dCtor127.1 = true
kernel_rfl_theorem ctorB127 : ctorTypedB 96 dCtor127.2.2 = true
kernel_rfl_theorem famB128 : famTypedB (envPre 128) 96 dRec128.1.family = true
kernel_rfl_theorem ctorB128 : ctorTypedAllB 96 dRec128.1 = true
kernel_rfl_theorem freshB128 : ((envPre 128).members 128).isNone = true
theorem classB128 : (match recNEL.mclass with | .recursorM => true | _ => false) = true := rfl
kernel_rfl_theorem mtB128 : Rcic.Declarative.exprClosedAt 0 recNEL.mtype = true
theorem famX128 : (extendEnv (envPre 128) 128 recNEL).members dRec128.1.family.ref = some dRec128.1.family.member := by
  rw [extendEnv_members_ne (by decide : dRec128.1.family.ref ≠ 128)]
  exact dRec128.1.family.present
kernel_rfl_theorem ixC128_0 : Rcic.Declarative.exprClosedAt 0 (dRec128.1.constructors[0]'(by decide)).mtype = true
kernel_rfl_theorem ixF128_0E : (dRec128.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (envPre 128) (dRec128.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR128_0E0 : constsMemberFuel (envPre 128) (dRec128.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec128.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR128_0E1 : constsMemberFuel (envPre 128) (dRec128.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec128.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri128_0E : (dRec128.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (envPre 128) (dRec128.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR128_0E0
    | 1 => ixR128_0E1
    | k+2 => absurd hk (by have : (dRec128.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF128_0X : (dRec128.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 128) 128 recNEL) (dRec128.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR128_0X0 : constsMemberFuel (extendEnv (envPre 128) 128 recNEL) (dRec128.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec128.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR128_0X1 : constsMemberFuel (extendEnv (envPre 128) 128 recNEL) (dRec128.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec128.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri128_0X : (dRec128.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 128) 128 recNEL) (dRec128.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR128_0X0
    | 1 => ixR128_0X1
    | k+2 => absurd hk (by have : (dRec128.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc128_0 : Rcic.Declarative.exprClosedAt (dRec128.1.family.parameters.length + 1 + dRec128.1.constructors.length + dRec128.1.family.indices.length + (dRec128.1.constructorViews ⟨0, by decide⟩).fields.length) (descriptorSchema dRec128.1 dRec128.2 ⟨0, by decide⟩) = true
theorem ctorChk128_0 : recCtorCheckB dRec128.1 dRec128.2 ⟨0, by decide⟩ = true :=
  recCtorCheckB_of ixC128_0 ixF128_0E ri128_0E ixF128_0X ri128_0X famX128 ixSc128_0
kernel_rfl_theorem ixC128_1 : Rcic.Declarative.exprClosedAt 0 (dRec128.1.constructors[1]'(by decide)).mtype = true
kernel_rfl_theorem ixF128_1E : (dRec128.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (envPre 128) (dRec128.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR128_1E0 : constsMemberFuel (envPre 128) (dRec128.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec128.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR128_1E1 : constsMemberFuel (envPre 128) (dRec128.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec128.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri128_1E : (dRec128.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (envPre 128) (dRec128.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR128_1E0
    | 1 => ixR128_1E1
    | k+2 => absurd hk (by have : (dRec128.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF128_1X : (dRec128.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 128) 128 recNEL) (dRec128.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR128_1X0 : constsMemberFuel (extendEnv (envPre 128) 128 recNEL) (dRec128.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec128.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR128_1X1 : constsMemberFuel (extendEnv (envPre 128) 128 recNEL) (dRec128.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec128.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri128_1X : (dRec128.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 128) 128 recNEL) (dRec128.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR128_1X0
    | 1 => ixR128_1X1
    | k+2 => absurd hk (by have : (dRec128.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc128_1 : Rcic.Declarative.exprClosedAt (dRec128.1.family.parameters.length + 1 + dRec128.1.constructors.length + dRec128.1.family.indices.length + (dRec128.1.constructorViews ⟨1, by decide⟩).fields.length) (descriptorSchema dRec128.1 dRec128.2 ⟨1, by decide⟩) = true
theorem ctorChk128_1 : recCtorCheckB dRec128.1 dRec128.2 ⟨1, by decide⟩ = true :=
  recCtorCheckB_of ixC128_1 ixF128_1E ri128_1E ixF128_1X ri128_1X famX128 ixSc128_1
theorem idxB128 : recIdxAdmittedTB dRec128.1 dRec128.2 = true :=
  recIdxAdmittedB_of freshB128 classB128 mtB128 fun ⟨i, hi⟩ =>
    match i with
    | 0 => ctorChk128_0
    | 1 => ctorChk128_1
    | k+2 => absurd hi (by have : dRec128.1.constructors.length = 2 := rfl; omega)
kernel_rfl_theorem iotaB128_0 : iotaEqB (a := dRec128.1) (h14 := dRec128.2) (synCheck (extendEnv (envPre 128) 128 recNEL) recNEL.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB128_1 : iotaEqB (a := dRec128.1) (h14 := dRec128.2) (synCheck (extendEnv (envPre 128) 128 recNEL) recNEL.arity) 1 (by decide) = true
def typedFam125 : IndGroupTypedT admFamNEL := famTypedT_of (fuel := 96) dFam125 famB125
def typedCtor126 : IndGroupTypedT admCtorNelNil :=
  ⟨famTypedT_of (fuel := 96) dCtor126.1 famB126, ctorTypedT_of (fuel := 96) ctorB126⟩
def typedCtor127 : IndGroupTypedT admCtorNelCons :=
  ⟨famTypedT_of (fuel := 96) dCtor127.1 famB127, ctorTypedT_of (fuel := 96) ctorB127⟩
theorem iotaAllB128 : finAllB dRec128.1.constructors.length
    (iotaEqB (a := dRec128.1) (h14 := dRec128.2) (synCheck (extendEnv (envPre 128) 128 recNEL) recNEL.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB128_0
    | 1 => iotaB128_1
    | k+2 => absurd hi (by have : dRec128.1.constructors.length = 2 := rfl; omega)
def iotaT128 : ∀ i, IotaEquationTypedT dRec128.1 i (dRec128.2.fuelAt i) (dRec128.2.shapesAt i) :=
  iotaEqsT_of iotaAllB128
def idxT128 : IdxAdmittedT admRecNEL := idxT_of admRecNEL idxB128
def typedRec128 : IndGroupTypedT admRecNEL :=
  ⟨famTypedT_of (fuel := 96) dRec128.1.family famB128,
   ctorTypedAll_of ctorB128,
   iotaT128⟩
def mem125 : GroupMembersT (extendEnv (envPre 125) 125 mNEL) (envPre 125)
    [(125, mNEL), (126, mNelNil), (127, mNelCons), (128, recNEL)] (extendEnv (envPre 128) 128 recNEL) :=
  (GroupMembersT.cons _ 125 mNEL _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamNEL PUnit.unit _ tyT125.2 (fun h => absurd h (by decide)) typedFam125
    (GroupMembersT.cons _ 126 mNelNil _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorNelNil PUnit.unit _ tyT126.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS126).2⟩) typedCtor126
    (GroupMembersT.cons _ 127 mNelCons _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorNelCons PUnit.unit _ tyT127.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS127).2⟩) typedCtor127
    (GroupMembersT.cons _ 128 recNEL _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecNEL idxT128 _ tyT128.2 (fun h => absurd h (by decide)) typedRec128
    (.nil _)))))
def wft129 : EnvWfT (envPre 129) :=
  wfTOfExtend (r := 128) (m := recNEL) (by decide) rfl
    (.group (envPre 125) 125 mNEL [(126, mNelNil), (127, mNelCons)] 128 recNEL _ wft125 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem125)
/- slots 129–132: family mNTB, recursor recNTB -/
kernel_rfl_theorem tyB129 : (sortTyAtC (envPre 129) mNTB.arity 96 [] mNTB.mtype).isSome = true
def tyT129 : Σ u, HasTyT (envPre 129) mNTB.arity [] mNTB.mtype (.sort u) :=
  (sortTyAtC (envPre 129) mNTB.arity 96 [] mNTB.mtype).get tyB129
kernel_rfl_theorem tyB130 : (sortTyAtC (envPre 130) mNtbHere.arity 96 [] mNtbHere.mtype).isSome = true
def tyT130 : Σ u, HasTyT (envPre 130) mNtbHere.arity [] mNtbHere.mtype (.sort u) :=
  (sortTyAtC (envPre 130) mNtbHere.arity 96 [] mNtbHere.mtype).get tyB130
kernel_rfl_theorem tyS130 : (sortTyAtC (extendEnv (envPre 129) 129 mNTB) mNtbHere.arity 96 [] mNtbHere.mtype).isSome = true
kernel_rfl_theorem tyB131 : (sortTyAtC (envPre 131) mNtbNext.arity 96 [] mNtbNext.mtype).isSome = true
def tyT131 : Σ u, HasTyT (envPre 131) mNtbNext.arity [] mNtbNext.mtype (.sort u) :=
  (sortTyAtC (envPre 131) mNtbNext.arity 96 [] mNtbNext.mtype).get tyB131
kernel_rfl_theorem tyS131 : (sortTyAtC (extendEnv (envPre 129) 129 mNTB) mNtbNext.arity 96 [] mNtbNext.mtype).isSome = true
kernel_rfl_theorem tyB132 : (sortTyAtC (envPre 132) recNTB.arity 96 [] recNTB.mtype).isSome = true
def tyT132 : Σ u, HasTyT (envPre 132) recNTB.arity [] recNTB.mtype (.sort u) :=
  (sortTyAtC (envPre 132) recNTB.arity 96 [] recNTB.mtype).get tyB132
def dFam129 := (admFamView? admFamNTB).get rfl
def dCtor130 := (admCtorViews? admCtorNtbHere).get rfl
def dCtor131 := (admCtorViews? admCtorNtbNext).get rfl
def dRec132 := (admRecData admRecNTB).get rfl
kernel_rfl_theorem famB129 : famTypedB (extendEnv (envPre 129) 129 mNTB) 96 dFam129 = true
kernel_rfl_theorem famB130 : famTypedB (envPre 130) 96 dCtor130.1 = true
kernel_rfl_theorem ctorB130 : ctorTypedB 96 dCtor130.2.2 = true
kernel_rfl_theorem famB131 : famTypedB (envPre 131) 96 dCtor131.1 = true
kernel_rfl_theorem ctorB131 : ctorTypedB 96 dCtor131.2.2 = true
kernel_rfl_theorem famB132 : famTypedB (envPre 132) 96 dRec132.1.family = true
kernel_rfl_theorem ctorB132 : ctorTypedAllB 96 dRec132.1 = true
kernel_rfl_theorem freshB132 : ((envPre 132).members 132).isNone = true
theorem classB132 : (match recNTB.mclass with | .recursorM => true | _ => false) = true := rfl
kernel_rfl_theorem mtB132 : Rcic.Declarative.exprClosedAt 0 recNTB.mtype = true
theorem famX132 : (extendEnv (envPre 132) 132 recNTB).members dRec132.1.family.ref = some dRec132.1.family.member := by
  rw [extendEnv_members_ne (by decide : dRec132.1.family.ref ≠ 132)]
  exact dRec132.1.family.present
kernel_rfl_theorem ixC132_0 : Rcic.Declarative.exprClosedAt 0 (dRec132.1.constructors[0]'(by decide)).mtype = true
kernel_rfl_theorem ixF132_0E : (dRec132.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (envPre 132) (dRec132.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR132_0E0 : constsMemberFuel (envPre 132) (dRec132.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec132.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR132_0E1 : constsMemberFuel (envPre 132) (dRec132.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec132.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR132_0E2 : constsMemberFuel (envPre 132) (dRec132.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec132.1.constructorViews ⟨0, by decide⟩).resultIndices[2]'(by decide)) = true
theorem ri132_0E : (dRec132.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (envPre 132) (dRec132.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR132_0E0
    | 1 => ixR132_0E1
    | 2 => ixR132_0E2
    | k+3 => absurd hk (by have : (dRec132.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 3 := rfl; omega)
kernel_rfl_theorem ixF132_0X : (dRec132.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 132) 132 recNTB) (dRec132.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR132_0X0 : constsMemberFuel (extendEnv (envPre 132) 132 recNTB) (dRec132.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec132.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR132_0X1 : constsMemberFuel (extendEnv (envPre 132) 132 recNTB) (dRec132.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec132.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR132_0X2 : constsMemberFuel (extendEnv (envPre 132) 132 recNTB) (dRec132.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec132.1.constructorViews ⟨0, by decide⟩).resultIndices[2]'(by decide)) = true
theorem ri132_0X : (dRec132.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 132) 132 recNTB) (dRec132.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR132_0X0
    | 1 => ixR132_0X1
    | 2 => ixR132_0X2
    | k+3 => absurd hk (by have : (dRec132.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 3 := rfl; omega)
kernel_rfl_theorem ixSc132_0 : Rcic.Declarative.exprClosedAt (dRec132.1.family.parameters.length + 1 + dRec132.1.constructors.length + dRec132.1.family.indices.length + (dRec132.1.constructorViews ⟨0, by decide⟩).fields.length) (descriptorSchema dRec132.1 dRec132.2 ⟨0, by decide⟩) = true
theorem ctorChk132_0 : recCtorCheckB dRec132.1 dRec132.2 ⟨0, by decide⟩ = true :=
  recCtorCheckB_of ixC132_0 ixF132_0E ri132_0E ixF132_0X ri132_0X famX132 ixSc132_0
kernel_rfl_theorem ixC132_1 : Rcic.Declarative.exprClosedAt 0 (dRec132.1.constructors[1]'(by decide)).mtype = true
kernel_rfl_theorem ixF132_1E : (dRec132.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (envPre 132) (dRec132.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR132_1E0 : constsMemberFuel (envPre 132) (dRec132.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec132.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR132_1E1 : constsMemberFuel (envPre 132) (dRec132.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec132.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR132_1E2 : constsMemberFuel (envPre 132) (dRec132.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec132.1.constructorViews ⟨1, by decide⟩).resultIndices[2]'(by decide)) = true
theorem ri132_1E : (dRec132.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (envPre 132) (dRec132.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR132_1E0
    | 1 => ixR132_1E1
    | 2 => ixR132_1E2
    | k+3 => absurd hk (by have : (dRec132.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 3 := rfl; omega)
kernel_rfl_theorem ixF132_1X : (dRec132.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 132) 132 recNTB) (dRec132.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR132_1X0 : constsMemberFuel (extendEnv (envPre 132) 132 recNTB) (dRec132.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec132.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR132_1X1 : constsMemberFuel (extendEnv (envPre 132) 132 recNTB) (dRec132.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec132.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR132_1X2 : constsMemberFuel (extendEnv (envPre 132) 132 recNTB) (dRec132.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec132.1.constructorViews ⟨1, by decide⟩).resultIndices[2]'(by decide)) = true
theorem ri132_1X : (dRec132.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 132) 132 recNTB) (dRec132.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR132_1X0
    | 1 => ixR132_1X1
    | 2 => ixR132_1X2
    | k+3 => absurd hk (by have : (dRec132.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 3 := rfl; omega)
kernel_rfl_theorem ixSc132_1 : Rcic.Declarative.exprClosedAt (dRec132.1.family.parameters.length + 1 + dRec132.1.constructors.length + dRec132.1.family.indices.length + (dRec132.1.constructorViews ⟨1, by decide⟩).fields.length) (descriptorSchema dRec132.1 dRec132.2 ⟨1, by decide⟩) = true
theorem ctorChk132_1 : recCtorCheckB dRec132.1 dRec132.2 ⟨1, by decide⟩ = true :=
  recCtorCheckB_of ixC132_1 ixF132_1E ri132_1E ixF132_1X ri132_1X famX132 ixSc132_1
theorem idxB132 : recIdxAdmittedTB dRec132.1 dRec132.2 = true :=
  recIdxAdmittedB_of freshB132 classB132 mtB132 fun ⟨i, hi⟩ =>
    match i with
    | 0 => ctorChk132_0
    | 1 => ctorChk132_1
    | k+2 => absurd hi (by have : dRec132.1.constructors.length = 2 := rfl; omega)
kernel_rfl_theorem iotaB132_0 : iotaEqB (a := dRec132.1) (h14 := dRec132.2) (synCheck (extendEnv (envPre 132) 132 recNTB) recNTB.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB132_1 : iotaEqB (a := dRec132.1) (h14 := dRec132.2) (synCheck (extendEnv (envPre 132) 132 recNTB) recNTB.arity) 1 (by decide) = true
def typedFam129 : IndGroupTypedT admFamNTB := famTypedT_of (fuel := 96) dFam129 famB129
def typedCtor130 : IndGroupTypedT admCtorNtbHere :=
  ⟨famTypedT_of (fuel := 96) dCtor130.1 famB130, ctorTypedT_of (fuel := 96) ctorB130⟩
def typedCtor131 : IndGroupTypedT admCtorNtbNext :=
  ⟨famTypedT_of (fuel := 96) dCtor131.1 famB131, ctorTypedT_of (fuel := 96) ctorB131⟩
theorem iotaAllB132 : finAllB dRec132.1.constructors.length
    (iotaEqB (a := dRec132.1) (h14 := dRec132.2) (synCheck (extendEnv (envPre 132) 132 recNTB) recNTB.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB132_0
    | 1 => iotaB132_1
    | k+2 => absurd hi (by have : dRec132.1.constructors.length = 2 := rfl; omega)
def iotaT132 : ∀ i, IotaEquationTypedT dRec132.1 i (dRec132.2.fuelAt i) (dRec132.2.shapesAt i) :=
  iotaEqsT_of iotaAllB132
def idxT132 : IdxAdmittedT admRecNTB := idxT_of admRecNTB idxB132
def typedRec132 : IndGroupTypedT admRecNTB :=
  ⟨famTypedT_of (fuel := 96) dRec132.1.family famB132,
   ctorTypedAll_of ctorB132,
   iotaT132⟩
def mem129 : GroupMembersT (extendEnv (envPre 129) 129 mNTB) (envPre 129)
    [(129, mNTB), (130, mNtbHere), (131, mNtbNext), (132, recNTB)] (extendEnv (envPre 132) 132 recNTB) :=
  (GroupMembersT.cons _ 129 mNTB _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamNTB PUnit.unit _ tyT129.2 (fun h => absurd h (by decide)) typedFam129
    (GroupMembersT.cons _ 130 mNtbHere _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorNtbHere PUnit.unit _ tyT130.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS130).2⟩) typedCtor130
    (GroupMembersT.cons _ 131 mNtbNext _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorNtbNext PUnit.unit _ tyT131.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS131).2⟩) typedCtor131
    (GroupMembersT.cons _ 132 recNTB _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecNTB idxT132 _ tyT132.2 (fun h => absurd h (by decide)) typedRec132
    (.nil _)))))
def wft133 : EnvWfT (envPre 133) :=
  wfTOfExtend (r := 132) (m := recNTB) (by decide) rfl
    (.group (envPre 129) 129 mNTB [(130, mNtbHere), (131, mNtbNext)] 132 recNTB _ wft129 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem129)

end Rcic.Scm.SrcG

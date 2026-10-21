import rcic.ScmSrcGroupsEnvWfT8

/-! `EnvWfT` for srcEnvG slots in this file's range. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/- slots 77–80: family mBLC, recursor recBLC -/
kernel_rfl_theorem tyB77 : (sortTyAtC (envPre 77) mBLC.arity 96 [] mBLC.mtype).isSome = true
def tyT77 : Σ u, HasTyT (envPre 77) mBLC.arity [] mBLC.mtype (.sort u) :=
  (sortTyAtC (envPre 77) mBLC.arity 96 [] mBLC.mtype).get tyB77
kernel_rfl_theorem tyB78 : (sortTyAtC (envPre 78) mBlcNil.arity 96 [] mBlcNil.mtype).isSome = true
def tyT78 : Σ u, HasTyT (envPre 78) mBlcNil.arity [] mBlcNil.mtype (.sort u) :=
  (sortTyAtC (envPre 78) mBlcNil.arity 96 [] mBlcNil.mtype).get tyB78
kernel_rfl_theorem tyS78 : (sortTyAtC (extendEnv (envPre 77) 77 mBLC) mBlcNil.arity 96 [] mBlcNil.mtype).isSome = true
kernel_rfl_theorem tyB79 : (sortTyAtC (envPre 79) mBlcCons.arity 96 [] mBlcCons.mtype).isSome = true
def tyT79 : Σ u, HasTyT (envPre 79) mBlcCons.arity [] mBlcCons.mtype (.sort u) :=
  (sortTyAtC (envPre 79) mBlcCons.arity 96 [] mBlcCons.mtype).get tyB79
kernel_rfl_theorem tyS79 : (sortTyAtC (extendEnv (envPre 77) 77 mBLC) mBlcCons.arity 96 [] mBlcCons.mtype).isSome = true
kernel_rfl_theorem tyB80 : (sortTyAtC (envPre 80) recBLC.arity 96 [] recBLC.mtype).isSome = true
def tyT80 : Σ u, HasTyT (envPre 80) recBLC.arity [] recBLC.mtype (.sort u) :=
  (sortTyAtC (envPre 80) recBLC.arity 96 [] recBLC.mtype).get tyB80
def dFam77 := (admFamView? admFamBLC).get rfl
def dCtor78 := (admCtorViews? admCtorBlcNil).get rfl
def dCtor79 := (admCtorViews? admCtorBlcCons).get rfl
def dRec80 := (admRecData admRecBLC).get rfl
kernel_rfl_theorem famB77 : famTypedB (extendEnv (envPre 77) 77 mBLC) 96 dFam77 = true
kernel_rfl_theorem famB78 : famTypedB (envPre 78) 96 dCtor78.1 = true
kernel_rfl_theorem ctorB78 : ctorTypedB 96 dCtor78.2.2 = true
kernel_rfl_theorem famB79 : famTypedB (envPre 79) 96 dCtor79.1 = true
kernel_rfl_theorem ctorB79 : ctorTypedB 96 dCtor79.2.2 = true
kernel_rfl_theorem famB80 : famTypedB (envPre 80) 96 dRec80.1.family = true
kernel_rfl_theorem ctorB80 : ctorTypedAllB 96 dRec80.1 = true
kernel_rfl_theorem freshB80 : ((envPre 80).members 80).isNone = true
theorem classB80 : (match recBLC.mclass with | .recursorM => true | _ => false) = true := rfl
kernel_rfl_theorem mtB80 : Rcic.Declarative.exprClosedAt 0 recBLC.mtype = true
theorem famX80 : (extendEnv (envPre 80) 80 recBLC).members dRec80.1.family.ref = some dRec80.1.family.member := by
  rw [extendEnv_members_ne (by decide : dRec80.1.family.ref ≠ 80)]
  exact dRec80.1.family.present
kernel_rfl_theorem ixC80_0 : Rcic.Declarative.exprClosedAt 0 (dRec80.1.constructors[0]'(by decide)).mtype = true
kernel_rfl_theorem ixF80_0E : (dRec80.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (envPre 80) (dRec80.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR80_0E0 : constsMemberFuel (envPre 80) (dRec80.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec80.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR80_0E1 : constsMemberFuel (envPre 80) (dRec80.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec80.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri80_0E : (dRec80.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (envPre 80) (dRec80.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR80_0E0
    | 1 => ixR80_0E1
    | k+2 => absurd hk (by have : (dRec80.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF80_0X : (dRec80.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 80) 80 recBLC) (dRec80.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR80_0X0 : constsMemberFuel (extendEnv (envPre 80) 80 recBLC) (dRec80.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec80.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR80_0X1 : constsMemberFuel (extendEnv (envPre 80) 80 recBLC) (dRec80.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec80.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri80_0X : (dRec80.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 80) 80 recBLC) (dRec80.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR80_0X0
    | 1 => ixR80_0X1
    | k+2 => absurd hk (by have : (dRec80.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc80_0 : Rcic.Declarative.exprClosedAt (dRec80.1.family.parameters.length + 1 + dRec80.1.constructors.length + dRec80.1.family.indices.length + (dRec80.1.constructorViews ⟨0, by decide⟩).fields.length) (descriptorSchema dRec80.1 dRec80.2 ⟨0, by decide⟩) = true
theorem ctorChk80_0 : recCtorCheckB dRec80.1 dRec80.2 ⟨0, by decide⟩ = true :=
  recCtorCheckB_of ixC80_0 ixF80_0E ri80_0E ixF80_0X ri80_0X famX80 ixSc80_0
kernel_rfl_theorem ixC80_1 : Rcic.Declarative.exprClosedAt 0 (dRec80.1.constructors[1]'(by decide)).mtype = true
kernel_rfl_theorem ixF80_1E : (dRec80.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (envPre 80) (dRec80.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR80_1E0 : constsMemberFuel (envPre 80) (dRec80.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec80.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR80_1E1 : constsMemberFuel (envPre 80) (dRec80.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec80.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri80_1E : (dRec80.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (envPre 80) (dRec80.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR80_1E0
    | 1 => ixR80_1E1
    | k+2 => absurd hk (by have : (dRec80.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF80_1X : (dRec80.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 80) 80 recBLC) (dRec80.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR80_1X0 : constsMemberFuel (extendEnv (envPre 80) 80 recBLC) (dRec80.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec80.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR80_1X1 : constsMemberFuel (extendEnv (envPre 80) 80 recBLC) (dRec80.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec80.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri80_1X : (dRec80.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 80) 80 recBLC) (dRec80.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR80_1X0
    | 1 => ixR80_1X1
    | k+2 => absurd hk (by have : (dRec80.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc80_1 : Rcic.Declarative.exprClosedAt (dRec80.1.family.parameters.length + 1 + dRec80.1.constructors.length + dRec80.1.family.indices.length + (dRec80.1.constructorViews ⟨1, by decide⟩).fields.length) (descriptorSchema dRec80.1 dRec80.2 ⟨1, by decide⟩) = true
theorem ctorChk80_1 : recCtorCheckB dRec80.1 dRec80.2 ⟨1, by decide⟩ = true :=
  recCtorCheckB_of ixC80_1 ixF80_1E ri80_1E ixF80_1X ri80_1X famX80 ixSc80_1
theorem idxB80 : recIdxAdmittedTB dRec80.1 dRec80.2 = true :=
  recIdxAdmittedB_of freshB80 classB80 mtB80 fun ⟨i, hi⟩ =>
    match i with
    | 0 => ctorChk80_0
    | 1 => ctorChk80_1
    | k+2 => absurd hi (by have : dRec80.1.constructors.length = 2 := rfl; omega)
kernel_rfl_theorem iotaB80_0 : iotaEqB (a := dRec80.1) (h14 := dRec80.2) (synCheck (extendEnv (envPre 80) 80 recBLC) recBLC.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB80_1 : iotaEqB (a := dRec80.1) (h14 := dRec80.2) (synCheck (extendEnv (envPre 80) 80 recBLC) recBLC.arity) 1 (by decide) = true
def typedFam77 : IndGroupTypedT admFamBLC := famTypedT_of (fuel := 96) dFam77 famB77
def typedCtor78 : IndGroupTypedT admCtorBlcNil :=
  ⟨famTypedT_of (fuel := 96) dCtor78.1 famB78, ctorTypedT_of (fuel := 96) ctorB78⟩
def typedCtor79 : IndGroupTypedT admCtorBlcCons :=
  ⟨famTypedT_of (fuel := 96) dCtor79.1 famB79, ctorTypedT_of (fuel := 96) ctorB79⟩
theorem iotaAllB80 : finAllB dRec80.1.constructors.length
    (iotaEqB (a := dRec80.1) (h14 := dRec80.2) (synCheck (extendEnv (envPre 80) 80 recBLC) recBLC.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB80_0
    | 1 => iotaB80_1
    | k+2 => absurd hi (by have : dRec80.1.constructors.length = 2 := rfl; omega)
def iotaT80 : ∀ i, IotaEquationTypedT dRec80.1 i (dRec80.2.fuelAt i) (dRec80.2.shapesAt i) :=
  iotaEqsT_of iotaAllB80
def idxT80 : IdxAdmittedT admRecBLC := idxT_of admRecBLC idxB80
def typedRec80 : IndGroupTypedT admRecBLC :=
  ⟨famTypedT_of (fuel := 96) dRec80.1.family famB80,
   ctorTypedAll_of ctorB80,
   iotaT80⟩
def mem77 : GroupMembersT (extendEnv (envPre 77) 77 mBLC) (envPre 77)
    [(77, mBLC), (78, mBlcNil), (79, mBlcCons), (80, recBLC)] (extendEnv (envPre 80) 80 recBLC) :=
  (GroupMembersT.cons _ 77 mBLC _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamBLC PUnit.unit _ tyT77.2 (fun h => absurd h (by decide)) typedFam77
    (GroupMembersT.cons _ 78 mBlcNil _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorBlcNil PUnit.unit _ tyT78.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS78).2⟩) typedCtor78
    (GroupMembersT.cons _ 79 mBlcCons _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorBlcCons PUnit.unit _ tyT79.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS79).2⟩) typedCtor79
    (GroupMembersT.cons _ 80 recBLC _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecBLC idxT80 _ tyT80.2 (fun h => absurd h (by decide)) typedRec80
    (.nil _)))))
def wft81 : EnvWfT (envPre 81) :=
  wfTOfExtend (r := 80) (m := recBLC) (by decide) rfl
    (.group (envPre 77) 77 mBLC [(78, mBlcNil), (79, mBlcCons)] 80 recBLC _ wft77 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem77)
/- slots 81–83: family mSEA, recursor recSEA -/
kernel_rfl_theorem tyB81 : (sortTyAtC (envPre 81) mSEA.arity 96 [] mSEA.mtype).isSome = true
def tyT81 : Σ u, HasTyT (envPre 81) mSEA.arity [] mSEA.mtype (.sort u) :=
  (sortTyAtC (envPre 81) mSEA.arity 96 [] mSEA.mtype).get tyB81
kernel_rfl_theorem tyB82 : (sortTyAtC (envPre 82) mSeIntro.arity 96 [] mSeIntro.mtype).isSome = true
def tyT82 : Σ u, HasTyT (envPre 82) mSeIntro.arity [] mSeIntro.mtype (.sort u) :=
  (sortTyAtC (envPre 82) mSeIntro.arity 96 [] mSeIntro.mtype).get tyB82
kernel_rfl_theorem tyS82 : (sortTyAtC (extendEnv (envPre 81) 81 mSEA) mSeIntro.arity 96 [] mSeIntro.mtype).isSome = true
kernel_rfl_theorem tyB83 : (sortTyAtC (envPre 83) recSEA.arity 96 [] recSEA.mtype).isSome = true
def tyT83 : Σ u, HasTyT (envPre 83) recSEA.arity [] recSEA.mtype (.sort u) :=
  (sortTyAtC (envPre 83) recSEA.arity 96 [] recSEA.mtype).get tyB83
def dFam81 := (admFamView? admFamSEA).get rfl
def dCtor82 := (admCtorViews? admCtorSeIntro).get rfl
def dRec83 := (admRecData admRecSEA).get rfl
kernel_rfl_theorem famB81 : famTypedB (extendEnv (envPre 81) 81 mSEA) 96 dFam81 = true
kernel_rfl_theorem famB82 : famTypedB (envPre 82) 96 dCtor82.1 = true
kernel_rfl_theorem ctorB82 : ctorTypedB 96 dCtor82.2.2 = true
kernel_rfl_theorem famB83 : famTypedB (envPre 83) 96 dRec83.1.family = true
kernel_rfl_theorem ctorB83 : ctorTypedAllB 96 dRec83.1 = true
kernel_rfl_theorem freshB83 : ((envPre 83).members 83).isNone = true
theorem classB83 : (match recSEA.mclass with | .recursorM => true | _ => false) = true := rfl
kernel_rfl_theorem mtB83 : Rcic.Declarative.exprClosedAt 0 recSEA.mtype = true
theorem famX83 : (extendEnv (envPre 83) 83 recSEA).members dRec83.1.family.ref = some dRec83.1.family.member := by
  rw [extendEnv_members_ne (by decide : dRec83.1.family.ref ≠ 83)]
  exact dRec83.1.family.present
kernel_rfl_theorem ixC83_0 : Rcic.Declarative.exprClosedAt 0 (dRec83.1.constructors[0]'(by decide)).mtype = true
kernel_rfl_theorem ixF83_0E : (dRec83.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (envPre 83) (dRec83.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR83_0E0 : constsMemberFuel (envPre 83) (dRec83.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec83.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR83_0E1 : constsMemberFuel (envPre 83) (dRec83.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec83.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri83_0E : (dRec83.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (envPre 83) (dRec83.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR83_0E0
    | 1 => ixR83_0E1
    | k+2 => absurd hk (by have : (dRec83.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF83_0X : (dRec83.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 83) 83 recSEA) (dRec83.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR83_0X0 : constsMemberFuel (extendEnv (envPre 83) 83 recSEA) (dRec83.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec83.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR83_0X1 : constsMemberFuel (extendEnv (envPre 83) 83 recSEA) (dRec83.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec83.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri83_0X : (dRec83.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 83) 83 recSEA) (dRec83.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR83_0X0
    | 1 => ixR83_0X1
    | k+2 => absurd hk (by have : (dRec83.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc83_0 : Rcic.Declarative.exprClosedAt (dRec83.1.family.parameters.length + 1 + dRec83.1.constructors.length + dRec83.1.family.indices.length + (dRec83.1.constructorViews ⟨0, by decide⟩).fields.length) (descriptorSchema dRec83.1 dRec83.2 ⟨0, by decide⟩) = true
theorem ctorChk83_0 : recCtorCheckB dRec83.1 dRec83.2 ⟨0, by decide⟩ = true :=
  recCtorCheckB_of ixC83_0 ixF83_0E ri83_0E ixF83_0X ri83_0X famX83 ixSc83_0
theorem idxB83 : recIdxAdmittedTB dRec83.1 dRec83.2 = true :=
  recIdxAdmittedB_of freshB83 classB83 mtB83 fun ⟨i, hi⟩ =>
    match i with
    | 0 => ctorChk83_0
    | k+1 => absurd hi (by have : dRec83.1.constructors.length = 1 := rfl; omega)
kernel_rfl_theorem iotaB83_0 : iotaEqB (a := dRec83.1) (h14 := dRec83.2) (synCheck (extendEnv (envPre 83) 83 recSEA) recSEA.arity) 0 (by decide) = true
def typedFam81 : IndGroupTypedT admFamSEA := famTypedT_of (fuel := 96) dFam81 famB81
def typedCtor82 : IndGroupTypedT admCtorSeIntro :=
  ⟨famTypedT_of (fuel := 96) dCtor82.1 famB82, ctorTypedT_of (fuel := 96) ctorB82⟩
theorem iotaAllB83 : finAllB dRec83.1.constructors.length
    (iotaEqB (a := dRec83.1) (h14 := dRec83.2) (synCheck (extendEnv (envPre 83) 83 recSEA) recSEA.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB83_0
    | k+1 => absurd hi (by have : dRec83.1.constructors.length = 1 := rfl; omega)
def iotaT83 : ∀ i, IotaEquationTypedT dRec83.1 i (dRec83.2.fuelAt i) (dRec83.2.shapesAt i) :=
  iotaEqsT_of iotaAllB83
def idxT83 : IdxAdmittedT admRecSEA := idxT_of admRecSEA idxB83
def typedRec83 : IndGroupTypedT admRecSEA :=
  ⟨famTypedT_of (fuel := 96) dRec83.1.family famB83,
   ctorTypedAll_of ctorB83,
   iotaT83⟩
def mem81 : GroupMembersT (extendEnv (envPre 81) 81 mSEA) (envPre 81)
    [(81, mSEA), (82, mSeIntro), (83, recSEA)] (extendEnv (envPre 83) 83 recSEA) :=
  (GroupMembersT.cons _ 81 mSEA _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamSEA PUnit.unit _ tyT81.2 (fun h => absurd h (by decide)) typedFam81
    (GroupMembersT.cons _ 82 mSeIntro _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorSeIntro PUnit.unit _ tyT82.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS82).2⟩) typedCtor82
    (GroupMembersT.cons _ 83 recSEA _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecSEA idxT83 _ tyT83.2 (fun h => absurd h (by decide)) typedRec83
    (.nil _))))
def wft84 : EnvWfT (envPre 84) :=
  wfTOfExtend (r := 83) (m := recSEA) (by decide) rfl
    (.group (envPre 81) 81 mSEA [(82, mSeIntro)] 83 recSEA _ wft81 rfl
      (fun c hc => by simp at hc; rcases hc with rfl <;> rfl) rfl mem81)
/- slots 84–87: family mFTE, recursor recFTE -/
kernel_rfl_theorem tyB84 : (sortTyAtC (envPre 84) mFTE.arity 96 [] mFTE.mtype).isSome = true
def tyT84 : Σ u, HasTyT (envPre 84) mFTE.arity [] mFTE.mtype (.sort u) :=
  (sortTyAtC (envPre 84) mFTE.arity 96 [] mFTE.mtype).get tyB84
kernel_rfl_theorem tyB85 : (sortTyAtC (envPre 85) mFteNil.arity 96 [] mFteNil.mtype).isSome = true
def tyT85 : Σ u, HasTyT (envPre 85) mFteNil.arity [] mFteNil.mtype (.sort u) :=
  (sortTyAtC (envPre 85) mFteNil.arity 96 [] mFteNil.mtype).get tyB85
kernel_rfl_theorem tyS85 : (sortTyAtC (extendEnv (envPre 84) 84 mFTE) mFteNil.arity 96 [] mFteNil.mtype).isSome = true
kernel_rfl_theorem tyB86 : (sortTyAtC (envPre 86) mFteCons.arity 96 [] mFteCons.mtype).isSome = true
def tyT86 : Σ u, HasTyT (envPre 86) mFteCons.arity [] mFteCons.mtype (.sort u) :=
  (sortTyAtC (envPre 86) mFteCons.arity 96 [] mFteCons.mtype).get tyB86
kernel_rfl_theorem tyS86 : (sortTyAtC (extendEnv (envPre 84) 84 mFTE) mFteCons.arity 96 [] mFteCons.mtype).isSome = true
kernel_rfl_theorem tyB87 : (sortTyAtC (envPre 87) recFTE.arity 96 [] recFTE.mtype).isSome = true
def tyT87 : Σ u, HasTyT (envPre 87) recFTE.arity [] recFTE.mtype (.sort u) :=
  (sortTyAtC (envPre 87) recFTE.arity 96 [] recFTE.mtype).get tyB87
def dFam84 := (admFamView? admFamFTE).get rfl
def dCtor85 := (admCtorViews? admCtorFteNil).get rfl
def dCtor86 := (admCtorViews? admCtorFteCons).get rfl
def dRec87 := (admRecData admRecFTE).get rfl
kernel_rfl_theorem famB84 : famTypedB (extendEnv (envPre 84) 84 mFTE) 96 dFam84 = true
kernel_rfl_theorem famB85 : famTypedB (envPre 85) 96 dCtor85.1 = true
kernel_rfl_theorem ctorB85 : ctorTypedB 96 dCtor85.2.2 = true
kernel_rfl_theorem famB86 : famTypedB (envPre 86) 96 dCtor86.1 = true
kernel_rfl_theorem ctorB86 : ctorTypedB 96 dCtor86.2.2 = true
kernel_rfl_theorem famB87 : famTypedB (envPre 87) 96 dRec87.1.family = true
kernel_rfl_theorem ctorB87 : ctorTypedAllB 96 dRec87.1 = true
kernel_rfl_theorem freshB87 : ((envPre 87).members 87).isNone = true
theorem classB87 : (match recFTE.mclass with | .recursorM => true | _ => false) = true := rfl
kernel_rfl_theorem mtB87 : Rcic.Declarative.exprClosedAt 0 recFTE.mtype = true
theorem famX87 : (extendEnv (envPre 87) 87 recFTE).members dRec87.1.family.ref = some dRec87.1.family.member := by
  rw [extendEnv_members_ne (by decide : dRec87.1.family.ref ≠ 87)]
  exact dRec87.1.family.present
kernel_rfl_theorem ixC87_0 : Rcic.Declarative.exprClosedAt 0 (dRec87.1.constructors[0]'(by decide)).mtype = true
kernel_rfl_theorem ixF87_0E : (dRec87.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (envPre 87) (dRec87.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR87_0E0 : constsMemberFuel (envPre 87) (dRec87.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec87.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR87_0E1 : constsMemberFuel (envPre 87) (dRec87.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec87.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri87_0E : (dRec87.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (envPre 87) (dRec87.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR87_0E0
    | 1 => ixR87_0E1
    | k+2 => absurd hk (by have : (dRec87.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF87_0X : (dRec87.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 87) 87 recFTE) (dRec87.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR87_0X0 : constsMemberFuel (extendEnv (envPre 87) 87 recFTE) (dRec87.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec87.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR87_0X1 : constsMemberFuel (extendEnv (envPre 87) 87 recFTE) (dRec87.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec87.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri87_0X : (dRec87.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 87) 87 recFTE) (dRec87.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR87_0X0
    | 1 => ixR87_0X1
    | k+2 => absurd hk (by have : (dRec87.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc87_0 : Rcic.Declarative.exprClosedAt (dRec87.1.family.parameters.length + 1 + dRec87.1.constructors.length + dRec87.1.family.indices.length + (dRec87.1.constructorViews ⟨0, by decide⟩).fields.length) (descriptorSchema dRec87.1 dRec87.2 ⟨0, by decide⟩) = true
theorem ctorChk87_0 : recCtorCheckB dRec87.1 dRec87.2 ⟨0, by decide⟩ = true :=
  recCtorCheckB_of ixC87_0 ixF87_0E ri87_0E ixF87_0X ri87_0X famX87 ixSc87_0
kernel_rfl_theorem ixC87_1 : Rcic.Declarative.exprClosedAt 0 (dRec87.1.constructors[1]'(by decide)).mtype = true
kernel_rfl_theorem ixF87_1E : (dRec87.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (envPre 87) (dRec87.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR87_1E0 : constsMemberFuel (envPre 87) (dRec87.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec87.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR87_1E1 : constsMemberFuel (envPre 87) (dRec87.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec87.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri87_1E : (dRec87.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (envPre 87) (dRec87.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR87_1E0
    | 1 => ixR87_1E1
    | k+2 => absurd hk (by have : (dRec87.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixF87_1X : (dRec87.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 87) 87 recFTE) (dRec87.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR87_1X0 : constsMemberFuel (extendEnv (envPre 87) 87 recFTE) (dRec87.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec87.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR87_1X1 : constsMemberFuel (extendEnv (envPre 87) 87 recFTE) (dRec87.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec87.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
theorem ri87_1X : (dRec87.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 87) 87 recFTE) (dRec87.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR87_1X0
    | 1 => ixR87_1X1
    | k+2 => absurd hk (by have : (dRec87.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 2 := rfl; omega)
kernel_rfl_theorem ixSc87_1 : Rcic.Declarative.exprClosedAt (dRec87.1.family.parameters.length + 1 + dRec87.1.constructors.length + dRec87.1.family.indices.length + (dRec87.1.constructorViews ⟨1, by decide⟩).fields.length) (descriptorSchema dRec87.1 dRec87.2 ⟨1, by decide⟩) = true
theorem ctorChk87_1 : recCtorCheckB dRec87.1 dRec87.2 ⟨1, by decide⟩ = true :=
  recCtorCheckB_of ixC87_1 ixF87_1E ri87_1E ixF87_1X ri87_1X famX87 ixSc87_1
theorem idxB87 : recIdxAdmittedTB dRec87.1 dRec87.2 = true :=
  recIdxAdmittedB_of freshB87 classB87 mtB87 fun ⟨i, hi⟩ =>
    match i with
    | 0 => ctorChk87_0
    | 1 => ctorChk87_1
    | k+2 => absurd hi (by have : dRec87.1.constructors.length = 2 := rfl; omega)
kernel_rfl_theorem iotaB87_0 : iotaEqB (a := dRec87.1) (h14 := dRec87.2) (synCheck (extendEnv (envPre 87) 87 recFTE) recFTE.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB87_1 : iotaEqB (a := dRec87.1) (h14 := dRec87.2) (synCheck (extendEnv (envPre 87) 87 recFTE) recFTE.arity) 1 (by decide) = true
def typedFam84 : IndGroupTypedT admFamFTE := famTypedT_of (fuel := 96) dFam84 famB84
def typedCtor85 : IndGroupTypedT admCtorFteNil :=
  ⟨famTypedT_of (fuel := 96) dCtor85.1 famB85, ctorTypedT_of (fuel := 96) ctorB85⟩
def typedCtor86 : IndGroupTypedT admCtorFteCons :=
  ⟨famTypedT_of (fuel := 96) dCtor86.1 famB86, ctorTypedT_of (fuel := 96) ctorB86⟩
theorem iotaAllB87 : finAllB dRec87.1.constructors.length
    (iotaEqB (a := dRec87.1) (h14 := dRec87.2) (synCheck (extendEnv (envPre 87) 87 recFTE) recFTE.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB87_0
    | 1 => iotaB87_1
    | k+2 => absurd hi (by have : dRec87.1.constructors.length = 2 := rfl; omega)
def iotaT87 : ∀ i, IotaEquationTypedT dRec87.1 i (dRec87.2.fuelAt i) (dRec87.2.shapesAt i) :=
  iotaEqsT_of iotaAllB87
def idxT87 : IdxAdmittedT admRecFTE := idxT_of admRecFTE idxB87
def typedRec87 : IndGroupTypedT admRecFTE :=
  ⟨famTypedT_of (fuel := 96) dRec87.1.family famB87,
   ctorTypedAll_of ctorB87,
   iotaT87⟩
def mem84 : GroupMembersT (extendEnv (envPre 84) 84 mFTE) (envPre 84)
    [(84, mFTE), (85, mFteNil), (86, mFteCons), (87, recFTE)] (extendEnv (envPre 87) 87 recFTE) :=
  (GroupMembersT.cons _ 84 mFTE _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamFTE PUnit.unit _ tyT84.2 (fun h => absurd h (by decide)) typedFam84
    (GroupMembersT.cons _ 85 mFteNil _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorFteNil PUnit.unit _ tyT85.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS85).2⟩) typedCtor85
    (GroupMembersT.cons _ 86 mFteCons _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorFteCons PUnit.unit _ tyT86.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS86).2⟩) typedCtor86
    (GroupMembersT.cons _ 87 recFTE _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecFTE idxT87 _ tyT87.2 (fun h => absurd h (by decide)) typedRec87
    (.nil _)))))
def wft88 : EnvWfT (envPre 88) :=
  wfTOfExtend (r := 87) (m := recFTE) (by decide) rfl
    (.group (envPre 84) 84 mFTE [(85, mFteNil), (86, mFteCons)] 87 recFTE _ wft84 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem84)

end Rcic.Scm.SrcG

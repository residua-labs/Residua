import rcic.ScmSrcGroupsEnvWfT9

/-! `EnvWfT` for srcEnvG slots in this file's range. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/- slots 88–91: family mNthB, recursor recNthB -/
kernel_rfl_theorem tyB88 : (sortTyAtC (envPre 88) mNthB.arity 96 [] mNthB.mtype).isSome = true
def tyT88 : Σ u, HasTyT (envPre 88) mNthB.arity [] mNthB.mtype (.sort u) :=
  (sortTyAtC (envPre 88) mNthB.arity 96 [] mNthB.mtype).get tyB88
kernel_rfl_theorem tyB89 : (sortTyAtC (envPre 89) mNthBHere.arity 96 [] mNthBHere.mtype).isSome = true
def tyT89 : Σ u, HasTyT (envPre 89) mNthBHere.arity [] mNthBHere.mtype (.sort u) :=
  (sortTyAtC (envPre 89) mNthBHere.arity 96 [] mNthBHere.mtype).get tyB89
kernel_rfl_theorem tyS89 : (sortTyAtC (extendEnv (envPre 88) 88 mNthB) mNthBHere.arity 96 [] mNthBHere.mtype).isSome = true
kernel_rfl_theorem tyB90 : (sortTyAtC (envPre 90) mNthBNext.arity 96 [] mNthBNext.mtype).isSome = true
def tyT90 : Σ u, HasTyT (envPre 90) mNthBNext.arity [] mNthBNext.mtype (.sort u) :=
  (sortTyAtC (envPre 90) mNthBNext.arity 96 [] mNthBNext.mtype).get tyB90
kernel_rfl_theorem tyS90 : (sortTyAtC (extendEnv (envPre 88) 88 mNthB) mNthBNext.arity 96 [] mNthBNext.mtype).isSome = true
kernel_rfl_theorem tyB91 : (sortTyAtC (envPre 91) recNthB.arity 96 [] recNthB.mtype).isSome = true
def tyT91 : Σ u, HasTyT (envPre 91) recNthB.arity [] recNthB.mtype (.sort u) :=
  (sortTyAtC (envPre 91) recNthB.arity 96 [] recNthB.mtype).get tyB91
def dFam88 := (admFamView? admFamNthB).get rfl
def dCtor89 := (admCtorViews? admCtorNthBHere).get rfl
def dCtor90 := (admCtorViews? admCtorNthBNext).get rfl
def dRec91 := (admRecData admRecNthB).get rfl
kernel_rfl_theorem famB88 : famTypedB (extendEnv (envPre 88) 88 mNthB) 96 dFam88 = true
kernel_rfl_theorem famB89 : famTypedB (envPre 89) 96 dCtor89.1 = true
kernel_rfl_theorem ctorB89 : ctorTypedB 96 dCtor89.2.2 = true
kernel_rfl_theorem famB90 : famTypedB (envPre 90) 96 dCtor90.1 = true
kernel_rfl_theorem ctorB90 : ctorTypedB 96 dCtor90.2.2 = true
kernel_rfl_theorem famB91 : famTypedB (envPre 91) 96 dRec91.1.family = true
kernel_rfl_theorem ctorB91 : ctorTypedAllB 96 dRec91.1 = true
kernel_rfl_theorem freshB91 : ((envPre 91).members 91).isNone = true
theorem classB91 : (match recNthB.mclass with | .recursorM => true | _ => false) = true := rfl
kernel_rfl_theorem mtB91 : Rcic.Declarative.exprClosedAt 0 recNthB.mtype = true
theorem famX91 : (extendEnv (envPre 91) 91 recNthB).members dRec91.1.family.ref = some dRec91.1.family.member := by
  rw [extendEnv_members_ne (by decide : dRec91.1.family.ref ≠ 91)]
  exact dRec91.1.family.present
kernel_rfl_theorem ixC91_0 : Rcic.Declarative.exprClosedAt 0 (dRec91.1.constructors[0]'(by decide)).mtype = true
kernel_rfl_theorem ixF91_0E : (dRec91.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (envPre 91) (dRec91.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR91_0E0 : constsMemberFuel (envPre 91) (dRec91.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec91.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR91_0E1 : constsMemberFuel (envPre 91) (dRec91.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec91.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR91_0E2 : constsMemberFuel (envPre 91) (dRec91.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec91.1.constructorViews ⟨0, by decide⟩).resultIndices[2]'(by decide)) = true
theorem ri91_0E : (dRec91.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (envPre 91) (dRec91.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR91_0E0
    | 1 => ixR91_0E1
    | 2 => ixR91_0E2
    | k+3 => absurd hk (by have : (dRec91.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 3 := rfl; omega)
kernel_rfl_theorem ixF91_0X : (dRec91.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 91) 91 recNthB) (dRec91.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR91_0X0 : constsMemberFuel (extendEnv (envPre 91) 91 recNthB) (dRec91.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec91.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR91_0X1 : constsMemberFuel (extendEnv (envPre 91) 91 recNthB) (dRec91.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec91.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR91_0X2 : constsMemberFuel (extendEnv (envPre 91) 91 recNthB) (dRec91.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec91.1.constructorViews ⟨0, by decide⟩).resultIndices[2]'(by decide)) = true
theorem ri91_0X : (dRec91.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 91) 91 recNthB) (dRec91.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR91_0X0
    | 1 => ixR91_0X1
    | 2 => ixR91_0X2
    | k+3 => absurd hk (by have : (dRec91.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 3 := rfl; omega)
kernel_rfl_theorem ixSc91_0 : Rcic.Declarative.exprClosedAt (dRec91.1.family.parameters.length + 1 + dRec91.1.constructors.length + dRec91.1.family.indices.length + (dRec91.1.constructorViews ⟨0, by decide⟩).fields.length) (descriptorSchema dRec91.1 dRec91.2 ⟨0, by decide⟩) = true
theorem ctorChk91_0 : recCtorCheckB dRec91.1 dRec91.2 ⟨0, by decide⟩ = true :=
  recCtorCheckB_of ixC91_0 ixF91_0E ri91_0E ixF91_0X ri91_0X famX91 ixSc91_0
kernel_rfl_theorem ixC91_1 : Rcic.Declarative.exprClosedAt 0 (dRec91.1.constructors[1]'(by decide)).mtype = true
kernel_rfl_theorem ixF91_1E : (dRec91.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (envPre 91) (dRec91.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR91_1E0 : constsMemberFuel (envPre 91) (dRec91.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec91.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR91_1E1 : constsMemberFuel (envPre 91) (dRec91.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec91.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR91_1E2 : constsMemberFuel (envPre 91) (dRec91.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec91.1.constructorViews ⟨1, by decide⟩).resultIndices[2]'(by decide)) = true
theorem ri91_1E : (dRec91.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (envPre 91) (dRec91.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR91_1E0
    | 1 => ixR91_1E1
    | 2 => ixR91_1E2
    | k+3 => absurd hk (by have : (dRec91.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 3 := rfl; omega)
kernel_rfl_theorem ixF91_1X : (dRec91.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 91) 91 recNthB) (dRec91.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR91_1X0 : constsMemberFuel (extendEnv (envPre 91) 91 recNthB) (dRec91.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec91.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR91_1X1 : constsMemberFuel (extendEnv (envPre 91) 91 recNthB) (dRec91.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec91.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR91_1X2 : constsMemberFuel (extendEnv (envPre 91) 91 recNthB) (dRec91.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec91.1.constructorViews ⟨1, by decide⟩).resultIndices[2]'(by decide)) = true
theorem ri91_1X : (dRec91.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 91) 91 recNthB) (dRec91.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR91_1X0
    | 1 => ixR91_1X1
    | 2 => ixR91_1X2
    | k+3 => absurd hk (by have : (dRec91.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 3 := rfl; omega)
kernel_rfl_theorem ixSc91_1 : Rcic.Declarative.exprClosedAt (dRec91.1.family.parameters.length + 1 + dRec91.1.constructors.length + dRec91.1.family.indices.length + (dRec91.1.constructorViews ⟨1, by decide⟩).fields.length) (descriptorSchema dRec91.1 dRec91.2 ⟨1, by decide⟩) = true
theorem ctorChk91_1 : recCtorCheckB dRec91.1 dRec91.2 ⟨1, by decide⟩ = true :=
  recCtorCheckB_of ixC91_1 ixF91_1E ri91_1E ixF91_1X ri91_1X famX91 ixSc91_1
theorem idxB91 : recIdxAdmittedTB dRec91.1 dRec91.2 = true :=
  recIdxAdmittedB_of freshB91 classB91 mtB91 fun ⟨i, hi⟩ =>
    match i with
    | 0 => ctorChk91_0
    | 1 => ctorChk91_1
    | k+2 => absurd hi (by have : dRec91.1.constructors.length = 2 := rfl; omega)
kernel_rfl_theorem iotaB91_0 : iotaEqB (a := dRec91.1) (h14 := dRec91.2) (synCheck (extendEnv (envPre 91) 91 recNthB) recNthB.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB91_1 : iotaEqB (a := dRec91.1) (h14 := dRec91.2) (synCheck (extendEnv (envPre 91) 91 recNthB) recNthB.arity) 1 (by decide) = true
def typedFam88 : IndGroupTypedT admFamNthB := famTypedT_of (fuel := 96) dFam88 famB88
def typedCtor89 : IndGroupTypedT admCtorNthBHere :=
  ⟨famTypedT_of (fuel := 96) dCtor89.1 famB89, ctorTypedT_of (fuel := 96) ctorB89⟩
def typedCtor90 : IndGroupTypedT admCtorNthBNext :=
  ⟨famTypedT_of (fuel := 96) dCtor90.1 famB90, ctorTypedT_of (fuel := 96) ctorB90⟩
theorem iotaAllB91 : finAllB dRec91.1.constructors.length
    (iotaEqB (a := dRec91.1) (h14 := dRec91.2) (synCheck (extendEnv (envPre 91) 91 recNthB) recNthB.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB91_0
    | 1 => iotaB91_1
    | k+2 => absurd hi (by have : dRec91.1.constructors.length = 2 := rfl; omega)
def iotaT91 : ∀ i, IotaEquationTypedT dRec91.1 i (dRec91.2.fuelAt i) (dRec91.2.shapesAt i) :=
  iotaEqsT_of iotaAllB91
def idxT91 : IdxAdmittedT admRecNthB := idxT_of admRecNthB idxB91
def typedRec91 : IndGroupTypedT admRecNthB :=
  ⟨famTypedT_of (fuel := 96) dRec91.1.family famB91,
   ctorTypedAll_of ctorB91,
   iotaT91⟩
def mem88 : GroupMembersT (extendEnv (envPre 88) 88 mNthB) (envPre 88)
    [(88, mNthB), (89, mNthBHere), (90, mNthBNext), (91, recNthB)] (extendEnv (envPre 91) 91 recNthB) :=
  (GroupMembersT.cons _ 88 mNthB _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamNthB PUnit.unit _ tyT88.2 (fun h => absurd h (by decide)) typedFam88
    (GroupMembersT.cons _ 89 mNthBHere _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorNthBHere PUnit.unit _ tyT89.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS89).2⟩) typedCtor89
    (GroupMembersT.cons _ 90 mNthBNext _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorNthBNext PUnit.unit _ tyT90.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS90).2⟩) typedCtor90
    (GroupMembersT.cons _ 91 recNthB _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecNthB idxT91 _ tyT91.2 (fun h => absurd h (by decide)) typedRec91
    (.nil _)))))
def wft92 : EnvWfT (envPre 92) :=
  wfTOfExtend (r := 91) (m := recNthB) (by decide) rfl
    (.group (envPre 88) 88 mNthB [(89, mNthBHere), (90, mNthBNext)] 91 recNthB _ wft88 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem88)
/- slots 92–95: family mNthF, recursor recNthF -/
kernel_rfl_theorem tyB92 : (sortTyAtC (envPre 92) mNthF.arity 96 [] mNthF.mtype).isSome = true
def tyT92 : Σ u, HasTyT (envPre 92) mNthF.arity [] mNthF.mtype (.sort u) :=
  (sortTyAtC (envPre 92) mNthF.arity 96 [] mNthF.mtype).get tyB92
kernel_rfl_theorem tyB93 : (sortTyAtC (envPre 93) mNthFHere.arity 96 [] mNthFHere.mtype).isSome = true
def tyT93 : Σ u, HasTyT (envPre 93) mNthFHere.arity [] mNthFHere.mtype (.sort u) :=
  (sortTyAtC (envPre 93) mNthFHere.arity 96 [] mNthFHere.mtype).get tyB93
kernel_rfl_theorem tyS93 : (sortTyAtC (extendEnv (envPre 92) 92 mNthF) mNthFHere.arity 96 [] mNthFHere.mtype).isSome = true
kernel_rfl_theorem tyB94 : (sortTyAtC (envPre 94) mNthFNext.arity 96 [] mNthFNext.mtype).isSome = true
def tyT94 : Σ u, HasTyT (envPre 94) mNthFNext.arity [] mNthFNext.mtype (.sort u) :=
  (sortTyAtC (envPre 94) mNthFNext.arity 96 [] mNthFNext.mtype).get tyB94
kernel_rfl_theorem tyS94 : (sortTyAtC (extendEnv (envPre 92) 92 mNthF) mNthFNext.arity 96 [] mNthFNext.mtype).isSome = true
kernel_rfl_theorem tyB95 : (sortTyAtC (envPre 95) recNthF.arity 96 [] recNthF.mtype).isSome = true
def tyT95 : Σ u, HasTyT (envPre 95) recNthF.arity [] recNthF.mtype (.sort u) :=
  (sortTyAtC (envPre 95) recNthF.arity 96 [] recNthF.mtype).get tyB95
def dFam92 := (admFamView? admFamNthF).get rfl
def dCtor93 := (admCtorViews? admCtorNthFHere).get rfl
def dCtor94 := (admCtorViews? admCtorNthFNext).get rfl
def dRec95 := (admRecData admRecNthF).get rfl
kernel_rfl_theorem famB92 : famTypedB (extendEnv (envPre 92) 92 mNthF) 96 dFam92 = true
kernel_rfl_theorem famB93 : famTypedB (envPre 93) 96 dCtor93.1 = true
kernel_rfl_theorem ctorB93 : ctorTypedB 96 dCtor93.2.2 = true
kernel_rfl_theorem famB94 : famTypedB (envPre 94) 96 dCtor94.1 = true
kernel_rfl_theorem ctorB94 : ctorTypedB 96 dCtor94.2.2 = true
kernel_rfl_theorem famB95 : famTypedB (envPre 95) 96 dRec95.1.family = true
kernel_rfl_theorem ctorB95 : ctorTypedAllB 96 dRec95.1 = true
kernel_rfl_theorem freshB95 : ((envPre 95).members 95).isNone = true
theorem classB95 : (match recNthF.mclass with | .recursorM => true | _ => false) = true := rfl
kernel_rfl_theorem mtB95 : Rcic.Declarative.exprClosedAt 0 recNthF.mtype = true
theorem famX95 : (extendEnv (envPre 95) 95 recNthF).members dRec95.1.family.ref = some dRec95.1.family.member := by
  rw [extendEnv_members_ne (by decide : dRec95.1.family.ref ≠ 95)]
  exact dRec95.1.family.present
kernel_rfl_theorem ixC95_0 : Rcic.Declarative.exprClosedAt 0 (dRec95.1.constructors[0]'(by decide)).mtype = true
kernel_rfl_theorem ixF95_0E : (dRec95.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (envPre 95) (dRec95.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR95_0E0 : constsMemberFuel (envPre 95) (dRec95.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec95.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR95_0E1 : constsMemberFuel (envPre 95) (dRec95.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec95.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR95_0E2 : constsMemberFuel (envPre 95) (dRec95.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec95.1.constructorViews ⟨0, by decide⟩).resultIndices[2]'(by decide)) = true
kernel_rfl_theorem ixR95_0E3 : constsMemberFuel (envPre 95) (dRec95.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec95.1.constructorViews ⟨0, by decide⟩).resultIndices[3]'(by decide)) = true
theorem ri95_0E : (dRec95.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (envPre 95) (dRec95.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR95_0E0
    | 1 => ixR95_0E1
    | 2 => ixR95_0E2
    | 3 => ixR95_0E3
    | k+4 => absurd hk (by have : (dRec95.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 4 := rfl; omega)
kernel_rfl_theorem ixF95_0X : (dRec95.1.constructorViews ⟨0, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 95) 95 recNthF) (dRec95.2.fuelAt ⟨0, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR95_0X0 : constsMemberFuel (extendEnv (envPre 95) 95 recNthF) (dRec95.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec95.1.constructorViews ⟨0, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR95_0X1 : constsMemberFuel (extendEnv (envPre 95) 95 recNthF) (dRec95.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec95.1.constructorViews ⟨0, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR95_0X2 : constsMemberFuel (extendEnv (envPre 95) 95 recNthF) (dRec95.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec95.1.constructorViews ⟨0, by decide⟩).resultIndices[2]'(by decide)) = true
kernel_rfl_theorem ixR95_0X3 : constsMemberFuel (extendEnv (envPre 95) 95 recNthF) (dRec95.2.fuelAt ⟨0, by decide⟩ + 1) ((dRec95.1.constructorViews ⟨0, by decide⟩).resultIndices[3]'(by decide)) = true
theorem ri95_0X : (dRec95.1.constructorViews ⟨0, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 95) 95 recNthF) (dRec95.2.fuelAt ⟨0, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR95_0X0
    | 1 => ixR95_0X1
    | 2 => ixR95_0X2
    | 3 => ixR95_0X3
    | k+4 => absurd hk (by have : (dRec95.1.constructorViews ⟨0, by decide⟩).resultIndices.length = 4 := rfl; omega)
kernel_rfl_theorem ixSc95_0 : Rcic.Declarative.exprClosedAt (dRec95.1.family.parameters.length + 1 + dRec95.1.constructors.length + dRec95.1.family.indices.length + (dRec95.1.constructorViews ⟨0, by decide⟩).fields.length) (descriptorSchema dRec95.1 dRec95.2 ⟨0, by decide⟩) = true
theorem ctorChk95_0 : recCtorCheckB dRec95.1 dRec95.2 ⟨0, by decide⟩ = true :=
  recCtorCheckB_of ixC95_0 ixF95_0E ri95_0E ixF95_0X ri95_0X famX95 ixSc95_0
kernel_rfl_theorem ixC95_1 : Rcic.Declarative.exprClosedAt 0 (dRec95.1.constructors[1]'(by decide)).mtype = true
kernel_rfl_theorem ixF95_1E : (dRec95.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (envPre 95) (dRec95.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR95_1E0 : constsMemberFuel (envPre 95) (dRec95.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec95.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR95_1E1 : constsMemberFuel (envPre 95) (dRec95.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec95.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR95_1E2 : constsMemberFuel (envPre 95) (dRec95.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec95.1.constructorViews ⟨1, by decide⟩).resultIndices[2]'(by decide)) = true
kernel_rfl_theorem ixR95_1E3 : constsMemberFuel (envPre 95) (dRec95.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec95.1.constructorViews ⟨1, by decide⟩).resultIndices[3]'(by decide)) = true
theorem ri95_1E : (dRec95.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (envPre 95) (dRec95.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR95_1E0
    | 1 => ixR95_1E1
    | 2 => ixR95_1E2
    | 3 => ixR95_1E3
    | k+4 => absurd hk (by have : (dRec95.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 4 := rfl; omega)
kernel_rfl_theorem ixF95_1X : (dRec95.1.constructorViews ⟨1, by decide⟩).fields.all (constsMemberFuel (extendEnv (envPre 95) 95 recNthF) (dRec95.2.fuelAt ⟨1, by decide⟩ + 1)) = true
kernel_rfl_theorem ixR95_1X0 : constsMemberFuel (extendEnv (envPre 95) 95 recNthF) (dRec95.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec95.1.constructorViews ⟨1, by decide⟩).resultIndices[0]'(by decide)) = true
kernel_rfl_theorem ixR95_1X1 : constsMemberFuel (extendEnv (envPre 95) 95 recNthF) (dRec95.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec95.1.constructorViews ⟨1, by decide⟩).resultIndices[1]'(by decide)) = true
kernel_rfl_theorem ixR95_1X2 : constsMemberFuel (extendEnv (envPre 95) 95 recNthF) (dRec95.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec95.1.constructorViews ⟨1, by decide⟩).resultIndices[2]'(by decide)) = true
kernel_rfl_theorem ixR95_1X3 : constsMemberFuel (extendEnv (envPre 95) 95 recNthF) (dRec95.2.fuelAt ⟨1, by decide⟩ + 1) ((dRec95.1.constructorViews ⟨1, by decide⟩).resultIndices[3]'(by decide)) = true
theorem ri95_1X : (dRec95.1.constructorViews ⟨1, by decide⟩).resultIndices.all (constsMemberFuel (extendEnv (envPre 95) 95 recNthF) (dRec95.2.fuelAt ⟨1, by decide⟩ + 1)) = true :=
  allB_of_each fun ⟨k, hk⟩ =>
    match k with
    | 0 => ixR95_1X0
    | 1 => ixR95_1X1
    | 2 => ixR95_1X2
    | 3 => ixR95_1X3
    | k+4 => absurd hk (by have : (dRec95.1.constructorViews ⟨1, by decide⟩).resultIndices.length = 4 := rfl; omega)
kernel_rfl_theorem ixSc95_1 : Rcic.Declarative.exprClosedAt (dRec95.1.family.parameters.length + 1 + dRec95.1.constructors.length + dRec95.1.family.indices.length + (dRec95.1.constructorViews ⟨1, by decide⟩).fields.length) (descriptorSchema dRec95.1 dRec95.2 ⟨1, by decide⟩) = true
theorem ctorChk95_1 : recCtorCheckB dRec95.1 dRec95.2 ⟨1, by decide⟩ = true :=
  recCtorCheckB_of ixC95_1 ixF95_1E ri95_1E ixF95_1X ri95_1X famX95 ixSc95_1
theorem idxB95 : recIdxAdmittedTB dRec95.1 dRec95.2 = true :=
  recIdxAdmittedB_of freshB95 classB95 mtB95 fun ⟨i, hi⟩ =>
    match i with
    | 0 => ctorChk95_0
    | 1 => ctorChk95_1
    | k+2 => absurd hi (by have : dRec95.1.constructors.length = 2 := rfl; omega)
kernel_rfl_theorem iotaB95_0 : iotaEqB (a := dRec95.1) (h14 := dRec95.2) (synCheck (extendEnv (envPre 95) 95 recNthF) recNthF.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB95_1 : iotaEqB (a := dRec95.1) (h14 := dRec95.2) (synCheck (extendEnv (envPre 95) 95 recNthF) recNthF.arity) 1 (by decide) = true
def typedFam92 : IndGroupTypedT admFamNthF := famTypedT_of (fuel := 96) dFam92 famB92
def typedCtor93 : IndGroupTypedT admCtorNthFHere :=
  ⟨famTypedT_of (fuel := 96) dCtor93.1 famB93, ctorTypedT_of (fuel := 96) ctorB93⟩
def typedCtor94 : IndGroupTypedT admCtorNthFNext :=
  ⟨famTypedT_of (fuel := 96) dCtor94.1 famB94, ctorTypedT_of (fuel := 96) ctorB94⟩
theorem iotaAllB95 : finAllB dRec95.1.constructors.length
    (iotaEqB (a := dRec95.1) (h14 := dRec95.2) (synCheck (extendEnv (envPre 95) 95 recNthF) recNthF.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB95_0
    | 1 => iotaB95_1
    | k+2 => absurd hi (by have : dRec95.1.constructors.length = 2 := rfl; omega)
def iotaT95 : ∀ i, IotaEquationTypedT dRec95.1 i (dRec95.2.fuelAt i) (dRec95.2.shapesAt i) :=
  iotaEqsT_of iotaAllB95
def idxT95 : IdxAdmittedT admRecNthF := idxT_of admRecNthF idxB95
def typedRec95 : IndGroupTypedT admRecNthF :=
  ⟨famTypedT_of (fuel := 96) dRec95.1.family famB95,
   ctorTypedAll_of ctorB95,
   iotaT95⟩
def mem92 : GroupMembersT (extendEnv (envPre 92) 92 mNthF) (envPre 92)
    [(92, mNthF), (93, mNthFHere), (94, mNthFNext), (95, recNthF)] (extendEnv (envPre 95) 95 recNthF) :=
  (GroupMembersT.cons _ 92 mNthF _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamNthF PUnit.unit _ tyT92.2 (fun h => absurd h (by decide)) typedFam92
    (GroupMembersT.cons _ 93 mNthFHere _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorNthFHere PUnit.unit _ tyT93.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS93).2⟩) typedCtor93
    (GroupMembersT.cons _ 94 mNthFNext _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorNthFNext PUnit.unit _ tyT94.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS94).2⟩) typedCtor94
    (GroupMembersT.cons _ 95 recNthF _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecNthF idxT95 _ tyT95.2 (fun h => absurd h (by decide)) typedRec95
    (.nil _)))))
def wft96 : EnvWfT (envPre 96) :=
  wfTOfExtend (r := 95) (m := recNthF) (by decide) rfl
    (.group (envPre 92) 92 mNthF [(93, mNthFHere), (94, mNthFNext)] 95 recNthF _ wft92 rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem92)

end Rcic.Scm.SrcG

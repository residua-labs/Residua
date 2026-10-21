import rcic.ScmSrcGroupsEnvWfTAux

/-! `EnvWfT` for srcEnvG slots in this file's range. -/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/- slots 0–3: family mN, recursor recN -/
kernel_rfl_theorem tyB0 : (sortTyAtC (envPre 0) mN.arity 96 [] mN.mtype).isSome = true
def tyT0 : Σ u, HasTyT (envPre 0) mN.arity [] mN.mtype (.sort u) :=
  (sortTyAtC (envPre 0) mN.arity 96 [] mN.mtype).get tyB0
kernel_rfl_theorem tyB1 : (sortTyAtC (envPre 1) mZero.arity 96 [] mZero.mtype).isSome = true
def tyT1 : Σ u, HasTyT (envPre 1) mZero.arity [] mZero.mtype (.sort u) :=
  (sortTyAtC (envPre 1) mZero.arity 96 [] mZero.mtype).get tyB1
kernel_rfl_theorem tyS1 : (sortTyAtC (extendEnv (envPre 0) 0 mN) mZero.arity 96 [] mZero.mtype).isSome = true
kernel_rfl_theorem tyB2 : (sortTyAtC (envPre 2) mSucc.arity 96 [] mSucc.mtype).isSome = true
def tyT2 : Σ u, HasTyT (envPre 2) mSucc.arity [] mSucc.mtype (.sort u) :=
  (sortTyAtC (envPre 2) mSucc.arity 96 [] mSucc.mtype).get tyB2
kernel_rfl_theorem tyS2 : (sortTyAtC (extendEnv (envPre 0) 0 mN) mSucc.arity 96 [] mSucc.mtype).isSome = true
kernel_rfl_theorem tyB3 : (sortTyAtC (envPre 3) recN.arity 96 [] recN.mtype).isSome = true
def tyT3 : Σ u, HasTyT (envPre 3) recN.arity [] recN.mtype (.sort u) :=
  (sortTyAtC (envPre 3) recN.arity 96 [] recN.mtype).get tyB3
def dFam0 := (admFamView? admFamN).get rfl
def dCtor1 := (admCtorViews? admCtorZero).get rfl
def dCtor2 := (admCtorViews? admCtorSucc).get rfl
def dRec3 := (admRecData admRecN).get rfl
kernel_rfl_theorem famB0 : famTypedB (extendEnv (envPre 0) 0 mN) 96 dFam0 = true
kernel_rfl_theorem famB1 : famTypedB (envPre 1) 96 dCtor1.1 = true
kernel_rfl_theorem ctorB1 : ctorTypedB 96 dCtor1.2.2 = true
kernel_rfl_theorem famB2 : famTypedB (envPre 2) 96 dCtor2.1 = true
kernel_rfl_theorem ctorB2 : ctorTypedB 96 dCtor2.2.2 = true
kernel_rfl_theorem famB3 : famTypedB (envPre 3) 96 dRec3.1.family = true
kernel_rfl_theorem ctorB3 : ctorTypedAllB 96 dRec3.1 = true
kernel_rfl_theorem idxB3 : recIdxAdmittedTB dRec3.1 dRec3.2 = true
kernel_rfl_theorem iotaB3_0 : iotaEqB (a := dRec3.1) (h14 := dRec3.2) (synCheck (extendEnv (envPre 3) 3 recN) recN.arity) 0 (by decide) = true
kernel_rfl_theorem iotaB3_1 : iotaEqB (a := dRec3.1) (h14 := dRec3.2) (synCheck (extendEnv (envPre 3) 3 recN) recN.arity) 1 (by decide) = true
def typedFam0 : IndGroupTypedT admFamN := famTypedT_of (fuel := 96) dFam0 famB0
def typedCtor1 : IndGroupTypedT admCtorZero :=
  ⟨famTypedT_of (fuel := 96) dCtor1.1 famB1, ctorTypedT_of (fuel := 96) ctorB1⟩
def typedCtor2 : IndGroupTypedT admCtorSucc :=
  ⟨famTypedT_of (fuel := 96) dCtor2.1 famB2, ctorTypedT_of (fuel := 96) ctorB2⟩
theorem iotaAllB3 : finAllB dRec3.1.constructors.length
    (iotaEqB (a := dRec3.1) (h14 := dRec3.2) (synCheck (extendEnv (envPre 3) 3 recN) recN.arity)) = true :=
  finAllB_of_each fun ⟨i, hi⟩ =>
    match i with
    | 0 => iotaB3_0
    | 1 => iotaB3_1
    | k+2 => absurd hi (by have : dRec3.1.constructors.length = 2 := rfl; omega)
def iotaT3 : ∀ i, IotaEquationTypedT dRec3.1 i (dRec3.2.fuelAt i) (dRec3.2.shapesAt i) :=
  iotaEqsT_of iotaAllB3
def idxT3 : IdxAdmittedT admRecN := idxT_of admRecN idxB3
def typedRec3 : IndGroupTypedT admRecN :=
  ⟨famTypedT_of (fuel := 96) dRec3.1.family famB3,
   ctorTypedAll_of ctorB3,
   iotaT3⟩
def mem0 : GroupMembersT (extendEnv (envPre 0) 0 mN) (envPre 0)
    [(0, mN), (1, mZero), (2, mSucc), (3, recN)] (extendEnv (envPre 3) 3 recN) :=
  (GroupMembersT.cons _ 0 mN _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    admFamN PUnit.unit _ tyT0.2 (fun h => absurd h (by decide)) typedFam0
    (GroupMembersT.cons _ 1 mZero _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorZero PUnit.unit _ tyT1.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS1).2⟩) typedCtor1
    (GroupMembersT.cons _ 2 mSucc _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admCtorSucc PUnit.unit _ tyT2.2 (fun _ => ⟨((sortTyAtC _ _ _ _ _).get tyS2).2⟩) typedCtor2
    (GroupMembersT.cons _ 3 recN _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
    admRecN idxT3 _ tyT3.2 (fun h => absurd h (by decide)) typedRec3
    (.nil _)))))
def wft4 : EnvWfT (envPre 4) :=
  wfTOfExtend (r := 3) (m := recN) (by decide) rfl
    (.group (envPre 0) 0 mN [(1, mZero), (2, mSucc)] 3 recN _ .empty rfl
      (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl mem0)

end Rcic.Scm.SrcG

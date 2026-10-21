import rcic.RcicPiSourceOriginCalls
import rcic.RcicParRedTSubst

/-!
A-1: original-answer transport and exact same/mixed-substitution outputs.
The answer is an input from the original request; no global U is supplied.
All judgments and prior producers are unchanged. closure_claim = 0.
-/

namespace Rcic.Declarative.F8OriginSubst
open F8PiSourceOrigin
variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
variable {a b A T P Q N N' : Expr Nat}

/-- Actual original typing, transported once; no new uniqueness request. -/
def substTy0 (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hv : HasTyT E n Γ N A) (ht : HasTyT E n (.assumption A :: Γ) a T) :
    HasTyT E n Γ (instantiate0 N a) (instantiate0 N T) := by
  have out := hasTyT_substS hcl hinst N A (j := 0) ht (by simp)
    (by simpa only [lift_zero] using hv)
  simpa only [lift_zero] using out

/-- The answer is obtained before substitution and transported as data. -/
def substChain0 (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hv : HasTyT E n Γ N A) (answer : TyConvT E n (.assumption A :: Γ) T P) :
    TyConvT E n Γ (instantiate0 N T) (instantiate0 N P) := by
  have out := tyConvT_substS hcl hinst N A (j := 0) answer (by simp)
    (by simpa only [lift_zero] using hv)
  simpa only [lift_zero] using out

/-- The real proof constructor after SAME substitution of all six fields.
This is a producer for a specified root, not an implementation of general D. -/
def proof_root_subst0 (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hP : HasTyT E n (.assumption A :: Γ) P (.sort .zero))
    (hQ : HasTyT E n (.assumption A :: Γ) Q (.sort .zero))
    (hp : HasTyT E n (.assumption A :: Γ) a P)
    (hq : HasTyT E n (.assumption A :: Γ) b Q)
    (ha : HasTyT E n (.assumption A :: Γ) a T)
    (hb : HasTyT E n (.assumption A :: Γ) b T)
    (hv : HasTyT E n Γ N A) :
    ParRedT (PEqLeafT E n) E n Γ (instantiate0 N a) (instantiate0 N b)
      (instantiate0 N T) :=
  .peq _ _ _ _
    ⟨.proof _ _ _ _ _ (substTy0 hcl hinst hv hP) (substTy0 hcl hinst hv hQ)
       (substTy0 hcl hinst hv hp) (substTy0 hcl hinst hv hq),
     substTy0 hcl hinst hv ha, substTy0 hcl hinst hv hb⟩

/-- Attached to the EXACT root above, retaining the transported original hp.
The only answer input is the original, pre-substitution type chain. -/
def proof_root_subst0_answer (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hP : HasTyT E n (.assumption A :: Γ) P (.sort .zero))
    (hQ : HasTyT E n (.assumption A :: Γ) Q (.sort .zero))
    (hp : HasTyT E n (.assumption A :: Γ) a P)
    (hq : HasTyT E n (.assumption A :: Γ) b Q)
    (ha : HasTyT E n (.assumption A :: Γ) a T)
    (hb : HasTyT E n (.assumption A :: Γ) b T)
    (hv : HasTyT E n Γ N A) (answer : TyConvT E n (.assumption A :: Γ) T P) :
    AnsweredOrigin (proof_root_subst0 hcl hinst hP hQ hp hq ha hb hv) :=
  ⟨.proof (substTy0 hcl hinst hv hP) (substTy0 hcl hinst hv hQ)
      (substTy0 hcl hinst hv hp) (substTy0 hcl hinst hv hq)
      (substTy0 hcl hinst hv ha) (substTy0 hcl hinst hv hb),
    substChain0 hcl hinst hv answer⟩

/-- Caller-facing same-substitution data, with the exact-output certificate. -/
def subst_proof_root_answered (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hP : HasTyT E n (.assumption A :: Γ) P (.sort .zero))
    (hQ : HasTyT E n (.assumption A :: Γ) Q (.sort .zero))
    (hp : HasTyT E n (.assumption A :: Γ) a P)
    (hq : HasTyT E n (.assumption A :: Γ) b Q)
    (ha : HasTyT E n (.assumption A :: Γ) a T)
    (hb : HasTyT E n (.assumption A :: Γ) b T)
    (hv : HasTyT E n Γ N A) (answer : TyConvT E n (.assumption A :: Γ) T P) :
    Σ' h : ParRedT (PEqLeafT E n) E n Γ (instantiate0 N a) (instantiate0 N b)
      (instantiate0 N T), AnsweredOrigin h :=
  ⟨proof_root_subst0 hcl hinst hP hQ hp hq ha hb hv,
    proof_root_subst0_answer hcl hinst hP hQ hp hq ha hb hv answer⟩

/-- MIXED substitution: the actual argument ConvT pays the index-alignment seam.
No raw PEqT or evaluator reduction is accepted in its place. -/
def mixed_subst_answered (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {u w : Level} (hA : HasTyT E n Γ A (.sort u))
    (hT : HasTyT E n (.assumption A :: Γ) T (.sort w))
    (hP : HasTyT E n (.assumption A :: Γ) P (.sort .zero))
    (ha : HasTyT E n (.assumption A :: Γ) a T)
    (hb : HasTyT E n (.assumption A :: Γ) b T)
    (hv : HasTyT E n Γ N A) (hv' : HasTyT E n Γ N' A)
    (hNN : ConvT E n Γ N N' A)
    (answer : TyConvT E n (.assumption A :: Γ) T P) :
    Σ' h : ParRedT (PEqLeafT E n) E n Γ (instantiate0 N a) (instantiate0 N' b)
      (instantiate0 N T), AnsweredOrigin h ×'
        ConvT E n Γ (instantiate0 N a) (instantiate0 N' b) (instantiate0 N T) :=
  let cidx := convT_inst0_pair_sort hA hT hNN hv hv'
  let left := substTy0 hcl hinst hv ha
  let right := HasTyT.conv _ _ _ _ w (substTy0 hcl hinst hv' hb)
    (.symm _ _ _ _ cidx)
  let hPN := substTy0 hcl hinst hv hP
  let cTP := substChain0 hcl hinst hv answer
  let data := peqLeafT_reconcile_propIndex hPN cTP left right
  ⟨.peq _ _ _ _ data.1,
    generated_leaf_origin_answer hPN cTP left right, data.2⟩

end Rcic.Declarative.F8OriginSubst

import rcic.RcicAnnLR3EqHead
import rcic.RcicAnnLR3HeadSubstBoundary

/-!
# Variance of positive normality under typed substitution

The LR3 normality predicate is positive.  This does not make it stable
under arbitrary typed substitutions: an assumption can be replaced by a
typed beta redex.  All the witnesses below use the admitted Eq fixture
and the actual contextual LR3 head relation.

The second witness records the independent index issue.  Two distinct
neutral variables of type Prop can be identified by a typed substitution.
Consequently a distinct-variable apartness certificate cannot be required
to persist under every typed substitution.  No separation or completeness
claim for a new apartness relation is made here.

These are qualifications on possible transport laws.  They do not refute
a semantic recursor clause or supply an Eq semantic environment.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3NormalSubstBoundary

open Rcic.Declarative EqLargeFixture LR3

abbrev closedProof : ExprA := reflAt parameter
abbrev proofRedex : ExprA := LR3HeadSubstBoundary.closedMajor
abbrev redexSubst : SubstA := LR3HeadSubstBoundary.closeSubstitution

def closedProofTyped : HasTyA env (iotaIfaceA env) 0 [] closedProof domain :=
  reflTyped .nil parameterTyped

def proofRedexTyped : HasTyA env (iotaIfaceA env) 0 [] proofRedex domain :=
  LR3HeadBoundary.betaMajorTyped .nil closedProofTyped

def redexSubstTyped : SubstTyA env (iotaIfaceA env) 0 [] redexSubst context :=
  LR3HeadSubstBoundary.closingTyped

theorem assumptionNormal : NormalA3 env (iotaIfaceA env) 0 context (.bvar 0) :=
  .neutral (.bvar 0 rfl)

theorem substitutedAssumptionHead : HeadA3 env (iotaIfaceA env) 0 []
    (substA redexSubst (.bvar 0)) closedProof (substA redexSubst domain) :=
  .primitive _ _ _ (.beta domain .zero (.bvar 0) closedProof)
    (.nonConstHead (.lam domain .zero (.bvar 0)))
    ⟨LR3HeadBoundary.betaMajorStep .nil closedProofTyped⟩

theorem substitutedAssumptionNotNormal :
    ¬ NormalA3 env (iotaIfaceA env) 0 [] (substA redexSubst (.bvar 0)) :=
  fun hn => normalA3_no_head hn substitutedAssumptionHead

/-- The strong, raw substitution law is stated explicitly so its
counterexample cannot be confused with a finite-chain or semantic law. -/
def RawNormalSubstA3 (H : HeadLayerA3 env (iotaIfaceA env) 0) : Prop :=
  ∀ (Γ Δ : LCtxA) (σ : SubstA) (a A : ExprA),
    CtxWfA env (iotaIfaceA env) 0 Γ →
    CtxWfA env (iotaIfaceA env) 0 Δ →
    SubstTyA env (iotaIfaceA env) 0 Δ σ Γ →
    HasTyA env (iotaIfaceA env) 0 Γ a A →
    H.normal Γ a → H.normal Δ (substA σ a)

theorem contextual_not_rawNormalSubstA3 :
    ¬ RawNormalSubstA3 (contextualHeadLayerA3 env (iotaIfaceA env) 0) := by
  intro h
  exact substitutedAssumptionNotNormal
    (h context [] redexSubst (.bvar 0) domain contextWf .nil redexSubstTyped
      majorTyped assumptionNormal)

theorem inhabited_normal_subst_boundary :
    eraseEnv env = eqEnvT ∧ Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 context) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 []) ∧
    Nonempty (SubstTyA env (iotaIfaceA env) 0 [] redexSubst context) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context (.bvar 0) domain) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] proofRedex domain) ∧
    NormalA3 env (iotaIfaceA env) 0 context (.bvar 0) ∧
    HeadA3 env (iotaIfaceA env) 0 []
      (substA redexSubst (.bvar 0)) closedProof (substA redexSubst domain) ∧
    ¬ NormalA3 env (iotaIfaceA env) 0 [] (substA redexSubst (.bvar 0)) :=
  ⟨erase_env, wf, ⟨contextWf⟩, ⟨.nil⟩, ⟨redexSubstTyped⟩, ⟨majorTyped⟩,
    ⟨proofRedexTyped⟩, assumptionNormal, substitutedAssumptionHead,
    substitutedAssumptionNotNormal⟩

abbrev indexContext : LCtxA :=
  [.assumption (.sort .zero), .assumption (.sort .zero)]

abbrev collapseIndices : SubstA :=
  SubstA.cons parameter (SubstA.cons parameter SubstA.id)

def indexContextWf : CtxWfA env (iotaIfaceA env) 0 indexContext :=
  .assumption (.assumption .nil (.sort [] .zero)) (.sort _ .zero)

def firstIndexTyped : HasTyA env (iotaIfaceA env) 0 indexContext
    (.bvar 0) (.sort .zero) :=
  .bvar _ 0 (.sort .zero) one rfl (.sort _ .zero)

def secondIndexTyped : HasTyA env (iotaIfaceA env) 0 indexContext
    (.bvar 1) (.sort .zero) :=
  .bvar _ 1 (.sort .zero) one rfl (.sort _ .zero)

def collapseIndicesTyped :
    SubstTyA env (iotaIfaceA env) 0 [] collapseIndices indexContext where
  ty := fun i A h => by
    cases i with
    | zero =>
        have hA : A = .sort .zero := Option.some.inj h.symm
        subst A
        exact parameterTyped
    | succ i =>
        cases i with
        | zero =>
            have hA : A = .sort .zero := Option.some.inj h.symm
            subst A
            exact parameterTyped
        | succ i => cases h
  val := fun i A v _ h => by
    cases i with
    | zero => cases h
    | succ i =>
        cases i with
        | zero => cases h
        | succ i => cases h

theorem firstIndexNormal : NormalA3 env (iotaIfaceA env) 0 indexContext (.bvar 0) :=
  .neutral (.bvar 0 rfl)

theorem secondIndexNormal : NormalA3 env (iotaIfaceA env) 0 indexContext (.bvar 1) :=
  .neutral (.bvar 1 rfl)

theorem sourceIndicesDiffer : (ExprA.bvar 0) ≠ .bvar 1 := by
  intro h
  cases h

theorem substitutedIndicesEqual :
    substA collapseIndices (.bvar 0) = substA collapseIndices (.bvar 1) := rfl

def substitutedIndicesConv : ConvA env (iotaIfaceA env) 0 []
    (substA collapseIndices (.bvar 0)) (substA collapseIndices (.bvar 1))
    (substA collapseIndices (.sort .zero)) :=
  .refl [] parameter (.sort .zero) parameterTyped

/-- The neutral-variable data and every typing/substitution premise are
inhabited.  Their substituted indices are definitionally identical. -/
theorem inhabited_index_collapse :
    eraseEnv env = eqEnvT ∧ Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 indexContext) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 []) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 indexContext (.bvar 0) (.sort .zero)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 indexContext (.bvar 1) (.sort .zero)) ∧
    NormalA3 env (iotaIfaceA env) 0 indexContext (.bvar 0) ∧
    NormalA3 env (iotaIfaceA env) 0 indexContext (.bvar 1) ∧
    (ExprA.bvar 0) ≠ .bvar 1 ∧
    Nonempty (SubstTyA env (iotaIfaceA env) 0 [] collapseIndices indexContext) ∧
    substA collapseIndices (.bvar 0) = substA collapseIndices (.bvar 1) ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 []
      (substA collapseIndices (.bvar 0)) (substA collapseIndices (.bvar 1))
      (substA collapseIndices (.sort .zero))) :=
  ⟨erase_env, wf, ⟨indexContextWf⟩, ⟨.nil⟩, ⟨firstIndexTyped⟩, ⟨secondIndexTyped⟩,
    firstIndexNormal, secondIndexNormal, sourceIndicesDiffer, ⟨collapseIndicesTyped⟩,
    substitutedIndicesEqual, ⟨substitutedIndicesConv⟩⟩

#print axioms closedProof
#print axioms proofRedex
#print axioms redexSubst
#print axioms closedProofTyped
#print axioms proofRedexTyped
#print axioms redexSubstTyped
#print axioms assumptionNormal
#print axioms substitutedAssumptionHead
#print axioms substitutedAssumptionNotNormal
#print axioms RawNormalSubstA3
#print axioms contextual_not_rawNormalSubstA3
#print axioms inhabited_normal_subst_boundary
#print axioms indexContext
#print axioms collapseIndices
#print axioms indexContextWf
#print axioms firstIndexTyped
#print axioms secondIndexTyped
#print axioms collapseIndicesTyped
#print axioms firstIndexNormal
#print axioms secondIndexNormal
#print axioms sourceIndicesDiffer
#print axioms substitutedIndicesEqual
#print axioms substitutedIndicesConv
#print axioms inhabited_index_collapse

end Rcic.Declarative.Ann.LR3NormalSubstBoundary

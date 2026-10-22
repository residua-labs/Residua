import rcic.RcicAnnLR3NormalSubstBoundary
import rcic.RcicAnnLR3SubstLaws

/-!
# Typed substitution need not preserve a directed head chain

The source context defines a proof variable by a closed beta redex.
Its zeta-local step is an actual `HeadA3` step.  A typed substitution
maps the variable to the beta redex's normal reduct; the substitution's
value field is the symmetric beta conversion.

After substitution the source is positive normal, while the substituted
right endpoint is the distinct beta redex.  Thus the general substitution
law for LR3 heads must be conversion-valued, or use stronger operational
substitution data.  The K-only exact law is unaffected.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3LetSubstBoundary

open Rcic.Declarative EqLargeFixture LR3 LR3NormalSubstBoundary

abbrev letContext : LCtxA := [.letBinding domain proofRedex]
abbrev normalSubst : SubstA := SubstA.cons closedProof SubstA.id

def letContextWf : CtxWfA env (iotaIfaceA env) 0 letContext :=
  .letBinding .nil (eqTyped .nil parameterTyped parameterTyped) proofRedexTyped

def sourceTyped : HasTyA env (iotaIfaceA env) 0 letContext (.bvar 0) domain :=
  .bvar _ 0 domain .zero rfl (eqTyped letContextWf parameterTyped parameterTyped)

def redexTypedInLet : HasTyA env (iotaIfaceA env) 0 letContext proofRedex domain :=
  LR3HeadBoundary.betaMajorTyped letContextWf (reflTyped letContextWf parameterTyped)

theorem localHead : HeadA3 env (iotaIfaceA env) 0 letContext
    (.bvar 0) proofRedex domain :=
  .primitive _ _ _ (.varE 0) (.nonApp (.bvar 0))
    ⟨.zetaLocal letContext 0 domain proofRedex rfl rfl redexTypedInLet⟩

def normalSubstTyped : SubstTyA env (iotaIfaceA env) 0 [] normalSubst letContext where
  ty := fun i A h => by
    cases i with
    | zero =>
        have hA : A = domain := Option.some.inj h.symm
        subst A
        exact closedProofTyped
    | succ i => cases h
  val := fun i A v hty hv => by
    cases i with
    | zero =>
        have hA : A = domain := Option.some.inj hty.symm
        have hv' : v = proofRedex := Option.some.inj hv.symm
        subst A
        subst v
        exact .symm [] proofRedex closedProof domain
          (tyHRedA_conv (LR3HeadBoundary.betaMajorStep .nil closedProofTyped))
    | succ i => cases hty

theorem closedProofNormal (Γ : LCtxA) : NormalA3 env (iotaIfaceA env) 0 Γ closedProof :=
  .neutral (.appIdle
    (.appIdle (.rigid 64 [] reflMember rfl rfl)
      (.noGroup rfl rfl) (by decide) (by decide) (by decide))
    (.noGroup rfl rfl) (by decide) (by decide) (by decide))

theorem substitutedSourceNormal :
    NormalA3 env (iotaIfaceA env) 0 [] (substA normalSubst (.bvar 0)) :=
  closedProofNormal []

theorem substitutedEndpointsDiffer :
    substA normalSubst (.bvar 0) ≠ substA normalSubst proofRedex := by decide

theorem substitutedNotHead (T : ExprA) :
    ¬ HeadA3 env (iotaIfaceA env) 0 []
      (substA normalSubst (.bvar 0)) (substA normalSubst proofRedex) T :=
  fun hs => normalA3_no_head substitutedSourceNormal hs

theorem substitutedNotChain (T : ExprA) :
    ¬ TyHRedStarA3 env (iotaIfaceA env) 0
      (contextualHeadLayerA3 env (iotaIfaceA env) 0) []
      (substA normalSubst (.bvar 0)) (substA normalSubst proofRedex) T := by
  rintro ⟨t⟩
  apply substitutedEndpointsDiffer
  exact (tmChainA3_trace t).eq_of_normal (by
    rintro b ⟨U, hs⟩
    exact normalA3_no_head substitutedSourceNormal hs)

/-- The positive replacement is supplied at exactly the same endpoints. -/
theorem substitutedConv : Nonempty (ConvA env (iotaIfaceA env) 0 []
    (substA normalSubst (.bvar 0)) (substA normalSubst proofRedex)
    (substA normalSubst domain)) :=
  contextualHeadLayerA3_substConv closed liftIface (iotaFnA_recHead env) substIface
    letContext [] normalSubst (.bvar 0) proofRedex domain letContextWf normalSubstTyped
    localHead

def RawHeadSubstA3 (H : HeadLayerA3 env (iotaIfaceA env) 0) : Prop :=
  ∀ (Γ Δ : LCtxA) (σ : SubstA) (a b T : ExprA),
    CtxWfA env (iotaIfaceA env) 0 Γ → CtxWfA env (iotaIfaceA env) 0 Δ →
    SubstTyA env (iotaIfaceA env) 0 Δ σ Γ → H.step Γ a b T →
    H.step Δ (substA σ a) (substA σ b) (substA σ T)

def DirectedHeadSubstA3 (H : HeadLayerA3 env (iotaIfaceA env) 0) : Prop :=
  ∀ (Γ Δ : LCtxA) (σ : SubstA) (a b T : ExprA),
    CtxWfA env (iotaIfaceA env) 0 Γ → CtxWfA env (iotaIfaceA env) 0 Δ →
    SubstTyA env (iotaIfaceA env) 0 Δ σ Γ → H.step Γ a b T →
    TyHRedStarA3 env (iotaIfaceA env) 0 H Δ
      (substA σ a) (substA σ b) (substA σ T)

theorem contextual_not_rawHeadSubstA3 :
    ¬ RawHeadSubstA3 (contextualHeadLayerA3 env (iotaIfaceA env) 0) := by
  intro h
  exact substitutedNotHead _
    (h letContext [] normalSubst (.bvar 0) proofRedex domain letContextWf .nil
      normalSubstTyped localHead)

theorem contextual_not_directedHeadSubstA3 :
    ¬ DirectedHeadSubstA3 (contextualHeadLayerA3 env (iotaIfaceA env) 0) := by
  intro h
  exact substitutedNotChain _
    (h letContext [] normalSubst (.bvar 0) proofRedex domain letContextWf .nil
      normalSubstTyped localHead)

theorem inhabited_directed_subst_boundary :
    eraseEnv env = eqEnvT ∧ Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 letContext) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 []) ∧
    Nonempty (SubstTyA env (iotaIfaceA env) 0 [] normalSubst letContext) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 letContext (.bvar 0) domain) ∧
    HeadA3 env (iotaIfaceA env) 0 letContext (.bvar 0) proofRedex domain ∧
    NormalA3 env (iotaIfaceA env) 0 [] (substA normalSubst (.bvar 0)) ∧
    substA normalSubst (.bvar 0) ≠ substA normalSubst proofRedex ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 []
      (substA normalSubst (.bvar 0)) (substA normalSubst proofRedex)
      (substA normalSubst domain)) ∧
    ¬ TyHRedStarA3 env (iotaIfaceA env) 0
      (contextualHeadLayerA3 env (iotaIfaceA env) 0) []
      (substA normalSubst (.bvar 0)) (substA normalSubst proofRedex)
      (substA normalSubst domain) :=
  ⟨erase_env, wf, ⟨letContextWf⟩, ⟨.nil⟩, ⟨normalSubstTyped⟩, ⟨sourceTyped⟩,
    localHead, substitutedSourceNormal, substitutedEndpointsDiffer, substitutedConv,
    substitutedNotChain _⟩

#print axioms letContext
#print axioms normalSubst
#print axioms letContextWf
#print axioms sourceTyped
#print axioms redexTypedInLet
#print axioms localHead
#print axioms normalSubstTyped
#print axioms closedProofNormal
#print axioms substitutedSourceNormal
#print axioms substitutedEndpointsDiffer
#print axioms substitutedNotHead
#print axioms substitutedNotChain
#print axioms substitutedConv
#print axioms RawHeadSubstA3
#print axioms DirectedHeadSubstA3
#print axioms contextual_not_rawHeadSubstA3
#print axioms contextual_not_directedHeadSubstA3
#print axioms inhabited_directed_subst_boundary

end Rcic.Declarative.Ann.LR3LetSubstBoundary

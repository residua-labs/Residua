import rcic.RcicAnnLR3EqHead
import rcic.RcicAnnLR3SubstLaws

/-!
# Typed substitution at sort carriers is conversion-valued

The source variable here is a type: `P : Sort 1`.  A typed substitution
maps it to `(fun X : Sort 1 => X) (Sort 0)`, whose beta reduct is `Sort 0`.
Thus restricting positive-normality transport to sort-typed subjects does
not restore raw substitution preservation.

The local-let variant defines `P` by that beta redex and substitutes its
normal reduct.  The substitution's value field is the landed
`idSort1_beta` conversion, reversed.  The original local step therefore
becomes a conversion from a normal type to a different expression, with
no directed head chain between the substituted endpoints.

Every context and typing premise is supplied in the admitted Eq
environment.  These are D2 contract boundaries; they make no claim about
the existence of either semantic environment requested in D1 or D3.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3TypeSubstBoundary

open Rcic.Declarative EqLargeFixture LR3

abbrev typeRedex : ExprA :=
  .app (.lam (.sort one) (.succ one) (.bvar 0)) (.sort .zero)

abbrev typeContext : LCtxA := [.assumption (.sort one)]

abbrev redexTypeSubst : SubstA := SubstA.cons typeRedex SubstA.id

def typeRedexTyped (Γ : LCtxA) :
    HasTyA env (iotaIfaceA env) 0 Γ typeRedex (.sort one) :=
  .app Γ _ (.sort .zero) (.sort one) (.sort one) (.succ one) (.succ one) (.succ one)
    (.sort _ one) (.sort Γ one)
    (.lam Γ (.sort one) (.succ one) (.bvar 0) (.sort one) (.succ one)
      (.sort Γ one) (.sort _ one)
      (.bvar _ 0 (.sort one) (.succ one) rfl (.sort _ one)))
    (.sort Γ .zero)

def typeRedexStep (Γ : LCtxA) :
    TyHRedA env (iotaIfaceA env) 0 Γ typeRedex (.sort .zero) (.sort one) :=
  .beta Γ (.sort one) (.succ one) (.bvar 0) (.sort .zero) (.sort one)
    (.sort Γ one)
    (.bvar _ 0 (.sort one) (.succ one) rfl (.sort _ one))
    (.sort Γ .zero) (.sort Γ .zero)

def typeContextWf : CtxWfA env (iotaIfaceA env) 0 typeContext :=
  .assumption .nil (.sort [] one)

def typeVariableTyped :
    HasTyA env (iotaIfaceA env) 0 typeContext (.bvar 0) (.sort one) :=
  .bvar _ 0 (.sort one) (.succ one) rfl (.sort _ one)

def redexTypeSubstTyped :
    SubstTyA env (iotaIfaceA env) 0 [] redexTypeSubst typeContext where
  ty := fun i A h => by
    cases i with
    | zero =>
        have hA : A = .sort one := Option.some.inj h.symm
        subst A
        exact typeRedexTyped []
    | succ i => cases h
  val := fun i A v _ h => by
    cases i with
    | zero => cases h
    | succ i => cases h

theorem typeVariableNormal :
    NormalA3 env (iotaIfaceA env) 0 typeContext (.bvar 0) :=
  .neutral (.bvar 0 rfl)

theorem substitutedTypeHead : HeadA3 env (iotaIfaceA env) 0 []
    (substA redexTypeSubst (.bvar 0)) (.sort .zero) (.sort one) :=
  .primitive _ _ _ (.beta (.sort one) (.succ one) (.bvar 0) (.sort .zero))
    (.nonConstHead (.lam (.sort one) (.succ one) (.bvar 0)))
    ⟨typeRedexStep []⟩

theorem substitutedTypeNotNormal :
    ¬ NormalA3 env (iotaIfaceA env) 0 [] (substA redexTypeSubst (.bvar 0)) :=
  fun hn => normalA3_no_head hn substitutedTypeHead

/-- Raw normality preservation restricted to sort-typed subjects. -/
def RawTypeNormalSubstA3 (H : HeadLayerA3 env (iotaIfaceA env) 0) : Prop :=
  ∀ (Γ Δ : LCtxA) (σ : SubstA) (a : ExprA) (u : Level),
    CtxWfA env (iotaIfaceA env) 0 Γ → CtxWfA env (iotaIfaceA env) 0 Δ →
    SubstTyA env (iotaIfaceA env) 0 Δ σ Γ →
    HasTyA env (iotaIfaceA env) 0 Γ a (.sort u) →
    H.normal Γ a → H.normal Δ (substA σ a)

theorem contextual_not_rawTypeNormalSubstA3 :
    ¬ RawTypeNormalSubstA3 (contextualHeadLayerA3 env (iotaIfaceA env) 0) := by
  intro h
  exact substitutedTypeNotNormal
    (h typeContext [] redexTypeSubst (.bvar 0) one typeContextWf .nil
      redexTypeSubstTyped typeVariableTyped typeVariableNormal)

theorem inhabited_type_normal_subst_boundary :
    eraseEnv env = eqEnvT ∧ Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 typeContext) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 []) ∧
    Nonempty (SubstTyA env (iotaIfaceA env) 0 [] redexTypeSubst typeContext) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 typeContext (.bvar 0) (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 []
      (substA redexTypeSubst (.bvar 0)) (.sort one)) ∧
    NormalA3 env (iotaIfaceA env) 0 typeContext (.bvar 0) ∧
    HeadA3 env (iotaIfaceA env) 0 []
      (substA redexTypeSubst (.bvar 0)) (.sort .zero) (.sort one) ∧
    ¬ NormalA3 env (iotaIfaceA env) 0 [] (substA redexTypeSubst (.bvar 0)) :=
  ⟨erase_env, wf, ⟨typeContextWf⟩, ⟨.nil⟩, ⟨redexTypeSubstTyped⟩,
    ⟨typeVariableTyped⟩, ⟨typeRedexTyped []⟩, typeVariableNormal,
    substitutedTypeHead, substitutedTypeNotNormal⟩

abbrev typeLetContext : LCtxA := [.letBinding (.sort one) typeRedex]

abbrev normalTypeSubst : SubstA := SubstA.cons (.sort .zero) SubstA.id

def typeLetContextWf : CtxWfA env (iotaIfaceA env) 0 typeLetContext :=
  .letBinding .nil (.sort [] one) (typeRedexTyped [])

def typeLetVariableTyped :
    HasTyA env (iotaIfaceA env) 0 typeLetContext (.bvar 0) (.sort one) :=
  .bvar _ 0 (.sort one) (.succ one) rfl (.sort _ one)

theorem typeLocalHead : HeadA3 env (iotaIfaceA env) 0 typeLetContext
    (.bvar 0) typeRedex (.sort one) :=
  .primitive _ _ _ (.varE 0) (.nonApp (.bvar 0))
    ⟨.zetaLocal typeLetContext 0 (.sort one) typeRedex rfl rfl
      (typeRedexTyped typeLetContext)⟩

def normalTypeSubstTyped :
    SubstTyA env (iotaIfaceA env) 0 [] normalTypeSubst typeLetContext where
  ty := fun i A h => by
    cases i with
    | zero =>
        have hA : A = .sort one := Option.some.inj h.symm
        subst A
        exact .sort [] .zero
    | succ i => cases h
  val := fun i A v hty hv => by
    cases i with
    | zero =>
        have hA : A = .sort one := Option.some.inj hty.symm
        have hv' : v = typeRedex := Option.some.inj hv.symm
        subst A
        subst v
        exact .symm [] typeRedex (.sort .zero) (.sort one)
          (idSort1_beta env (iotaIfaceA env) 0)
    | succ i => cases hty

theorem substitutedTypeSourceNormal :
    NormalA3 env (iotaIfaceA env) 0 [] (substA normalTypeSubst (.bvar 0)) :=
  .sort .zero

theorem substitutedTypeEndpointsDiffer :
    substA normalTypeSubst (.bvar 0) ≠ substA normalTypeSubst typeRedex := by decide

theorem substitutedTypeNotChain :
    ¬ TyHRedStarA3 env (iotaIfaceA env) 0
      (contextualHeadLayerA3 env (iotaIfaceA env) 0) []
      (substA normalTypeSubst (.bvar 0)) (substA normalTypeSubst typeRedex)
      (.sort one) := by
  rintro ⟨t⟩
  apply substitutedTypeEndpointsDiffer
  exact (tmChainA3_trace t).eq_of_normal (by
    rintro b ⟨U, hs⟩
    exact normalA3_no_head substitutedTypeSourceNormal hs)

/-- The valid conversion-valued law applies to the same type endpoints. -/
theorem substitutedTypeConv : Nonempty (ConvA env (iotaIfaceA env) 0 []
    (substA normalTypeSubst (.bvar 0)) (substA normalTypeSubst typeRedex)
    (.sort one)) :=
  contextualHeadLayerA3_substConv closed liftIface (iotaFnA_recHead env) substIface
    typeLetContext [] normalTypeSubst (.bvar 0) typeRedex (.sort one)
    typeLetContextWf normalTypeSubstTyped typeLocalHead

/-- Even the proposed finite-chain transport can be restricted to types. -/
def DirectedTypeHeadSubstA3 (H : HeadLayerA3 env (iotaIfaceA env) 0) : Prop :=
  ∀ (Γ Δ : LCtxA) (σ : SubstA) (a b : ExprA) (u : Level),
    CtxWfA env (iotaIfaceA env) 0 Γ → CtxWfA env (iotaIfaceA env) 0 Δ →
    SubstTyA env (iotaIfaceA env) 0 Δ σ Γ →
    HasTyA env (iotaIfaceA env) 0 Γ a (.sort u) →
    H.step Γ a b (.sort u) →
    TyHRedStarA3 env (iotaIfaceA env) 0 H Δ
      (substA σ a) (substA σ b) (.sort u)

theorem contextual_not_directedTypeHeadSubstA3 :
    ¬ DirectedTypeHeadSubstA3 (contextualHeadLayerA3 env (iotaIfaceA env) 0) := by
  intro h
  exact substitutedTypeNotChain
    (h typeLetContext [] normalTypeSubst (.bvar 0) typeRedex one
      typeLetContextWf .nil normalTypeSubstTyped typeLetVariableTyped typeLocalHead)

theorem inhabited_type_directed_subst_boundary :
    eraseEnv env = eqEnvT ∧ Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 typeLetContext) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 []) ∧
    Nonempty (SubstTyA env (iotaIfaceA env) 0 [] normalTypeSubst typeLetContext) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 typeLetContext (.bvar 0) (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 typeLetContext typeRedex (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 []
      (substA normalTypeSubst (.bvar 0)) (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 []
      (substA normalTypeSubst typeRedex) (.sort one)) ∧
    HeadA3 env (iotaIfaceA env) 0 typeLetContext (.bvar 0) typeRedex (.sort one) ∧
    NormalA3 env (iotaIfaceA env) 0 [] (substA normalTypeSubst (.bvar 0)) ∧
    substA normalTypeSubst (.bvar 0) ≠ substA normalTypeSubst typeRedex ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 []
      (substA normalTypeSubst (.bvar 0)) (substA normalTypeSubst typeRedex)
      (.sort one)) ∧
    ¬ TyHRedStarA3 env (iotaIfaceA env) 0
      (contextualHeadLayerA3 env (iotaIfaceA env) 0) []
      (substA normalTypeSubst (.bvar 0)) (substA normalTypeSubst typeRedex)
      (.sort one) :=
  ⟨erase_env, wf, ⟨typeLetContextWf⟩, ⟨.nil⟩, ⟨normalTypeSubstTyped⟩,
    ⟨typeLetVariableTyped⟩, ⟨typeRedexTyped typeLetContext⟩, ⟨.sort [] .zero⟩,
    ⟨typeRedexTyped []⟩, typeLocalHead, substitutedTypeSourceNormal,
    substitutedTypeEndpointsDiffer, substitutedTypeConv, substitutedTypeNotChain⟩

#print axioms typeRedex
#print axioms typeContext
#print axioms redexTypeSubst
#print axioms typeRedexTyped
#print axioms typeRedexStep
#print axioms typeContextWf
#print axioms typeVariableTyped
#print axioms redexTypeSubstTyped
#print axioms typeVariableNormal
#print axioms substitutedTypeHead
#print axioms substitutedTypeNotNormal
#print axioms RawTypeNormalSubstA3
#print axioms contextual_not_rawTypeNormalSubstA3
#print axioms inhabited_type_normal_subst_boundary
#print axioms typeLetContext
#print axioms normalTypeSubst
#print axioms typeLetContextWf
#print axioms typeLetVariableTyped
#print axioms typeLocalHead
#print axioms normalTypeSubstTyped
#print axioms substitutedTypeSourceNormal
#print axioms substitutedTypeEndpointsDiffer
#print axioms substitutedTypeNotChain
#print axioms substitutedTypeConv
#print axioms DirectedTypeHeadSubstA3
#print axioms contextual_not_directedTypeHeadSubstA3
#print axioms inhabited_type_directed_subst_boundary

end Rcic.Declarative.Ann.LR3TypeSubstBoundary

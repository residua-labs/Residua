import rcic.RcicAnnLR3HeadLayer
import rcic.RcicAnnKEqPositive
import rcic.RcicRouteCIndexSyntactic

/-!
# Distinct positive neutral variables need not be apart indices

The two variables below are proofs of the same inhabited Eq proposition.
Both are positive LR3 neutrals and their syntax differs, but old annotated
conversion relates them by proof irrelevance. The declared index telescope
therefore relates them too. An index-apartness language must account for
the declared domain; distinct variable numbers alone are insufficient.

This is a boundary for a proposed blanket separation constructor. It does
not refute a domain-sensitive apartness language or supply the recursor
semantic arm. All context and closing-substitution premises are inhabited.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3.ProofIndexBoundary

open Rcic.Declarative EqLargeFixture

abbrev proofPairContext : LCtxA := .assumption domain :: context

def proofPairContextWf : CtxWfA env (iotaIfaceA env) 0 proofPairContext :=
  .assumption contextWf (eqTyped contextWf parameterTyped parameterTyped)

def proofDomainTyped :
    HasTyA env (iotaIfaceA env) 0 proofPairContext domain (.sort .zero) :=
  eqTyped proofPairContextWf parameterTyped parameterTyped

def leftProofTyped :
    HasTyA env (iotaIfaceA env) 0 proofPairContext (.bvar 1) domain :=
  .bvar proofPairContext 1 domain .zero rfl proofDomainTyped

def rightProofTyped :
    HasTyA env (iotaIfaceA env) 0 proofPairContext (.bvar 0) domain :=
  .bvar proofPairContext 0 domain .zero rfl proofDomainTyped

theorem leftProofNeutral :
    NeutralA3 env (iotaIfaceA env) 0 proofPairContext (.bvar 1) :=
  .bvar 1 rfl

theorem rightProofNeutral :
    NeutralA3 env (iotaIfaceA env) 0 proofPairContext (.bvar 0) :=
  .bvar 0 rfl

theorem proofVariablesDiffer : (ExprA.bvar 1) ≠ .bvar 0 := by decide

def proofVariablesConvert :
    ConvA env (iotaIfaceA env) 0 proofPairContext (.bvar 1) (.bvar 0) domain :=
  .irr proofPairContext domain (.bvar 1) (.bvar 0)
    proofDomainTyped leftProofTyped rightProofTyped

abbrev proofIndexTelescope : ExprA := .pi domain .zero (.sort .zero) one

def proofIndexTelescopeTyped :
    HasTyA env (iotaIfaceA env) 0 proofPairContext proofIndexTelescope
      (.sort (.imax .zero one)) :=
  .pi proofPairContext domain .zero (.sort .zero) one proofDomainTyped
    (.sort (.assumption domain :: proofPairContext) .zero)

theorem proofIndexGuard : ConvArgsA env (iotaIfaceA env) 0 proofPairContext
    proofIndexTelescope [.bvar 1] [.bvar 0] :=
  .cons domain .zero (.sort .zero) one (.bvar 1) (.bvar 0) [] []
    ⟨proofVariablesConvert⟩ (.nil (.sort .zero))

theorem proofDeclaredIndexRelated : RouteCIndex.DeclaredIndexRelA
    env (iotaIfaceA env) 0 proofPairContext proofIndexTelescope 0 []
      (.bvar 1) (.bvar 0) :=
  ⟨domain, .zero, .sort .zero, one, rfl, ⟨proofVariablesConvert⟩⟩

def closeProofPair : SubstA := fun _ => reflAt parameter

def proofPairClosingTyped :
    SubstTyA env (iotaIfaceA env) 0 [] closeProofPair proofPairContext where
  ty := by
    intro i A h
    cases i with
    | zero =>
        cases h
        exact reflTyped .nil parameterTyped
    | succ i =>
        cases i with
        | zero =>
            cases h
            exact reflTyped .nil parameterTyped
        | succ i =>
            simp [lookupTypeA, proofPairContext, context, List.get?] at h
  val := by
    intro i A v _ hV
    cases i with
    | zero => cases hV
    | succ i =>
        cases i with
        | zero => cases hV
        | succ i =>
            simp [lookupValueA, proofPairContext, context, List.get?] at hV

/-- Even positive normality, typing, context well-formedness and distinct
variable indices do not imply nonconversion at a proposition domain. -/
theorem inhabited_proof_index_boundary :
    eraseEnv env = eqEnvT ∧
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 proofPairContext) ∧
    Nonempty (SubstTyA env (iotaIfaceA env) 0 [] closeProofPair proofPairContext) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 proofPairContext domain (.sort .zero)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 proofPairContext (.bvar 1) domain) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 proofPairContext (.bvar 0) domain) ∧
    NeutralA3 env (iotaIfaceA env) 0 proofPairContext (.bvar 1) ∧
    NeutralA3 env (iotaIfaceA env) 0 proofPairContext (.bvar 0) ∧
    (ExprA.bvar 1) ≠ .bvar 0 ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 proofPairContext (.bvar 1) (.bvar 0) domain) ∧
    ConvArgsA env (iotaIfaceA env) 0 proofPairContext
      proofIndexTelescope [.bvar 1] [.bvar 0] :=
  ⟨erase_env, wf, ⟨proofPairContextWf⟩, ⟨proofPairClosingTyped⟩,
    ⟨proofDomainTyped⟩, ⟨leftProofTyped⟩, ⟨rightProofTyped⟩,
    leftProofNeutral, rightProofNeutral, proofVariablesDiffer,
    ⟨proofVariablesConvert⟩, proofIndexGuard⟩

#print axioms proofPairContext
#print axioms proofPairContextWf
#print axioms proofDomainTyped
#print axioms leftProofTyped
#print axioms rightProofTyped
#print axioms leftProofNeutral
#print axioms rightProofNeutral
#print axioms proofVariablesDiffer
#print axioms proofVariablesConvert
#print axioms proofIndexTelescope
#print axioms proofIndexTelescopeTyped
#print axioms proofIndexGuard
#print axioms proofDeclaredIndexRelated
#print axioms closeProofPair
#print axioms proofPairClosingTyped
#print axioms inhabited_proof_index_boundary

end Rcic.Declarative.Ann.LR3.ProofIndexBoundary

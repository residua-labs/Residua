import rcic.RcicAnnEqLargeFixture

/-!
# Two local Eq boundaries for straightforward observation extensions

This is a scoped test of a proposed semantic combination: all proofs are
observed as bottom, elimination is strict in its major, and the Type-level
Pi minor remains observable. The combination already fails on the admitted
Eq environment's closed, canonical iota call. No K head rule or stuck-major
argument is needed for this test.

The general separation theorem states only these three local observation
laws. The finite observation below inhabits them; it is not advertised as a
model of the rest of the calculus. Conversion soundness is the conclusion
refuted by the actual, positively typed iota instance, not an assumed law of
the finite observation.

The companion test keeps a neutral proof observation separate from its
refl observation. The existing context's actual `ConvA.irr` node refutes
soundness of that choice. Together the tests distinguish two specific
unmodified choices: retaining the proof-relevant observation fails `irr`,
while collapsing proofs and retaining strict major elimination fails iota.

In particular this does not rule out a non-strict Eq interpretation using
the endpoints, motive, and minor. It is not the complete M-no or D-no
alternative. `closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3.StrictProofModelBoundary

open Rcic.Declarative EqLargeFixture

universe u

abbrev canonicalMajorA3 : ExprA := reflAt parameter
abbrev canonicalCallA3 : ExprA := call canonicalMajorA3

/-- Closing the existing inhabited call typing at its supplied refl proof.
This uses landed typed substitution, without any semantic premise. -/
theorem canonicalCallTypedA3 :
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] canonicalCallA3 (.sort one)) := by
  obtain ⟨hc⟩ := conversion
  have ht := convA_hasTy_left closed liftIface (iotaFnA_recHead env)
    substIface contextWf hc
  have hr : HasTyA env (iotaIfaceA env) 0 [] canonicalMajorA3 domain :=
    reflTyped .nil parameterTyped
  have hd : HasTyA env (iotaIfaceA env) 0 [] domain (.sort .zero) :=
    eqTyped .nil parameterTyped parameterTyped
  have hclosed := hasTyA_inst0 closed liftIface
    (iotaRecHeadTypedA_of (iotaFnA_recHead env)) substIface .nil ht hr hd
  exact ⟨hclosed⟩

/-- The concrete interface fires directly on the closed constructor major. -/
theorem canonicalIotaRelA3 :
    (iotaIfaceA env).rel env [] canonicalCallA3 result :=
  ⟨by decide, by decide⟩

/-- An actual `ConvA.iota` node, with both closed endpoint typings supplied. -/
theorem canonicalIotaConversionA3 :
    Nonempty (ConvA env (iotaIfaceA env) 0 []
      canonicalCallA3 result (.sort one)) := by
  obtain ⟨ht⟩ := canonicalCallTypedA3
  exact ⟨.iota [] canonicalCallA3 result (.sort one)
    canonicalIotaRelA3 ht resultTyped⟩

/-- Only the local equations of the strict-major candidate are recorded.
There is no typing-soundness or conversion-soundness field. -/
structure StrictEqCallObservationA3 (D : Type u) where
  bottom : D
  denote : ExprA → D
  eliminate : D → D
  call_eq : ∀ p : ExprA, denote (call p) = eliminate (denote p)
  proof_eq : denote canonicalMajorA3 = bottom
  strict : eliminate bottom = bottom
  minor_ne : denote result ≠ bottom

/-- Soundness restricted to closed annotated conversion in this one admitted
environment. The boundary needs only its explicit canonical iota node. -/
def ClosedConversionSoundObservationA3 {D : Type u} (denote : ExprA → D) : Prop :=
  ∀ (a b T : ExprA), ConvA env (iotaIfaceA env) 0 [] a b T →
    denote a = denote b

/-- The candidate's local equations separate the two actual iota endpoints. -/
theorem strictEqCallImagesSeparatedA3 {D : Type u}
    (O : StrictEqCallObservationA3 D) :
    O.denote canonicalCallA3 ≠ O.denote result := by
  intro he
  apply O.minor_ne
  calc
    O.denote result = O.denote canonicalCallA3 := he.symm
    _ = O.eliminate (O.denote canonicalMajorA3) := O.call_eq canonicalMajorA3
    _ = O.eliminate O.bottom := congrArg O.eliminate O.proof_eq
    _ = O.bottom := O.strict

/-- The supplied closed iota conversion refutes soundness of this scoped
candidate. This is not a refutation of other proof-irrelevant models. -/
theorem strictEqCallNotSoundA3 {D : Type u}
    (O : StrictEqCallObservationA3 D) :
    ¬ ClosedConversionSoundObservationA3 O.denote := by
  intro hsound
  obtain ⟨hc⟩ := canonicalIotaConversionA3
  exact strictEqCallImagesSeparatedA3 O
    (hsound canonicalCallA3 result (.sort one) hc)

/-- A finite observation makes the local candidate assumptions jointly
inhabited. It records only an exposed Pi head versus bottom. -/
inductive FiniteObservationA3 where
  | bottom
  | pi

def finiteDenotationA3 : ExprA → FiniteObservationA3
  | .pi _ _ _ _ => .pi
  | _ => .bottom

def finiteEliminationA3 (_ : FiniteObservationA3) : FiniteObservationA3 :=
  .bottom

/-- Concrete data, with no hypothetical global model laws. -/
def finiteStrictEqCallObservationA3 : StrictEqCallObservationA3 FiniteObservationA3 where
  bottom := .bottom
  denote := finiteDenotationA3
  eliminate := finiteEliminationA3
  call_eq := fun _ => rfl
  proof_eq := rfl
  strict := rfl
  minor_ne := by intro h; cases h

/-- Admission, the empty context, the constructor major, both endpoints,
the actual iota relation/conversion, and the local semantic candidate are
all inhabited. Only conversion soundness of that candidate is refuted. -/
theorem inhabitedStrictEqIotaBoundaryA3 :
    eraseEnv env = eqEnvT ∧
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 []) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] canonicalMajorA3 domain) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] canonicalCallA3 (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] result (.sort one)) ∧
    (iotaIfaceA env).rel env [] canonicalCallA3 result ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 [] canonicalCallA3 result (.sort one)) ∧
    Nonempty (StrictEqCallObservationA3 FiniteObservationA3) ∧
    ¬ ClosedConversionSoundObservationA3 finiteDenotationA3 :=
  ⟨erase_env, wf, ⟨.nil⟩, ⟨reflTyped .nil parameterTyped⟩,
    canonicalCallTypedA3, ⟨resultTyped⟩, canonicalIotaRelA3,
    canonicalIotaConversionA3, ⟨finiteStrictEqCallObservationA3⟩,
    strictEqCallNotSoundA3 finiteStrictEqCallObservationA3⟩

/-- The actual proof-irrelevance constructor in the existing inhabited
context. All three premises are supplied by the Eq fixture. -/
def neutralReflIrrNodeA3 :
    ConvA env (iotaIfaceA env) 0 context (.bvar 0) canonicalMajorA3 domain :=
  .irr context domain (.bvar 0) canonicalMajorA3
    (eqTyped contextWf parameterTyped parameterTyped) majorTyped
    (reflTyped contextWf parameterTyped)

/-- Conversion soundness in the one actual Eq-proof context used by the
second test. It imposes no soundness law on the finite observation below. -/
def ContextConversionSoundObservationA3 {D : Type u} (denote : ExprA → D) : Prop :=
  ∀ (a b T : ExprA), ConvA env (iotaIfaceA env) 0 context a b T →
    denote a = denote b

/-- Any observation that keeps these two actual proofs separate fails this
specific irrelevance node. No claim about other models is made. -/
theorem retainedProofObservationNotSoundA3 {D : Type u} (denote : ExprA → D)
    (hsep : denote (.bvar 0) ≠ denote canonicalMajorA3) :
    ¬ ContextConversionSoundObservationA3 denote := by
  intro hsound
  exact hsep (hsound (.bvar 0) canonicalMajorA3 domain neutralReflIrrNodeA3)

/-- The finite record of a retained constructor observation. -/
inductive ProofObservationA3 where
  | bottom
  | ref

/-- Only the constructor head is observed. This is a supplied local
observation, without a claim that it interprets the other typing rules. -/
def retainedRefDenotationA3 (e : ExprA) : ProofObservationA3 :=
  match (appsSpineA e).1 with
  | .const r _ => if r = 64 then .ref else .bottom
  | _ => .bottom

theorem retainedRefImagesSeparatedA3 :
    retainedRefDenotationA3 (.bvar 0) ≠ retainedRefDenotationA3 canonicalMajorA3 := by
  intro h
  cases h

/-- Admission, context, proposition typing, both proof typings, the exact
irrelevance node, and the distinguishing observation are all supplied. -/
theorem inhabitedRetainedProofBoundaryA3 :
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 context) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context domain (.sort .zero)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context (.bvar 0) domain) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context canonicalMajorA3 domain) ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 context (.bvar 0) canonicalMajorA3 domain) ∧
    retainedRefDenotationA3 (.bvar 0) ≠ retainedRefDenotationA3 canonicalMajorA3 ∧
    ¬ ContextConversionSoundObservationA3 retainedRefDenotationA3 :=
  ⟨wf, ⟨contextWf⟩, ⟨eqTyped contextWf parameterTyped parameterTyped⟩,
    ⟨majorTyped⟩, ⟨reflTyped contextWf parameterTyped⟩, ⟨neutralReflIrrNodeA3⟩,
    retainedRefImagesSeparatedA3,
    retainedProofObservationNotSoundA3 retainedRefDenotationA3 retainedRefImagesSeparatedA3⟩

#print axioms canonicalMajorA3
#print axioms canonicalCallA3
#print axioms canonicalCallTypedA3
#print axioms canonicalIotaRelA3
#print axioms canonicalIotaConversionA3
#print axioms StrictEqCallObservationA3
#print axioms StrictEqCallObservationA3.mk
#print axioms StrictEqCallObservationA3.bottom
#print axioms StrictEqCallObservationA3.denote
#print axioms StrictEqCallObservationA3.eliminate
#print axioms StrictEqCallObservationA3.call_eq
#print axioms StrictEqCallObservationA3.proof_eq
#print axioms StrictEqCallObservationA3.strict
#print axioms StrictEqCallObservationA3.minor_ne
#print axioms ClosedConversionSoundObservationA3
#print axioms strictEqCallImagesSeparatedA3
#print axioms strictEqCallNotSoundA3
#print axioms FiniteObservationA3
#print axioms FiniteObservationA3.bottom
#print axioms FiniteObservationA3.pi
#print axioms finiteDenotationA3
#print axioms finiteEliminationA3
#print axioms finiteStrictEqCallObservationA3
#print axioms inhabitedStrictEqIotaBoundaryA3
#print axioms neutralReflIrrNodeA3
#print axioms ContextConversionSoundObservationA3
#print axioms retainedProofObservationNotSoundA3
#print axioms ProofObservationA3
#print axioms ProofObservationA3.bottom
#print axioms ProofObservationA3.ref
#print axioms retainedRefDenotationA3
#print axioms retainedRefImagesSeparatedA3
#print axioms inhabitedRetainedProofBoundaryA3

end Rcic.Declarative.Ann.LR3.StrictProofModelBoundary

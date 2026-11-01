import rcic.RcicF3IndexedPropGroupAttack
import rcic.RcicF3IndexedPropPlainAttack
import rcic.RcicF3PropEvalSafeIndexAttack

/-!
# Produced indexed-bound Prop contract with explicit legacy scope

The two universal producer conjuncts are the literal candidate-constructor
step and the uniformly-Prop / anySort / PendA group step. The latter uses
the separate BoundGIndexed inside IndexedPropGroup.GroupStepAt, retaining
WalkAgree, BoundDG and the actual predecessor. Its result is the existing
PointwiseRole.GInv with legacy IotaAt.

All component witnesses use the same supplied Premises4. NoLegacyWitness
is an explicit conjunct: the AccR package's legacy IotaAt obligation has
no applicable legacy witness. The concrete AccR child domain is empty;
the separate True redex has no constructor fields or indices. Their
witness types retain these limits. This contract supplies neither modern
Acc computation, imported-Acc non-vacuity nor universal plain IotaAt.

The five A1 components, the evaluation/group components and the separate
plain-spine/True components are recomposed without modifying their types.
The additional two-key and Wrap continuations are outside this contract.
scope_closure_claim = 0. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.AIndexedPropContract
open Rcic.Declarative

/-- The complete constructor producer type, including the normalized
candidate, actual typed motive/minors, full level vector and predecessor.
This is the type of IndexedPropEval.constructor_step, not a fixture-only
existence statement or an assumed recursive-child evaluator. -/
def CandidateConstructorProducer : Prop :=
  ∀ (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (C : PropEval.Context) (hM : C.M = mkM P μ)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT C.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : C.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv C.E C.f fm) C.E
      ((C.f, fm) :: ctors ++ [(C.rr, C.rm)]) C.E')
    (hBound : IndexedFieldBounds.BoundGIndexed K
      (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α C.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans C.E)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (RawFamily.ofFrame P μ (famDataOf C.node.a) (NormPropEval.base P μ C) vs))
    (fullvs : List Nat) (hσfull : C.σ = σOf fullvs)
    (hvs : ∀ u, u ∈ fullvs → u ≤ K C.rr)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel = 0)
    (hpolicy : C.node.a.policy = .anySort)
    (v : Level)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort v)))))
    (hminors : TelFits C.M C.σ C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors),
    ∀ vs i z, RawFamily.CtorAt P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node))
      (NormPropEval.candidate P μ C) vs i z →
        PropEvalCandidate.EvalPredicate C vs i z

theorem candidate_constructor_producer : CandidateConstructorProducer :=
  @IndexedPropEval.constructor_step

theorem candidate_constructor_nonrefutable (P : Premises4) :
    ¬ (CandidateConstructorProducer → (Premises4 → False)) :=
  fun h => h candidate_constructor_producer P

/-- Exactly the universal type of IndexedPropGroup.legacy_group_step.
The separate GroupStepAt contains BoundGIndexed, WalkAgree, BoundDG and
the predecessor; no extra group-step hypothesis is added here. Its iota
conclusion is the existing legacy IotaAt through PointwiseRole.GInv. -/
def LegacyGroupProducer : Prop :=
  ∀ (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hProp : UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .anySort)
    (hPend : ∃ node : RecNode E E' f rr rm, PendA node),
    IndexedPropGroup.GroupStepAt P K hE hfam hctors hrec hmem

theorem legacy_group_producer : LegacyGroupProducer :=
  @IndexedPropGroup.legacy_group_step

theorem legacy_group_nonrefutable (P : Premises4) :
    ¬ (LegacyGroupProducer → (Premises4 → False)) :=
  fun h => h legacy_group_producer P

/-- The five already-produced A1 components, with one shared model P.
These retain the old AccP bound refutation, safe-index comparison, the
ordinary/unrevealed rows, normalization and the mixed-key attacks. -/
def A1Components (P : Premises4) : Prop :=
  AccBoundScopeAttack.Witness P ∧
  PropEvalSafeIndex.Witness P ∧
  IndexedFieldBounds.Witness P ∧
  IndexedBoundNormalization.Witness P ∧
  PropEvalSafeIndexAttack.Witness P

theorem a1_components (P : Premises4) : A1Components P :=
  ⟨AccBoundScopeAttack.component_witness P,
    PropEvalSafeIndex.component_witness P,
    IndexedFieldBounds.component_witness P,
    IndexedBoundNormalization.component_witness P,
    PropEvalSafeIndexAttack.component_witness P⟩

theorem a1_components_nonrefutable (P : Premises4) :
    ¬ (A1Components P → (Premises4 → False)) :=
  fun h => h (a1_components P) P

/-- Literal same-P composition. The evaluation witness includes step,
closure, totality, typed value and the concrete installed AccR equation.
The group witness includes stored memberships, legacy RecPkg, GInv,
AllSound and the unchanged old-target refutation. The plain witness
combines the separate data spine with the zero-index True redex.
NoLegacyWitness is repeated at this surface to expose the legacy scope. -/
def Components (P : Premises4) : Prop :=
  A1Components P ∧
  IndexedPropEvalAttack.Witness P ∧
  IndexedPropGroupAttack.Witness P ∧
  IndexedPropPlainAttack.Witness P ∧
  IndexedPropGroupAttack.NoLegacyWitness

theorem components (P : Premises4) : Components P :=
  ⟨a1_components P, IndexedPropEvalAttack.component_witness P,
    IndexedPropGroupAttack.component_witness P,
    IndexedPropPlainAttack.component_witness P,
    IndexedPropGroupAttack.no_legacy_witness⟩

theorem components_nonrefutable (P : Premises4) :
    ¬ (Components P → (Premises4 → False)) :=
  fun h => h (components P) P

/-- The complete checkpoint target: two universal producers and all
same-P components. No universal plain or modern iota law is a conjunct. -/
def Target : Prop :=
  CandidateConstructorProducer ∧ LegacyGroupProducer ∧ (∀ P, Components P)

theorem target : Target :=
  ⟨candidate_constructor_producer, legacy_group_producer, components⟩

/-- Relative non-refutability uses the produced target and the same
explicit P; it supplies no unconditional inhabitant of Premises4. -/
theorem target_nonrefutable (P : Premises4) :
    ¬ (Target → (Premises4 → False)) :=
  fun h => h target P

end Rcic.F3.PSet.AIndexedPropContract

#print axioms Rcic.F3.PSet.AIndexedPropContract.candidate_constructor_producer
#print axioms Rcic.F3.PSet.AIndexedPropContract.candidate_constructor_nonrefutable
#print axioms Rcic.F3.PSet.AIndexedPropContract.legacy_group_producer
#print axioms Rcic.F3.PSet.AIndexedPropContract.legacy_group_nonrefutable
#print axioms Rcic.F3.PSet.AIndexedPropContract.a1_components
#print axioms Rcic.F3.PSet.AIndexedPropContract.a1_components_nonrefutable
#print axioms Rcic.F3.PSet.AIndexedPropContract.components
#print axioms Rcic.F3.PSet.AIndexedPropContract.components_nonrefutable
#print axioms Rcic.F3.PSet.AIndexedPropContract.target
#print axioms Rcic.F3.PSet.AIndexedPropContract.target_nonrefutable

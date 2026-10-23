import rcic.RcicAnnLR3GuardedReaderSource
import rcic.RcicAnnLR3GuardedEqFamily

/- An actual large Eq-recursion call at open proposition indices.
   closure_claim = 0. The source derivation does not assume conversion of the
   two indices, and no conversion from this call to its minor is asserted. -/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.GuardedOpenEqCall

open Rcic.Declarative
open EqLargeFixture GuardedReaderSource

private def applyConcrete {Γ : LCtxA}
    (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {f a D C : ExprA} {u v : Level}
    (hf : HasTyA env (iotaIfaceA env) 0 Γ f (.pi D u C v))
    (ha : HasTyA env (iotaIfaceA env) 0 Γ a D) :
    HasTyA env (iotaIfaceA env) 0 Γ (.app f a) (instantiate0A a C) := by
  have parts := hasTyA_pi_parts
    (hasTyA_regular closed liftIface (iotaFnA_recHead env) substIface hΓ hf).2
  exact .app Γ f a D C u v v parts.2
    (hasTyA_inst0 closed liftIface (iotaRecHeadTypedA_of (iotaFnA_recHead env))
      substIface hΓ parts.2 ha parts.1) hf ha

abbrev context : LCtxA := proofContext
abbrev left : ExprA := liftedLeftIndex
abbrev right : ExprA := liftedRightIndex
abbrev domain : ExprA := eqAt left right

abbrev tail (x a : ExprA) : ExprA :=
  .pi (eqAt x a) .zero (.sort two) (.succ two)

abbrev tailLam (x a : ExprA) : ExprA :=
  .lam (eqAt x a) .zero (.sort one)

abbrev motiveBody : ExprA := tailLam (.bvar 3) (.bvar 0)
abbrev motive : ExprA := .lam (.sort .zero) one motiveBody
abbrev motiveTy : ExprA :=
  .pi (.sort .zero) one (tail (.bvar 3) (.bvar 0)) (.imax .zero (.succ two))
abbrev motiveAt (a p : ExprA) : ExprA := .app (.app motive a) p

abbrev motiveContext : LCtxA := .assumption (.sort .zero) :: context

def motiveContextWf : CtxWfA env (iotaIfaceA env) 0 motiveContext :=
  .assumption proofContextWf (.sort context .zero)

def motiveLeftTyped : HasTyA env (iotaIfaceA env) 0
    motiveContext (.bvar 3) (.sort .zero) :=
  .bvar motiveContext 3 (.sort .zero) one rfl (.sort motiveContext .zero)

def motiveVarTyped : HasTyA env (iotaIfaceA env) 0
    motiveContext (.bvar 0) (.sort .zero) :=
  .bvar motiveContext 0 (.sort .zero) one rfl (.sort motiveContext .zero)

def tailLamTyped {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ)
    {x a : ExprA} (hx : HasTyA env (iotaIfaceA env) 0 Γ x (.sort .zero))
    (ha : HasTyA env (iotaIfaceA env) 0 Γ a (.sort .zero)) :
    HasTyA env (iotaIfaceA env) 0 Γ (tailLam x a) (tail x a) :=
  .lam Γ (eqAt x a) .zero (.sort one) (.sort two) (.succ two)
    (eqTyped hΓ hx ha) (.sort _ two) (.sort _ one)

def motiveTyped : HasTyA env (iotaIfaceA env) 0 context motive motiveTy :=
  .lam context (.sort .zero) one motiveBody (tail (.bvar 3) (.bvar 0))
    (.imax .zero (.succ two)) (.sort context .zero)
    (.pi _ (eqAt (.bvar 3) (.bvar 0)) .zero (.sort two) (.succ two)
      (eqTyped motiveContextWf motiveLeftTyped motiveVarTyped) (.sort _ two))
    (tailLamTyped motiveContextWf motiveLeftTyped motiveVarTyped)

def motiveAtTyped {a p : ExprA}
    (ha : HasTyA env (iotaIfaceA env) 0 context a (.sort .zero))
    (hp : HasTyA env (iotaIfaceA env) 0 context p (eqAt left a)) :
    HasTyA env (iotaIfaceA env) 0 context (motiveAt a p) (.sort two) :=
  applyConcrete proofContextWf (applyConcrete proofContextWf motiveTyped ha) hp

def motiveBeta {a p : ExprA}
    (ha : HasTyA env (iotaIfaceA env) 0 context a (.sort .zero))
    (hp : HasTyA env (iotaIfaceA env) 0 context p (eqAt left a)) :
    ConvA env (iotaIfaceA env) 0 context (motiveAt a p) (.sort one) (.sort two) := by
  have hfirst : ConvA env (iotaIfaceA env) 0 context (.app motive a)
      (tailLam left a) (tail left a) :=
    .beta context (.sort .zero) one motiveBody a (tail (.bvar 3) (.bvar 0))
      (.sort context .zero)
      (tailLamTyped motiveContextWf motiveLeftTyped motiveVarTyped) ha
      (tailLamTyped proofContextWf liftedLeftIndexTyped ha)
  have hc : ConvA env (iotaIfaceA env) 0 context (motiveAt a p)
      (.app (tailLam left a) p) (.sort two) :=
    .app context (.app motive a) (tailLam left a) p p
      (eqAt left a) (.sort two) .zero (.succ two) hfirst
      (.refl context p _ hp) (.sort _ two)
      (applyConcrete proofContextWf
        (tailLamTyped proofContextWf liftedLeftIndexTyped ha) hp)
  exact .trans context _ _ _ _ hc
    (.beta context (eqAt left a) .zero (.sort one) p (.sort two)
      (eqTyped proofContextWf liftedLeftIndexTyped ha)
      (.sort _ one) hp (.sort context one))

def motiveTypeConv {a p : ExprA}
    (ha : HasTyA env (iotaIfaceA env) 0 context a (.sort .zero))
    (hp : HasTyA env (iotaIfaceA env) 0 context p (eqAt left a)) :
    TyConvA env (iotaIfaceA env) 0 context (motiveAt a p) (.sort one) :=
  .of context _ _ two two two (motiveAtTyped ha hp) (eqNA_refl _)
    (.sort context one) (eqNA_refl _) (motiveBeta ha hp)

abbrev pre : List ExprA := [.sort .zero, left, motive, result, right]
abbrev recPrefix : ExprA := foldAppsA (.const 65 [two]) pre
abbrev call (p : ExprA) : ExprA := .app recPrefix p

theorem callTyped {p : ExprA}
    (hp : HasTyA env (iotaIfaceA env) 0 context p domain) :
    Nonempty (HasTyA env (iotaIfaceA env) 0 context (call p) (.sort one)) := by
  obtain ⟨hr⟩ := recConstTyped context
  have h0 := applyConcrete proofContextWf hr (.sort context .zero)
  have h1 := applyConcrete proofContextWf h0 liftedLeftIndexTyped
  have h2 := applyConcrete proofContextWf h1 motiveTyped
  have hm := hasTyA_of_tyConvA
    (resultTyped (E := env) (I := iotaIfaceA env) (n := 0) (Γ := context))
    (motiveTypeConv liftedLeftIndexTyped
      (reflTyped proofContextWf liftedLeftIndexTyped)).symm
  have h3 := applyConcrete proofContextWf h2 hm
  have h4 := applyConcrete proofContextWf h3 liftedRightIndexTyped
  have h5 := applyConcrete proofContextWf h4 hp
  exact ⟨hasTyA_of_tyConvA h5 (motiveTypeConv liftedRightIndexTyped hp)⟩

theorem open_call_typed :
    Nonempty (HasTyA env (iotaIfaceA env) 0 context (call proofTerm) (.sort one)) :=
  callTyped proofTermTyped

theorem inhabited_open_call :
    Nonempty OpenEqSource ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context (call proofTerm) (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 context result (.sort one)) :=
  ⟨inhabited_open_eq_source, open_call_typed, ⟨resultTyped⟩⟩

open UnitModel TaggedSaturatedTower

/-- Inputs to the policy for this one fixed source call. The actual source
admission/context and its call typing are retained, not passed as unproved
external premises. -/
structure PolicyInput where
  sourceInput : OpenEqInput
  callTyped : HasTyA env (iotaIfaceA env) 0 context (call proofTerm) (.sort one)

def PolicyInput.assignment (i : PolicyInput) : IndexAssignment :=
  i.sourceInput.assignment

theorem proposition_policy_input (P : Prop) :
    ∃ i : PolicyInput, i.assignment = propositionAssignment P 0 := by
  obtain ⟨s, hs⟩ := inhabited_proposition_input P 0
  obtain ⟨ht⟩ := open_call_typed
  exact ⟨⟨s, ht⟩, hs⟩

/-- The Pi minor is produced from the actual source result and this valuation. -/
def minorCode (ν : Valuation) (a : IndexAssignment) : Code.{0} 1 :=
  TaggedKPiFixture.code env TaggedKEvaluation.eqSyntax ν (rawEnvironment a)

theorem minorCode_image (ν : Valuation) (a : IndexAssignment) :
    (minorCode ν a).view.value = TaggedKEvaluation.image ν (rawEnvironment a) result := rfl

theorem minorCode_tag (ν : Valuation) (a : IndexAssignment) :
    (minorCode ν a).tag = .pi := rfl

theorem minorCode_inhabited (ν : Valuation) (a : IndexAssignment) :
    ∃ f : (minorCode ν a).Element, (minorCode ν a).view.relation f f :=
  TaggedKPiFixture.code_inhabited env TaggedKEvaluation.eqSyntax ν (rawEnvironment a)

/-- A token for this fixed call in this local scope; a whole-language semantic
neutral identity producer is not asserted. The caller cannot substitute a
family code, a different minor, or a different fallback into this policy. -/
def callName : Nat := 0

def Read (ν : Valuation) (i : PolicyInput) (C : Code.{0} 1) : Prop :=
  GuardedReaderSource.Reads i.assignment (minorCode ν i.assignment) callName C

theorem read_functional {ν : Valuation} {i : PolicyInput} {C D : Code.{0} 1}
    (hC : Read ν i C) (hD : Read ν i D) : C = D :=
  GuardedReaderSource.reads_functional hC hD

theorem read_true {ν : Valuation} {i : PolicyInput} {C : Code.{0} 1}
    (hG : guard i.assignment) (hC : Read ν i C) : C = minorCode ν i.assignment :=
  GuardedCodeRead.output_eq_of_guard hG hC

theorem read_false {ν : Valuation} {i : PolicyInput} {C : Code.{0} 1}
    (hG : ¬ guard i.assignment) (hC : Read ν i C) : C = Code.neutral 1 callName :=
  GuardedCodeRead.output_eq_of_not_guard hG hC

theorem read_true_related {ν : Valuation} {i : PolicyInput} {C : Code.{0} 1}
    (hG : guard i.assignment) (hC : Read ν i C) :
    CodeRelated C (minorCode ν i.assignment) :=
  GuardedCodeRead.codeRelated_of_guard hG hC

def readDecision (ν : Valuation) (i : PolicyInput)
    (d : Decidable (guard i.assignment)) : Code.{0} 1 :=
  GuardedCodeRead.ofDecision d (minorCode ν i.assignment) (Code.neutral 1 callName)

theorem readDecision_reads (ν : Valuation) (i : PolicyInput)
    (d : Decidable (guard i.assignment)) : Read ν i (readDecision ν i d) :=
  GuardedCodeRead.ofDecision_reads d _ _

/-- Exact logical totality for the specified local policy on the constructed
open-source/retained-assignment class. This is not whole-language adequacy. -/
def PropositionTotal (ν : Valuation) : Prop :=
  ∀ P : Prop, ∃ (i : PolicyInput) (C : Code.{0} 1),
    i.assignment = propositionAssignment P 0 ∧ Read ν i C

theorem proposition_total_iff_em (ν : Valuation) :
    PropositionTotal ν ↔ (∀ P : Prop, P ∨ ¬ P) := by
  constructor
  · intro h P
    obtain ⟨i, C, hi, hC⟩ := h P
    have hR : GuardedReaderSource.Reads (propositionAssignment P 0)
        (minorCode ν i.assignment) callName C := by
      change GuardedReaderSource.Reads i.assignment (minorCode ν i.assignment) callName C at hC
      rw [hi] at hC ⊢
      exact hC
    exact (proposition_read_exists_iff P (minorCode ν i.assignment) 0 callName).mp ⟨C, hR⟩
  · intro h P
    obtain ⟨i, hi⟩ := proposition_policy_input P
    obtain ⟨C, hC⟩ :=
      (proposition_read_exists_iff P (minorCode ν i.assignment) 0 callName).mpr (h P)
    refine ⟨i, C, hi, ?_⟩
    change GuardedReaderSource.Reads i.assignment (minorCode ν i.assignment) callName C
    rw [hi] at hC ⊢
    exact hC

theorem total_data_reader_implies_em (ν : Valuation)
    (run : PolicyInput → Code.{0} 1) (sound : ∀ i, Read ν i (run i)) :
    ∀ P : Prop, P ∨ ¬ P := by
  apply (proposition_total_iff_em ν).mp
  intro P
  obtain ⟨i, hi⟩ := proposition_policy_input P
  exact ⟨i, run i, hi, sound i⟩

/-- All source-variable, Eq-decoder and minor image obligations for this
local input. The recursor result's image law belongs to the new guarded
normalization semantics and is not silently borrowed from the old evaluator. -/
structure InputImages (ν : Valuation) (i : PolicyInput) : Prop where
  left_image : ValueEq
    (TaggedKEvaluation.image ν (rawEnvironment i.assignment) liftedLeftIndex)
    i.assignment.left.view.value
  right_image : ValueEq
    (TaggedKEvaluation.image ν (rawEnvironment i.assignment) liftedRightIndex)
    i.assignment.right.view.value
  equality_image : ValueEq (GuardedEqFamily.code ν i.assignment).view.value
    (TaggedKEvaluation.image ν (rawEnvironment i.assignment) liftedEqualityType)
  evaluated_major_member : (GuardedEqFamily.code ν i.assignment).view.relation
    (⟨TaggedKEvaluation.image ν (rawEnvironment i.assignment) proofTerm⟩ :
      (GuardedEqFamily.code ν i.assignment).Element)
    (⟨TaggedKEvaluation.image ν (rawEnvironment i.assignment) proofTerm⟩ :
      (GuardedEqFamily.code ν i.assignment).Element)
  minor_image : (minorCode ν i.assignment).view.value =
    TaggedKEvaluation.image ν (rawEnvironment i.assignment) result
  minor_inhabited : ∃ f : (minorCode ν i.assignment).Element,
    (minorCode ν i.assignment).view.relation f f

theorem proposition_policy_images (ν : Valuation) (P : Prop) :
    ∃ i : PolicyInput, i.assignment = propositionAssignment P 0 ∧ InputImages ν i := by
  obtain ⟨i, hi⟩ := proposition_policy_input P
  refine ⟨i, hi, ?_⟩
  constructor
  · rw [hi]
    exact proposition_left_image ν P 0
  · rw [hi]
    exact proposition_right_image ν P 0
  · exact GuardedEqFamily.code_actual_image ν i.assignment
  · rw [hi]
    exact GuardedEqFamily.proposition_actual_major_member ν P 0
  · exact minorCode_image ν i.assignment
  · exact minorCode_inhabited ν i.assignment

/-- The totality classification continues to hold after requiring all the
constructed source/variable/decoder/minor image evidence together. -/
def InterpretedTotal (ν : Valuation) : Prop :=
  ∀ P : Prop, ∃ (i : PolicyInput) (C : Code.{0} 1),
    i.assignment = propositionAssignment P 0 ∧ InputImages ν i ∧ Read ν i C

theorem interpreted_total_iff_em (ν : Valuation) :
    InterpretedTotal ν ↔ (∀ P : Prop, P ∨ ¬ P) := by
  constructor
  · intro h
    apply (proposition_total_iff_em ν).mp
    intro P
    obtain ⟨i, C, hi, _, hC⟩ := h P
    exact ⟨i, C, hi, hC⟩
  · intro h P
    obtain ⟨i, hi, himages⟩ := proposition_policy_images ν P
    obtain ⟨C, hC⟩ :=
      (proposition_read_exists_iff P (minorCode ν i.assignment) 0 callName).mpr (h P)
    refine ⟨i, C, hi, himages, ?_⟩
    change GuardedReaderSource.Reads i.assignment (minorCode ν i.assignment) callName C
    rw [hi] at hC ⊢
    exact hC

end Rcic.Declarative.Ann.LR3.GuardedOpenEqCall

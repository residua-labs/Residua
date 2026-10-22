import rcic.RcicAnnLR3CandidateActionProducts

/-!
# A fixed-erasure boundary for the unrestricted retained universe

Two actual stage-one codes have the same erased type value. The first is
the universe of stage-zero codes; every member erases to a defined exact
sort-zero value. The second is the empty PER's raw-neutral completion at
that same type value; every member erases to a raw neutral atom. Both
codes, both element carriers and the enclosing universe memberships are
inhabited, but their legal members have disjoint erasures.

Consequently a retained action for `forall X : Sort 1, X` cannot commute
with fixed raw application on every existing stage-one code. Retaining
the output as data does not repair this collision. Completing only the
type values with bottom does not repair it either. An arbitrary member
section does exist; exactly its raw-erasure compatibility is impossible.

This refutes the attachment of all current `StratifiedCandidates.Code 1`
fibres to an erasure-compatible dependent-product reflection interface.
It does not refute the source theory, admitted families, previously
supplied universe-valued actions, or a model with different code fibres
or erasure. The actual source type, context, variable and application are
supplied below. No Fundamental theorem is assumed. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.EnrichedReflectionBoundary

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open StratifiedCandidates CandidateAction

/-- Its members retain actual stage-zero codes. -/
def universeFibre : Code 1 := universeCode 0

/-- An existing permitted stage-one construction, at exactly the same
type value, whose members are solely raw neutral atoms. -/
def neutralFibre : Code 1 :=
  predicative 0 universeFibre.value universeFibre.level universeFibre.defined
    (fun _ _ => False) ⟨False.elim, fun h _ => False.elim h⟩

theorem same_type_value : universeFibre.value = neutralFibre.value := rfl

theorem universe_fibre_laws : RelLaws universeFibre.relation := universeFibre.lawful

theorem neutral_fibre_laws : RelLaws neutralFibre.relation := neutralFibre.lawful

theorem universe_fibre_member (name : Nat) :
    universeFibre.relation (universeFibre.point name) (universeFibre.point name) :=
  universeFibre.point_member name

theorem neutral_fibre_member (name : Nat) :
    neutralFibre.relation (neutralFibre.point name) (neutralFibre.point name) :=
  neutralFibre.point_member name

theorem universe_member_erasure {x : Carrier 1}
    (hx : universeFibre.relation x x) :
    SortMember (some 0) (StratifiedCandidates.erase 1 x) ∧ TypeDefined (StratifiedCandidates.erase 1 x) :=
  universe_elimination 0 x hx

theorem neutral_member_form {y : Carrier 1}
    (hy : neutralFibre.relation y y) :
    ∃ name : Nat, y = raw 1 (NeutralPER.neutralAtom name) := by
  change False ∨ (y = y ∧ RawNeutral 1 y) at hy
  rcases hy with hf | ⟨_, hn⟩
  · exact False.elim hf
  · exact hn

/-- The obstruction concerns every legal member, not just the chosen
designated points. Both membership premises have explicit witnesses. -/
theorem legal_erasures_disjoint {x y : Carrier 1}
    (hx : universeFibre.relation x x) (hy : neutralFibre.relation y y) :
    ¬ ValueEq (StratifiedCandidates.erase 1 x) (StratifiedCandidates.erase 1 y) := by
  intro he
  obtain ⟨name, rfl⟩ := neutral_member_form hy
  exact NeutralPER.neutralAtom_not_sort_member name (some 0)
    (sortMember_congr he (universe_member_erasure hx).1)

theorem codes_not_related : ¬ CodeRelated 1 universeFibre neutralFibre := by
  intro h
  have hx := universe_fibre_member 0
  have hy := (h.transport _ _).mp hx
  exact legal_erasures_disjoint hx hy (ValueEq.refl _)

/-- The two conflicting arguments are ordinary members of the next
universe, without any semantic or source premise left to instantiate. -/
theorem universe_arguments_inhabited :
    (universeCode 1).relation (encode 1 universeFibre) (encode 1 universeFibre) ∧
    (universeCode 1).relation (encode 1 neutralFibre) (encode 1 neutralFibre) ∧
    StratifiedCandidates.erase 2 (encode 1 universeFibre) = StratifiedCandidates.erase 2 (encode 1 neutralFibre) :=
  ⟨universe_member 1 _, universe_member 1 _, rfl⟩

/-- A section carries its chosen legal member as data. -/
def MemberSection : Type :=
  (C : Code 1) → {x : Carrier 1 // (view 1 C).relation x x}

/-- The unrestricted family is pointwise inhabited constructively.
Selecting a member is not the failed operation. -/
def designatedSection : MemberSection :=
  fun C => ⟨(view 1 C).point 0, (view 1 C).point_member 0⟩

def ErasureExtensional (run : MemberSection) : Prop :=
  ∀ C D : Code 1, ValueEq (view 1 C).value (view 1 D).value →
    ValueEq (StratifiedCandidates.erase 1 (run C).val) (StratifiedCandidates.erase 1 (run D).val)

theorem no_extensional_section (run : MemberSection) : ¬ ErasureExtensional run := by
  intro h
  exact legal_erasures_disjoint (run universeFibre).property (run neutralFibre).property
    (h universeFibre neutralFibre (ValueEq.refl _))

/-- This is the minimum unpaired application obligation of a retained
member of the dependent product over all existing stage-one codes. -/
def RealizesEveryFibre (f : Value) : Prop :=
  ∃ run : MemberSection, ∀ C : Code 1,
    ValueEq (NeutralPi.applyValue f (view 1 C).value) (StratifiedCandidates.erase 1 (run C).val)

theorem no_raw_dependent_action (f : Value) : ¬ RealizesEveryFibre f := by
  rintro ⟨run, hrun⟩
  apply no_extensional_section run
  intro C D hCD
  exact (hrun C).symm.trans
    ((NeutralPi.applyValue_congr (ValueEq.refl f) hCD).trans (hrun D))

def closedUniverseFibre : ClosedCode 1 := close 1 universeFibre
def closedNeutralFibre : ClosedCode 1 := close 1 neutralFibre

theorem closed_same_type_value :
    eraseCode closedUniverseFibre = eraseCode closedNeutralFibre := rfl

theorem closed_legal_erasures_disjoint {x y : Carrier 1}
    (hx : (view 1 closedUniverseFibre.code).relation x x)
    (hy : (view 1 closedNeutralFibre.code).relation y y) :
    ¬ ValueEq (StratifiedCandidates.erase 1 x) (StratifiedCandidates.erase 1 y) :=
  legal_erasures_disjoint hx hy

def ClosedMemberSection : Type :=
  (C : ClosedCode 1) → {x : Carrier 1 // (view 1 C.code).relation x x}

def designatedClosedSection : ClosedMemberSection :=
  fun C => ⟨(view 1 C.code).point 0, (view 1 C.code).point_member 0⟩

/-- This uses the same bottom-completed input values as the actual
retained action constructors; their completion cannot remove the clash. -/
def RealizesEveryClosedFibre (f : Value) : Prop :=
  ∃ run : ClosedMemberSection, ∀ C : ClosedCode 1,
    ValueEq (NeutralPi.applyValue f (eraseCode C)) (StratifiedCandidates.erase 1 (run C).val)

theorem no_closed_dependent_action (f : Value) : ¬ RealizesEveryClosedFibre f := by
  rintro ⟨run, hrun⟩
  exact closed_legal_erasures_disjoint
    (run closedUniverseFibre).property (run closedNeutralFibre).property
    ((hrun closedUniverseFibre).symm.trans (hrun closedNeutralFibre))

abbrev one : Level := .succ .zero
abbrev two : Level := .succ one

/-- The first predicative identity-codomain product, with its actual
source annotations. -/
def sourceType : ExprA := .pi (.sort one) two (.bvar 0) one

def source_type_formed (Γ : LCtxA) :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 Γ sourceType (.sort (.imax two one)) :=
  .pi Γ (.sort one) two (.bvar 0) one (.sort Γ one)
    (.bvar _ 0 (.sort one) two rfl (.sort _ one))

def context : LCtxA := [.assumption sourceType]

def context_wf : CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 context :=
  .assumption .nil (source_type_formed [])

def source_variable_typed :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 context (.bvar 0) sourceType :=
  .bvar context 0 sourceType (.imax two one) rfl (source_type_formed context)

def applicationContext : LCtxA := .assumption (.sort one) :: context

def application_context_wf :
    CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 applicationContext :=
  .assumption context_wf (.sort context one)

def source_function_typed :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 applicationContext (.bvar 1) sourceType :=
  .bvar applicationContext 1 sourceType (.imax two one) rfl
    (source_type_formed applicationContext)

def source_argument_typed :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 applicationContext (.bvar 0) (.sort one) :=
  .bvar applicationContext 0 (.sort one) two rfl (.sort applicationContext one)

def source_application_typed :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 applicationContext
      (.app (.bvar 1) (.bvar 0)) (.bvar 0) :=
  .app applicationContext (.bvar 1) (.bvar 0) (.sort one) (.bvar 0) two one one
    (.bvar _ 0 (.sort one) two rfl (.sort _ one))
    source_argument_typed source_function_typed source_argument_typed

/-- The codomain producer is available on the entire bottom-completed
stage-one carrier. It retains the argument itself, with the actual
EnvironmentEval equation and paired transport. -/
def codomainBody (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    CandidateActionProducts.Body (ClosedCode 1) eraseCode CodeRel
      emptyEnvA F ν ρ (.bvar 0) 1 where
  run := id
  image := fun C => bound_image emptyEnvA F ν (EnvI.cons (eraseCode C) ρ)
    0 (eraseCode C) rfl C.bot
  respect := fun _ _ h => h

theorem codomain_retains (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (C : ClosedCode 1) : (codomainBody F ν ρ).run C = C := rfl

theorem codomain_paired (F G : EnvironmentEval.FamilySyntax) (ν μ : Valuation)
    (ρ σ : EnvI) {C D : ClosedCode 1} (h : CodeRel C D) :
    CodeRel ((codomainBody F ν ρ).run C) ((codomainBody G μ σ).run D) := h

/-- The body is also an actual source lambda action. Its result is a
code, unlike the impossible element-valued action refuted above. -/
def codomainAction (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    Action (ClosedCode 1) eraseCode CodeRel 1 :=
  CandidateActionProducts.bodyAction (.sort one) two (codomainBody F ν ρ)

theorem codomain_action_retains (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (C : ClosedCode 1) : (codomainAction F ν ρ).run C = C := rfl

/-- Every original retained code participates, with its complete element
relation preserved. The universe and codomain premises are supplied. -/
theorem codomain_premises_inhabited (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    Nonempty (CandidateActionProducts.Body (ClosedCode 1) eraseCode CodeRel
      emptyEnvA F ν ρ (.bvar 0) 1) ∧
    (∀ C : Code 1, CodeRelated 1 C (close 1 C).code ∧
      (view 1 (close 1 C).code).relation = (view 1 C).relation ∧
      (universeCode 1).relation (encode 1 (close 1 C).code) (encode 1 (close 1 C).code) ∧
      (codomainBody F ν ρ).run (close 1 C) = close 1 C ∧
      ValueEq (EnvironmentEval.denote emptyEnvA F ν
        (EnvI.cons (eraseCode (close 1 C)) ρ) (.bvar 0))
        (eraseCode ((codomainBody F ν ρ).run (close 1 C)))) ∧
    (¬ ∃ f : Value, RealizesEveryClosedFibre f) :=
  ⟨⟨codomainBody F ν ρ⟩,
    fun C => ⟨completeCode_related 1 C, close_preserves_fibre 1 C,
      universe_member 1 _, rfl, (codomainBody F ν ρ).image (close 1 C)⟩,
    fun ⟨f, hf⟩ => no_closed_dependent_action f hf⟩

/-- No policy for the other source constructors can supply this missing
dependent action at a source variable's fixed EnvironmentEval image. -/
theorem source_variable_has_no_action (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    ¬ RealizesEveryClosedFibre
      (EnvironmentEval.denote emptyEnvA F ν ρ (.bvar 0)) :=
  no_closed_dependent_action _

/-- All structural and code premises are inhabited; the conjunction
contains the impossibility itself rather than an unsupplied model IH. -/
theorem boundary_inhabited :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 context) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      sourceType (.sort (.imax two one))) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 context (.bvar 0) sourceType) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 applicationContext) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 applicationContext
      (.app (.bvar 1) (.bvar 0)) (.bvar 0)) ∧
    RelLaws universeFibre.relation ∧ RelLaws neutralFibre.relation ∧
    universeFibre.relation (universeFibre.point 0) (universeFibre.point 0) ∧
    neutralFibre.relation (neutralFibre.point 0) (neutralFibre.point 0) ∧
    (universeCode 1).relation (encode 1 universeFibre) (encode 1 universeFibre) ∧
    (universeCode 1).relation (encode 1 neutralFibre) (encode 1 neutralFibre) ∧
    universeFibre.value = neutralFibre.value ∧
    Nonempty MemberSection ∧ Nonempty ClosedMemberSection ∧
    (¬ ∃ f : Value, RealizesEveryFibre f) ∧
    (¬ ∃ f : Value, RealizesEveryClosedFibre f) :=
  ⟨⟨.empty⟩, ⟨context_wf⟩, ⟨source_type_formed []⟩, ⟨source_variable_typed⟩,
    ⟨application_context_wf⟩, ⟨source_application_typed⟩,
    universe_fibre_laws, neutral_fibre_laws, universe_fibre_member 0, neutral_fibre_member 0,
    universe_member 1 _, universe_member 1 _, same_type_value,
    ⟨designatedSection⟩, ⟨designatedClosedSection⟩,
    fun ⟨f, hf⟩ => no_raw_dependent_action f hf,
    fun ⟨f, hf⟩ => no_closed_dependent_action f hf⟩

end Rcic.Declarative.Ann.LR3.EnrichedReflectionBoundary

import rcic.RcicAnnLR3SaturatedPiElements
import rcic.RcicAnnLR3EnrichedReflectionBoundary

/-!
# An actual reflected element action for forall X : Sort 1, X

The domain retains every restricted stage-one code, with its entire fibre
preserved by bottom completion. The dependent body is the actual source
variable evaluator and returns that retained code. The product's reflected
element is an actual native lambda; its application has a legal retained
result in every input fibre, including the exact universe fibre.

This supplies a positive product on its explicit element-action carrier.
It has not been embedded in SaturatedTower.Code 2 and is not a general
source constructor arm. closure_claim = 0.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.SaturatedPiElementsControl
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open StratifiedCandidates CandidateActionProducts SaturatedPiElements

abbrev PositiveDomain :=
  {C : CandidateAction.ClosedCode 1 // SaturatedTower.Closed 1 C.code}

def positiveDomainErase (C : PositiveDomain) : Value :=
  CandidateAction.eraseCode C.1

def positiveDomainRel (C D : PositiveDomain) : Prop :=
  CandidateAction.CodeRel C.1 D.1

theorem positiveDomain_laws : RelLaws positiveDomainRel :=
  ⟨fun h => (CandidateAction.codeRel_laws 1).symm h,
    fun h g => (CandidateAction.codeRel_laws 1).trans h g⟩

def positiveDomainCode (C : PositiveDomain) : SaturatedTower.Code 1 :=
  ⟨C.1.code, C.2⟩

theorem positiveDomain_relation (C D : PositiveDomain) :
    positiveDomainRel C D ↔
      SaturatedTower.Relation 1 (positiveDomainCode C) (positiveDomainCode D) :=
  Iff.rfl

def retainPositiveCode (C : SaturatedTower.Code 1) : PositiveDomain where
  val := CandidateAction.close 1 C.1
  property := by
    intro name
    change (view 1 (CandidateAction.close 1 C.1).code).relation
      (SaturatedTower.reflect 1 name) (SaturatedTower.reflect 1 name)
    rw [CandidateAction.close_preserves_fibre]
    exact C.2 name

theorem retainPositiveCode_fibre (C : SaturatedTower.Code 1) :
    (view 1 (retainPositiveCode C).1.code).relation =
      (view 1 C.1).relation :=
  CandidateAction.close_preserves_fibre 1 C.1

def positiveIdentityBody
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    Body PositiveDomain positiveDomainErase positiveDomainRel E F ν ρ (.bvar 0) 1 where
  run := fun C => C.1
  image := fun C => CandidateAction.bound_image E F ν
    (EnvI.cons (positiveDomainErase C) ρ) 0
    (CandidateAction.eraseCode C.1) rfl C.1.bot
  respect := fun _ _ h => h

theorem positiveIdentityBody_retains
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (C : SaturatedTower.Code 1) :
    (view 1 ((positiveIdentityBody E F ν ρ).run (retainPositiveCode C)).code).relation =
      (view 1 C.1).relation :=
  retainPositiveCode_fibre C

def forallPositive
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    PointedPER 2 (SourceElementAction (positiveIdentityBody emptyEnvA F ν ρ)) :=
  positivePi (k := 0) (n := 1) (positiveIdentityBody emptyEnvA F ν ρ)
    positiveDomain_laws (fun C => C.2)
    (.sort EnrichedReflectionBoundary.one)
    EnrichedReflectionBoundary.two EnrichedReflectionBoundary.one rfl rfl

theorem forallPositive_source_value
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    (forallPositive F ν ρ).value =
      EnvironmentEval.denote emptyEnvA F ν ρ EnrichedReflectionBoundary.sourceType := rfl

def forallPositive_source_formed (Γ : LCtxA) :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 Γ
      EnrichedReflectionBoundary.sourceType
      (.sort (.imax EnrichedReflectionBoundary.two EnrichedReflectionBoundary.one)) :=
  EnrichedReflectionBoundary.source_type_formed Γ

theorem forallPositive_reflection_member
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (name : Nat) :
    (forallPositive F ν ρ).relation
      ((forallPositive F ν ρ).point name) ((forallPositive F ν ρ).point name) :=
  (forallPositive F ν ρ).point_member name

theorem forallPositive_reflection_run
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (name : Nat) (C : PositiveDomain) :
    ((forallPositive F ν ρ).point name).run C =
      SaturatedTower.reflect 1 name := rfl

theorem forallPositive_reflection_application
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (name : Nat) (C : PositiveDomain) :
    ValueEq (NeutralPi.applyValue
      ((forallPositive F ν ρ).point name).value (positiveDomainErase C))
      (NativeMemberValues.value (some 0) name) := by
  have h := ((forallPositive F ν ρ).point name).erased C
  change ValueEq _ (StratifiedCandidates.erase 1 (SaturatedTower.reflect 1 name)) at h
  rw [SaturatedTower.reflect_erasure] at h
  exact h

theorem forallPositive_reflection_in_fibre
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (name : Nat) (C : PositiveDomain) :
    (view 1 C.1.code).relation
      (((forallPositive F ν ρ).point name).run C)
      (((forallPositive F ν ρ).point name).run C) :=
  C.2 name

theorem forallPositive_reflection_in_retained_fibre
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (name : Nat) (C : SaturatedTower.Code 1) :
    (view 1 C.1).relation
      (((forallPositive F ν ρ).point name).run (retainPositiveCode C))
      (((forallPositive F ν ρ).point name).run (retainPositiveCode C)) :=
  C.2 name

theorem forallPositive_reflection_in_universe
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (name : Nat) :
    (view 1 (SaturatedTower.universeCode 0).1).relation
      (((forallPositive F ν ρ).point name).run
        (retainPositiveCode (SaturatedTower.universeCode 0)))
      (((forallPositive F ν ρ).point name).run
        (retainPositiveCode (SaturatedTower.universeCode 0))) :=
  (SaturatedTower.universeCode 0).2 name

/-- Source admission, the real product image and every reflected output
are supplied together. The element-action carrier remains explicit. -/
theorem forallPositive_control
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (name : Nat) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0
      EnrichedReflectionBoundary.applicationContext) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0
      EnrichedReflectionBoundary.applicationContext
      (.app (.bvar 1) (.bvar 0)) (.bvar 0)) ∧
    (forallPositive F ν ρ).value =
      EnvironmentEval.denote emptyEnvA F ν ρ EnrichedReflectionBoundary.sourceType ∧
    (forallPositive F ν ρ).relation
      ((forallPositive F ν ρ).point name) ((forallPositive F ν ρ).point name) ∧
    (∀ C : SaturatedTower.Code 1, ∃ x : StratifiedCandidates.Carrier 1,
      (view 1 C.1).relation x x ∧
      ValueEq (NeutralPi.applyValue ((forallPositive F ν ρ).point name).value
        (positiveDomainErase (retainPositiveCode C))) (StratifiedCandidates.erase 1 x)) :=
  ⟨⟨.empty⟩, ⟨EnrichedReflectionBoundary.application_context_wf⟩,
    ⟨EnrichedReflectionBoundary.source_application_typed⟩,
    forallPositive_source_value F ν ρ, forallPositive_reflection_member F ν ρ name,
    fun C => ⟨((forallPositive F ν ρ).point name).run (retainPositiveCode C),
      forallPositive_reflection_in_retained_fibre F ν ρ name C,
      ((forallPositive F ν ρ).point name).erased (retainPositiveCode C)⟩⟩

end Rcic.Declarative.Ann.LR3.SaturatedPiElementsControl


namespace Rcic.Declarative.Ann.LR3.SaturatedPiElementsControl
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements StratifiedCandidates

theorem positiveDomain_erasure (C : PositiveDomain) :
    positiveDomainErase C = StratifiedCandidates.erase 2
      (SaturatedTower.encode 1 (positiveDomainCode C)) := rfl

theorem positiveDomain_level (C : PositiveDomain) :
    SortMember (some 1) (positiveDomainErase C) :=
  (view 1 C.1.code).level

theorem positiveDomain_universe (C : PositiveDomain) :
    SaturatedTower.UniverseRel 1
      (SaturatedTower.encode 1 (positiveDomainCode C))
      (SaturatedTower.encode 1 (positiveDomainCode C)) :=
  SaturatedTower.universe_member 1 (positiveDomainCode C)

theorem positiveDomain_related_iff (C D : PositiveDomain) :
    SaturatedTower.UniverseRel 1
      (SaturatedTower.encode 1 (positiveDomainCode C))
      (SaturatedTower.encode 1 (positiveDomainCode D)) ↔ positiveDomainRel C D :=
  ⟨fun h => h.1, fun h => ⟨h, C.2, D.2⟩⟩

end Rcic.Declarative.Ann.LR3.SaturatedPiElementsControl

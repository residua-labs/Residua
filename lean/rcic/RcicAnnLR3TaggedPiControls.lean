import rcic.RcicAnnLR3TaggedSaturatedTower
import rcic.RcicAnnLR3SaturatedPiElementsControl
import rcic.RcicAnnLR3SaturatedCandidatePiBoundary

/-!
# The supplied positive product is a certified Code 2

The embedding preserves the entire existing action carrier and the
actual source product image. Reflection, run, application and each old
retained output fibre are composed from the supplied positive-product
control. The domain remains PositiveDomain; it is not silently enlarged
to all heterogeneous tagged Code 1 values. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TaggedPiControls
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open StratifiedCandidates CandidateActionProducts
open TaggedSaturatedTower SaturatedPiElements SaturatedPiElementsControl

def forallPositiveCode
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    TaggedSaturatedTower.Code.{0} 2 :=
  piCode (k := 0) (n := 1) (positiveIdentityBody emptyEnvA F ν ρ)
    positiveDomain_laws (fun C => C.2)
    (.sort EnrichedReflectionBoundary.one)
    EnrichedReflectionBoundary.two EnrichedReflectionBoundary.one rfl rfl

theorem forallPositiveCode_tag
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    (forallPositiveCode F ν ρ).tag = .pi := rfl

theorem forallPositiveCode_carrier
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    (forallPositiveCode F ν ρ).Element =
      SourceElementAction (positiveIdentityBody emptyEnvA F ν ρ) := rfl

theorem forallPositiveCode_view
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    (forallPositiveCode F ν ρ).view = forallPositive F ν ρ := rfl

theorem forallPositiveCode_source_value
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    (forallPositiveCode F ν ρ).view.value =
      EnvironmentEval.denote emptyEnvA F ν ρ EnrichedReflectionBoundary.sourceType := rfl

def forallPositiveCode_source_formed (Γ : LCtxA) :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 Γ
      EnrichedReflectionBoundary.sourceType
      (.sort (.imax EnrichedReflectionBoundary.two EnrichedReflectionBoundary.one)) :=
  forallPositive_source_formed Γ

theorem forallPositiveCode_reflection_member
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (name : Nat) :
    (forallPositiveCode F ν ρ).view.relation
      ((forallPositiveCode F ν ρ).view.point name)
      ((forallPositiveCode F ν ρ).view.point name) :=
  (forallPositiveCode F ν ρ).view.point_member name

theorem forallPositiveCode_reflection_run
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (name : Nat) (C : PositiveDomain) :
    ((forallPositiveCode F ν ρ).view.point name).run C =
      SaturatedTower.reflect 1 name := rfl

theorem forallPositiveCode_reflection_application
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (name : Nat) (C : PositiveDomain) :
    ValueEq (NeutralPi.applyValue
      ((forallPositiveCode F ν ρ).erase ((forallPositiveCode F ν ρ).view.point name))
      (positiveDomainErase C)) (NativeMemberValues.value (some 0) name) :=
  forallPositive_reflection_application F ν ρ name C

theorem forallPositiveCode_reflection_in_retained_fibre
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (name : Nat) (C : SaturatedTower.Code 1) :
    (view 1 C.1).relation
      (((forallPositiveCode F ν ρ).view.point name).run (retainPositiveCode C))
      (((forallPositiveCode F ν ρ).view.point name).run (retainPositiveCode C)) :=
  C.2 name

theorem forallPositiveCode_related_application
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (f g : (forallPositiveCode F ν ρ).Element)
    (hfg : (forallPositiveCode F ν ρ).view.relation f g)
    {C D : PositiveDomain} (hCD : positiveDomainRel C D) :
    ValueEq (NeutralPi.applyValue ((forallPositiveCode F ν ρ).erase f)
      (positiveDomainErase C)) (StratifiedCandidates.erase 1 (f.run C)) ∧
    ValueEq (NeutralPi.applyValue ((forallPositiveCode F ν ρ).erase g)
      (positiveDomainErase D)) (StratifiedCandidates.erase 1 (g.run D)) ∧
    (view 1 C.1.code).relation (f.run C) (g.run D) := by
  refine ⟨f.erased C, g.erased D, ?_⟩
  exact elementRel_paired positiveDomain_laws
    (fun X _ => (view 1 X.1.code).lawful) hfg hCD

theorem forallPositiveCode_control
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (name : Nat) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0
      EnrichedReflectionBoundary.applicationContext) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0
      EnrichedReflectionBoundary.applicationContext
      (.app (.bvar 1) (.bvar 0)) (.bvar 0)) ∧
    (forallPositiveCode F ν ρ).view.value =
      EnvironmentEval.denote emptyEnvA F ν ρ EnrichedReflectionBoundary.sourceType ∧
    (forallPositiveCode F ν ρ).view.relation
      ((forallPositiveCode F ν ρ).view.point name)
      ((forallPositiveCode F ν ρ).view.point name) ∧
    (∀ C : SaturatedTower.Code 1, ∃ x : StratifiedCandidates.Carrier 1,
      (view 1 C.1).relation x x ∧
      ValueEq (NeutralPi.applyValue
        ((forallPositiveCode F ν ρ).erase ((forallPositiveCode F ν ρ).view.point name))
        (positiveDomainErase (retainPositiveCode C)))
        (StratifiedCandidates.erase 1 x)) :=
  forallPositive_control F ν ρ name

/-- Actual application excludes the old level-only reflected raw point;
the distinction does not merely follow from unequal tag constructors. -/
theorem forallPositiveCode_reflection_not_typed_point
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (name : Nat) (i : Option Nat) (badName : Nat) :
    ¬ ValueEq
      ((forallPositiveCode F ν ρ).erase ((forallPositiveCode F ν ρ).view.point name))
      (NativeMemberValues.value i badName) := by
  intro hf
  let X : PositiveDomain := retainPositiveCode (SaturatedTower.universeCode 0)
  have hx : positiveDomainErase X .bot := X.1.bot
  have hfx := NeutralPi.applyValue_congr hf
    (ValueEq.refl (positiveDomainErase X))
  have he := hfx.symm.trans
    (forallPositiveCode_reflection_application F ν ρ name X)
  exact SaturatedCandidatePiBoundary.native_typed_application_not_sort
    i (some 0) badName (positiveDomainErase X) hx
    (sortMember_congr he.symm (NativeMemberValues.value_level (some 0) name))

theorem forallPositiveCode_in_universe
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    (TaggedSaturatedTower.universeCode.{0} 2).view.relation
      (TaggedSaturatedTower.universeEncode 2 (forallPositiveCode F ν ρ))
      (TaggedSaturatedTower.universeEncode 2 (forallPositiveCode F ν ρ)) :=
  TaggedSaturatedTower.universe_member 2 (forallPositiveCode F ν ρ)

theorem forallPositiveCode_decode
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    TaggedSaturatedTower.universeDecode 2
      (TaggedSaturatedTower.universeEncode 2 (forallPositiveCode F ν ρ)) =
      forallPositiveCode F ν ρ := rfl

end Rcic.Declarative.Ann.LR3.TaggedPiControls

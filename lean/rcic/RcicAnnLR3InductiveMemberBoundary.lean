import rcic.RcicAnnLR3FunctionEval
import rcic.RcicAnnRecPins

/-!
# The inherited fixture evaluator does not interpret every admitted member

The actual admitted Nat group stores its family at reference 10 with type
`Sort 1`. The inherited `UnitModel.translate` has special meanings only
for the Eq fixture's references 63--65, so this Nat family is interpreted
as a raw neutral constant. Such an atom has no exact universe membership.

For every code algebra attached to this fixed evaluator, the exact paired
`Ty_const` contract therefore fails at this admitted member. The source
environment, member lookup, level-list premises, type-formation child,
paired child induction hypothesis, and related empty realizations are all
supplied below. The contradiction uses the generic universe elimination
law; it does not assume the legacy universe carrier or a fundamental
theorem. This is an obstruction to the particular evaluator attachment,
not to the admitted source class, the Value carrier, or other evaluators.
No source declaration or admission rule is changed. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.InductiveMemberBoundary

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements

abbrev one : Level := .succ .zero
abbrev two : Level := .succ one

def zeroValuation : Valuation := fun _ => some 0

def model (C : CodeSystem) : AnnSemantics := FunctionEval.annSemantics C

def source_admitted : EnvWfA (iotaIfaceA pinNatBuiltEnvA) pinNatBuiltEnvA :=
  pinNatBuilt_wf

def source_context : CtxWfA pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) 0 [] := .nil

theorem member_lookup : pinNatBuiltEnvA.members 10 = some pinNatFamA := rfl

theorem level_length : ([] : List Level).length = pinNatFamA.arity := rfl

theorem levels_bounded : levelsBounded 0 ([] : List Level) = true := rfl

def source_type : HasTyA pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) 0 []
    (instantiateLevelsA [] pinNatFamA.mtypeA) (.sort two) := .sort [] one

def source_member : HasTyA pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) 0 []
    (.const 10 []) (.sort one) := pinNatConstTy member_lookup

/-- The exact constructor's only child IH is an already supplied sort arm. -/
theorem type_ih (C : CodeSystem) :
    PairedTyGoal (model C) pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) 0 []
      (instantiateLevelsA [] pinNatFamA.mtypeA) (.sort two) :=
  PairedArms.ty_sort_supplied (model C) pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA)
    0 [] one

/-- This is the actual inherited constant image, independent of the code algebra. -/
theorem member_image (ν : Valuation) (ρ : EnvI) :
    ValueEq (UnitModel.denote ν ρ (.const 10 [])) (NeutralPER.neutralAtom 10) := by
  change ValueEq (denI ρ (.const 10 [])) (denI EnvI.bot (.const 10 []))
  exact FunctionEval.constant_environment ρ EnvI.bot 10 []

/-- No code algebra can repair this fixed raw image while retaining the
existing exact universe-elimination contract. -/
theorem ty_const_refuted (C : CodeSystem) :
    ¬ PairedArms.Ty_const (model C) pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) 0 := by
  intro h
  have hgoal := h [] 10 [] pinNatFamA two member_lookup level_length levels_bounded
    source_type (type_ih C)
  have hpaired := hgoal source_context zeroValuation zeroValuation EnvI.bot EnvI.bot
    (ValuationRel.refl _) (.nil _ _)
  have htyping : Judgment (model C) zeroValuation [] EnvI.bot
      (.const 10 []) (.const 10 []) (.sort one) := hpaired.left_typing
  have hsort : SortMember (some 1) (UnitModel.denote zeroValuation EnvI.bot (.const 10 [])) :=
    (sort_judgment_membership htyping).1
  exact NeutralPER.neutralAtom_not_sort_member 10 (some 1)
    (sortMember_congr (member_image zeroValuation EnvI.bot) hsort)

/-- Every source, child-IH, valuation, and realization premise of the
refuted exact arm invocation is inhabited at the real concrete iota. -/
theorem arm_premises_inhabited (C : CodeSystem) :
    Nonempty (EnvWfA (iotaIfaceA pinNatBuiltEnvA) pinNatBuiltEnvA) ∧
    Nonempty (CtxWfA pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) 0 []) ∧
    pinNatBuiltEnvA.members 10 = some pinNatFamA ∧
    ([] : List Level).length = pinNatFamA.arity ∧
    levelsBounded 0 ([] : List Level) = true ∧
    Nonempty (HasTyA pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) 0 []
      (instantiateLevelsA [] pinNatFamA.mtypeA) (.sort two)) ∧
    PairedTyGoal (model C) pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) 0 []
      (instantiateLevelsA [] pinNatFamA.mtypeA) (.sort two) ∧
    ValuationRel zeroValuation zeroValuation ∧
    PairedRealises (model C) zeroValuation zeroValuation [] EnvI.bot EnvI.bot ∧
    Nonempty (HasTyA pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) 0 []
      (.const 10 []) (.sort one)) ∧
    (¬ PairedArms.Ty_const (model C) pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) 0) :=
  ⟨⟨source_admitted⟩, ⟨source_context⟩, member_lookup, level_length, levels_bounded,
    ⟨source_type⟩, type_ih C, ValuationRel.refl _, .nil _ _, ⟨source_member⟩,
    ty_const_refuted C⟩

end Rcic.Declarative.Ann.LR3.InductiveMemberBoundary

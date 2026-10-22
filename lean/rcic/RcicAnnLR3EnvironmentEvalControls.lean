import rcic.RcicAnnLR3EnvironmentEval
import rcic.RcicAnnLR3InductiveCodes
import rcic.RcicAnnLR3TruthAxiomBoundary

/-!
# Admitted controls for the environment-aware delta producer

A genuine admitted definition stores `Prop : Type` at reference 90. Its
member lookup, arity, level bound, body derivation, exact paired body IH and
related empty realizations are all supplied. The exact new delta supplier
is invoked below; no Fundamental or arbitrary body interpretation is assumed.
An opaque declaration and the earlier empty-family axiom are neutral under
the same environment-aware evaluator. `closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.EnvironmentEvalControls

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements EnvironmentEval

abbrev one : Level := .succ .zero
abbrev two : Level := .succ one

def definitionMember : CheckedMemberA :=
  ⟨.definitionM, 0, .sort one, some (.sort .zero), 0, none⟩

def definitionEnv : ResolvedEnvA := extendEnvA emptyEnvA 90 definitionMember

def definition_admitted : EnvWfA (iotaIfaceA definitionEnv) definitionEnv :=
  .definitionM emptyEnvA 90 (.sort one) (.sort .zero) two .empty rfl
    (.sort [] one) (.sort [] .zero) (fun _ => rfl) (fun _ => rfl) rfl rfl

def model (C : CodeSystem) : AnnSemantics :=
  annSemantics C definitionEnv neutralFamilySyntax

def source_type (Γ : LCtxA) :
    HasTyA definitionEnv (iotaIfaceA definitionEnv) 0 Γ (.sort one) (.sort two) :=
  .sort Γ one

def source_body (Γ : LCtxA) :
    HasTyA definitionEnv (iotaIfaceA definitionEnv) 0 Γ (.sort .zero) (.sort one) :=
  .sort Γ .zero

def source_member (Γ : LCtxA) :
    HasTyA definitionEnv (iotaIfaceA definitionEnv) 0 Γ (.const 90 []) (.sort one) :=
  .const Γ 90 [] definitionMember two rfl rfl rfl (source_type Γ)

def source_delta (Γ : LCtxA) :
    ConvA definitionEnv (iotaIfaceA definitionEnv) 0 Γ
      (.const 90 []) (.sort .zero) (.sort one) :=
  .delta Γ 90 [] definitionMember (.sort .zero) rfl rfl rfl rfl rfl (source_body Γ)

theorem body_ih (C : CodeSystem) (Γ : LCtxA) :
    PairedTyGoal (model C) definitionEnv (iotaIfaceA definitionEnv) 0 Γ
      (.sort .zero) (.sort one) :=
  PairedArms.ty_sort_supplied (model C) definitionEnv (iotaIfaceA definitionEnv) 0 Γ .zero

theorem definition_ih (C : CodeSystem) (Γ : LCtxA) :
    PairedTyGoal (model C) definitionEnv (iotaIfaceA definitionEnv) 0 Γ
      (.const 90 []) (.sort one) :=
  definition_typing C neutralFamilySyntax
    (r := 90) (ls := []) (m := definitionMember) (b := .sort .zero)
    rfl rfl rfl (body_ih C Γ)

theorem delta_ih (C : CodeSystem) (Γ : LCtxA) :
    PairedConvGoal (model C) definitionEnv (iotaIfaceA definitionEnv) 0 Γ
      (.const 90 []) (.sort .zero) (.sort one) :=
  conv_delta_supplied C definitionEnv neutralFamilySyntax (iotaIfaceA definitionEnv) 0
    Γ 90 [] definitionMember (.sort .zero) rfl rfl rfl rfl rfl (source_body Γ) (body_ih C Γ)

theorem definition_image (C : CodeSystem) (ν : Valuation) (ρ : EnvI) :
    (model C).image ν [] ρ (.const 90 []) = universeValue (some 0) := by
  change EnvironmentEval.denote definitionEnv neutralFamilySyntax ν ρ (.const 90 []) = _
  rw [NeutralCodes.valueEq_eq (denote_delta (E := definitionEnv)
    (r := 90) (ls := []) (m := definitionMember) (b := .sort .zero)
    rfl rfl rfl neutralFamilySyntax ν ρ)]
  exact (model C).sort_image ν [] ρ .zero

theorem old_new_images_differ (C : CodeSystem) (ν : Valuation) (ρ : EnvI) :
    ¬ ValueEq ((model C).image ν [] ρ (.const 90 []))
      (UnitModel.denote ν ρ (.const 90 [])) := by
  intro h
  have hs : SortMember (some 1) ((model C).image ν [] ρ (.const 90 [])) := by
    rw [definition_image]
    exact sort_member EnvI.bot (some 0)
  have hold : ValueEq (UnitModel.denote ν ρ (.const 90 [])) (NeutralPER.neutralAtom 90) :=
    FunctionEval.constant_environment ρ EnvI.bot 90 []
  exact NeutralPER.neutralAtom_not_sort_member 90 (some 1)
    (sortMember_congr hold (sortMember_congr h hs))

def zeroValuation : Valuation := fun _ => some 0

/-- Every premise of the exact delta invocation is actual source data or
an already supplied sort theorem, including the paired empty realization. -/
theorem delta_control_inhabited (C : CodeSystem) :
    Nonempty (EnvWfA (iotaIfaceA definitionEnv) definitionEnv) ∧
    Nonempty (CtxWfA definitionEnv (iotaIfaceA definitionEnv) 0 []) ∧
    definitionEnv.members 90 = some definitionMember ∧
    definitionMember.bodyA = some (.sort .zero) ∧
    transparent definitionMember.mclass = true ∧
    ([] : List Level).length = definitionMember.arity ∧
    levelsBounded 0 ([] : List Level) = true ∧
    Nonempty (HasTyA definitionEnv (iotaIfaceA definitionEnv) 0 []
      (.sort .zero) (.sort one)) ∧
    Nonempty (HasTyA definitionEnv (iotaIfaceA definitionEnv) 0 []
      (.const 90 []) (.sort one)) ∧
    Nonempty (ConvA definitionEnv (iotaIfaceA definitionEnv) 0 []
      (.const 90 []) (.sort .zero) (.sort one)) ∧
    PairedTyGoal (model C) definitionEnv (iotaIfaceA definitionEnv) 0 []
      (.sort .zero) (.sort one) ∧
    ValuationRel zeroValuation zeroValuation ∧
    PairedRealises (model C) zeroValuation zeroValuation [] EnvI.bot EnvI.bot ∧
    PairedConvGoal (model C) definitionEnv (iotaIfaceA definitionEnv) 0 []
      (.const 90 []) (.sort .zero) (.sort one) :=
  ⟨⟨definition_admitted⟩, ⟨.nil⟩, rfl, rfl, rfl, rfl, rfl,
    ⟨source_body []⟩, ⟨source_member []⟩, ⟨source_delta []⟩,
    body_ih C [], ValuationRel.refl _, .nil _ _, delta_ih C []⟩

theorem concrete_delta_judgment :
    PairedJudgment (model InductiveCodes.legacyUniverseSystem)
      zeroValuation zeroValuation [] EnvI.bot EnvI.bot
      (.const 90 []) (.sort .zero) (.sort one) :=
  delta_ih InductiveCodes.legacyUniverseSystem [] .nil _ _ _ _
    (ValuationRel.refl _) (.nil _ _)

def opaqueMember : CheckedMemberA :=
  ⟨.opaqueM, 0, .sort one, some (.sort .zero), 0, none⟩

def opaqueEnv : ResolvedEnvA := extendEnvA emptyEnvA 91 opaqueMember

def opaque_admitted : EnvWfA (iotaIfaceA opaqueEnv) opaqueEnv :=
  .opaqueM emptyEnvA 91 (.sort one) (.sort .zero) two .empty rfl
    (.sort [] one) (.sort [] .zero) (fun _ => rfl) (fun _ => rfl) rfl rfl

theorem opaque_image (F : FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    ValueEq (EnvironmentEval.denote opaqueEnv F ν ρ (.const 91 []))
      (NeutralPER.neutralAtom 91) :=
  denote_opaque (m := opaqueMember) rfl rfl F ν ρ

theorem empty_axiom_image (F : FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    ValueEq (EnvironmentEval.denote TruthAxiomBoundary.badEnv F ν ρ
      TruthAxiomBoundary.badTerm) (NeutralPER.neutralAtom 81) :=
  denote_axiom (m := TruthAxiomBoundary.badAxiom) rfl rfl F ν ρ

theorem neutral_controls_inhabited :
    Nonempty (EnvWfA (iotaIfaceA opaqueEnv) opaqueEnv) ∧
    Nonempty (EnvWfA (iotaIfaceA TruthAxiomBoundary.badEnv) TruthAxiomBoundary.badEnv) ∧
    (∀ ν ρ, ValueEq (EnvironmentEval.denote opaqueEnv neutralFamilySyntax ν ρ (.const 91 []))
      (NeutralPER.neutralAtom 91)) ∧
    (∀ ν ρ, ValueEq (EnvironmentEval.denote TruthAxiomBoundary.badEnv neutralFamilySyntax ν ρ
      TruthAxiomBoundary.badTerm) (NeutralPER.neutralAtom 81)) :=
  ⟨⟨opaque_admitted⟩, ⟨TruthAxiomBoundary.badEnv_admitted _⟩,
    opaque_image neutralFamilySyntax, empty_axiom_image neutralFamilySyntax⟩

end Rcic.Declarative.Ann.LR3.EnvironmentEvalControls

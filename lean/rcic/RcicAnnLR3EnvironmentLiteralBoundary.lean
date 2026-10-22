import rcic.RcicAnnLR3EnvironmentEvalControls

/-!
# Literal expansions matter for evaluator agreement

The source literal zero expands to constant 1. An admitted environment can
define that reference to be `Prop : Type`. The environment-aware evaluator
therefore gives the literal that definition's image, while the inherited
fixture evaluator gives it the raw neutral numeral image.

Consequently, absence of a written `const` node is insufficient for whole
fragment agreement. `EnvironmentEval.CoreFree` excludes these hidden
references. This is an inhabited boundary for the proposed agreement
criterion, not a refutation of source typing, the environment-aware model,
or any external arm. Exact literal expansion is positively supplied by
`EnvironmentEval.denote_literal`. `closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.EnvironmentLiteralBoundary

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements EnvironmentEval

abbrev one : Level := .succ .zero
abbrev two : Level := .succ one

/-- A purely syntactic criterion that deliberately counts literals as
having no written constant nodes. It is not the evaluator's closure test. -/
def NoWrittenConstants : ExprA → Prop
  | .bvar _ | .sort _ | .lit _ => True
  | .const _ _ => False
  | .app f a => NoWrittenConstants f ∧ NoWrittenConstants a
  | .lam A _ b => NoWrittenConstants A ∧ NoWrittenConstants b
  | .pi A _ B _ => NoWrittenConstants A ∧ NoWrittenConstants B
  | .letE A v b => NoWrittenConstants A ∧ NoWrittenConstants v ∧ NoWrittenConstants b

def member : CheckedMemberA :=
  ⟨.definitionM, 0, .sort one, some (.sort .zero), 0, none⟩

def env : ResolvedEnvA := extendEnvA emptyEnvA 1 member

def admitted : EnvWfA (iotaIfaceA env) env :=
  .definitionM emptyEnvA 1 (.sort one) (.sort .zero) two .empty rfl
    (.sort [] one) (.sort [] .zero) (fun _ => rfl) (fun _ => rfl) rfl rfl

def source_expansion : HasTyA env (iotaIfaceA env) 0 [] (natExpandA 0) (.sort one) :=
  .const [] 1 [] member two rfl rfl rfl (.sort [] one)

def source_literal : HasTyA env (iotaIfaceA env) 0 [] (.lit 0) (.sort one) :=
  .lit [] 0 (.sort one) source_expansion

def model (C : CodeSystem) : AnnSemantics := annSemantics C env neutralFamilySyntax

theorem literal_image (C : CodeSystem) (ν : Valuation) (ρ : EnvI) :
    (model C).image ν [] ρ (.lit 0) = universeValue (some 0) := by
  change EnvironmentEval.denote env neutralFamilySyntax ν ρ (.lit 0) = _
  rw [NeutralCodes.valueEq_eq (denote_literal env neutralFamilySyntax ν ρ 0)]
  change EnvironmentEval.denote env neutralFamilySyntax ν ρ (.const 1 []) = _
  rw [NeutralCodes.valueEq_eq (denote_delta (E := env)
    (r := 1) (ls := []) (m := member) (b := .sort .zero)
    rfl rfl rfl neutralFamilySyntax ν ρ)]
  exact (model C).sort_image ν [] ρ .zero

theorem old_literal_image (ν : Valuation) (ρ : EnvI) :
    ValueEq (UnitModel.denote ν ρ (.lit 0)) (NeutralPER.neutralAtom 1) := by
  intro c
  constructor
  · intro hc
    rcases approxI_lit_inv hc with hc | hc
    · cases hc
      exact .bot _ _
    · exact (FunctionEval.constant_environment ρ EnvI.bot 1 [] c).mp hc
  · intro hc
    apply ApproxI.lit
    exact (FunctionEval.constant_environment ρ EnvI.bot 1 [] c).mpr hc

theorem literal_images_differ (C : CodeSystem) (ν : Valuation) (ρ : EnvI) :
    ¬ ValueEq ((model C).image ν [] ρ (.lit 0)) (UnitModel.denote ν ρ (.lit 0)) := by
  intro h
  have hs : SortMember (some 1) ((model C).image ν [] ρ (.lit 0)) := by
    rw [literal_image]
    exact sort_member EnvI.bot (some 0)
  exact NeutralPER.neutralAtom_not_sort_member 1 (some 1)
    (sortMember_congr (old_literal_image ν ρ) (sortMember_congr h hs))

theorem no_written_constants_agreement_refuted (C : CodeSystem) (ν : Valuation) (ρ : EnvI) :
    ¬ (∀ e, NoWrittenConstants e →
      ValueEq ((model C).image ν [] ρ e) (UnitModel.denote ν ρ e)) :=
  fun h => literal_images_differ C ν ρ (h (.lit 0) True.intro)

theorem inhabited_literal_boundary (C : CodeSystem) :
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 []) ∧
    env.members 1 = some member ∧
    member.bodyA = some (.sort .zero) ∧
    transparent member.mclass = true ∧
    NoWrittenConstants (.lit 0) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] (natExpandA 0) (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] (.lit 0) (.sort one)) ∧
    (∀ ν, ValuationRel ν ν) ∧
    (∀ ν, PairedRealises (model C) ν ν [] EnvI.bot EnvI.bot) ∧
    (∀ ν ρ, ¬ ValueEq ((model C).image ν [] ρ (.lit 0)) (UnitModel.denote ν ρ (.lit 0))) :=
  ⟨⟨admitted⟩, ⟨.nil⟩, rfl, rfl, rfl, True.intro,
    ⟨source_expansion⟩, ⟨source_literal⟩, ValuationRel.refl,
    fun _ => .nil _ _, literal_images_differ C⟩

end Rcic.Declarative.Ann.LR3.EnvironmentLiteralBoundary

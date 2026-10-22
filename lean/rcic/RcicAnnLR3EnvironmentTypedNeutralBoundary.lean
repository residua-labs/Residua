import rcic.RcicAnnLR3EnvironmentEval

/-!
# Raw neutral constants still need type-directed reflection

Environment-aware definition unfolding repairs delta. It does not make a
raw neutral atom a semantic type. An admitted axiom `A : Type` is the exact
control: its source type formation and paired child IH are supplied, but
the evaluator's fixed raw-atom axiom policy has no exact universe tag.

The theorem quantifies over every attached CodeSystem and every family
syntax hook. It refutes this raw-atom policy at the exact `Ty_const` arm;
it does not refute type-directed neutral reflection, admitted axioms, or
an environment-aware evaluator with semantic member interpretations.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.EnvironmentTypedNeutralBoundary

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements EnvironmentEval

abbrev one : Level := .succ .zero
abbrev two : Level := .succ one

def member : CheckedMemberA := ⟨.axiomM, 0, .sort one, none, 0, none⟩
def env : ResolvedEnvA := extendEnvA emptyEnvA 92 member

def admitted : EnvWfA (iotaIfaceA env) env :=
  .axiomM emptyEnvA 92 (.sort one) two .empty rfl (.sort [] one) (fun _ => rfl) rfl

def model (C : CodeSystem) (F : FamilySyntax) : AnnSemantics := annSemantics C env F

def source_type : HasTyA env (iotaIfaceA env) 0 [] (.sort one) (.sort two) :=
  .sort [] one

def source_member : HasTyA env (iotaIfaceA env) 0 [] (.const 92 []) (.sort one) :=
  .const [] 92 [] member two rfl rfl rfl source_type

theorem type_ih (C : CodeSystem) (F : FamilySyntax) :
    PairedTyGoal (model C F) env (iotaIfaceA env) 0 [] (.sort one) (.sort two) :=
  PairedArms.ty_sort_supplied (model C F) env (iotaIfaceA env) 0 [] one

def zeroValuation : Valuation := fun _ => some 0

theorem member_image (F : FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    ValueEq (EnvironmentEval.denote env F ν ρ (.const 92 []))
      (NeutralPER.neutralAtom 92) :=
  denote_axiom (m := member) rfl rfl F ν ρ

theorem raw_axiom_ty_const_refuted (C : CodeSystem) (F : FamilySyntax) :
    ¬ PairedArms.Ty_const (model C F) env (iotaIfaceA env) 0 := by
  intro h
  have hgoal := h [] 92 [] member two rfl rfl rfl source_type (type_ih C F)
  have hpaired := hgoal .nil zeroValuation zeroValuation EnvI.bot EnvI.bot
    (ValuationRel.refl _) (.nil _ _)
  have hsort : SortMember (some 1)
      (EnvironmentEval.denote env F zeroValuation EnvI.bot (.const 92 [])) :=
    (sort_judgment_membership hpaired.left_typing).1
  exact NeutralPER.neutralAtom_not_sort_member 92 (some 1)
    (sortMember_congr (member_image F zeroValuation EnvI.bot) hsort)

/-- Every source premise, the exact child IH, and the related worlds
are supplied. Arbitrary family hooks do not change the axiom policy. -/
theorem raw_axiom_boundary_inhabited (C : CodeSystem) (F : FamilySyntax) :
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 []) ∧
    env.members 92 = some member ∧
    member.mclass = .axiomM ∧
    ([] : List Level).length = member.arity ∧
    levelsBounded 0 ([] : List Level) = true ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 []
      (instantiateLevelsA [] member.mtypeA) (.sort two)) ∧
    PairedTyGoal (model C F) env (iotaIfaceA env) 0 []
      (instantiateLevelsA [] member.mtypeA) (.sort two) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] (.const 92 []) (.sort one)) ∧
    ValuationRel zeroValuation zeroValuation ∧
    PairedRealises (model C F) zeroValuation zeroValuation [] EnvI.bot EnvI.bot ∧
    (¬ PairedArms.Ty_const (model C F) env (iotaIfaceA env) 0) :=
  ⟨⟨admitted⟩, ⟨.nil⟩, rfl, rfl, rfl, rfl, ⟨source_type⟩,
    type_ih C F, ⟨source_member⟩, ValuationRel.refl _, .nil _ _,
    raw_axiom_ty_const_refuted C F⟩

end Rcic.Declarative.Ann.LR3.EnvironmentTypedNeutralBoundary

import rcic.RcicAnnLR3EnvironmentTelescopeInsertion

/-!
# An admitted type alias missed by the configured member policy

The source environment contains a transparent definition `A : Sort 1 :=
Sort 0` and an axiom `P : A`. Its admission, the const type-formation
premise, the delta conversion, and the converted typing `P : Sort 0`
are supplied below.

The single configured EnvironmentEval unfolds A correctly. Both current
syntactic member tests nevertheless reject P's stored type, a constant
application, and retain its raw neutral atom. That atom has no universe
tag. The exact paired Ty_const arm already fails, with its type-formation
IH supplied by the actual delta image and the sort arm.

This is a boundary of EnvironmentTelescopeInsertion's current syntactic
dispatch policy. It does not refute admitted aliases, neutral PERs, or a
type-directed policy that follows the admitted member's type conversion.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.ConfiguredAliasBoundary

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements

abbrev one : Level := .succ .zero
abbrev two : Level := .succ one

def aliasMember : CheckedMemberA :=
  ⟨.definitionM, 0, .sort one, some (.sort .zero), 0, none⟩

def aliasEnv : ResolvedEnvA := extendEnvA emptyEnvA 94 aliasMember

def member : CheckedMemberA := ⟨.axiomM, 0, .const 94 [], none, 0, none⟩

def env : ResolvedEnvA := extendEnvA aliasEnv 95 member

def alias_admitted (I : IotaIfaceA) : EnvWfA I aliasEnv :=
  .definitionM emptyEnvA 94 (.sort one) (.sort .zero) two .empty rfl
    (.sort [] one) (.sort [] .zero) (fun _ => rfl) (fun _ => rfl) rfl rfl

def alias_type_in_base (I : IotaIfaceA) (Γ : LCtxA) :
    HasTyA aliasEnv I 0 Γ (.const 94 []) (.sort one) :=
  .const Γ 94 [] aliasMember two rfl rfl rfl (.sort Γ one)

def admitted : EnvWfA (iotaIfaceA env) env :=
  .axiomM aliasEnv 95 (.const 94 []) one (alias_admitted _) rfl
    (alias_type_in_base _ []) (fun _ => rfl) rfl

def source_alias_type (Γ : LCtxA) :
    HasTyA env (iotaIfaceA env) 0 Γ (.const 94 []) (.sort one) :=
  .const Γ 94 [] aliasMember two rfl rfl rfl (.sort Γ one)

def source_member (Γ : LCtxA) :
    HasTyA env (iotaIfaceA env) 0 Γ (.const 95 []) (.const 94 []) :=
  .const Γ 95 [] member one rfl rfl rfl (source_alias_type Γ)

def source_delta (Γ : LCtxA) :
    ConvA env (iotaIfaceA env) 0 Γ (.const 94 []) (.sort .zero) (.sort one) :=
  .delta Γ 94 [] aliasMember (.sort .zero) rfl rfl rfl rfl rfl (.sort Γ .zero)

def source_converted (Γ : LCtxA) :
    HasTyA env (iotaIfaceA env) 0 Γ (.const 95 []) (.sort .zero) :=
  .conv Γ (.const 95 []) (.const 94 []) (.sort .zero) one one
    (source_member Γ) (source_alias_type Γ) (fun _ => rfl)
    (.sort Γ .zero) (source_delta Γ)

/-- Both syntactic recognition tests fail on this admitted alias type. -/
theorem policy_misses_alias :
    EnvironmentTelescopeInsertion.eligible member = none ∧
    EnvironmentMemberInsertion.eligibleLevel member = none ∧
    (EnvironmentTelescopeInsertion.internalView env).members 95 = some member :=
  ⟨rfl, rfl, rfl⟩

def model (C : CodeSystem) (F : EnvironmentEval.FamilySyntax) : AnnSemantics :=
  EnvironmentEval.annSemantics C (EnvironmentTelescopeInsertion.internalView env)
    (EnvironmentTelescopeInsertion.hook env F)

theorem alias_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    ValueEq (EnvironmentTelescopeInsertion.image env F ν ρ (.const 94 []))
      (EnvironmentTelescopeInsertion.image env F ν ρ (.sort .zero)) :=
  EnvironmentTelescopeInsertion.image_delta (m := aliasMember)
    (b := .sort .zero) rfl rfl rfl F ν ρ

theorem model_alias_image (C : CodeSystem) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (Γ : LCtxA) (ρ : EnvI) :
    (model C F).image ν Γ ρ (.const 94 []) =
      (model C F).image ν Γ ρ (.sort .zero) :=
  NeutralCodes.valueEq_eq (alias_image F ν ρ)

theorem member_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    ValueEq (EnvironmentTelescopeInsertion.image env F ν ρ (.const 95 []))
      (NeutralPER.neutralAtom 95) :=
  EnvironmentEval.denote_axiom (m := member) policy_misses_alias.2.2 rfl
    (EnvironmentTelescopeInsertion.hook env F) ν ρ

theorem member_not_sort_member (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (k : Option Nat) :
    ¬ SortMember k (EnvironmentTelescopeInsertion.image env F ν ρ (.const 95 [])) := by
  intro h
  exact NeutralPER.neutralAtom_not_sort_member 95 k
    (sortMember_congr (member_image F ν ρ) h)

/-- The exact type-formation IH for P is supplied at arbitrary paired
worlds. It uses the configured delta equation, not a fundamental premise. -/
theorem alias_type_ih (C : CodeSystem) (F : EnvironmentEval.FamilySyntax) (Γ : LCtxA) :
    PairedTyGoal (model C F) env (iotaIfaceA env) 0 Γ (.const 94 []) (.sort one) := by
  intro hΓ ν μ ρ σ hν hρ
  have h := PairedArms.ty_sort_supplied (model C F) env (iotaIfaceA env) 0 Γ .zero
    hΓ ν μ ρ σ hν hρ
  simpa only [PairedJudgment, model_alias_image] using h

def zeroValuation : Valuation := fun _ => some 0

theorem empty_paired_realises (C : CodeSystem) (F : EnvironmentEval.FamilySyntax) :
    PairedRealises (model C F) zeroValuation zeroValuation [] EnvI.bot EnvI.bot :=
  .nil _ _

theorem configured_ty_const_refuted (C : CodeSystem)
    (F : EnvironmentEval.FamilySyntax) :
    ¬ PairedArms.Ty_const (model C F) env (iotaIfaceA env) 0 := by
  intro h
  have hgoal := h [] 95 [] member one rfl rfl rfl
    (source_alias_type []) (alias_type_ih C F [])
  have hpaired := hgoal .nil zeroValuation zeroValuation EnvI.bot EnvI.bot
    (ValuationRel.refl _) (empty_paired_realises C F)
  have hj : Judgment (model C F) zeroValuation [] EnvI.bot
      (.const 95 []) (.const 95 []) (.const 94 []) := hpaired.left_typing
  have hs : Judgment (model C F) zeroValuation [] EnvI.bot
      (.const 95 []) (.const 95 []) (.sort .zero) := by
    simpa only [Judgment, model_alias_image] using hj
  exact member_not_sort_member F zeroValuation EnvI.bot (some 0)
    (sort_judgment_membership hs).1

theorem configured_fundamental_refuted (C : CodeSystem)
    (F : EnvironmentEval.FamilySyntax) :
    ¬ PairedFundamental (model C F) env (iotaIfaceA env) 0 := by
  intro h
  have hpaired := h.1 (source_converted []) .nil
    zeroValuation zeroValuation EnvI.bot EnvI.bot
    (ValuationRel.refl _) (empty_paired_realises C F)
  exact member_not_sort_member F zeroValuation EnvI.bot (some 0)
    (sort_judgment_membership hpaired.left_typing).1

/-- No selection of context environments can supply the source sort port
for this fixed configured evaluator: the failure is already at []. -/
theorem configured_sort_membership_refuted (F : EnvironmentEval.FamilySyntax)
    (choose : Valuation → LCtxA → EnvI) :
    ¬ AnnSortMembershipSound env (iotaIfaceA env) 0
      (fun ν Γ e => EnvironmentTelescopeInsertion.image env F ν (choose ν Γ) e) := by
  intro h
  exact member_not_sort_member F zeroValuation (choose zeroValuation []) (some 0)
    (h zeroValuation [] (.const 95 []) .zero .nil (source_converted [])).1

/-- The source environment and every exact const premise, including the
paired IH and empty paired realization, are inhabited at the one model. -/
theorem configured_alias_boundary_inhabited (C : CodeSystem)
    (F : EnvironmentEval.FamilySyntax) :
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 []) ∧
    env.members 95 = some member ∧
    ([] : List Level).length = member.arity ∧
    levelsBounded 0 ([] : List Level) = true ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 []
      (instantiateLevelsA [] member.mtypeA) (.sort one)) ∧
    PairedTyGoal (model C F) env (iotaIfaceA env) 0 []
      (instantiateLevelsA [] member.mtypeA) (.sort one) ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 []
      (.const 94 []) (.sort .zero) (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] (.const 95 []) (.sort .zero)) ∧
    ValuationRel zeroValuation zeroValuation ∧
    PairedRealises (model C F) zeroValuation zeroValuation [] EnvI.bot EnvI.bot ∧
    (¬ PairedArms.Ty_const (model C F) env (iotaIfaceA env) 0) :=
  ⟨⟨admitted⟩, ⟨.nil⟩, rfl, rfl, rfl, ⟨source_alias_type []⟩,
    alias_type_ih C F [], ⟨source_delta []⟩, ⟨source_converted []⟩,
    ValuationRel.refl _, empty_paired_realises C F, configured_ty_const_refuted C F⟩

end Rcic.Declarative.Ann.LR3.ConfiguredAliasBoundary

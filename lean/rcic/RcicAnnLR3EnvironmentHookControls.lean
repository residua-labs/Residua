import rcic.RcicAnnLR3EnvironmentPortConditions

/-!
# Inhabited controls for the explicit family-hook conditions

The source fixture is an admitted empty family at Sort 1 with one universe
parameter. All compared constant occurrences are source-typed; the two
equivalent universe lists also give an actual `ConvA.consts` derivation.

An open hook fails local closure and environment independence. A closed
hook that inspects level syntax fails the exact `eqNList` coherence port.
A closed hook that reads an unused ambient level parameter satisfies that
same-valuation port but fails the stronger evaluated-arguments port.
Thus admission alone supplies neither of these extra hook properties.

These are counterexamples to unrestricted raw evaluator equalities and to
named hook ports. Different raw values can be related by a PER, so no
source class, Fundamental statement or conversion arm is refuted here.
No external constructor arm is implemented. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.EnvironmentHookControls

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements
open EnvironmentEval EnvironmentPortConditions

abbrev one : Level := .succ .zero
abbrev two : Level := .succ one

/-- A phantom universe parameter is allowed by the actual group judgment.
The empty constructor list is explicit, not an assumed family signature. -/
def family : CheckedMemberA :=
  ⟨.inductiveM, 1, .sort one, none, 0, none⟩

def env : ResolvedEnvA := extendEnvA emptyEnvA 97 family

def familyView : FamViewA family where
  params := []
  indices := []
  sort := one
  stored := rfl
  nparams := rfl
  profile := .inr (fun _ => Nat.succ_pos 0)

def admitted : EnvWfA (iotaIfaceA env) env :=
  .group emptyEnvA 97 family two .empty rfl rfl (fun _ => rfl)
    (.sort [] one) rfl familyView [] rfl

def context_wf : CtxWfA env (iotaIfaceA env) 0 [] := .nil

theorem member_lookup : env.members 97 = some family := rfl
theorem member_hookClass : HookClass family := .inl rfl

abbrev leftLevels : List Level := [.zero]
abbrev rightLevels : List Level := [.imax .zero .zero]
abbrev leftTerm : ExprA := .const 97 leftLevels
abbrev rightTerm : ExprA := .const 97 rightLevels

theorem levels_equal : eqNList leftLevels rightLevels := ⟨fun _ => rfl, True.intro⟩

def type_formed : HasTyA env (iotaIfaceA env) 0 [] (.sort one) (.sort two) :=
  .sort [] one

def left_typed : HasTyA env (iotaIfaceA env) 0 [] leftTerm (.sort one) :=
  .const [] 97 leftLevels family two member_lookup rfl rfl type_formed

def right_typed : HasTyA env (iotaIfaceA env) 0 [] rightTerm (.sort one) :=
  .const [] 97 rightLevels family two member_lookup rfl rfl type_formed

def constants_convert : ConvA env (iotaIfaceA env) 0 [] leftTerm rightTerm (.sort one) :=
  .consts [] 97 leftLevels rightLevels family member_lookup rfl rfl rfl levels_equal right_typed

theorem member_has_no_body (ls : List Level) : definitionBody env 97 ls = none := rfl

/-- A common exact image lemma for the actual admitted family reference. -/
theorem denote_family (F : FamilySyntax) (ν : Valuation) (ρ : EnvI) (ls : List Level) :
    ValueEq (EnvironmentEval.denote env F ν ρ (.const 97 ls)) (denI ρ (F ν 97 ls family)) :=
  denote_rigid (member_has_no_body ls) F ν ρ

theorem native_constants_distinct (ρ σ : EnvI) {r s : Nat} (hne : r ≠ s) :
    ¬ ValueEq (denI ρ (.const r [])) (denI σ (.const s [])) := by
  intro h
  have hs := (h (.spine r [])).mp (ApproxI.const ρ r [])
  rcases approxI_const_inv hs with hb | he
  · cases hb
  · cases he
    exact hne rfl

def zeroValuation : Valuation := fun _ => some 0

def openHook : FamilySyntax := fun _ _ _ _ => .bvar 0

def nontrivialEnvironment : EnvI := EnvI.cons (NeutralPER.neutralAtom 701) EnvI.bot

theorem open_hook_not_liftFixed : ¬ HookLiftFixed env openHook := by
  intro h
  have he := h zeroValuation 97 leftLevels family member_lookup member_hookClass 0
  change (Expr.bvar 1 : Expr Nat) = .bvar 0 at he
  cases he

theorem open_hook_environments_differ :
    ¬ ValueEq (denI nontrivialEnvironment (openHook zeroValuation 97 leftLevels family))
      (denI EnvI.bot (openHook zeroValuation 97 leftLevels family)) := by
  intro h
  have hleft : denI nontrivialEnvironment (.bvar 0) (.spine 701 []) :=
    .bvar (NeutralPER.neutralAtom_observed 701)
  have hright := (h (.spine 701 [])).mp hleft
  rcases approxI_bvar_inv hright with hb | hb
  · cases hb
  · cases hb

theorem open_hook_not_environmentIndependent : ¬ HookEnvironmentIndependent env openHook :=
  fun h => open_hook_environments_differ
    (h zeroValuation 97 leftLevels family member_lookup member_hookClass nontrivialEnvironment EnvI.bot)

theorem open_hook_source_images_differ :
    ¬ ValueEq (EnvironmentEval.denote env openHook zeroValuation nontrivialEnvironment leftTerm)
      (EnvironmentEval.denote env openHook zeroValuation EnvI.bot leftTerm) := by
  intro h
  exact open_hook_environments_differ
    ((denote_family openHook zeroValuation nontrivialEnvironment leftLevels).symm.trans
      (h.trans (denote_family openHook zeroValuation EnvI.bot leftLevels)))

theorem open_hook_control_inhabited :
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 []) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] leftTerm (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] (.sort one) (.sort two)) ∧
    env.members 97 = some family ∧ HookClass family ∧
    DefinitionBodiesClosed env ∧ MemberLevelCompatibility env ∧
    (¬ HookLiftFixed env openHook) ∧ (¬ HookEnvironmentIndependent env openHook) ∧
    (¬ ValueEq (EnvironmentEval.denote env openHook zeroValuation nontrivialEnvironment leftTerm)
      (EnvironmentEval.denote env openHook zeroValuation EnvI.bot leftTerm)) :=
  ⟨⟨admitted⟩, ⟨context_wf⟩, ⟨left_typed⟩, ⟨type_formed⟩, member_lookup, member_hookClass,
    definitionBodiesClosed_of_envWfA admitted, memberLevelCompatibility_of_envWfA admitted,
    open_hook_not_liftFixed, open_hook_not_environmentIndependent, open_hook_source_images_differ⟩

/-- This hook is closed but distinguishes two definitionally different,
extensionally equal source level expressions. -/
def syntaxHook : FamilySyntax := fun _ _ ls _ =>
  match ls with
  | .zero :: _ => .const 701 []
  | _ => .const 702 []

theorem syntax_hook_liftFixed (E : ResolvedEnvA) : HookLiftFixed E syntaxHook := by
  intro _ _ ls _ _ _ _
  cases ls with
  | nil => rfl
  | cons l ls => cases l <;> rfl

theorem syntax_hook_environmentIndependent (E : ResolvedEnvA) :
    HookEnvironmentIndependent E syntaxHook := by
  intro _ _ ls _ _ _ ρ σ
  cases ls with
  | nil => exact FunctionEval.constant_environment ρ σ 702 []
  | cons l ls => cases l <;> exact FunctionEval.constant_environment ρ σ _ []

theorem syntax_hook_values_differ (ν : Valuation) (ρ σ : EnvI) :
    ¬ ValueEq (denI ρ (syntaxHook ν 97 leftLevels family))
      (denI σ (syntaxHook ν 97 rightLevels family)) :=
  native_constants_distinct ρ σ (by decide : 701 ≠ 702)

theorem syntax_hook_not_eqNCompatible : ¬ HookEqNCompatible env syntaxHook :=
  fun h => syntax_hook_values_differ zeroValuation EnvI.bot EnvI.bot
    (h zeroValuation 97 family member_lookup member_hookClass
      leftLevels rightLevels rfl rfl levels_equal EnvI.bot)

theorem syntax_hook_not_evaluatedArgsCompatible : ¬ HookEvaluatedArgsCompatible env syntaxHook :=
  fun h => syntax_hook_not_eqNCompatible (hookEqNCompatible_of_evaluatedArgs h)

theorem syntax_hook_source_images_differ (ν : Valuation) (ρ σ : EnvI) :
    ¬ ValueEq (EnvironmentEval.denote env syntaxHook ν ρ leftTerm) (EnvironmentEval.denote env syntaxHook ν σ rightTerm) := by
  intro h
  exact syntax_hook_values_differ ν ρ σ
    ((denote_family syntaxHook ν ρ leftLevels).symm.trans
      (h.trans (denote_family syntaxHook ν σ rightLevels)))

theorem syntax_hook_control_inhabited :
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 []) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] leftTerm (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] rightTerm (.sort one)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] (.sort one) (.sort two)) ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 [] leftTerm rightTerm (.sort one)) ∧
    env.members 97 = some family ∧ HookClass family ∧
    HookLiftFixed env syntaxHook ∧ HookEnvironmentIndependent env syntaxHook ∧
    eqNList leftLevels rightLevels ∧
    (¬ HookEqNCompatible env syntaxHook) ∧
    (¬ HookEvaluatedArgsCompatible env syntaxHook) ∧
    (¬ ValueEq (EnvironmentEval.denote env syntaxHook zeroValuation EnvI.bot leftTerm)
      (EnvironmentEval.denote env syntaxHook zeroValuation EnvI.bot rightTerm)) :=
  ⟨⟨admitted⟩, ⟨context_wf⟩, ⟨left_typed⟩, ⟨right_typed⟩, ⟨type_formed⟩,
    ⟨constants_convert⟩, member_lookup, member_hookClass,
    syntax_hook_liftFixed env, syntax_hook_environmentIndependent env, levels_equal,
    syntax_hook_not_eqNCompatible, syntax_hook_not_evaluatedArgsCompatible,
    syntax_hook_source_images_differ zeroValuation EnvI.bot EnvI.bot⟩

/-- Same-valuation level coherence does not prohibit dependence on an
ambient parameter unused by the actual member argument list. -/
def ambientHook : FamilySyntax := fun ν _ _ _ =>
  if ν 0 = some 0 then .const 701 [] else .const 702 []

def oneValuation : Valuation := fun _ => some 1

theorem ambient_hook_liftFixed (E : ResolvedEnvA) : HookLiftFixed E ambientHook := by
  intro ν _ _ _ _ _ c
  by_cases h : ν 0 = some 0 <;> simp [ambientHook, h, lift]

theorem ambient_hook_environmentIndependent (E : ResolvedEnvA) :
    HookEnvironmentIndependent E ambientHook := by
  intro ν _ _ _ _ _ ρ σ
  by_cases h : ν 0 = some 0
  · simpa [ambientHook, h] using FunctionEval.constant_environment ρ σ 701 []
  · simpa [ambientHook, h] using FunctionEval.constant_environment ρ σ 702 []

theorem ambient_hook_eqNCompatible (E : ResolvedEnvA) : HookEqNCompatible E ambientHook :=
  fun _ _ _ _ _ _ _ _ _ _ _ => ValueEq.refl _

theorem ambient_evaluated_args_equal :
    EvaluatedArgs zeroValuation oneValuation leftLevels leftLevels := rfl

theorem ambient_hook_values_differ :
    ¬ ValueEq (denI EnvI.bot (ambientHook zeroValuation 97 leftLevels family))
      (denI EnvI.bot (ambientHook oneValuation 97 leftLevels family)) :=
  native_constants_distinct EnvI.bot EnvI.bot (by decide : 701 ≠ 702)

theorem ambient_hook_not_evaluatedArgsCompatible :
    ¬ HookEvaluatedArgsCompatible env ambientHook :=
  fun h => ambient_hook_values_differ
    (h zeroValuation oneValuation 97 family member_lookup member_hookClass
      leftLevels leftLevels rfl rfl ambient_evaluated_args_equal EnvI.bot)

theorem left_source_instantiation : instantiateLevelsA leftLevels leftTerm = leftTerm := rfl

theorem ambient_hook_not_levelInstantiationCompatible :
    ¬ HookLevelInstantiationCompatible env ambientHook := by
  intro h
  have he := h oneValuation 97 family member_lookup member_hookClass
    leftLevels leftLevels rfl EnvI.bot
  exact native_constants_distinct EnvI.bot EnvI.bot (by decide : 702 ≠ 701) he

/-- Every source-side premise and the weaker hook conditions are inhabited;
only the expressly stronger cross-valuation port is refuted. -/
theorem stronger_hook_port_control_inhabited :
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 []) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] leftTerm (.sort one)) ∧
    env.members 97 = some family ∧ HookClass family ∧
    HookLiftFixed env ambientHook ∧ HookEnvironmentIndependent env ambientHook ∧
    HookEqNCompatible env ambientHook ∧
    EvaluatedArgs zeroValuation oneValuation leftLevels leftLevels ∧
    instantiateLevelsA leftLevels leftTerm = leftTerm ∧
    (¬ HookEvaluatedArgsCompatible env ambientHook) ∧
    (¬ HookLevelInstantiationCompatible env ambientHook) :=
  ⟨⟨admitted⟩, ⟨context_wf⟩, ⟨left_typed⟩, member_lookup, member_hookClass,
    ambient_hook_liftFixed env, ambient_hook_environmentIndependent env,
    ambient_hook_eqNCompatible env, ambient_evaluated_args_equal,
    left_source_instantiation, ambient_hook_not_evaluatedArgsCompatible,
    ambient_hook_not_levelInstantiationCompatible⟩

end Rcic.Declarative.Ann.LR3.EnvironmentHookControls

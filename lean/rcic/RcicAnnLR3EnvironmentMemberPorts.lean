import rcic.RcicAnnLR3EnvironmentMemberInsertion
import rcic.RcicAnnLR3EnvironmentPortConditions

/-!
# Environment and hook ports survive compositional member insertion

The internal member view is not asserted admitted. Its actual stored data
inherit `EnvClosedA` and `EnvLevelsA` from the source environment, and its
selected bodies are exactly the source bodies. Native typed member values
are syntactically closed, locally environment-independent, and depend only
on the evaluated stored result level. Consequently the constructed hook
inherits the explicit family-hook ports from its fallback hook.

The level-instantiation and evaluated-arguments ports use the stored type's
actual level bound. That bound is supplied by source admission, including
when the current internal view itself is not an admitted source environment.
No external evaluator or source constructor arm is proved here.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.EnvironmentMemberPorts

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements EnvironmentEval EnvironmentPortConditions
open EnvironmentMemberInsertion

theorem internalView_lookup {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    (h : (internalView E).members r = some m) :
    ∃ source, E.members r = some source ∧ m = route source := by
  cases hs : E.members r with
  | none => simp [internalView, hs] at h
  | some source =>
      have he : route source = m := by simpa [internalView, hs] using h
      exact ⟨source, rfl, he.symm⟩

theorem internalView_closed {E : ResolvedEnvA} (hE : EnvClosedA E) :
    EnvClosedA (internalView E) := by
  intro r m hm
  rcases internalView_lookup hm with ⟨source, hs, rfl⟩
  constructor
  · rw [route_type]
    exact (hE r source hs).1
  · intro b hb
    rw [route_body] at hb
    exact (hE r source hs).2 b hb

theorem internalView_levels {E : ResolvedEnvA} (hE : EnvLevelsA E) :
    EnvLevelsA (internalView E) := by
  intro r m hm
  rcases internalView_lookup hm with ⟨source, hs, rfl⟩
  rw [route_type, route_arity, route_body]
  exact hE r source hs

theorem internalView_body_conditions {E : ResolvedEnvA} {I : IotaIfaceA}
    (hE : EnvWfA I E) :
    StoredTypesClosed (internalView E) ∧ StoredBodiesClosed (internalView E) ∧
    StoredTypesLevelBounded (internalView E) ∧ StoredBodiesLevelBounded (internalView E) ∧
    DefinitionBodiesClosed (internalView E) ∧ MemberLevelCompatibility (internalView E) := by
  have hc := internalView_closed (envWfA_closed hE)
  have hl := internalView_levels (envWfA_levels hE)
  refine ⟨fun r m hm => (hc r m hm).1, fun r m hm b hb => (hc r m hm).2 b hb,
    fun r m hm => (hl r m hm).1, fun r m hm b hb => (hl r m hm).2 b hb, ?_, ?_⟩
  · intro r ls b hb
    rw [definitionBody_preserved] at hb
    exact definitionBodiesClosed_of_envWfA hE r ls b hb
  · intro r m hm ms ls hlen
    exact ⟨instLevels_mtype hl hm hlen ls, fun b hb => instLevels_mbody hl hm hb hlen ls⟩

theorem native_term_liftFixed (k : Option Nat) (name c : Nat) :
    lift c 1 (NativeMemberValues.term k name) = NativeMemberValues.term k name := rfl

theorem native_term_environmentIndependent (k : Option Nat) (name : Nat) (ρ σ : EnvI) :
    ValueEq (denI ρ (NativeMemberValues.term k name))
      (denI σ (NativeMemberValues.term k name)) :=
  (NativeMemberValues.environment ρ k name).trans (NativeMemberValues.environment σ k name).symm

theorem eligible_type {m : CheckedMemberA} {l : Level}
    (h : eligibleLevel m = some l) : m.mtypeA = .sort l := by
  rcases m with ⟨mc, ar, ty, body, np, norm⟩
  cases mc <;> cases ty <;> simp_all [eligibleLevel]

theorem eligible_levelBounded {E : ResolvedEnvA} (hE : EnvLevelsA E)
    {r : Nat} {m : CheckedMemberA} {l : Level}
    (hm : E.members r = some m) (hl : eligibleLevel m = some l) :
    levelBounded m.arity l = true := by
  have hb := (hE r m hm).1
  rw [eligible_type hl] at hb
  exact hb

/-- A bounded stored result level reads only the supplied member arguments.
This helper compares the full Option Nat evaluations, including `none`. -/
theorem eval_instLevel_of_evaluatedArgs {ν μ : Valuation} {ls ms : List Level} {n : Nat}
    (hl : ls.length = n) (hr : ms.length = n) (ha : EvaluatedArgs ν μ ls ms) :
    ∀ l : Level, levelBounded n l = true →
      eval ν (instLevel ls l) = eval μ (instLevel ms l)
  | .zero, _ => rfl
  | .succ l, h => by
      change (eval ν (instLevel ls l)).map (· + 1) = (eval μ (instLevel ms l)).map (· + 1)
      rw [eval_instLevel_of_evaluatedArgs hl hr ha l h]
  | .max a b, h => by
      change ((eval ν (instLevel ls a)).bind fun x => (eval ν (instLevel ls b)).map (max x ·)) =
        ((eval μ (instLevel ms a)).bind fun x => (eval μ (instLevel ms b)).map (max x ·))
      rw [eval_instLevel_of_evaluatedArgs hl hr ha a (boolAnd_left h),
        eval_instLevel_of_evaluatedArgs hl hr ha b (boolAnd_right h)]
  | .imax a b, h => by
      change ((eval ν (instLevel ls b)).bind fun y =>
        if y = 0 then some 0 else (eval ν (instLevel ls a)).map fun x => max x y) =
        ((eval μ (instLevel ms b)).bind fun y =>
          if y = 0 then some 0 else (eval μ (instLevel ms a)).map fun x => max x y)
      rw [eval_instLevel_of_evaluatedArgs hl hr ha a (boolAnd_left h),
        eval_instLevel_of_evaluatedArgs hl hr ha b (boolAnd_right h)]
  | .param i, h => by
      have hi : i < n := of_decide_eq_true h
      have hil : i < ls.length := by rw [hl]; exact hi
      have hir : i < ms.length := by rw [hr]; exact hi
      have he := congrArg (fun xs : List (Option Nat) => xs[i]?) ha
      simp only [List.getElem?_map, List.getElem?_eq_getElem hil,
        List.getElem?_eq_getElem hir, Option.map_some] at he
      simpa only [instLevel_param, List.getElem?_eq_getElem hil,
        List.getElem?_eq_getElem hir, Option.getD_some] using Option.some.inj he

theorem hook_liftFixed {E : ResolvedEnvA} {F : FamilySyntax}
    (hF : HookLiftFixed E F) : HookLiftFixed (internalView E) (hook E F) := by
  intro ν r ls m hm hc c
  rcases internalView_lookup hm with ⟨source, hs, rfl⟩
  cases he : eligibleLevel source with
  | none =>
      have hc' : HookClass source := by simpa [route, he] using hc
      simpa [hook, hs, he] using hF ν r ls source hs hc' c
  | some l =>
      simpa [hook, hs, he] using native_term_liftFixed (eval ν (instLevel ls l)) r c

theorem hook_environmentIndependent {E : ResolvedEnvA} {F : FamilySyntax}
    (hF : HookEnvironmentIndependent E F) :
    HookEnvironmentIndependent (internalView E) (hook E F) := by
  intro ν r ls m hm hc ρ σ
  rcases internalView_lookup hm with ⟨source, hs, rfl⟩
  cases he : eligibleLevel source with
  | none =>
      have hc' : HookClass source := by simpa [route, he] using hc
      simpa [hook, hs, he] using hF ν r ls source hs hc' ρ σ
  | some l =>
      simpa [hook, hs, he] using native_term_environmentIndependent (eval ν (instLevel ls l)) r ρ σ

theorem hook_eqNCompatible {E : ResolvedEnvA} {F : FamilySyntax}
    (hF : HookEqNCompatible E F) : HookEqNCompatible (internalView E) (hook E F) := by
  intro ν r m hm hc ls ms hl hr heq ρ
  rcases internalView_lookup hm with ⟨source, hs, rfl⟩
  rw [route_arity] at hl hr
  cases he : eligibleLevel source with
  | none =>
      have hc' : HookClass source := by simpa [route, he] using hc
      simpa [hook, hs, he] using hF ν r source hs hc' ls ms hl hr heq ρ
  | some l =>
      simp only [hook, hs, he]
      rw [instLevel_eqNList heq l ν]
      exact ValueEq.refl _

theorem hook_evaluatedArgsCompatible {E : ResolvedEnvA} {F : FamilySyntax}
    (hE : EnvLevelsA E) (hF : HookEvaluatedArgsCompatible E F) :
    HookEvaluatedArgsCompatible (internalView E) (hook E F) := by
  intro ν μ r m hm hc ls ms hl hr heq ρ
  rcases internalView_lookup hm with ⟨source, hs, rfl⟩
  rw [route_arity] at hl hr
  cases he : eligibleLevel source with
  | none =>
      have hc' : HookClass source := by simpa [route, he] using hc
      simpa [hook, hs, he] using hF ν μ r source hs hc' ls ms hl hr heq ρ
  | some l =>
      simp only [hook, hs, he]
      rw [eval_instLevel_of_evaluatedArgs hl hr heq l (eligible_levelBounded hE hs he)]
      exact ValueEq.refl _

theorem hook_levelInstantiationCompatible {E : ResolvedEnvA} {F : FamilySyntax}
    (hE : EnvLevelsA E) (hF : HookLevelInstantiationCompatible E F) :
    HookLevelInstantiationCompatible (internalView E) (hook E F) := by
  intro ν r m hm hc ls ms hlen ρ
  rcases internalView_lookup hm with ⟨source, hs, rfl⟩
  rw [route_arity] at hlen
  cases he : eligibleLevel source with
  | none =>
      have hc' : HookClass source := by simpa [route, he] using hc
      simpa [hook, hs, he] using hF ν r source hs hc' ls ms hlen ρ
  | some l =>
      have hb : levelBounded ms.length l = true := by
        rw [hlen]
        exact eligible_levelBounded hE hs he
      simp only [hook, hs, he]
      rw [← instLevel_instLevel ls ms l hb, eval_instLevel ls ν (instLevel ms l)]
      exact ValueEq.refl _

/-- All ports for the actual constructed member policy with default neutral
family hooks. Source admission supplies the only environment assumption. -/
theorem default_hook_conditions {E : ResolvedEnvA} {I : IotaIfaceA} (hE : EnvWfA I E) :
    HookLiftFixed (internalView E) (hook E neutralFamilySyntax) ∧
    HookEnvironmentIndependent (internalView E) (hook E neutralFamilySyntax) ∧
    HookEqNCompatible (internalView E) (hook E neutralFamilySyntax) ∧
    HookEvaluatedArgsCompatible (internalView E) (hook E neutralFamilySyntax) ∧
    HookLevelInstantiationCompatible (internalView E) (hook E neutralFamilySyntax) :=
  ⟨hook_liftFixed (neutral_hook_liftFixed E),
    hook_environmentIndependent (neutral_hook_environmentIndependent E),
    hook_eqNCompatible (neutral_hook_eqNCompatible E),
    hook_evaluatedArgsCompatible (envWfA_levels hE) (neutral_hook_evaluatedArgsCompatible E),
    hook_levelInstantiationCompatible (envWfA_levels hE) (neutral_hook_levelInstantiationCompatible E)⟩

end Rcic.Declarative.Ann.LR3.EnvironmentMemberPorts

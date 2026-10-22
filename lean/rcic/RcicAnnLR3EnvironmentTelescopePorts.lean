import rcic.RcicAnnLR3EnvironmentTelescopeInsertion
import rcic.RcicAnnLR3EnvironmentMemberPorts

/-!
# Exact hook ports for the composed sort-ending telescope policy

Both internal lookup views preserve the source's closed and level-bounded
member data. A syntactic telescope's final stored level inherits its bound
from the stored type. The native lambda tower is closed and independent of
the local environment, and all level compatibility comes from the evaluated
final level. These facts supply the hook conditions for the actual composed
EnvironmentEval configuration, including its default neutral fallback.

No internal view is claimed source-admitted. No external evaluator law,
general member telescope semantics or source constructor arm is supplied.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.EnvironmentTelescopePorts

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements EnvironmentEval EnvironmentPortConditions
open EnvironmentTelescopeInsertion

theorem telescopeView_lookup {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    (h : (telescopeView E).members r = some m) :
    ∃ source, E.members r = some source ∧ m = route source := by
  cases hs : E.members r with
  | none => simp [telescopeView, hs] at h
  | some source =>
      have he : route source = m := by simpa [telescopeView, hs] using h
      exact ⟨source, rfl, he.symm⟩

theorem telescopeView_closed {E : ResolvedEnvA} (hE : EnvClosedA E) :
    EnvClosedA (telescopeView E) := by
  intro r m hm
  rcases telescopeView_lookup hm with ⟨source, hs, rfl⟩
  constructor
  · rw [route_type]
    exact (hE r source hs).1
  · intro b hb
    rw [route_body] at hb
    exact (hE r source hs).2 b hb

theorem telescopeView_levels {E : ResolvedEnvA} (hE : EnvLevelsA E) :
    EnvLevelsA (telescopeView E) := by
  intro r m hm
  rcases telescopeView_lookup hm with ⟨source, hs, rfl⟩
  rw [route_type, route_arity, route_body]
  exact hE r source hs

theorem internalView_closed {E : ResolvedEnvA} (hE : EnvClosedA E) :
    EnvClosedA (internalView E) :=
  EnvironmentMemberPorts.internalView_closed (telescopeView_closed hE)

theorem internalView_levels {E : ResolvedEnvA} (hE : EnvLevelsA E) :
    EnvLevelsA (internalView E) :=
  EnvironmentMemberPorts.internalView_levels (telescopeView_levels hE)

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

theorem native_term_liftFixed (k : Option Nat) (name : Nat) :
    ∀ depth c : Nat, lift c 1 (NativeTelescopeValues.term depth k name) =
      NativeTelescopeValues.term depth k name
  | 0, c => EnvironmentMemberPorts.native_term_liftFixed k name c
  | depth + 1, c => by
      simp only [NativeTelescopeValues.term, lift, native_term_liftFixed k name depth (c + 1)]

theorem native_term_environmentIndependent (depth : Nat) (k : Option Nat) (name : Nat)
    (ρ σ : EnvI) : ValueEq (denI ρ (NativeTelescopeValues.term depth k name))
      (denI σ (NativeTelescopeValues.term depth k name)) :=
  (NativeTelescopeValues.environment depth ρ k name).trans
    (NativeTelescopeValues.environment depth σ k name).symm

/-- Extracting a telescope tail does not introduce a level outside the
stored type's actual bound. The codomain syntax remains explicit. -/
theorem sortTail_levelBounded (n : Nat) :
    ∀ (A : ExprA) (depth : Nat) (l : Level),
      exprLevelsBoundedA n A = true → sortTail A = some (depth, l) →
        levelBounded n l = true
  | .sort l', depth, l, hb, ht => by
      have he : (0, l') = (depth, l) := Option.some.inj ht
      cases he
      exact hb
  | .pi _ _ B _, depth, l, hb, ht => by
      cases hs : sortTail B with
      | none => simp [sortTail, hs] at ht
      | some p =>
          rcases p with ⟨d, v⟩
          have he : (d + 1, v) = (depth, l) := by simpa [sortTail, hs] using ht
          have hv : v = l := congrArg Prod.snd he
          rw [← hv]
          exact sortTail_levelBounded n B d v (boolAnd_right (boolAnd_left hb)) hs
  | .bvar _, _, _, _, ht => by cases ht
  | .const _ _, _, _, _, ht => by cases ht
  | .app _ _, _, _, _, ht => by cases ht
  | .lam _ _ _, _, _, _, ht => by cases ht
  | .letE _ _ _, _, _, _, ht => by cases ht
  | .lit _, _, _, _, ht => by cases ht

theorem eligible_tail {m : CheckedMemberA} {p : Nat × Level}
    (h : eligible m = some p) : sortTail m.mtypeA = some p := by
  unfold eligible at h
  split at h <;> simp_all

theorem eligible_levelBounded {E : ResolvedEnvA} (hE : EnvLevelsA E)
    {r : Nat} {m : CheckedMemberA} {depth : Nat} {l : Level}
    (hm : E.members r = some m) (hl : eligible m = some (depth, l)) :
    levelBounded m.arity l = true :=
  sortTail_levelBounded m.arity m.mtypeA depth l (hE r m hm).1 (eligible_tail hl)

theorem telescopeHook_liftFixed {E : ResolvedEnvA} {F : FamilySyntax}
    (hF : HookLiftFixed E F) : HookLiftFixed (telescopeView E) (telescopeHook E F) := by
  intro ν r ls m hm hc c
  rcases telescopeView_lookup hm with ⟨source, hs, rfl⟩
  cases he : eligible source with
  | none =>
      have hc' : HookClass source := by simpa [route, he] using hc
      simpa [telescopeHook, hs, he] using hF ν r ls source hs hc' c
  | some p =>
      rcases p with ⟨depth, l⟩
      simpa [telescopeHook, hs, he] using native_term_liftFixed (eval ν (instLevel ls l)) r depth c

theorem telescopeHook_environmentIndependent {E : ResolvedEnvA} {F : FamilySyntax}
    (hF : HookEnvironmentIndependent E F) :
    HookEnvironmentIndependent (telescopeView E) (telescopeHook E F) := by
  intro ν r ls m hm hc ρ σ
  rcases telescopeView_lookup hm with ⟨source, hs, rfl⟩
  cases he : eligible source with
  | none =>
      have hc' : HookClass source := by simpa [route, he] using hc
      simpa [telescopeHook, hs, he] using hF ν r ls source hs hc' ρ σ
  | some p =>
      rcases p with ⟨depth, l⟩
      simpa [telescopeHook, hs, he] using
        native_term_environmentIndependent depth (eval ν (instLevel ls l)) r ρ σ

theorem telescopeHook_eqNCompatible {E : ResolvedEnvA} {F : FamilySyntax}
    (hF : HookEqNCompatible E F) :
    HookEqNCompatible (telescopeView E) (telescopeHook E F) := by
  intro ν r m hm hc ls ms hl hr heq ρ
  rcases telescopeView_lookup hm with ⟨source, hs, rfl⟩
  rw [route_arity] at hl hr
  cases he : eligible source with
  | none =>
      have hc' : HookClass source := by simpa [route, he] using hc
      simpa [telescopeHook, hs, he] using hF ν r source hs hc' ls ms hl hr heq ρ
  | some p =>
      rcases p with ⟨depth, l⟩
      simp only [telescopeHook, hs, he]
      rw [instLevel_eqNList heq l ν]
      exact ValueEq.refl _

theorem telescopeHook_evaluatedArgsCompatible {E : ResolvedEnvA} {F : FamilySyntax}
    (hE : EnvLevelsA E) (hF : HookEvaluatedArgsCompatible E F) :
    HookEvaluatedArgsCompatible (telescopeView E) (telescopeHook E F) := by
  intro ν μ r m hm hc ls ms hl hr heq ρ
  rcases telescopeView_lookup hm with ⟨source, hs, rfl⟩
  rw [route_arity] at hl hr
  cases he : eligible source with
  | none =>
      have hc' : HookClass source := by simpa [route, he] using hc
      simpa [telescopeHook, hs, he] using hF ν μ r source hs hc' ls ms hl hr heq ρ
  | some p =>
      rcases p with ⟨depth, l⟩
      simp only [telescopeHook, hs, he]
      rw [EnvironmentMemberPorts.eval_instLevel_of_evaluatedArgs hl hr heq l
        (eligible_levelBounded hE hs he)]
      exact ValueEq.refl _

theorem telescopeHook_levelInstantiationCompatible {E : ResolvedEnvA} {F : FamilySyntax}
    (hE : EnvLevelsA E) (hF : HookLevelInstantiationCompatible E F) :
    HookLevelInstantiationCompatible (telescopeView E) (telescopeHook E F) := by
  intro ν r m hm hc ls ms hlen ρ
  rcases telescopeView_lookup hm with ⟨source, hs, rfl⟩
  rw [route_arity] at hlen
  cases he : eligible source with
  | none =>
      have hc' : HookClass source := by simpa [route, he] using hc
      simpa [telescopeHook, hs, he] using hF ν r source hs hc' ls ms hlen ρ
  | some p =>
      rcases p with ⟨depth, l⟩
      have hb : levelBounded ms.length l = true := by
        rw [hlen]
        exact eligible_levelBounded hE hs he
      simp only [telescopeHook, hs, he]
      rw [← instLevel_instLevel ls ms l hb, eval_instLevel ls ν (instLevel ms l)]
      exact ValueEq.refl _

theorem hook_liftFixed {E : ResolvedEnvA} {F : FamilySyntax}
    (hF : HookLiftFixed E F) : HookLiftFixed (internalView E) (hook E F) :=
  EnvironmentMemberPorts.hook_liftFixed (telescopeHook_liftFixed hF)

theorem hook_environmentIndependent {E : ResolvedEnvA} {F : FamilySyntax}
    (hF : HookEnvironmentIndependent E F) :
    HookEnvironmentIndependent (internalView E) (hook E F) :=
  EnvironmentMemberPorts.hook_environmentIndependent (telescopeHook_environmentIndependent hF)

theorem hook_eqNCompatible {E : ResolvedEnvA} {F : FamilySyntax}
    (hF : HookEqNCompatible E F) : HookEqNCompatible (internalView E) (hook E F) :=
  EnvironmentMemberPorts.hook_eqNCompatible (telescopeHook_eqNCompatible hF)

theorem hook_evaluatedArgsCompatible {E : ResolvedEnvA} {F : FamilySyntax}
    (hE : EnvLevelsA E) (hF : HookEvaluatedArgsCompatible E F) :
    HookEvaluatedArgsCompatible (internalView E) (hook E F) :=
  EnvironmentMemberPorts.hook_evaluatedArgsCompatible (telescopeView_levels hE)
    (telescopeHook_evaluatedArgsCompatible hE hF)

theorem hook_levelInstantiationCompatible {E : ResolvedEnvA} {F : FamilySyntax}
    (hE : EnvLevelsA E) (hF : HookLevelInstantiationCompatible E F) :
    HookLevelInstantiationCompatible (internalView E) (hook E F) :=
  EnvironmentMemberPorts.hook_levelInstantiationCompatible (telescopeView_levels hE)
    (telescopeHook_levelInstantiationCompatible hE hF)

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

end Rcic.Declarative.Ann.LR3.EnvironmentTelescopePorts

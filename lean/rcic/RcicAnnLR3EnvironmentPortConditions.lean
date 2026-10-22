import rcic.RcicAnnLR3EnvironmentEval
import rcic.RcicAnnSubst
import rcic.RcicAnnLevels

/-!
# Admission supplies and exact family-hook ports for EnvironmentEval

Stored member closure, level bounds, instantiated body closure and nested
member-level instantiation are consequences of the actual environment
judgment. Family hooks are a separate evaluator argument: their local
environment independence and level coherence do not follow from admission.

The native syntactic `HookLiftFixed` port is a sufficient closure condition;
`HookEnvironmentIndependent` states the exact denotational independence.
`HookEqNCompatible` is the same-valuation constant-congruence port.
`HookEvaluatedArgsCompatible` is deliberately stronger: it identifies hooks
under different ambient valuations whenever their member arguments evaluate
equally. The inherited paired `ValuationRel` is pointwise equality, so every
hook respects it without an extra premise.

All hook ports are restricted to actual members whose class consults the
hook. The default neutral hook supplies every port below. These leaf laws
are not the external substitution, lifting, literal or constructor arms.
No Fundamental theorem or unrestricted family semantics is supplied.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.EnvironmentPortConditions

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements EnvironmentEval

def SourceClosed (e : ExprA) : Prop := ∀ c, liftA c 1 e = e

def StoredTypesClosed (E : ResolvedEnvA) : Prop :=
  ∀ r m, E.members r = some m → SourceClosed m.mtypeA

def StoredBodiesClosed (E : ResolvedEnvA) : Prop :=
  ∀ r m, E.members r = some m →
    ∀ b, m.bodyA = some b → SourceClosed b

def StoredTypesLevelBounded (E : ResolvedEnvA) : Prop :=
  ∀ r m, E.members r = some m → exprLevelsBoundedA m.arity m.mtypeA = true

def StoredBodiesLevelBounded (E : ResolvedEnvA) : Prop :=
  ∀ r m, E.members r = some m →
    ∀ b, m.bodyA = some b → exprLevelsBoundedA m.arity b = true

def DefinitionBodiesClosed (E : ResolvedEnvA) : Prop :=
  ∀ r ls b, definitionBody E r ls = some b → SourceClosed b

/-- The stored type and body obey the exact nested-instantiation equations
at the member's declared arity. There is no total-valuation restriction. -/
def MemberLevelCompatibility (E : ResolvedEnvA) : Prop :=
  ∀ r m, E.members r = some m →
    ∀ ms ls : List Level, ms.length = m.arity →
      instantiateLevelsA ls (instantiateLevelsA ms m.mtypeA) =
        instantiateLevelsA (ms.map (instLevel ls)) m.mtypeA ∧
      ∀ b, m.bodyA = some b →
        instantiateLevelsA ls (instantiateLevelsA ms b) =
          instantiateLevelsA (ms.map (instLevel ls)) b

theorem storedTypesClosed_of_envWfA {E : ResolvedEnvA} {I : IotaIfaceA}
    (hE : EnvWfA I E) : StoredTypesClosed E :=
  fun r m hm => (envWfA_closed hE r m hm).1

theorem storedBodiesClosed_of_envWfA {E : ResolvedEnvA} {I : IotaIfaceA}
    (hE : EnvWfA I E) : StoredBodiesClosed E :=
  fun r m hm b hb => (envWfA_closed hE r m hm).2 b hb

theorem storedTypesLevelBounded_of_envWfA {E : ResolvedEnvA} {I : IotaIfaceA}
    (hE : EnvWfA I E) : StoredTypesLevelBounded E :=
  fun r m hm => (envWfA_levels hE r m hm).1

theorem storedBodiesLevelBounded_of_envWfA {E : ResolvedEnvA} {I : IotaIfaceA}
    (hE : EnvWfA I E) : StoredBodiesLevelBounded E :=
  fun r m hm b hb => (envWfA_levels hE r m hm).2 b hb

theorem memberLevelCompatibility_of_envWfA {E : ResolvedEnvA} {I : IotaIfaceA}
    (hE : EnvWfA I E) : MemberLevelCompatibility E :=
  fun _ _ hm _ ls hlen =>
    ⟨instLevels_mtype (envWfA_levels hE) hm hlen ls,
      fun _ hb => instLevels_mbody (envWfA_levels hE) hm hb hlen ls⟩

/-- The finite evaluator's actual body comes from a stored transparent
member, with the source level substitution explicitly retained. -/
theorem definitionBody_origin {E : ResolvedEnvA} {r : Nat} {ls : List Level}
    {out : ExprA} (h : definitionBody E r ls = some out) :
    ∃ (m : CheckedMemberA) (b : ExprA),
      E.members r = some m ∧ m.bodyA = some b ∧
      transparent m.mclass = true ∧ out = instantiateLevelsA ls b := by
  cases hm : E.members r with
  | none => simp [definitionBody, hm] at h
  | some m =>
      cases ht : transparent m.mclass with
      | false => simp [definitionBody, hm, ht] at h
      | true =>
          cases hb : m.bodyA with
          | none => simp [definitionBody, hm, ht, hb] at h
          | some b =>
              have he : instantiateLevelsA ls b = out := by
                simpa [definitionBody, hm, ht, hb] using h
              exact ⟨m, b, rfl, hb, ht, he.symm⟩

theorem definitionBodiesClosed_of_stored {E : ResolvedEnvA}
    (hE : StoredBodiesClosed E) : DefinitionBodiesClosed E := by
  intro r ls out h
  rcases definitionBody_origin h with ⟨m, b, hm, hb, _, rfl⟩
  exact liftA_instantiateLevelsA_closed (hE r m hm b hb) ls

theorem definitionBodiesClosed_of_envWfA {E : ResolvedEnvA} {I : IotaIfaceA}
    (hE : EnvWfA I E) : DefinitionBodiesClosed E :=
  definitionBodiesClosed_of_stored (storedBodiesClosed_of_envWfA hE)

/-- Nested level substitution of an actual selected definition body.
This is a member leaf law, not an evaluator level-substitution theorem. -/
theorem definitionBody_instantiation {E : ResolvedEnvA} {I : IotaIfaceA}
    (hE : EnvWfA I E) {r : Nat} {m : CheckedMemberA}
    (hm : E.members r = some m) {ms : List Level}
    (hlen : ms.length = m.arity) (ls : List Level) {body : ExprA}
    (hbody : definitionBody E r ms = some body) :
    definitionBody E r (ms.map (instLevel ls)) =
      some (instantiateLevelsA ls body) := by
  rcases definitionBody_origin hbody with ⟨m', b, hm', hb, ht, rfl⟩
  have he : m' = m := Option.some.inj (hm'.symm.trans hm)
  subst m'
  rw [instLevels_mbody (envWfA_levels hE) hm hb hlen ls]
  exact definitionBody_of_member hm hb ht

theorem admitted_body_conditions {E : ResolvedEnvA} {I : IotaIfaceA}
    (hE : EnvWfA I E) :
    StoredTypesClosed E ∧ StoredBodiesClosed E ∧
    StoredTypesLevelBounded E ∧ StoredBodiesLevelBounded E ∧
    DefinitionBodiesClosed E ∧ MemberLevelCompatibility E :=
  ⟨storedTypesClosed_of_envWfA hE, storedBodiesClosed_of_envWfA hE,
    storedTypesLevelBounded_of_envWfA hE, storedBodiesLevelBounded_of_envWfA hE,
    definitionBodiesClosed_of_envWfA hE, memberLevelCompatibility_of_envWfA hE⟩

/-- Exactly the classes for which `rigidTerm` consults `FamilySyntax`. -/
def HookClass (m : CheckedMemberA) : Prop :=
  m.mclass = .inductiveM ∨ m.mclass = .constructorM ∨ m.mclass = .recursorM

def HookLiftFixed (E : ResolvedEnvA) (F : FamilySyntax) : Prop :=
  ∀ (ν : Valuation) (r : Nat) (ls : List Level) (m : CheckedMemberA),
    E.members r = some m → HookClass m →
      ∀ c, lift c 1 (F ν r ls m) = F ν r ls m

def HookEnvironmentIndependent (E : ResolvedEnvA) (F : FamilySyntax) : Prop :=
  ∀ (ν : Valuation) (r : Nat) (ls : List Level) (m : CheckedMemberA),
    E.members r = some m → HookClass m →
      ∀ ρ σ : EnvI, ValueEq (denI ρ (F ν r ls m)) (denI σ (F ν r ls m))

/-- Same-valuation coherence at the two source constant argument lists.
No condition is imposed at list lengths unsupported by source typing. -/
def HookEqNCompatible (E : ResolvedEnvA) (F : FamilySyntax) : Prop :=
  ∀ (ν : Valuation) (r : Nat) (m : CheckedMemberA),
    E.members r = some m → HookClass m →
      ∀ ls ms : List Level, ls.length = m.arity → ms.length = m.arity →
        eqNList ls ms → ∀ ρ : EnvI,
          ValueEq (denI ρ (F ν r ls m)) (denI ρ (F ν r ms m))

def EvaluatedArgs (ν μ : Valuation) (ls ms : List Level) : Prop :=
  ls.map (eval ν) = ms.map (eval μ)

/-- A stronger member-argument factorisation port: hooks cannot inspect
unused ambient valuation entries or the syntax of an evaluated argument. -/
def HookEvaluatedArgsCompatible (E : ResolvedEnvA) (F : FamilySyntax) : Prop :=
  ∀ (ν μ : Valuation) (r : Nat) (m : CheckedMemberA),
    E.members r = some m → HookClass m →
      ∀ ls ms : List Level, ls.length = m.arity → ms.length = m.arity →
        EvaluatedArgs ν μ ls ms → ∀ ρ : EnvI,
          ValueEq (denI ρ (F ν r ls m)) (denI ρ (F μ r ms m))

theorem evaluatedArgs_of_eqNList (ν : Valuation) :
    ∀ {ls ms : List Level}, eqNList ls ms → EvaluatedArgs ν ν ls ms
  | [], [], _ => rfl
  | _ :: _, [], h => False.elim h
  | [], _ :: _, h => False.elim h
  | l :: ls, m :: ms, h => by
      change eval ν l :: ls.map (eval ν) = eval ν m :: ms.map (eval ν)
      rw [h.1 ν, evaluatedArgs_of_eqNList ν h.2]

theorem hookEqNCompatible_of_evaluatedArgs {E : ResolvedEnvA} {F : FamilySyntax}
    (hF : HookEvaluatedArgsCompatible E F) : HookEqNCompatible E F :=
  fun ν r m hm hc ls ms hl hm' he ρ =>
    hF ν ν r m hm hc ls ms hl hm' (evaluatedArgs_of_eqNList ν he) ρ

/-- Pointwise equality of valuations automatically transports every hook.
This is not the stronger argument-factorisation condition above. -/
theorem hook_of_valuationRel (F : FamilySyntax) {ν μ : Valuation}
    (h : ValuationRel ν μ) (r : Nat) (ls : List Level) (m : CheckedMemberA) :
    F ν r ls m = F μ r ls m := by
  have he : ν = μ := funext h
  cases he
  rfl

theorem hook_paired_compatible {E : ResolvedEnvA} {F : FamilySyntax}
    (hlocal : HookEnvironmentIndependent E F) (hlevels : HookEqNCompatible E F)
    {ν μ : Valuation} (hν : ValuationRel ν μ) {r : Nat} {m : CheckedMemberA}
    (hm : E.members r = some m) (hc : HookClass m) {ls ms : List Level}
    (hl : ls.length = m.arity) (hr : ms.length = m.arity) (he : eqNList ls ms)
    (ρ σ : EnvI) : ValueEq (denI ρ (F ν r ls m)) (denI σ (F μ r ms m)) := by
  have hv : ν = μ := funext hν
  cases hv
  exact (hlevels ν r m hm hc ls ms hl hr he ρ).trans
    (hlocal ν r ms m hm hc ρ σ)

theorem neutral_hook_liftFixed (E : ResolvedEnvA) :
    HookLiftFixed E neutralFamilySyntax :=
  fun _ _ _ _ _ _ _ => rfl

theorem neutral_hook_environmentIndependent (E : ResolvedEnvA) :
    HookEnvironmentIndependent E neutralFamilySyntax :=
  fun _ r _ _ _ _ ρ σ => FunctionEval.constant_environment ρ σ r []

theorem neutral_hook_evaluatedArgsCompatible (E : ResolvedEnvA) :
    HookEvaluatedArgsCompatible E neutralFamilySyntax :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ => ValueEq.refl _

theorem neutral_hook_eqNCompatible (E : ResolvedEnvA) :
    HookEqNCompatible E neutralFamilySyntax :=
  hookEqNCompatible_of_evaluatedArgs (neutral_hook_evaluatedArgsCompatible E)

theorem neutral_hook_conditions (E : ResolvedEnvA) :
    HookLiftFixed E neutralFamilySyntax ∧
    HookEnvironmentIndependent E neutralFamilySyntax ∧
    HookEqNCompatible E neutralFamilySyntax ∧
    HookEvaluatedArgsCompatible E neutralFamilySyntax :=
  ⟨neutral_hook_liftFixed E, neutral_hook_environmentIndependent E,
    neutral_hook_eqNCompatible E, neutral_hook_evaluatedArgsCompatible E⟩

/-- The syntactic leaf law exposed to a translation-lifting proof. -/
theorem rigidTerm_liftFixed {E : ResolvedEnvA} {F : FamilySyntax}
    (hF : HookLiftFixed E F) (ν : Valuation) (r : Nat) (ls : List Level) (c : Nat) :
    lift c 1 (rigidTerm E F ν r ls) = rigidTerm E F ν r ls := by
  cases hm : E.members r with
  | none => simp [rigidTerm, hm, lift]
  | some m =>
      cases hc : m.mclass with
      | axiomM => simp [rigidTerm, hm, hc, lift]
      | definitionM => simp [rigidTerm, hm, hc, lift]
      | theoremM => simp [rigidTerm, hm, hc, lift]
      | opaqueM => simp [rigidTerm, hm, hc, lift]
      | inductiveM => simpa [rigidTerm, hm, hc] using hF ν r ls m hm (.inl hc) c
      | constructorM => simpa [rigidTerm, hm, hc] using hF ν r ls m hm (.inr (.inl hc)) c
      | recursorM => simpa [rigidTerm, hm, hc] using hF ν r ls m hm (.inr (.inr hc)) c

/-- Exact local-environment independence of the rigid leaf's denotation. -/
theorem rigidTerm_environmentIndependent {E : ResolvedEnvA} {F : FamilySyntax}
    (hF : HookEnvironmentIndependent E F) (ν : Valuation) (r : Nat) (ls : List Level)
    (ρ σ : EnvI) : ValueEq (denI ρ (rigidTerm E F ν r ls))
      (denI σ (rigidTerm E F ν r ls)) := by
  cases hm : E.members r with
  | none => simpa [rigidTerm, hm] using FunctionEval.constant_environment ρ σ r []
  | some m =>
      cases hc : m.mclass with
      | axiomM => simpa [rigidTerm, hm, hc] using FunctionEval.constant_environment ρ σ r []
      | definitionM => simpa [rigidTerm, hm, hc] using FunctionEval.constant_environment ρ σ r []
      | theoremM => simpa [rigidTerm, hm, hc] using FunctionEval.constant_environment ρ σ r []
      | opaqueM => simpa [rigidTerm, hm, hc] using FunctionEval.constant_environment ρ σ r []
      | inductiveM => simpa [rigidTerm, hm, hc] using hF ν r ls m hm (.inl hc) ρ σ
      | constructorM => simpa [rigidTerm, hm, hc] using hF ν r ls m hm (.inr (.inl hc)) ρ σ
      | recursorM => simpa [rigidTerm, hm, hc] using hF ν r ls m hm (.inr (.inr hc)) ρ σ

theorem denote_rigid_environmentIndependent {E : ResolvedEnvA} {F : FamilySyntax}
    (hF : HookEnvironmentIndependent E F) {r : Nat} {ls : List Level}
    (hr : definitionBody E r ls = none) (ν : Valuation) (ρ σ : EnvI) :
    ValueEq (EnvironmentEval.denote E F ν ρ (.const r ls))
      (EnvironmentEval.denote E F ν σ (.const r ls)) :=
  (denote_rigid hr F ν ρ).trans
    ((rigidTerm_environmentIndependent hF ν r ls ρ σ).trans (denote_rigid hr F ν σ).symm)

/-- The exact composed valuation appearing in the inherited level evaluator.
Uninstantiated parameter positions retain their original ambient meaning. -/
def instantiatedValuation (ν : Valuation) (ls : List Level) : Valuation :=
  fun i => eval ν ((ls[i]?).getD (.param i))

theorem evaluatedArgs_instantiation (ν : Valuation) (ls : List Level) :
    ∀ ms : List Level,
      EvaluatedArgs ν (instantiatedValuation ν ls) (ms.map (instLevel ls)) ms
  | [] => rfl
  | l :: ms => by
      change eval ν (instLevel ls l) :: (ms.map (instLevel ls)).map (eval ν) =
        eval (instantiatedValuation ν ls) l :: ms.map (eval (instantiatedValuation ν ls))
      rw [eval_instLevel ls ν l]
      exact congrArg (List.cons (eval (instantiatedValuation ν ls) l))
        (evaluatedArgs_instantiation ν ls ms)

/-- The precise hook leaf law needed when source level instantiation moves
from the expression to the ambient valuation. It is weaker than arbitrary
evaluated-argument factorisation and independent of mere `ValuationRel`. -/
def HookLevelInstantiationCompatible (E : ResolvedEnvA) (F : FamilySyntax) : Prop :=
  ∀ (ν : Valuation) (r : Nat) (m : CheckedMemberA),
    E.members r = some m → HookClass m →
      ∀ ls ms : List Level, ms.length = m.arity → ∀ ρ : EnvI,
        ValueEq (denI ρ (F ν r (ms.map (instLevel ls)) m))
          (denI ρ (F (instantiatedValuation ν ls) r ms m))

theorem hookLevelInstantiationCompatible_of_evaluatedArgs
    {E : ResolvedEnvA} {F : FamilySyntax} (hF : HookEvaluatedArgsCompatible E F) :
    HookLevelInstantiationCompatible E F :=
  fun ν r m hm hc ls ms hlen ρ =>
    hF ν (instantiatedValuation ν ls) r m hm hc (ms.map (instLevel ls)) ms
      (length_map_arity hlen (instLevel ls)) hlen (evaluatedArgs_instantiation ν ls ms) ρ

theorem neutral_hook_levelInstantiationCompatible (E : ResolvedEnvA) :
    HookLevelInstantiationCompatible E neutralFamilySyntax :=
  hookLevelInstantiationCompatible_of_evaluatedArgs (neutral_hook_evaluatedArgsCompatible E)

end Rcic.Declarative.Ann.LR3.EnvironmentPortConditions

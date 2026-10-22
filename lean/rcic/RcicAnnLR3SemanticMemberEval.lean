import rcic.RcicAnnLR3ConfiguredAliasBoundary

/-!
# Semantic dispatch from evaluated stored universe types

UniverseMeaning retains a universe code together with its actual
EnvironmentEval image. Its sort and delta constructors are producers.
The semantic result is uniform in the family hook, so installing the
resulting member interpretation uses that same evaluator without a
circular hook premise. The concrete alias control is supplied by the readback module.
This module does not claim a general stored-type interpreter or enriched Fundamental.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.SemanticMemberEval
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements

/-- Route every rigid axiom/opaque member to the semantic hook. -/
def route (m : CheckedMemberA) : CheckedMemberA :=
  match m.mclass with
  | .axiomM | .opaqueM => { m with mclass := .inductiveM }
  | _ => m

def view (E : ResolvedEnvA) : ResolvedEnvA where
  members := fun r => (E.members r).map route

theorem route_body (m : CheckedMemberA) : (route m).bodyA = m.bodyA := by
  cases h : m.mclass <;> simp [route, h]

theorem route_transparent (m : CheckedMemberA) :
    transparent (route m).mclass = transparent m.mclass := by
  cases h : m.mclass <;> simp [route, h, transparent]

theorem definitionBody_preserved (E : ResolvedEnvA) (r : Nat) (ls : List Level) :
    EnvironmentEval.definitionBody (view E) r ls =
      EnvironmentEval.definitionBody E r ls := by
  cases hm : E.members r with
  | none => simp [EnvironmentEval.definitionBody, view, hm]
  | some m =>
      simp [EnvironmentEval.definitionBody, view, hm, route_body, route_transparent]

/-- A retained universe result of interpreting a stored type. This is
not membership of the source member being constructed. -/
structure UniverseMeaning (E : ResolvedEnvA) (ν : Valuation) (A : ExprA) where
  level : Option Nat
  image : ∀ (F : EnvironmentEval.FamilySyntax) (ρ : EnvI),
    ValueEq (EnvironmentEval.denote E F ν ρ A) (universeValue level)

/-- Actual sort interpretation supplies the initial retained code. -/
def sortMeaning (E : ResolvedEnvA) (ν : Valuation) (l : Level) :
    UniverseMeaning E ν (.sort l) where
  level := eval ν l
  image := by
    intro F ρ
    have h := (EnvironmentEval.annSemantics NeutralCodes.codeSystem E F).sort_image ν [] ρ l
    change EnvironmentEval.denote E F ν ρ (.sort l) = universeValue (eval ν l) at h
    exact fun c => by rw [h]

/-- Interpret a transparent alias by the evaluator's existing delta law.
The result code is retained unchanged; no syntax normalizer is used. -/
def deltaMeaning {E : ResolvedEnvA} {ν : Valuation} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} {b : ExprA} (hm : E.members r = some m)
    (hb : m.bodyA = some b) (ht : transparent m.mclass = true)
    (body : UniverseMeaning E ν (instantiateLevelsA ls b)) :
    UniverseMeaning E ν (.const r ls) where
  level := body.level
  image := fun F ρ => (EnvironmentEval.denote_delta hm hb ht F ν ρ).trans (body.image F ρ)

/-- Dispatch consumes the interpreted code, not the stored syntax. -/
def dispatch {E : ResolvedEnvA} {ν : Valuation} {A : ExprA}
    (meaning : UniverseMeaning E ν A) (name : Nat) : Expr Nat :=
  NativeMemberValues.term meaning.level name

theorem dispatch_environment {E : ResolvedEnvA} {ν : Valuation} {A : ExprA}
    (meaning : UniverseMeaning E ν A) (name : Nat) (ρ : EnvI) :
    ValueEq (denI ρ (dispatch meaning name)) (NativeMemberValues.value meaning.level name) :=
  NativeMemberValues.environment ρ meaning.level name

theorem dispatch_sort_member {E : ResolvedEnvA} {ν : Valuation} {A : ExprA}
    (meaning : UniverseMeaning E ν A) (name : Nat) :
    SortMember meaning.level (NativeMemberValues.value meaning.level name) ∧
    TypeDefined (NativeMemberValues.value meaning.level name) :=
  ⟨NativeMemberValues.value_level _ _, NativeMemberValues.value_defined _ _⟩

/-- Delta changes the source stored type while preserving the actual
semantic dispatch result. This composes through arbitrary finite chains. -/
theorem dispatch_delta {E : ResolvedEnvA} {ν : Valuation} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} {b : ExprA} (hm : E.members r = some m)
    (hb : m.bodyA = some b) (ht : transparent m.mclass = true)
    (body : UniverseMeaning E ν (instantiateLevelsA ls b)) (name : Nat) :
    dispatch (deltaMeaning hm hb ht body) name = dispatch body name := rfl

end Rcic.Declarative.Ann.LR3.SemanticMemberEval

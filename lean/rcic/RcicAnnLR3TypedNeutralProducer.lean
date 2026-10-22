import rcic.RcicAnnLR3EnvironmentPi

/-!
# Type-directed neutral values with their actual element code

The result retains its type value, element PER and CodeI derivation. The
legacy fragment has a supplied reflection operation. Universe reflection
produces a tagged neutral type, including at `none`; it does not reuse a
raw neutral atom as a type. Dependent function reflection uses complete
legal graphs and the environment evaluator's finite-demand theorem.

The product producer is explicitly scoped to old-universe-coded fibres.
It does not assert reflection for every CodeI derivation, universe closure,
candidate-aware universal quantification, or a source constant arm.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TypedNeutralProducer

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements InductiveCodes

/-- Ordinary data retains the actual code and its reflected element.
The element relation is a parameter, not selected from a Prop existential. -/
structure TypedNeutral (k : Option Nat) (V : Value) (R : Relation) where
  code : CodeI k V R
  value : Value
  member : Member R value

/-- Actual reflection on the legacy code fragment. -/
def ofLegacy {k : Option Nat} {V : Value} {R : Relation}
    (h : NeutralCodes.Code k V R) (name : Nat) : TypedNeutral k V R where
  code := .old h
  value := NeutralCodes.reflect V name
  member := NeutralCodes.reflect_member h name

theorem ofLegacy_related {k l : Option Nat} {V W : Value} {R S : Relation}
    (hV : NeutralCodes.Code k V R) (hW : NeutralCodes.Code l W S)
    (hRS : Same R S) (name : Nat) :
    R (ofLegacy hV name).value (ofLegacy hW name).value :=
  NeutralCodes.reflect_relation hV hW hRS name

/-- Universe-valued neutrals carry the type tag required at the actual
universe. No totality condition on the level valuation is imposed. -/
def universeNeutral (k : Option Nat) (name : Nat) :
    TypedNeutral (k.map Nat.succ) (universeValue k) (NeutralCodes.UniversePER k) where
  code := .old (NeutralCodes.code_universe k)
  value := NeutralCodes.reify (.neutralType k name)
  member := NeutralCodes.reflectDescriptor_member (.univ k) name

theorem universe_reflection (k : Option Nat) (name : Nat) :
    ValueEq (universeNeutral k name).value (NeutralCodes.reflect (universeValue k) name) :=
  (NeutralCodes.reflect_at
    (V := universeValue k) (d := .univ k) (ValueEq.refl _) name).symm

/-- Decoding this supplied universe element retains its explicit PER. -/
theorem universe_element_code (k : Option Nat) (name : Nat) :
    CodeI k (universeNeutral k name).value (NeutralCodes.El (.neutralType k name)) :=
  .old (NeutralCodes.code (.neutralType k name))

theorem universe_element_level (k : Option Nat) (name : Nat) :
    SortMember k (universeNeutral k name).value :=
  code_level (universe_element_code k name)

theorem universe_element_defined (k : Option Nat) (name : Nat) :
    TypeDefined (universeNeutral k name).value :=
  code_defined (universe_element_code k name)

theorem universe_not_raw_atom (k : Option Nat) (name : Nat) :
    ¬ ValueEq (universeNeutral k name).value (NeutralPER.neutralAtom name) := by
  intro h
  exact NeutralPER.neutralAtom_not_sort_member name k
    (sortMember_congr h (universe_element_level k name))

theorem universe_none_control (name : Nat) :
    Member (NeutralCodes.UniversePER none) (universeNeutral none name).value ∧
    CodeI none (universeNeutral none name).value (NeutralCodes.El (.neutralType none name)) ∧
    TypeDefined (universeNeutral none name).value :=
  ⟨(universeNeutral none name).member, universe_element_code none name,
    universe_element_defined none name⟩

/-- Product coding uses the supplied decoded legacy fibres, while its
type value is the environment evaluator's actual dependent product. -/
theorem environment_pi_code {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax}
    {ν : Valuation} {ρ : EnvI} {A B : ExprA} {u v : Level} {D : Relation}
    (hA : CodeI (eval ν u) (EnvironmentEval.denote E F ν ρ A) D)
    (hB : DecodedPi.CodeFamily (eval ν v) D
      (fun x => EnvironmentEval.denote E F ν (EnvI.cons x ρ) B)) :
    CodeI (imaxLevel (eval ν u) (eval ν v))
      (EnvironmentEval.denote E F ν ρ (.pi A u B v))
      (DecodedPi.functionPER (eval ν v) D
        (fun x => EnvironmentEval.denote E F ν (EnvI.cons x ρ) B)) := by
  apply CodeI.pi (kA := eval ν u) (kB := eval ν v)
    (A := EnvironmentEval.denote E F ν ρ A)
    (C := EnvironmentEval.denote E F ν ρ (.lam A u B)) (RA := D)
    (RB := fun x => DecodedPi.decodedEl (eval ν v)
      (EnvironmentEval.denote E F ν (EnvI.cons x ρ) B)) hA
  · intro x y hxy
    exact code_value_eq
      (.old (DecodedPi.codeFamily_decodes hB (left_member (code_laws hA) hxy)))
      (EnvironmentEval.denote_lambda_application E F ν ρ A B u x).symm
  · exact DecodedPi.codeFamily_coherent hB
  · exact EnvironmentEval.denote_pi_value E F ν ρ A B u v
  · exact fun _ _ => Iff.rfl

/-- A constructed legal function neutral, with no supplied reflected-demand
or membership premise. The codomain formation premise remains explicit. -/
def environmentPi {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax}
    {ν : Valuation} {ρ : EnvI} {A B : ExprA} {u v : Level} {D : Relation}
    (hA : CodeI (eval ν u) (EnvironmentEval.denote E F ν ρ A) D)
    (hB : DecodedPi.CodeFamily (eval ν v) D
      (fun x => EnvironmentEval.denote E F ν (EnvI.cons x ρ) B)) (name : Nat) :
    TypedNeutral (imaxLevel (eval ν u) (eval ν v))
      (EnvironmentEval.denote E F ν ρ (.pi A u B v))
      (DecodedPi.functionPER (eval ν v) D
        (fun x => EnvironmentEval.denote E F ν (EnvI.cons x ρ) B)) where
  code := environment_pi_code hA hB
  value := DecodedPi.reflectionGraph D
    (fun x => EnvironmentEval.denote E F ν (EnvI.cons x ρ) B) name
  member := DecodedPi.reflectionGraph_member (code_laws hA) hB
    (EnvironmentEval.body_legalFiniteDemand E F ν ρ B D) name

theorem environmentPi_application {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax}
    {ν : Valuation} {ρ : EnvI} {A B : ExprA} {u v : Level} {D : Relation}
    (hA : CodeI (eval ν u) (EnvironmentEval.denote E F ν ρ A) D)
    (hB : DecodedPi.CodeFamily (eval ν v) D
      (fun x => EnvironmentEval.denote E F ν (EnvI.cons x ρ) B))
    (name : Nat) {x : Value} (hx : Member D x) :
    ValueEq (NeutralPi.applyValue (environmentPi hA hB name).value x)
      (NeutralCodes.reflect (EnvironmentEval.denote E F ν (EnvI.cons x ρ) B) name) :=
  DecodedPi.reflectionGraph_application hB
    (EnvironmentEval.body_legalFiniteDemand E F ν ρ B D) name hx

end Rcic.Declarative.Ann.LR3.TypedNeutralProducer

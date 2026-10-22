import rcic.RcicAnnLR3TypedNeutralProducer

/-!
# An inhabited control for the environment-aware function reflection

The source type is `Prop → Prop`. Its actual product image is coded, and
the reflected function returns tagged neutral propositions at every legal
argument. Both formation inputs of the function producer are supplied.
This control uses the legacy universe and makes no claim about quantifying
over all candidate-bearing values or product membership in that universe.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TypedNeutralPiControls

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements TypedNeutralProducer

abbrev one : Level := .succ .zero

def sourceType : ExprA := .pi (.sort .zero) one (.sort .zero) one

def source_formed : HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] sourceType
    (.sort (.imax one one)) :=
  .pi [] (.sort .zero) one (.sort .zero) one
    (.sort [] .zero) (.sort [.assumption (.sort .zero)] .zero)

private theorem sort_image (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (l : Level) :
    EnvironmentEval.denote E F ν ρ (.sort l) = universeValue (eval ν l) :=
  (EnvironmentEval.annSemantics InductiveCodes.legacyUniverseSystem E F).sort_image ν [] ρ l

theorem domain_code (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    InductiveCodes.CodeI (eval ν one) (EnvironmentEval.denote E F ν ρ (.sort .zero))
      (NeutralCodes.UniversePER (some 0)) := by
  rw [sort_image]
  exact .old (NeutralCodes.code_universe (some 0))

theorem fibres_coded (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    DecodedPi.CodeFamily (eval ν one) (NeutralCodes.UniversePER (some 0))
      (fun x => EnvironmentEval.denote E F ν (EnvI.cons x ρ) (.sort .zero)) := by
  intro x y _
  change NeutralCodes.UniversePER (eval ν one)
    (EnvironmentEval.denote E F ν (EnvI.cons x ρ) (.sort .zero))
    (EnvironmentEval.denote E F ν (EnvI.cons y ρ) (.sort .zero))
  rw [sort_image, sort_image]
  exact NeutralCodes.universe_member (some 0)

def reflected (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (name : Nat) :
    TypedNeutral (InductiveCodes.imaxLevel (eval ν one) (eval ν one))
      (EnvironmentEval.denote E F ν ρ sourceType)
      (DecodedPi.functionPER (eval ν one) (NeutralCodes.UniversePER (some 0))
        (fun x => EnvironmentEval.denote E F ν (EnvI.cons x ρ) (.sort .zero))) :=
  environmentPi (domain_code E F ν ρ) (fibres_coded E F ν ρ) name

theorem reflected_application (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (name : Nat) {x : Value}
    (hx : Member (NeutralCodes.UniversePER (some 0)) x) :
    ValueEq (NeutralPi.applyValue (reflected E F ν ρ name).value x)
      (universeNeutral (some 0) name).value := by
  have h := environmentPi_application (domain_code E F ν ρ)
    (fibres_coded E F ν ρ) name hx
  rw [sort_image] at h
  exact h.trans (universe_reflection (some 0) name).symm

theorem control_inhabited (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (name : Nat) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 []) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] sourceType
      (.sort (.imax one one))) ∧
    InductiveCodes.CodeI (InductiveCodes.imaxLevel (eval ν one) (eval ν one))
      (EnvironmentEval.denote emptyEnvA F ν ρ sourceType)
      (DecodedPi.functionPER (eval ν one) (NeutralCodes.UniversePER (some 0))
        (fun x => EnvironmentEval.denote emptyEnvA F ν (EnvI.cons x ρ) (.sort .zero))) ∧
    Member (DecodedPi.functionPER (eval ν one) (NeutralCodes.UniversePER (some 0))
      (fun x => EnvironmentEval.denote emptyEnvA F ν (EnvI.cons x ρ) (.sort .zero)))
      (reflected emptyEnvA F ν ρ name).value ∧
    (∀ x, Member (NeutralCodes.UniversePER (some 0)) x →
      ValueEq (NeutralPi.applyValue (reflected emptyEnvA F ν ρ name).value x)
        (universeNeutral (some 0) name).value) :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨source_formed⟩, (reflected emptyEnvA F ν ρ name).code,
    (reflected emptyEnvA F ν ρ name).member, fun _ hx => reflected_application _ _ _ _ _ hx⟩

end Rcic.Declarative.Ann.LR3.TypedNeutralPiControls

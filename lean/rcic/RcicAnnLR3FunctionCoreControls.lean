import rcic.RcicAnnLR3FunctionEval
import rcic.RcicAnnLR3PairedProducer

/-!
# An inhabited exact paired beta arm

The concrete inherited evaluator supplies beta without a fundamental
theorem premise. This control supplies all four source typing children,
all four paired child induction hypotheses, admission, context formation,
and related realizations. Its body is a sort, so it uses only already
supplied sort arms and does not duplicate any dispatched variable arm.

The nine-arm conjunction is for this explicit evaluator attachment.
Its scoped constant map is not an interpretation of arbitrary admitted
members. No larger grammar, admitted-member theorem, or complete source
fundamental theorem follows from this conjunction. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.FunctionCoreControls

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements

def model : AnnSemantics := FunctionEval.annSemantics NeutralCodes.codeSystem

theorem nine_arms_supplied (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Ty_sort model E I n ∧
    PairedArms.Ty_conv model E I n ∧
    PairedArms.Conv_refl model E I n ∧
    PairedArms.Conv_symm model E I n ∧
    PairedArms.Conv_trans model E I n ∧
    PairedArms.Conv_sorts model E I n ∧
    PairedArms.Conv_tyConv model E I n ∧
    PairedArms.Conv_irr model E I n ∧
    PairedArms.Conv_beta model E I n :=
  ⟨PairedArms.ty_sort_supplied model E I n,
    PairedArms.ty_conv_supplied model E I n PairedProducer.universeTransport,
    PairedArms.conv_refl_supplied model E I n,
    PairedArms.conv_symm_supplied model E I n,
    PairedArms.conv_trans_supplied model E I n,
    PairedArms.conv_sorts_supplied model E I n,
    PairedArms.conv_tyConv_supplied model E I n PairedProducer.universeTransport,
    PairedArms.conv_irr_supplied model E I n PairedProducer.propIrrelevance,
    FunctionEval.neutralCodes_conv_beta_supplied E I n⟩

abbrev one : Level := .succ .zero
abbrev two : Level := .succ one

def betaLeft : ExprA := .app (.lam (.sort one) two (.sort .zero)) (.sort .zero)
def betaRight : ExprA := .sort .zero
def betaType : ExprA := .sort one

def admitted : EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA := .empty

def betaSource : ConvA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] betaLeft betaRight betaType :=
  .beta [] (.sort one) two (.sort .zero) (.sort .zero) (.sort one)
    (.sort [] one) (.sort [.assumption (.sort one)] .zero)
    (.sort [] .zero) (.sort [] .zero)

theorem domainIH :
    PairedTyGoal model emptyEnvA (iotaIfaceA emptyEnvA) 0 [] (.sort one) (.sort two) :=
  PairedArms.ty_sort_supplied model _ _ _ [] one

theorem bodyIH :
    PairedTyGoal model emptyEnvA (iotaIfaceA emptyEnvA) 0 [.assumption (.sort one)]
      (.sort .zero) (.sort one) :=
  PairedArms.ty_sort_supplied model _ _ _ [.assumption (.sort one)] .zero

theorem argumentIH :
    PairedTyGoal model emptyEnvA (iotaIfaceA emptyEnvA) 0 [] (.sort .zero) (.sort one) :=
  PairedArms.ty_sort_supplied model _ _ _ [] .zero

theorem contractumIH :
    PairedTyGoal model emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      (instantiate0A (.sort .zero) (.sort .zero))
      (instantiate0A (.sort .zero) (.sort one)) :=
  argumentIH

/-- Every premise of this invocation of the exact beta arm is supplied. -/
theorem betaGoal :
    PairedConvGoal model emptyEnvA (iotaIfaceA emptyEnvA) 0 [] betaLeft betaRight betaType :=
  FunctionEval.conv_beta_supplied NeutralCodes.codeSystem emptyEnvA (iotaIfaceA emptyEnvA) 0
    [] (.sort one) two (.sort .zero) (.sort .zero) (.sort one)
    (.sort [] one) (.sort [.assumption (.sort one)] .zero)
    (.sort [] .zero) (.sort [] .zero) domainIH bodyIH argumentIH contractumIH

theorem betaJudgment (ν μ : Valuation) (hν : ValuationRel ν μ) :
    PairedJudgment model ν μ [] EnvI.bot EnvI.bot betaLeft betaRight betaType :=
  betaGoal .nil ν μ EnvI.bot EnvI.bot hν (.nil EnvI.bot EnvI.bot)

theorem beta_control_inhabited :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 []) ∧
    Nonempty (ConvA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] betaLeft betaRight betaType) ∧
    PairedTyGoal model emptyEnvA (iotaIfaceA emptyEnvA) 0 [] (.sort one) (.sort two) ∧
    PairedTyGoal model emptyEnvA (iotaIfaceA emptyEnvA) 0 [.assumption (.sort one)]
      (.sort .zero) (.sort one) ∧
    PairedTyGoal model emptyEnvA (iotaIfaceA emptyEnvA) 0 [] (.sort .zero) (.sort one) ∧
    PairedTyGoal model emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      (instantiate0A (.sort .zero) (.sort .zero))
      (instantiate0A (.sort .zero) (.sort one)) ∧
    (∀ ν μ, ValuationRel ν μ →
      PairedJudgment model ν μ [] EnvI.bot EnvI.bot betaLeft betaRight betaType) :=
  ⟨⟨admitted⟩, ⟨.nil⟩, ⟨betaSource⟩, domainIH, bodyIH, argumentIH, contractumIH,
    betaJudgment⟩

end Rcic.Declarative.Ann.LR3.FunctionCoreControls

import rcic.RcicAnnLR3InductiveLambdaArms
import rcic.RcicAnnLR3InductiveApplicationArms
import rcic.RcicAnnLR3InductiveEtaArms
import rcic.RcicAnnLR3InductiveIrrelevance
import rcic.RcicAnnLR3InductiveCodeControls

/-!
# Inhabited lambda/application controls and the exact scoped arm count

The fixture is the constant function `fun A : Type => Prop`, applied to
`Prop`, in the admitted empty environment. Every formation, body, argument
and result child is an actual sort derivation with its supplied paired
IH. The lambda and application IHs below are obtained by invoking the
new exact arms; neither uses Fundamental or the impossible legacy Ty_pi.
The two congruence controls invoke their exact new contracts as well.

The aggregate lists fifteen contracts for one explicit evaluator and one
code system. Seven externally dispatched arms are not imported or claimed.
Six contracts remain unprovided here. `closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.InductiveFunctionControls

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements InductiveCodes

def model : AnnSemantics := FunctionEval.annSemantics legacyUniverseSystem
def one : Level := .succ .zero
def two : Level := .succ one
def functionType : ExprA := .pi (.sort one) two (.sort one) two
def functionTerm : ExprA := .lam (.sort one) two (.sort .zero)
def applicationTerm : ExprA := .app functionTerm (.sort .zero)

def source_domain (Γ : LCtxA) :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 Γ (.sort one) (.sort two) :=
  .sort Γ one

def source_body (Γ : LCtxA) :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 (.assumption (.sort one) :: Γ)
      (.sort .zero) (.sort one) := .sort _ .zero

def source_function (Γ : LCtxA) :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 Γ functionTerm functionType :=
  .lam Γ (.sort one) two (.sort .zero) (.sort one) two
    (source_domain Γ) (source_domain (.assumption (.sort one) :: Γ)) (source_body Γ)

def source_application (Γ : LCtxA) :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 Γ applicationTerm (.sort one) :=
  .app Γ functionTerm (.sort .zero) (.sort one) (.sort one) two two two
    (source_domain (.assumption (.sort one) :: Γ)) (source_domain Γ)
    (source_function Γ) (.sort Γ .zero)

theorem function_IH (Γ : LCtxA) :
    PairedTyGoal model emptyEnvA (iotaIfaceA emptyEnvA) 0 Γ functionTerm functionType :=
  InductiveLambdaArms.ty_lam_supplied _ _ _ Γ (.sort one) two (.sort .zero) (.sort one) two
    (source_domain Γ) (source_domain (.assumption (.sort one) :: Γ)) (source_body Γ)
    (PairedArms.ty_sort_supplied model _ _ _ Γ one)
    (PairedArms.ty_sort_supplied model _ _ _ (.assumption (.sort one) :: Γ) one)
    (PairedArms.ty_sort_supplied model _ _ _ (.assumption (.sort one) :: Γ) .zero)

theorem application_IH (Γ : LCtxA) :
    PairedTyGoal model emptyEnvA (iotaIfaceA emptyEnvA) 0 Γ applicationTerm (.sort one) :=
  InductiveApplicationArms.ty_app_supplied _ _ _ Γ functionTerm (.sort .zero)
    (.sort one) (.sort one) two two two
    (source_domain (.assumption (.sort one) :: Γ)) (source_domain Γ)
    (source_function Γ) (.sort Γ .zero)
    (PairedArms.ty_sort_supplied model _ _ _ (.assumption (.sort one) :: Γ) one)
    (PairedArms.ty_sort_supplied model _ _ _ Γ one) (function_IH Γ)
    (PairedArms.ty_sort_supplied model _ _ _ Γ .zero)

theorem lambda_conversion_IH (Γ : LCtxA) :
    PairedConvGoal model emptyEnvA (iotaIfaceA emptyEnvA) 0 Γ
      functionTerm functionTerm functionType :=
  InductiveLambdaArms.conv_lam_supplied _ _ _ Γ (.sort one) (.sort one)
    (.sort .zero) (.sort .zero) (.sort one) two two two (fun _ => rfl)
    (.refl Γ (.sort one) (.sort two) (source_domain Γ))
    (.refl (.assumption (.sort one) :: Γ) (.sort .zero) (.sort one) (source_body Γ))
    (source_function Γ)
    (PairedArms.ty_sort_supplied model _ _ _ Γ one)
    (PairedArms.ty_sort_supplied model _ _ _ (.assumption (.sort one) :: Γ) .zero)
    (function_IH Γ)

theorem application_conversion_IH (Γ : LCtxA) :
    PairedConvGoal model emptyEnvA (iotaIfaceA emptyEnvA) 0 Γ
      applicationTerm applicationTerm (.sort one) :=
  InductiveApplicationArms.conv_app_supplied _ _ _ Γ functionTerm functionTerm
    (.sort .zero) (.sort .zero) (.sort one) (.sort one) two two
    (.refl Γ functionTerm functionType (source_function Γ))
    (.refl Γ (.sort .zero) (.sort one) (.sort Γ .zero))
    (source_domain (.assumption (.sort one) :: Γ)) (source_application Γ)
    (function_IH Γ) (PairedArms.ty_sort_supplied model _ _ _ Γ .zero)
    (PairedArms.ty_sort_supplied model _ _ _ (.assumption (.sort one) :: Γ) one)
    (application_IH Γ)

theorem controls_inhabited :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 []) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] functionTerm functionType) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] applicationTerm (.sort one)) ∧
    PairedTyGoal model emptyEnvA (iotaIfaceA emptyEnvA) 0 [] functionTerm functionType ∧
    PairedTyGoal model emptyEnvA (iotaIfaceA emptyEnvA) 0 [] applicationTerm (.sort one) ∧
    PairedConvGoal model emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      functionTerm functionTerm functionType ∧
    PairedConvGoal model emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      applicationTerm applicationTerm (.sort one) ∧
    PairedRealises model InductiveCodeControls.zeroValuation InductiveCodeControls.zeroValuation
      [] EnvI.bot EnvI.bot :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨source_function []⟩, ⟨source_application []⟩,
    function_IH [], application_IH [], lambda_conversion_IH [], application_conversion_IH [],
    .nil _ _⟩

theorem concrete_application_judgment :
    PairedJudgment model InductiveCodeControls.zeroValuation InductiveCodeControls.zeroValuation
      [] EnvI.bot EnvI.bot applicationTerm applicationTerm (.sort one) :=
  application_IH [] .nil _ _ _ _ (ValuationRel.refl _) (.nil _ _)

theorem fifteen_arms_supplied (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Ty_sort model E I n ∧ PairedArms.Ty_lam model E I n ∧
    PairedArms.Ty_app model E I n ∧ PairedArms.Ty_conv model E I n ∧
    PairedArms.Conv_refl model E I n ∧ PairedArms.Conv_symm model E I n ∧
    PairedArms.Conv_trans model E I n ∧ PairedArms.Conv_beta model E I n ∧
    PairedArms.Conv_app model E I n ∧ PairedArms.Conv_lam model E I n ∧
    PairedArms.Conv_sorts model E I n ∧ PairedArms.Conv_consts model E I n ∧
    PairedArms.Conv_eta model E I n ∧ PairedArms.Conv_irr model E I n ∧
    PairedArms.Conv_tyConv model E I n := by
  obtain ⟨hsort, hconv, hrefl, hsymm, htrans, hsorts, htyconv, hirr, hbeta⟩ :=
    InductiveIrrelevance.inherited_nine_arms E I n
  exact ⟨hsort, InductiveLambdaArms.ty_lam_supplied E I n,
    InductiveApplicationArms.ty_app_supplied E I n, hconv, hrefl, hsymm, htrans, hbeta,
    InductiveApplicationArms.conv_app_supplied E I n,
    InductiveLambdaArms.conv_lam_supplied E I n, hsorts,
    InductiveEtaArms.conv_consts_supplied E I n,
    InductiveEtaArms.conv_eta_supplied E I n, hirr, htyconv⟩

end Rcic.Declarative.Ann.LR3.InductiveFunctionControls

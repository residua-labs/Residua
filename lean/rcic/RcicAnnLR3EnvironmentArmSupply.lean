import rcic.RcicAnnLR3EnvironmentLambdaArms
import rcic.RcicAnnLR3InductiveIrrelevance

/-!
# One uniform arm cohort on the new environment-aware evaluator

These eleven exact contracts share one model and consume only their
stipulated child induction hypotheses. Eight are supplied by the existing
PER/universe algebra; the new lambda pair and delta equation supply the
other three. This does not transfer the old fifteen-arm theorem or any of
the seven external arms to the new evaluator. `closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.EnvironmentArmSupply
open Rcic.Declarative TypedStatements PairedStatements InductiveCodes
open EnvironmentLambdaArms

theorem eleven_arms_supplied (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (I : IotaIfaceA) (n : Nat) :
    PairedArms.Ty_sort (model E F) E I n ∧
    PairedArms.Ty_conv (model E F) E I n ∧
    PairedArms.Ty_lam (model E F) E I n ∧
    PairedArms.Conv_refl (model E F) E I n ∧
    PairedArms.Conv_symm (model E F) E I n ∧
    PairedArms.Conv_trans (model E F) E I n ∧
    PairedArms.Conv_sorts (model E F) E I n ∧
    PairedArms.Conv_tyConv (model E F) E I n ∧
    PairedArms.Conv_irr (model E F) E I n ∧
    PairedArms.Conv_lam (model E F) E I n ∧
    PairedArms.Conv_delta (model E F) E I n :=
  ⟨PairedArms.ty_sort_supplied _ E I n,
    PairedArms.ty_conv_supplied _ E I n legacyUniverseTransport,
    EnvironmentLambdaArms.ty_lam_supplied E F I n,
    PairedArms.conv_refl_supplied _ E I n,
    PairedArms.conv_symm_supplied _ E I n,
    PairedArms.conv_trans_supplied _ E I n,
    PairedArms.conv_sorts_supplied _ E I n,
    PairedArms.conv_tyConv_supplied _ E I n legacyUniverseTransport,
    PairedArms.conv_irr_supplied _ E I n InductiveIrrelevance.propIrrelevance,
    EnvironmentLambdaArms.conv_lam_supplied E F I n,
    EnvironmentEval.conv_delta_supplied legacyUniverseSystem E F I n⟩

end Rcic.Declarative.Ann.LR3.EnvironmentArmSupply

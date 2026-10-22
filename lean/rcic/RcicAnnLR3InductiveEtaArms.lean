import rcic.RcicAnnLR3InductiveCodes

/-!
# Exact eta and constant-level conversion contracts

Eta uses the actual product carrier and saturation of every coded domain.
It does not require bottom to be a literal observation of each function
value, nor assume a fundamental theorem.

The constant-level arm is specific to the inherited explicit evaluator,
which erases constant level lists. It supplies no interpretation of the
admitted member telescope and does not establish Ty_const or delta.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.InductiveEtaArms

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements InductiveCodes

def model : AnnSemantics := FunctionEval.annSemantics legacyUniverseSystem

theorem conv_eta_supplied (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Conv_eta model E I n := by
  intro Γ f A B u v hf hrt ihf ihrt hΓ ν μ ρ σ hν hρ
  obtain ⟨k, R, S, hp, hfg⟩ := ihf hΓ ν μ ρ σ hν hρ
  obtain ⟨kA, kB, D, C, hD, hC, hc, hR⟩ := denote_pi_view hp.left_code
  refine ⟨k, R, S, hp, (hR _ _).mpr ?_⟩
  exact FunctionSaturation.denote_eta_related (code_laws hD) (code_saturated hD) hc
    ((hR _ _).mp hfg)

theorem conv_consts_supplied (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Conv_consts model E I n := by
  intro Γ r ls ls' m hres hlen hwf hwf' heq hrt ihrt hΓ ν μ ρ σ hν hρ
  exact ihrt hΓ ν μ ρ σ hν hρ

end Rcic.Declarative.Ann.LR3.InductiveEtaArms

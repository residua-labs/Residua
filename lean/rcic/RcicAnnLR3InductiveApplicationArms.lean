import rcic.RcicAnnLR3InductiveCodes

/-!
# Actual paired application arms for relational product codes

Product inversion supplies the complete legal-domain function carrier.
The argument pair is transported into that domain, and the result is
transported from the dependent fibre to the source substitution image.
The substitution equation is composed from the inherited evaluator laws.
No fundamental theorem, selected fibre, or universe-closure premise is
added to either exact arm contract.

The attached evaluator and its legacy universe remain explicitly scoped.
These arms do not assert product formation into that legacy universe or
soundness of the admitted member telescope. `closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.InductiveApplicationArms

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements InductiveCodes

def model : AnnSemantics := FunctionEval.annSemantics legacyUniverseSystem

private theorem substitution_image (ν : Valuation) (ρ : EnvI) (a B : ExprA) :
    ValueEq (UnitModel.denote ν ρ (instantiate0A a B))
      (UnitModel.denote ν (EnvI.cons (UnitModel.denote ν ρ a) ρ) B) := by
  apply (beta_sound ν ρ (.sort .zero) B a .zero).symm.trans
  apply (NeutralPi.applyValue_denI ρ
    (translate ν (.lam (.sort .zero) .zero B)) (translate ν a)).symm.trans
  exact FunctionEval.denote_lambda_application ν ρ (.sort .zero) B .zero _

/-- The type images and output carriers are provided by the stipulated
result-type/typing child. All computation and function elimination here
are supplied by the actual relational product constructor. -/
theorem application_judgment {ν μ : Valuation} {Γ : LCtxA} {ρ σ : EnvI}
    {f g a b A B : ExprA} {u v : Level}
    (hf : PairedJudgment model ν μ Γ ρ σ f g (.pi A u B v))
    (ha : PairedJudgment model ν μ Γ ρ σ a b A)
    (ht : RelatedCode model.toCodeSystem
      (model.image ν Γ ρ (instantiate0A a B))
      (model.image μ Γ σ (instantiate0A a B))) :
    PairedJudgment model ν μ Γ ρ σ (.app f a) (.app g b) (instantiate0A a B) := by
  obtain ⟨kf, Rf, Sf, hcf, hfg⟩ := hf
  obtain ⟨ka, Ra, Sa, hca, hab⟩ := ha
  obtain ⟨kt, Rt, St, hct⟩ := ht
  obtain ⟨kA, kB, D, C, hD, hC, hcoherent, hRf⟩ := denote_pi_view hcf.left_code
  have harg : D (UnitModel.denote ν ρ a) (UnitModel.denote μ σ b) :=
    (code_coherent hca.left_code hD _ _).mp hab
  have hfun : FunctionPER NeutralPi.applyValue D C
      (UnitModel.denote ν ρ f) (UnitModel.denote μ σ g) := (hRf _ _).mp hfg
  have hresult := FunctionEval.denote_applications_related hfun harg
  have hcode : CodeI kB (UnitModel.denote ν ρ (instantiate0A a B))
      (C (UnitModel.denote ν ρ a)) :=
    code_value_eq (hC _ _ harg) (substitution_image ν ρ a B).symm
  refine ⟨kt, Rt, St, hct, ?_⟩
  exact (code_coherent hcode hct.left_code _ _).mp hresult

theorem ty_app_supplied (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Ty_app model E I n := by
  intro Γ f a A B u v w hB hTy hf ha ihB ihTy ihf iha hΓ ν μ ρ σ hν hρ
  have ht := (ihTy hΓ ν μ ρ σ hν hρ).related_types legacyUniverseTransport
  exact application_judgment (ihf hΓ ν μ ρ σ hν hρ) (iha hΓ ν μ ρ σ hν hρ) ht

theorem conv_app_supplied (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Conv_app model E I n := by
  intro Γ f g a b A B u v hfg hab hB hrt ihfg ihab ihB ihrt hΓ ν μ ρ σ hν hρ
  exact application_judgment (ihfg hΓ ν μ ρ σ hν hρ) (ihab hΓ ν μ ρ σ hν hρ)
    (ihrt hΓ ν μ ρ σ hν hρ).type_related

end Rcic.Declarative.Ann.LR3.InductiveApplicationArms

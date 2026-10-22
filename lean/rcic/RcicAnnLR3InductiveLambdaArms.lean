import rcic.RcicAnnLR3InductiveCodes

/-!
# Actual paired lambda arms for relational product codes

The stipulated formation children decode the domain and every legal
codomain fibre. The fibre relation is the explicit Prop-valued decodedEl,
so no relation is selected from a propositional existence proof. Native
lambda application then supplies the whole legal-domain function law.

Lambda congruence reuses the result typing child's actual product code,
inverts that code, and transports the body conversion into its fibre.
The required source context extension is obtained by syntax inversion of
the given lambda typing, without source regularity or a Fundamental
premise. Neither arm assumes or supplies product membership in the
legacy universe. The evaluator remains explicitly scoped.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.InductiveLambdaArms

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements InductiveCodes

def model : AnnSemantics := FunctionEval.annSemantics legacyUniverseSystem

private theorem sort_relation {ν μ : Valuation} {Γ : LCtxA} {ρ σ : EnvI}
    {A B : ExprA} {u : Level}
    (h : PairedJudgment model ν μ Γ ρ σ A B (.sort u)) :
    NeutralCodes.UniversePER (eval ν u)
      (UnitModel.denote ν ρ A) (UnitModel.denote μ σ B) := by
  obtain ⟨k, R, S, hp, hr⟩ := h
  have hc : model.Code k (universeValue (eval ν u)) R := by
    simpa only [model.sort_image] using hp.left_code
  exact (model.coherent hc (model.universe_code _) _ _).mp hr

private theorem sort_code_pair {ν μ : Valuation} {Γ : LCtxA} {ρ σ : EnvI}
    {A B : ExprA} {u : Level}
    (h : PairedJudgment model ν μ Γ ρ σ A B (.sort u)) :
    ∃ R S, CodePair model.toCodeSystem (eval ν u)
      (UnitModel.denote ν ρ A) (UnitModel.denote μ σ B) R S :=
  legacyUniverseTransport.relate (sort_relation h)

private theorem decoded_code_of_legacy_relation {k : Option Nat} {V W : Value}
    (h : NeutralCodes.UniversePER k V W) : CodeI k V (decodedEl k V) := by
  obtain ⟨R, S, hR, hS, hRS⟩ := NeutralCodes.universe_transport h
  exact decodedEl_code (CodeI.old hR)

private theorem decoded_same_of_legacy_relation {k : Option Nat} {V W : Value}
    (h : NeutralCodes.UniversePER k V W) : Same (decodedEl k V) (decodedEl k W) := by
  obtain ⟨R, S, hR, hS, hRS⟩ := NeutralCodes.universe_transport h
  intro x y
  exact (decodedEl_same (CodeI.old hR) x y).trans
    ((hRS x y).trans (decodedEl_same (CodeI.old hS) x y).symm)

/-- The source codomain family determines explicit decoded fibres and a
genuine native product code. The legal-domain premises are used directly. -/
theorem denote_pi_code {ν : Valuation} {ρ : EnvI} {A B : ExprA} {u v : Level}
    {D : Relation} (hA : CodeI (eval ν u) (UnitModel.denote ν ρ A) D)
    (hB : ∀ x y, D x y → NeutralCodes.UniversePER (eval ν v)
      (UnitModel.denote ν (EnvI.cons x ρ) B)
      (UnitModel.denote ν (EnvI.cons y ρ) B)) :
    CodeI (imaxLevel (eval ν u) (eval ν v))
      (UnitModel.denote ν ρ (.pi A u B v))
      (FunctionPER NeutralPi.applyValue D
        (fun x => decodedEl (eval ν v) (UnitModel.denote ν (EnvI.cons x ρ) B))) := by
  apply CodeI.pi (kA := eval ν u) (kB := eval ν v)
    (A := UnitModel.denote ν ρ A) (C := UnitModel.denote ν ρ (.lam A u B))
    (RA := D)
    (RB := fun x => decodedEl (eval ν v) (UnitModel.denote ν (EnvI.cons x ρ) B)) hA
  · intro x y hxy
    exact code_value_eq (decoded_code_of_legacy_relation (hB x y hxy))
      (FunctionEval.denote_lambda_application ν ρ A B u x).symm
  · intro x y hxy
    exact decoded_same_of_legacy_relation (hB x y hxy)
  · exact (piValue_annotated ν ρ A B u v).symm
  · exact fun _ _ => Iff.rfl

/-- An exact paired Ty_lam supplier. Both code formation and whole-domain
lambda relatedness are constructed from the three stipulated child IHs. -/
theorem ty_lam_supplied (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Ty_lam model E I n := by
  intro Γ A u body B v hA hB hbody ihA ihB ihbody hΓ ν μ ρ σ hν hρ
  have hΓA : CtxWfA E I n (.assumption A :: Γ) := .assumption hΓ hA
  obtain ⟨D, F, hAD⟩ := sort_code_pair (ihA hΓ ν μ ρ σ hν hρ)
  let C : Value → Relation := fun x =>
    decodedEl (eval ν v) (UnitModel.denote ν (EnvI.cons x ρ) B)
  let G : Value → Relation := fun x =>
    decodedEl (eval μ v) (UnitModel.denote μ (EnvI.cons x σ) B)
  have hBL : ∀ x y, D x y → NeutralCodes.UniversePER (eval ν v)
      (UnitModel.denote ν (EnvI.cons x ρ) B)
      (UnitModel.denote ν (EnvI.cons y ρ) B) := by
    intro x y hxy
    exact sort_relation (ihB hΓA ν ν (EnvI.cons x ρ) (EnvI.cons y ρ)
      (ValuationRel.refl ν)
      (.assumption hρ.left_diagonal (CodePair.diagonal hAD.left_code) hxy))
  have hBR : ∀ x y, F x y → NeutralCodes.UniversePER (eval μ v)
      (UnitModel.denote μ (EnvI.cons x σ) B)
      (UnitModel.denote μ (EnvI.cons y σ) B) := by
    intro x y hxy
    exact sort_relation (ihB hΓA μ μ (EnvI.cons x σ) (EnvI.cons y σ)
      (ValuationRel.refl μ)
      (.assumption hρ.right_diagonal (CodePair.diagonal hAD.right_code) hxy))
  have hAμ : CodeI (eval μ u) (UnitModel.denote μ σ A) F := by
    rw [← eval_of_valuationRel hν u]
    exact hAD.right_code
  have hPL : CodeI (imaxLevel (eval ν u) (eval ν v))
      (UnitModel.denote ν ρ (.pi A u B v))
      (FunctionPER NeutralPi.applyValue D C) := denote_pi_code hAD.left_code hBL
  have hPR : CodeI (imaxLevel (eval ν u) (eval ν v))
      (UnitModel.denote μ σ (.pi A u B v))
      (FunctionPER NeutralPi.applyValue F G) := by
    have h : CodeI (imaxLevel (eval μ u) (eval μ v))
        (UnitModel.denote μ σ (.pi A u B v))
        (FunctionPER NeutralPi.applyValue F G) := denote_pi_code hAμ hBR
    rw [← eval_of_valuationRel hν u, ← eval_of_valuationRel hν v] at h
    exact h
  refine ⟨imaxLevel (eval ν u) (eval ν v),
    FunctionPER NeutralPi.applyValue D C, FunctionPER NeutralPi.applyValue F G,
    ⟨hPL, hPR, ?_⟩, ?_⟩
  · apply functionPER_same (code_laws hAD.left_code) hAD.transport
    intro x hx
    have hb := sort_relation (ihB hΓA ν μ (EnvI.cons x ρ) (EnvI.cons x σ)
      hν (.assumption hρ hAD hx))
    change Same (decodedEl (eval ν v) _) (decodedEl (eval μ v) _)
    rw [← eval_of_valuationRel hν v]
    exact decoded_same_of_legacy_relation hb
  · apply FunctionEval.denote_lambdas_related
    intro x y hxy
    obtain ⟨kb, Rb, Sb, hcb, hrel⟩ :=
      ihbody hΓA ν μ (EnvI.cons x ρ) (EnvI.cons y σ) hν (.assumption hρ hAD hxy)
    exact (code_coherent hcb.left_code (decoded_code_of_legacy_relation (hBL x y hxy))
      _ _).mp hrel

/-- Source syntax inversion sufficient for the exact Conv_lam context.
In the conversion case, its explicit target-formation premise supplies
the domain through the inherited product-parts lemma. -/
def source_lam_pi_domain {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {A A' body B : ExprA} {u u' v : Level}
    (h : HasTyA E I n Γ (.lam A' u' body) (.pi A u B v)) :
    HasTyA E I n Γ A (.sort u) := by
  cases h with
  | lam => assumption
  | conv =>
    have hp : HasTyA E I n Γ A (.sort u) ×
        HasTyA E I n (.assumption A :: Γ) B (.sort v) :=
      hasTyA_pi_parts (by assumption)
    exact hp.1

/-- An exact paired Conv_lam supplier. Its existing result type code is
preserved and the stipulated body IH is transported into that code's
actual dependent fibre. -/
theorem conv_lam_supplied (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Conv_lam model E I n := by
  intro Γ A A' b b' B u u' v hu hA hb hrt ihA ihb ihrt hΓ ν μ ρ σ hν hρ
  have hΓA : CtxWfA E I n (.assumption A :: Γ) :=
    .assumption hΓ (source_lam_pi_domain hrt)
  have hAcross := (ihA hΓ ν μ ρ σ hν hρ).related_types legacyUniverseTransport
  have hAright := (ihA hΓ μ μ σ σ (ValuationRel.refl μ) hρ.right_diagonal).related_types
    legacyUniverseTransport
  obtain ⟨ka, Da, Sa, hAD⟩ := hAcross.trans hAright.symm
  obtain ⟨k, R, S, hp, _⟩ := ihrt hΓ ν μ ρ σ hν hρ
  obtain ⟨kA, kB, D, C, hD, hC, hcoherent, hR⟩ := denote_pi_view hp.left_code
  have hDDa : Same D Da := code_coherent hD hAD.left_code
  refine ⟨k, R, S, hp, (hR _ _).mpr ?_⟩
  apply FunctionEval.denote_lambdas_related
  intro x y hxy
  obtain ⟨kb, Rb, Sb, hcb, hrel⟩ :=
    ihb hΓA ν μ (EnvI.cons x ρ) (EnvI.cons y σ) hν
      (.assumption hρ hAD ((hDDa x y).mp hxy))
  exact (code_coherent hcb.left_code (hC x y hxy) _ _).mp hrel

end Rcic.Declarative.Ann.LR3.InductiveLambdaArms

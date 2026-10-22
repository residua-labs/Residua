import rcic.RcicAnnLR3EnvironmentPi
import rcic.RcicAnnLR3InductiveLambdaArms

/-!
# Exact paired lambda arms for the environment-aware evaluator

The environment evaluator's proved product shape and complete lambda graph
instantiate the existing CodeI algebra. Both lambda contracts use precisely
their stipulated child induction hypotheses. The source context extension
reuses the landed syntax inversion, without a regularity or Fundamental
premise. These suppliers are scoped to the legacy universe attachment;
they do not supply Ty_pi, Conv_pi or full universe closure.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.EnvironmentLambdaArms

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements InductiveCodes

def model (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax) : AnnSemantics :=
  EnvironmentEval.annSemantics legacyUniverseSystem E H

private theorem sort_relation {E : ResolvedEnvA} {H : EnvironmentEval.FamilySyntax}
    {ν μ : Valuation} {Γ : LCtxA} {ρ σ : EnvI} {A B : ExprA} {u : Level}
    (h : PairedJudgment (model E H) ν μ Γ ρ σ A B (.sort u)) :
    NeutralCodes.UniversePER (eval ν u)
      (EnvironmentEval.denote E H ν ρ A) (EnvironmentEval.denote E H μ σ B) := by
  obtain ⟨k, R, S, hp, hr⟩ := h
  have hc : (model E H).Code k (universeValue (eval ν u)) R := by
    simpa only [(model E H).sort_image] using hp.left_code
  exact ((model E H).coherent hc ((model E H).universe_code _) _ _).mp hr

private theorem sort_code_pair {E : ResolvedEnvA} {H : EnvironmentEval.FamilySyntax}
    {ν μ : Valuation} {Γ : LCtxA} {ρ σ : EnvI} {A B : ExprA} {u : Level}
    (h : PairedJudgment (model E H) ν μ Γ ρ σ A B (.sort u)) :
    ∃ R S, CodePair (model E H).toCodeSystem (eval ν u)
      (EnvironmentEval.denote E H ν ρ A) (EnvironmentEval.denote E H μ σ B) R S :=
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

/-- Inversion keeps the new evaluator's actual domain and dependent body
images. It is not an assertion of product membership in a universe. -/
theorem denote_pi_view {E : ResolvedEnvA} {H : EnvironmentEval.FamilySyntax}
    {ν : Valuation} {ρ : EnvI} {A B : ExprA} {u v : Level}
    {k : Option Nat} {R : Relation}
    (h : CodeI k (EnvironmentEval.denote E H ν ρ (.pi A u B v)) R) :
    ∃ kA kB RA RB, CodeI kA (EnvironmentEval.denote E H ν ρ A) RA ∧
      (∀ x y, RA x y → CodeI kB (EnvironmentEval.denote E H ν (EnvI.cons x ρ) B) (RB x)) ∧
      FamilyCoherent RA RB ∧ Same R (FunctionPER NeutralPi.applyValue RA RB) := by
  obtain ⟨kA, kB, RA, RB, hA, hB, hc, hr⟩ :=
    code_pi_view (EnvironmentEval.denote_bot E H ν ρ A)
      (code_value_eq h (EnvironmentEval.denote_pi_value E H ν ρ A B u v))
  exact ⟨kA, kB, RA, RB, hA, fun x y hxy => code_value_eq (hB x y hxy)
    (EnvironmentEval.denote_lambda_application E H ν ρ A B u x), hc, hr⟩

/-- Explicit decoded fibres produce a CodeI product for the actual new
evaluator, from a domain code and its legal codomain formation images. -/
theorem denote_pi_code {E : ResolvedEnvA} {H : EnvironmentEval.FamilySyntax}
    {ν : Valuation} {ρ : EnvI} {A B : ExprA} {u v : Level}
    {D : Relation} (hA : CodeI (eval ν u) (EnvironmentEval.denote E H ν ρ A) D)
    (hB : ∀ x y, D x y → NeutralCodes.UniversePER (eval ν v)
      (EnvironmentEval.denote E H ν (EnvI.cons x ρ) B)
      (EnvironmentEval.denote E H ν (EnvI.cons y ρ) B)) :
    CodeI (imaxLevel (eval ν u) (eval ν v))
      (EnvironmentEval.denote E H ν ρ (.pi A u B v))
      (FunctionPER NeutralPi.applyValue D
        (fun x => decodedEl (eval ν v) (EnvironmentEval.denote E H ν (EnvI.cons x ρ) B))) := by
  apply CodeI.pi (kA := eval ν u) (kB := eval ν v)
    (A := EnvironmentEval.denote E H ν ρ A)
    (C := EnvironmentEval.denote E H ν ρ (.lam A u B)) (RA := D)
    (RB := fun x => decodedEl (eval ν v) (EnvironmentEval.denote E H ν (EnvI.cons x ρ) B)) hA
  · intro x y hxy
    exact code_value_eq (decoded_code_of_legacy_relation (hB x y hxy))
      (EnvironmentEval.denote_lambda_application E H ν ρ A B u x).symm
  · intro x y hxy
    exact decoded_same_of_legacy_relation (hB x y hxy)
  · exact EnvironmentEval.denote_pi_value E H ν ρ A B u v
  · exact fun _ _ => Iff.rfl

/-- Exact Ty_lam at the environment-aware evaluator; the three required
child IHs supply both formation and the whole legal-domain lambda law. -/
theorem ty_lam_supplied (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax)
    (I : IotaIfaceA) (n : Nat) : PairedArms.Ty_lam (model E H) E I n := by
  intro Γ A u body B v hA hB hbody ihA ihB ihbody hΓ ν μ ρ σ hν hρ
  have hΓA : CtxWfA E I n (.assumption A :: Γ) := .assumption hΓ hA
  obtain ⟨D, F, hAD⟩ := sort_code_pair (ihA hΓ ν μ ρ σ hν hρ)
  let C : Value → Relation := fun x =>
    decodedEl (eval ν v) (EnvironmentEval.denote E H ν (EnvI.cons x ρ) B)
  let G : Value → Relation := fun x =>
    decodedEl (eval μ v) (EnvironmentEval.denote E H μ (EnvI.cons x σ) B)
  have hBL : ∀ x y, D x y → NeutralCodes.UniversePER (eval ν v)
      (EnvironmentEval.denote E H ν (EnvI.cons x ρ) B)
      (EnvironmentEval.denote E H ν (EnvI.cons y ρ) B) := by
    intro x y hxy
    exact sort_relation (ihB hΓA ν ν (EnvI.cons x ρ) (EnvI.cons y ρ)
      (ValuationRel.refl ν)
      (.assumption hρ.left_diagonal (CodePair.diagonal hAD.left_code) hxy))
  have hBR : ∀ x y, F x y → NeutralCodes.UniversePER (eval μ v)
      (EnvironmentEval.denote E H μ (EnvI.cons x σ) B)
      (EnvironmentEval.denote E H μ (EnvI.cons y σ) B) := by
    intro x y hxy
    exact sort_relation (ihB hΓA μ μ (EnvI.cons x σ) (EnvI.cons y σ)
      (ValuationRel.refl μ)
      (.assumption hρ.right_diagonal (CodePair.diagonal hAD.right_code) hxy))
  have hAμ : CodeI (eval μ u) (EnvironmentEval.denote E H μ σ A) F := by
    rw [← eval_of_valuationRel hν u]
    exact hAD.right_code
  have hPL : CodeI (imaxLevel (eval ν u) (eval ν v))
      (EnvironmentEval.denote E H ν ρ (.pi A u B v))
      (FunctionPER NeutralPi.applyValue D C) := denote_pi_code hAD.left_code hBL
  have hPR : CodeI (imaxLevel (eval ν u) (eval ν v))
      (EnvironmentEval.denote E H μ σ (.pi A u B v))
      (FunctionPER NeutralPi.applyValue F G) := by
    have h : CodeI (imaxLevel (eval μ u) (eval μ v))
        (EnvironmentEval.denote E H μ σ (.pi A u B v))
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
  · apply EnvironmentEval.denote_lambdas_related
    intro x y hxy
    obtain ⟨kb, Rb, Sb, hcb, hrel⟩ :=
      ihbody hΓA ν μ (EnvI.cons x ρ) (EnvI.cons y σ) hν (.assumption hρ hAD hxy)
    exact (code_coherent hcb.left_code (decoded_code_of_legacy_relation (hBL x y hxy))
      _ _).mp hrel

/-- Exact Conv_lam for the same evaluator and code system. The result
typing child supplies the product code used to transport the body IH. -/
theorem conv_lam_supplied (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax)
    (I : IotaIfaceA) (n : Nat) : PairedArms.Conv_lam (model E H) E I n := by
  intro Γ A A' b b' B u u' v hu hA hb hrt ihA ihb ihrt hΓ ν μ ρ σ hν hρ
  have hΓA : CtxWfA E I n (.assumption A :: Γ) :=
    .assumption hΓ (InductiveLambdaArms.source_lam_pi_domain hrt)
  have hAcross := (ihA hΓ ν μ ρ σ hν hρ).related_types legacyUniverseTransport
  have hAright := (ihA hΓ μ μ σ σ (ValuationRel.refl μ) hρ.right_diagonal).related_types
    legacyUniverseTransport
  obtain ⟨ka, Da, Sa, hAD⟩ := hAcross.trans hAright.symm
  obtain ⟨k, R, S, hp, _⟩ := ihrt hΓ ν μ ρ σ hν hρ
  obtain ⟨kA, kB, D, C, hD, hC, hcoherent, hR⟩ := denote_pi_view hp.left_code
  have hDDa : Same D Da := code_coherent hD hAD.left_code
  refine ⟨k, R, S, hp, (hR _ _).mpr ?_⟩
  apply EnvironmentEval.denote_lambdas_related
  intro x y hxy
  obtain ⟨kb, Rb, Sb, hcb, hrel⟩ :=
    ihb hΓA ν μ (EnvI.cons x ρ) (EnvI.cons y σ) hν
      (.assumption hρ hAD ((hDDa x y).mp hxy))
  exact (code_coherent hcb.left_code (hC x y hxy) _ _).mp hrel

def controlOne : Level := .succ .zero
def controlTwo : Level := .succ controlOne
def controlType : ExprA := .pi (.sort controlOne) controlTwo (.sort controlOne) controlTwo
def controlTerm : ExprA := .lam (.sort controlOne) controlTwo (.sort .zero)

def control_domain (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    HasTyA E I n Γ (.sort controlOne) (.sort controlTwo) := .sort Γ controlOne

def control_body (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    HasTyA E I n (.assumption (.sort controlOne) :: Γ) (.sort .zero) (.sort controlOne) :=
  .sort _ .zero

def control_function (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    HasTyA E I n Γ controlTerm controlType :=
  .lam Γ (.sort controlOne) controlTwo (.sort .zero) (.sort controlOne) controlTwo
    (control_domain E I n Γ) (control_domain E I n (.assumption (.sort controlOne) :: Γ))
    (control_body E I n Γ)

/-- Every child IH of this closed lambda is supplied by the actual sort
arm, uniformly in the admitted-member hooks. -/
theorem control_function_IH (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax)
    (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    PairedTyGoal (model E H) E I n Γ controlTerm controlType :=
  ty_lam_supplied E H I n Γ (.sort controlOne) controlTwo (.sort .zero)
    (.sort controlOne) controlTwo
    (control_domain E I n Γ) (control_domain E I n (.assumption (.sort controlOne) :: Γ))
    (control_body E I n Γ)
    (PairedArms.ty_sort_supplied (model E H) E I n Γ controlOne)
    (PairedArms.ty_sort_supplied (model E H) E I n (.assumption (.sort controlOne) :: Γ) controlOne)
    (PairedArms.ty_sort_supplied (model E H) E I n (.assumption (.sort controlOne) :: Γ) .zero)

theorem control_conversion_IH (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax)
    (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    PairedConvGoal (model E H) E I n Γ controlTerm controlTerm controlType :=
  conv_lam_supplied E H I n Γ (.sort controlOne) (.sort controlOne)
    (.sort .zero) (.sort .zero) (.sort controlOne) controlTwo controlTwo controlTwo (fun _ => rfl)
    (.refl Γ (.sort controlOne) (.sort controlTwo) (control_domain E I n Γ))
    (.refl (.assumption (.sort controlOne) :: Γ) (.sort .zero) (.sort controlOne)
      (control_body E I n Γ)) (control_function E I n Γ)
    (PairedArms.ty_sort_supplied (model E H) E I n Γ controlOne)
    (PairedArms.ty_sort_supplied (model E H) E I n (.assumption (.sort controlOne) :: Γ) .zero)
    (control_function_IH E H I n Γ)

theorem control_inhabited (H : EnvironmentEval.FamilySyntax) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 []) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] controlTerm controlType) ∧
    PairedTyGoal (model emptyEnvA H) emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      controlTerm controlType ∧
    PairedConvGoal (model emptyEnvA H) emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      controlTerm controlTerm controlType :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨control_function _ _ _ _⟩,
    control_function_IH _ H _ _ _, control_conversion_IH _ H _ _ _⟩

theorem control_judgment (E : ResolvedEnvA) (H : EnvironmentEval.FamilySyntax)
    (I : IotaIfaceA) (n : Nat) (ν μ : Valuation) (ρ σ : EnvI) (hν : ValuationRel ν μ) :
    PairedJudgment (model E H) ν μ [] ρ σ controlTerm controlTerm controlType :=
  control_function_IH E H I n [] .nil ν μ ρ σ hν (.nil _ _)

end Rcic.Declarative.Ann.LR3.EnvironmentLambdaArms

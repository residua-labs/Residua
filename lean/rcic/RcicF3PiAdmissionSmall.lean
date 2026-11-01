import rcic.RcicF3PiAdmission
import rcic.RcicF3PiLive
/-! Bounded raw typing and admitted independent small fields.
This is field-only composition, not universal A-axis closure.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiIndependent
open Rcic.Declarative
/-- Raw bounded typing pays smallness; successful admission pays independence. -/
theorem admitted_small_field (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) {E : ResolvedEnv} {n fuel f nu np ni depth inner : Nat}
    {Γ : LCtx} {T : Expr Nat} {l : Level} {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel f nu np ni depth T = .permitted (.recursive inner) idx)
    (hscope : np ≤ inner + depth) (d : HasTyT E n Γ T (.sort l))
    (hd : LOKt σ 4 K d) :
    ∃ ds args, ds.length = inner ∧ args.length = np + ni ∧
      (∀ X₁ X₂ ρ, recursiveTel P (upd μ f X₁) σ ds args ρ =
        recursiveTel P (upd μ f X₂) σ ds args ρ) ∧
      ∀ X, EnvSound (mkM P (upd μ f X)) σ K E n → BodiesOK E σ K →
      ∀ ρ, Fits (mkM P (upd μ f X)) σ Γ ρ → ∀ x,
      x ∈ Ed (mkM P (upd μ f X)) (den (mkM P (upd μ f X)) σ ρ T) →
      x ∈ Ed (mkM P (upd μ f X))
        ((PiSmallCompile.widen (recursiveTel P μ σ ds args ρ)).erasedType
          (mkM P (upd μ f X)) (fun xs => Ed (mkM P (upd μ f X))
            (fapps (X (((List.range nu).map Level.param).map (evalTotal σ))) xs))) := by
  obtain ⟨ds, args, hl, ha, hr, hds, hargs⟩ := admitted_shape h hscope
  refine ⟨ds, args, hl, ha, ?_, ?_⟩
  · intro X₁ X₂ ρ
    exact recursiveTel_free P μ f X₁ X₂ σ ds args hds hargs ρ
  · intro X hE hb ρ hρ x hx
    exact PiSmallValue.normalized_mem P μ f X σ K hE hb (fuel - 1) T _ ds args
      hr (instOK_of_lokt σ 4 K d hd) hds hargs ρ x
      (PiSmallValue.typed_value_small P (upd μ f X) σ K hE d hd ρ hρ hx) hx

end Rcic.F3.PSet.PiIndependent

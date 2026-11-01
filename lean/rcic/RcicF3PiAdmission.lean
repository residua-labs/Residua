import rcic.RcicF3PiIndependentField
/-! Admission-to-independent-signature composition. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiIndependent
open Rcic.Declarative
/-- Successful recursive admission supplies the complete free normalized
shape, before choosing a candidate family. Elementary inversion. -/
theorem admitted_shape {E : ResolvedEnv}
    {fuel f nu np ni depth inner : Nat} {T : Expr Nat} {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel f nu np ni depth T = .permitted (.recursive inner) idx)
    (hscope : np ≤ inner + depth) :
    ∃ ds args, ds.length = inner ∧ args.length = np + ni ∧
      piTelescopeFuel E (fuel - 1) T =
        some (ds, foldApps (.const f ((List.range nu).map Level.param)) args) ∧
      (∀ e ∈ ds, occursConst f e = false) ∧
      (∀ e ∈ args, occursConst f e = false) := by
  obtain ⟨ds, b, hr, hl, _, hd, hp⟩ := recursive_scans h
  have hs : np ≤ ds.length + depth - 1 + 1 := by rw [hl]; omega
  obtain ⟨ix, hb, hix, hfree⟩ := properFamilyFuel_shape hs hp
  refine ⟨ds, policyParameterLocals np (ds.length + depth - 1 + 1 - np) ++ ix,
    hl, ?_, ?_, domains_free _ _ hd, ?_⟩
  · simp only [List.length_append, policyParameterLocals_length, hix]
  · rw [← hb]; exact hr
  · intro e he
    rcases List.mem_append.mp he with he | he
    · simp only [policyParameterLocals, List.mem_map] at he
      obtain ⟨i, _, rfl⟩ := he
      rfl
    · exact hfree e he
/-- Admission supplies both the independent signature and membership for
all normalized inhabited inputs, without assumed family-free walls.
This is an elementary composition; domain smallness remains unclaimed. -/
theorem admitted_field (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n fuel f nu np ni depth inner : Nat} {T : Expr Nat}
    {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel f nu np ni depth T = .permitted (.recursive inner) idx)
    (hscope : np ≤ inner + depth) (hI : InstOK E σ K T) :
    ∃ ds args, ds.length = inner ∧ args.length = np + ni ∧
      (∀ X₁ X₂ ρ, recursiveTel P (upd μ f X₁) σ ds args ρ =
        recursiveTel P (upd μ f X₂) σ ds args ρ) ∧
      ∀ X, EnvSound (mkM P (upd μ f X)) σ K E n → BodiesOK E σ K →
      ∀ ρ x, x ∈ Ed (mkM P (upd μ f X)) (den (mkM P (upd μ f X)) σ ρ T) →
      x ∈ Ed (mkM P (upd μ f X))
        ((PiSyntaxCompile.compile (mkM P μ) σ (leafArgs P μ σ args) ds ρ).erasedType
          (mkM P (upd μ f X)) (fun xs => Ed (mkM P (upd μ f X))
            (fapps (X (((List.range nu).map Level.param).map (evalTotal σ))) xs))) := by
  obtain ⟨ds, args, hl, ha, hr, hd, hf⟩ := admitted_shape h hscope
  refine ⟨ds, args, hl, ha, ?_, ?_⟩
  · intro X₁ X₂ ρ
    exact recursiveTel_free P μ f X₁ X₂ σ ds args hd hf ρ
  · intro X hE hb ρ x hx
    exact normalized_mem P μ f X σ K hE hb (fuel - 1) T _ ds args hr hI hd hf ρ x hx

end Rcic.F3.PSet.PiIndependent

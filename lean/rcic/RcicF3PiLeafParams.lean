import rcic.RcicF3RawFamilyRec
import rcic.RcicF3PiRawParams
/-! Reachability and fixed-parameter readback for every path of the actual
dependent telescope. Original admission pays the prefix invariant; no
semantic parameter-readback wall is added. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSyntaxCompile
open Rcic.Declarative
universe u v
theorem result_fits {I : Type v} (M : Interp.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{u}) → I) : ∀ ds ρ p,
    ∃ xs, TelFits M σ ds ρ xs ∧ (compile M σ R ds ρ).result p = R (push xs ρ) := by
  intro ds
  induction ds with
  | nil =>
    intro ρ p
    exact ⟨[], trivial, rfl⟩
  | cons A ds ih =>
    intro ρ p
    let D := Ed M (den M σ ρ A)
    let a := PiCompile.classValue D p.1
    obtain ⟨xs, hx, hr⟩ := ih (vcons a ρ) p.2
    exact ⟨a :: xs, ⟨PiCompile.classValue_mem D p.1, hx⟩, hr⟩
end Rcic.F3.PSet.PiSyntaxCompile

namespace Rcic.F3.PSet.PiLeafParams
open Rcic.Declarative PiIndex RawFamilyRec
theorem result_parameters (M : Interp.{4}) (σ : Nat → Nat)
    (ds args : List (Expr Nat)) (ρ : Nat → PSet.{4}) (ps : List PSet.{4})
    (hp : ∀ xs, TelFits M σ ds ρ xs → (args.take ps.length).map (den M σ (push xs ρ)) = ps) :
    ∀ p, paramKey ps.length ((tel M σ ds args ρ).result p) = key ps := by
  intro p
  obtain ⟨xs, hx, hr⟩ := PiSyntaxCompile.result_fits M σ (read M σ args) ds ρ p
  change paramKey ps.length ((PiSyntaxCompile.compile M σ (read M σ args) ds ρ).result p) = _
  rw [hr]
  change key ((args.map (den M σ (push xs ρ))).take ps.length) = key ps
  rw [← List.map_take, hp xs hx]
theorem admitted_result_parameters (M : Interp.{4}) (σ : Nat → Nat)
    (ps pre : List PSet.{4}) (ρ : Nat → PSet.{4})
    {E : ResolvedEnv} {fuel f nu ni inner : Nat} {T : Expr Nat}
    {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel f nu ps.length ni (ps.length + pre.length) T =
      .permitted (.recursive inner) idx) :
    ∃ ds ix, ds.length = inner ∧ ix.length = ni ∧
      piTelescopeFuel E (fuel - 1) T = some (ds,
        foldApps (.const f ((List.range nu).map Level.param))
          (policyParameterLocals ps.length (pre.length + ds.length) ++ ix)) ∧
      ∀ p, paramKey ps.length
        ((tel M σ ds (policyParameterLocals ps.length (pre.length + ds.length) ++ ix)
          (push pre (push ps ρ))).result p) = key ps := by
  obtain ⟨ds, ix, hl, hi, hr, hp⟩ := PiRawParams.admitted_readback M σ ps pre ρ h
  refine ⟨ds, ix, hl, hi, hr, ?_⟩
  exact result_parameters M σ ds _ (push pre (push ps ρ)) ps
    (fun xs hxs => hp xs hxs.length)
end Rcic.F3.PSet.PiLeafParams

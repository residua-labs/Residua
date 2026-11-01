import rcic.RcicF3PiEraseMono
import rcic.RcicF3PiIndependentField
/-! Literal normalized recursive fields preserve their original values
under inclusion of candidate result fibres. Domain/index scans supply
independence; arbitrary dependent depth and numerical labels are retained.
This does not yet produce normalization/environment inputs for every group.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecTel
universe v
theorem erasedType_tables {I : Type v} (P : Premises4)
    (μ₁ μ₂ : Nat → List Nat → PSet.{4}) {m : Nat}
    (t : RecTel.{4,v} I m) (X : I → PSet.{4}) :
    t.erasedType (mkM P μ₁) X = t.erasedType (mkM P μ₂) X := by
  induction t with
  | ret i => rfl
  | pi A B ih =>
    simp only [erasedType]
    have he : ∀ q, Ed (mkM P μ₁) ((B q).erasedType (mkM P μ₁) X) =
        Ed (mkM P μ₂) ((B q).erasedType (mkM P μ₂) X) := by
      intro q
      rw [ih q]
      rfl
    rw [funext he]
    rfl
end Rcic.F3.PSet.RecTel

namespace Rcic.F3.PSet.PiIndependent
open Rcic.Declarative
theorem recursiveField_sub (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X Y : List Nat → PSet.{4}) (σ : Nat → Nat) (ls : List Level)
    (ds args : List (Expr Nat)) (hd : ∀ e ∈ ds, occursConst f e = false)
    (ha : ∀ e ∈ args, occursConst f e = false) (ρ : Nat → PSet.{4})
    (hsub : ∀ xs, Sub (Ed (mkM P μ) (fapps (X (ls.map (evalTotal σ))) xs))
      (Ed (mkM P μ) (fapps (Y (ls.map (evalTotal σ))) xs))) :
    Sub (Ed (mkM P (upd μ f X)) (den (mkM P (upd μ f X)) σ ρ
      (policyPi ds (foldApps (.const f ls) args))))
      (Ed (mkM P (upd μ f Y)) (den (mkM P (upd μ f Y)) σ ρ
        (policyPi ds (foldApps (.const f ls) args)))) := by
  let M := mkM P μ
  let t := PiSyntaxCompile.compile M σ (leafArgs P μ σ args) ds ρ
  intro x hx
  have hxT := mem_congr_right (recursiveField_ed P μ f X σ ls ds args hd ha ρ).symm hx
  rw [t.erasedType_tables P (upd μ f X) μ] at hxT
  have ht : t.DomainsDich := PiSyntaxCompile.compile_domains M σ _ ds ρ
  have hyT := t.erasedType_mono M ht
    (fun xs => Ed M (fapps (X (ls.map (evalTotal σ))) xs))
    (fun xs => Ed M (fapps (Y (ls.map (evalTotal σ))) xs))
    (fun _ => dich_ed M _) (fun _ => dich_ed M _) hsub x hxT
  rw [← t.erasedType_tables P (upd μ f Y) μ] at hyT
  exact mem_congr_right (recursiveField_ed P μ f Y σ ls ds args hd ha ρ) hyT
end Rcic.F3.PSet.PiIndependent

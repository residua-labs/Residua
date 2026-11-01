import rcic.RcicF3PiLive
/-! Actual data-field values give candidate-independent element-set
fidelity. The data-leaf condition is explicit; proof families are not
claimed here. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiLive
open Rcic.Declarative PiSmallCompile
/-- An actual small field with data leaves fixes a signature for every
candidate interpretation. Agreement concerns normalized element sets. -/
theorem data_field_ed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X : List Nat → PSet.{4}) (σ : Nat → Nat) (ls : List Level)
    (ds args : List (Expr Nat)) (hd : ∀ e ∈ ds, occursConst f e = false)
    (ha : ∀ e ∈ args, occursConst f e = false) (ρ : Nat → PSet.{4}) (g : PSet.{4})
    (hs : Small.{3,4} g)
    (hb : ∀ ρ', pempty ∉ Ed (mkM P (upd μ f X))
      (den (mkM P (upd μ f X)) σ ρ' (foldApps (.const f ls) args)))
    (hg : g ∈ Ed (mkM P (upd μ f X))
      (den (mkM P (upd μ f X)) σ ρ (policyPi ds (foldApps (.const f ls) args)))) :
    ∀ Y : List Nat → PSet.{4},
    let M := mkM P (upd μ f Y)
    Equiv (Ed M ((widen (PiIndependent.recursiveTel P μ σ ds args ρ)).erasedType M
      (fun xs => Ed M (fapps (Y (ls.map (evalTotal σ))) xs))))
      (Ed M (den M σ ρ (policyPi ds (foldApps (.const f ls) args)))) := by
  have hl := liveSmall_of_member P (upd μ f X) σ (foldApps (.const f ls) args)
    hb ds ρ g hs hg
  intro Y
  dsimp only
  have hlY := (liveSmall_free P μ f X Y σ ds ρ hd).mp hl
  have he := compile_ed P (upd μ f Y) σ (PiIndependent.leafArgs P μ σ args)
    (fun xs => Ed (mkM P (upd μ f Y)) (fapps (Y (ls.map (evalTotal σ))) xs))
    (fun _ => dich_ed _ _) (foldApps (.const f ls) args) (fun ρ' => by
      rw [PiIndependent.leaf_read P μ f Y σ ls args ha ρ']; exact Equiv.rfl) ds ρ hlY
  have ht := PiIndependent.smallCompile_free P μ f Y (μ f) σ
    (PiIndependent.leafArgs P μ σ args) ds ρ hd
  rw [PiIndependent.upd_self] at ht
  rw [ht] at he
  exact he

end Rcic.F3.PSet.PiLive

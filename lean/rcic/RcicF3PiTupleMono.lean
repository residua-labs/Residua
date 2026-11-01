import rcic.RcicF3PiIndependentMono
import rcic.RcicF3PiValueRule
import rcic.RcicF3PiPropField
import rcic.RcicF3RawFamilyLaws
/-! Monotonicity of normalized dependent constructor tuples. Leaf comparison
is required only at complete argument spines; raw frame applications supply
that comparison even at nonfitting spines. Universe-stage smallness and
original-field normalization remain distinct obligations. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecTel
universe u v
 theorem erasedType_mono_on {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u,v} I m) (ht : t.DomainsDich) (X Y : I → PSet.{u})
    (hX : ∀ i, Dich (X i)) (hY : ∀ i, Dich (Y i))
    (hsub : ∀ p, Sub (X (t.result p)) (Y (t.result p))) :
    Sub (Ed M (t.erasedType M X)) (Ed M (t.erasedType M Y)) := by
  intro f hf
  have hr := t.erasedRead_spec M ht X hX hf
  have hrel : t.Rel Y (t.erasedRead M f) := by
    apply (PiTel.all_iff _ _ _).mpr
    intro p
    exact hsub p _ ((PiTel.all_iff _ _ _).mp hr.1 p)
  exact mem_congr_left hr.2.symm (t.erasedEncode_mem M ht Y hY _ hrel)
end Rcic.F3.PSet.RecTel

namespace Rcic.F3.PSet.PiIndependent
open Rcic.Declarative
 theorem recursiveField_sub_length (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X Y : List Nat → PSet.{4}) (σ : Nat → Nat) (ls : List Level)
    (ds args : List (Expr Nat)) (hd : ∀ e ∈ ds, occursConst f e = false)
    (ha : ∀ e ∈ args, occursConst f e = false) (ρ : Nat → PSet.{4})
    (hsub : ∀ xs, xs.length = args.length →
      Sub (Ed (mkM P μ) (fapps (X (ls.map (evalTotal σ))) xs))
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
  have hyT := t.erasedType_mono_on M ht
    (fun xs => Ed M (fapps (X (ls.map (evalTotal σ))) xs))
    (fun xs => Ed M (fapps (Y (ls.map (evalTotal σ))) xs))
    (fun _ => dich_ed M _) (fun _ => dich_ed M _)
    (fun p => hsub _ (PiPropField.compile_result_property M σ
      (leafArgs P μ σ args) (fun xs => xs.length = args.length)
      (fun _ => List.length_map _ _) ds ρ p)) x hxT
  rw [← t.erasedType_tables P (upd μ f Y) μ] at hyT
  exact mem_congr_right (recursiveField_ed P μ f Y σ ls ds args hd ha ρ) hyT
end Rcic.F3.PSet.PiIndependent

namespace Rcic.F3.PSet.PiTupleMono
open Rcic.Declarative PiValueRule
 theorem fits_mono (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f ar : Nat)
    (X Y : List Nat → PSet.{4}) (σ : Nat → Nat) (ls : List Level)
    (hsub : ∀ xs, xs.length = ar →
      Sub (Ed (mkM P μ) (fapps (X (ls.map (evalTotal σ))) xs))
        (Ed (mkM P μ) (fapps (Y (ls.map (evalTotal σ))) xs))) :
    ∀ fs, Clean f ar fs → ∀ ρ xs,
    TelFits (mkM P (upd μ f X)) σ (fs.map (fieldExpr f ls)) ρ xs →
    TelFits (mkM P (upd μ f Y)) σ (fs.map (fieldExpr f ls)) ρ xs := by
  intro fs
  induction fs with
  | nil =>
    intro _ ρ xs hx
    cases xs with
    | nil => trivial
    | cons x xs => exact False.elim hx
  | cons a fs ih =>
    intro hc ρ xs hx
    cases xs with
    | nil => exact False.elim hx
    | cons x xs =>
      cases a with
      | plain A =>
        have he := PiIndependent.den_free P μ f X Y σ A hc.1 ρ
        have hx' := hx.1
        change x ∈ Ed (mkM P μ) (den (mkM P (upd μ f X)) σ ρ A) at hx'
        rw [he] at hx'
        exact ⟨hx', ih hc.2 (vcons x ρ) xs hx.2⟩
      | recursive ds args =>
        exact ⟨PiIndependent.recursiveField_sub_length P μ f X Y σ ls ds args
          hc.1 hc.2.1 ρ (fun ys hy => hsub ys (hy.trans hc.2.2.1)) x hx.1,
          ih hc.2.2.2 (vcons x ρ) xs hx.2⟩
end Rcic.F3.PSet.PiTupleMono

namespace Rcic.F3.PSet.RawFamily
open Rcic.Declarative
 theorem apply_ofFrame_sub (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C D : Frame) (hC : Admissible fd C) (hD : Admissible fd D)
    (hsub : ∀ vs i, Sub (C vs i) (D vs i)) (vs : List Nat) (xs : List PSet.{4})
    (hl : xs.length = (fd.params ++ fd.indices).length) :
    Sub (Ed (mkM P μ) (fapps (ofFrame P μ fd C vs) xs))
      (Ed (mkM P μ) (fapps (ofFrame P μ fd D vs) xs)) := by
  cases P.dec (TelFits (mkM P μ) (σOf vs) (fd.params ++ fd.indices) ρ0 xs) with
  | isTrue hf =>
    intro z hz
    exact mem_congr_right (apply_ofFrame_ed P μ fd D hD vs xs hf).symm
      (hsub vs (PiIndex.key xs) z
        (mem_congr_right (apply_ofFrame_ed P μ fd C hC vs xs hf) hz))
  | isFalse hf =>
    have he := fapps_fam_nofit P μ fd (σOf vs)
      (endValue_resp C vs (fd.params.length + fd.indices.length)) xs hl hf
    intro z hz
    exact (not_mem_pempty (mem_congr_right
      ((ed_congr (mkM P μ) he).trans (ed_pempty (mkM P μ))) hz)).elim

end Rcic.F3.PSet.RawFamily

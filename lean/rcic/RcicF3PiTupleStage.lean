import rcic.RcicF3PiStageValue
import rcic.RcicF3PiTupleMono
/-! Stage transport for normalized constructor tuples. Complete raw frame
applications supply the data face and stage bound even on nonfitting
spines; source tuple membership supplies actual staged field values.
Literal hidden-redex normalization and universal group closure remain
separate obligations. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamily
open Rcic.Declarative
 theorem apply_ofFrame_data (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C) (vs : List Nat)
    (h0 : evalTotal (σOf vs) fd.resLevel ≠ 0) (xs : List PSet.{4})
    (hl : xs.length = (fd.params ++ fd.indices).length) :
    Ed (mkM P μ) (fapps (ofFrame P μ fd C vs) xs) ∈ W4 (evalTotal (σOf vs) fd.resLevel) ∧
      ∀ z, z ∈ Ed (mkM P μ) (fapps (ofFrame P μ fd C vs) xs) → ¬ Equiv z pempty := by
  cases P.dec (TelFits (mkM P μ) (σOf vs) (fd.params ++ fd.indices) ρ0 xs) with
  | isTrue hf =>
    have he := apply_ofFrame_ed P μ fd C hC vs xs hf
    have hc := hC vs (PiIndex.key xs)
    rw [if_neg h0] at hc
    exact ⟨mem_congr_left he.symm hc.1,
      fun z hz => hc.2 z (mem_congr_right he hz)⟩
  | isFalse hf =>
    have he := fapps_fam_nofit P μ fd (σOf vs)
      (endValue_resp C vs (fd.params.length + fd.indices.length)) xs hl hf
    have he' := (ed_congr (mkM P μ) he).trans (ed_pempty (mkM P μ))
    exact ⟨mem_congr_left he'.symm (stageW4 P _).empty,
      fun _ hz => (not_mem_pempty (mem_congr_right he' hz)).elim⟩
end Rcic.F3.PSet.RawFamily

namespace Rcic.F3.PSet.PiIndependent
open Rcic.Declarative
 theorem recursiveField_stage (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X Y : List Nat → PSet.{4}) (σ : Nat → Nat) (ls : List Level)
    (ds args : List (Expr Nat)) (hd : ∀ e ∈ ds, occursConst f e = false)
    (ha : ∀ e ∈ args, occursConst f e = false) (ρ : Nat → PSet.{4})
    (W : PSet.{4}) (hW : Stage W)
    (hN : ∀ xs, xs.length = args.length →
      ¬ pempty ∈ Ed (mkM P μ) (fapps (X (ls.map (evalTotal σ))) xs))
    (hS : ∀ xs, xs.length = args.length →
      Ed (mkM P μ) (fapps (Y (ls.map (evalTotal σ))) xs) ∈ W)
    {x : PSet.{4}} (hx : x ∈ Ed (mkM P (upd μ f X))
      (den (mkM P (upd μ f X)) σ ρ (policyPi ds (foldApps (.const f ls) args))))
    (hs : x ∈ W) :
    Ed (mkM P (upd μ f Y)) (den (mkM P (upd μ f Y)) σ ρ
      (policyPi ds (foldApps (.const f ls) args))) ∈ W := by
  let M := mkM P μ
  let t := PiSyntaxCompile.compile M σ (leafArgs P μ σ args) ds ρ
  have hxT := mem_congr_right (recursiveField_ed P μ f X σ ls ds args hd ha ρ).symm hx
  rw [t.erasedType_tables P (upd μ f X) μ] at hxT
  have ht : t.DomainsDich := PiSyntaxCompile.compile_domains M σ _ ds ρ
  have hl : ∀ p, (t.result p).length = args.length :=
    PiPropField.compile_result_property M σ (leafArgs P μ σ args)
      (fun xs => xs.length = args.length) (fun _ => List.length_map _ _) ds ρ
  have he := t.erasedType_stage_from_value M hW ht
    (fun xs => Ed M (fapps (X (ls.map (evalTotal σ))) xs))
    (fun xs => Ed M (fapps (Y (ls.map (evalTotal σ))) xs))
    (fun _ => dich_ed M _) (fun _ => dich_ed M _)
    (fun p => hN _ (hl p)) (fun p => hS _ (hl p)) hxT hs
  rw [← t.erasedType_tables P (upd μ f Y) μ] at he
  exact mem_congr_left (recursiveField_ed P μ f Y σ ls ds args hd ha ρ) he
end Rcic.F3.PSet.PiIndependent

namespace Rcic.F3.PSet.PiTupleMono
open Rcic.Declarative PiValueRule
 theorem smallAlong (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f ar : Nat)
    (X Y : List Nat → PSet.{4}) (σ : Nat → Nat) (ls : List Level)
    (W : PSet.{4}) (hW : Stage W)
    (hN : ∀ xs, xs.length = ar →
      ¬ pempty ∈ Ed (mkM P μ) (fapps (X (ls.map (evalTotal σ))) xs))
    (hS : ∀ xs, xs.length = ar →
      Ed (mkM P μ) (fapps (Y (ls.map (evalTotal σ))) xs) ∈ W) :
    ∀ fs, Clean f ar fs → ∀ ρ xs,
    TelFits (mkM P (upd μ f X)) σ (fs.map (fieldExpr f ls)) ρ xs →
    SmallAlong (mkM P (upd μ f X)) σ W (fs.map (fieldExpr f ls)) ρ xs →
    SmallAlong (mkM P (upd μ f Y)) σ W (fs.map (fieldExpr f ls)) ρ xs := by
  intro fs
  induction fs with
  | nil =>
    intro _ ρ xs hx _
    cases xs with
    | nil => trivial
    | cons _ _ => exact False.elim hx
  | cons a fs ih =>
    intro hc ρ xs hx hs
    cases xs with
    | nil => exact False.elim hx
    | cons x xs =>
      cases a with
      | plain A =>
        have he := PiIndependent.den_free P μ f X Y σ A hc.1 ρ
        refine ⟨?_, ih hc.2 (vcons x ρ) xs hx.2 hs.2⟩
        change Ed (mkM P μ) (den (mkM P (upd μ f Y)) σ ρ A) ∈ W
        rw [← he]
        exact hs.1
      | recursive ds args =>
        exact ⟨PiIndependent.recursiveField_stage P μ f X Y σ ls ds args
          hc.1 hc.2.1 ρ W hW (fun ys hy => hN ys (hy.trans hc.2.2.1))
          (fun ys hy => hS ys (hy.trans hc.2.2.1)) hx.1 (hW.trans hs.1 hx.1),
          ih hc.2.2.2 (vcons x ρ) xs hx.2 hs.2⟩
end Rcic.F3.PSet.PiTupleMono

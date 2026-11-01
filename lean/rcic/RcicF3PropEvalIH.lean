import rcic.RcicF3PropEval
import rcic.RcicF3PiIndexedIHApply

/-!
# Indexed IH computation carries actual child evaluations

This bridge turns evaluation certificates for the full-key leaf map into
the literal child certificates required by Inputs.recursive. The bounded
extraction variant needs existence and functionality only at keys reached
by fitting normalized arguments. It does not assume or assert universal
evaluation totality. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEval
open Rcic.Declarative PiIndex

/-- Transport the leaf certificate along the computed, actual-domain IH. -/
theorem indexed_children (C : Context) (ds args : List (Expr Nat))
    (ρ : Nat → PSet.{4}) (g : Index.{4} → PSet.{4} → PSet.{4})
    (hg : ∀ i x y, Equiv x y → Equiv (g i x) (g i y)) (x : PSet.{4})
    (hleaf : ∀ zs, TelFits C.M C.σ ds ρ zs →
      Eval C (key (args.map (den C.M C.σ (push zs ρ))))
        (g (key (args.map (den C.M C.σ (push zs ρ)))) (fapps x zs))) :
    ∀ zs, TelFits C.M C.σ ds ρ zs →
      Eval C (key (args.map (den C.M C.σ (push zs ρ))))
        (fapps ((tel C.M C.σ ds args ρ).indexedIH C.M g x) zs) :=
  fun zs hzs => (hleaf zs hzs).output_congr
    (PiIndexedIHApply.indexed_apply C.M C.σ ds args ρ g hg x zs hzs)

/-- Bounded existence and uniqueness at reached keys construct the child IH values.
No representative or evaluation witness is selected by a choice operator. -/
theorem indexed_children_of_bounded (C : Context) (ds args : List (Expr Nat))
    (ρ : Nat → PSet.{4}) (T : Index.{4} → PSet.{4}) (x : PSet.{4})
    (hex : ∀ zs, TelFits C.M C.σ ds ρ zs →
      let i := key (args.map (den C.M C.σ (push zs ρ)))
      ∃ z, z ∈ T i ∧ Eval C i z)
    (hfun : ∀ zs, TelFits C.M C.σ ds ρ zs →
      let i := key (args.map (den C.M C.σ (push zs ρ)))
      ∀ z z', z ∈ T i → z' ∈ T i → Eval C i z → Eval C i z' → Equiv z z') :
    ∀ zs, TelFits C.M C.σ ds ρ zs →
      Eval C (key (args.map (den C.M C.σ (push zs ρ))))
        (fapps ((tel C.M C.σ ds args ρ).indexedIH C.M
          (fun i _ => PropEvalExtract.value (T i) (Eval C i)) x) zs) := by
  apply indexed_children C ds args ρ
    (fun i _ => PropEvalExtract.value (T i) (Eval C i)) (fun _ _ _ _ => Equiv.rfl) x
  intro zs hzs
  exact (PropEvalExtract.value_spec_of_output_congr
    (hex zs hzs) (hfun zs hzs)
    (fun _ hz _ => hz)
    (fun _ _ he h => h.output_congr he.symm)).2

end Rcic.F3.PSet.PropEval

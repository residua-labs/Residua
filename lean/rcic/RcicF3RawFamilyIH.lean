import rcic.RcicF3RawFamilyView
import rcic.RcicF3PiRecBridge
import rcic.RcicF3PiLeafParams
import rcic.RcicF3PiTupleMono
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamilyIH
open Rcic.Declarative PiIndex RawFamily
/-- A data family's normalized raw recursive field supplies the exact
existing depth-based IH. Mapping soundness is used only for children below
the current constructor, and the data face pays the erased-leaf case. -/
theorem ih_mem_below (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (vs : List Nat) (h0 : evalTotal (σOf vs) fd.resLevel ≠ 0)
    (ls : List Level) (hls : ls.map (evalTotal (σOf vs)) = vs)
    (ds args : List (Expr Nat)) (ha : args.length = (fd.params ++ fd.indices).length)
    (ρ : Nat → PSet.{4})
    (Q : Index.{4} → PSet.{4} → PSet.{4}) (hQ : ∀ i y, Dich (Q i y))
    (g : PSet.{4} → PSet.{4})
    (hg : ∀ x y, Equiv x y → Equiv (g x) (g y)) (z x : PSet.{4})
    (hmap : ∀ i y, MemT y z → y ∈ C vs i → g y ∈ Q i y)
    (hx : x ∈ Ed (mkM P (table P μ fd C))
      (den (mkM P (table P μ fd C)) (σOf vs) ρ
        (policyPi ds (foldApps (.const fd.fref ls) args))))
    (hxz : MemT x z) :
    let M := mkM P (table P μ fd C)
    ihAtN g ds.length x ∈ Ed M ((tel M (σOf vs) ds args ρ).erasedIHType M Q x) := by
  dsimp only
  let M := mkM P (table P μ fd C)
  let t := tel M (σOf vs) ds args ρ
  have hx' : x ∈ Ed M (t.erasedType M (fitFrame P μ fd C vs)) :=
    mem_congr_right (recursiveField_ed P μ fd C hC hf vs ls hls ds args ha ρ).symm hx
  have hp : ∀ i, pempty ∈ fitFrame P μ fd C vs i → Equiv (g pempty) pempty := by
    intro i hi
    have hface := (hC vs i).2
    rw [if_neg h0] at hface
    exact (hface pempty (mem_sep_subset hi) Equiv.rfl).elim
  exact t.ihAtN_mem_below M (PiSyntaxCompile.compile_domains M (σOf vs) _ ds ρ)
    (fitFrame P μ fd C vs) (fitFrame_dich P μ fd C hC vs) Q hQ g hg z
    (fun i y hy hi => hmap i y hy (mem_sep_subset hi)) hp hx' hxz
/-- Fixed-parameter variant of the local IH bridge. Admission supplies the
leaf-prefix equation through `PiLeafParams.admitted_result_parameters`. -/
theorem ih_mem_at_parameters (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (vs : List Nat) (h0 : evalTotal (σOf vs) fd.resLevel ≠ 0)
    (ls : List Level) (hls : ls.map (evalTotal (σOf vs)) = vs)
    (ds args : List (Expr Nat)) (ha : args.length = (fd.params ++ fd.indices).length)
    (ρ : Nat → PSet.{4}) (ps : List PSet.{4})
    (hp : ∀ p, RawFamilyRec.paramKey ps.length
      ((tel (mkM P (table P μ fd C)) (σOf vs) ds args ρ).result p) = key ps)
    (Q : Index.{4} → PSet.{4} → PSet.{4}) (hQ : ∀ i y, Dich (Q i y))
    (g : PSet.{4} → PSet.{4})
    (hg : ∀ x y, Equiv x y → Equiv (g x) (g y)) (z x : PSet.{4})
    (hmap : ∀ i y, RawFamilyRec.paramKey ps.length i = key ps →
      MemT y z → y ∈ C vs i → g y ∈ Q i y)
    (hx : x ∈ Ed (mkM P (table P μ fd C))
      (den (mkM P (table P μ fd C)) (σOf vs) ρ
        (policyPi ds (foldApps (.const fd.fref ls) args))))
    (hxz : MemT x z) :
    let M := mkM P (table P μ fd C)
    ihAtN g ds.length x ∈ Ed M ((tel M (σOf vs) ds args ρ).erasedIHType M Q x) := by
  dsimp only
  let M := mkM P (table P μ fd C)
  let t := tel M (σOf vs) ds args ρ
  let X := fitFrame P μ fd C vs
  let Y := fun i => sep (fun _ => RawFamilyRec.paramKey ps.length i = key ps) (X i)
  have hX : ∀ i, Dich (X i) := fitFrame_dich P μ fd C hC vs
  have hY : ∀ i, Dich (Y i) := by
    intro i
    cases hX i with
    | inl h => exact Or.inl (fun y hy => h y (mem_sep_subset hy))
    | inr h => exact Or.inr (fun hy => h (mem_sep_subset hy))
  have hx' : x ∈ Ed M (t.erasedType M X) :=
    mem_congr_right (recursiveField_ed P μ fd C hC hf vs ls hls ds args ha ρ).symm hx
  have ht := PiSyntaxCompile.compile_domains M (σOf vs) (read M (σOf vs) args) ds ρ
  have hy : x ∈ Ed M (t.erasedType M Y) :=
    t.erasedType_mono_on M ht X Y hX hY (fun p y ⟨j, he⟩ =>
      mem_sep.mpr ⟨j, hp p, he⟩) x hx'
  have hmap' : ∀ i y, MemT y z → y ∈ Y i → g y ∈ Q i y := by
    intro i y hy hi
    obtain ⟨j, hj, he⟩ := mem_sep.mp hi
    exact hmap i y hj hy (mem_sep_subset (mem_sep_subset hi))
  have hproof : ∀ i, pempty ∈ Y i → Equiv (g pempty) pempty := by
    intro i hi
    have hface := (hC vs i).2
    rw [if_neg h0] at hface
    exact (hface pempty (mem_sep_subset (mem_sep_subset hi)) Equiv.rfl).elim
  exact t.ihAtN_mem_below M ht Y hY Q hQ g hg z hmap' hproof hy hxz
end Rcic.F3.PSet.RawFamilyIH

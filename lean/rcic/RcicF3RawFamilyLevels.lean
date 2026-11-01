import rcic.RcicF3RawFamilyIH
import rcic.RcicF3Lvl
/-! Separate the syntax universe valuation from the family's own instance.
Recursor motive levels need not occur in the family vector. Decoder and IH
membership retain the canonical frame key; bounded family syntax alone pays
abstraction transport. This is a component, not a frame producer.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamily
open Rcic.Declarative PiIndex
theorem ofFrame_updated_levels (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (vs : List Nat) (σ : Nat → Nat) (ar : Nat)
    (hB : FamBounded fd ar) (hσ : ∀ i, i < ar → σ i = σOf vs i)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false) :
    Equiv (piLam (mkM P (table P μ fd C)) σ
      (endValue C vs (fd.params.length + fd.indices.length)) ρ0 (famType fd))
      (ofFrame P μ fd C vs) := by
  let M := mkM P (table P μ fd C)
  have he := piLam_levels M hσ (g' := endValue C vs (fd.params.length + fd.indices.length))
    (endValue_resp C vs (fd.params.length + fd.indices.length))
    (fun _ => Equiv.rfl) (.sort fd.resLevel) (fun _ => Equiv.rfl)
    (fd.params ++ fd.indices) (fun e he => by
      rcases List.mem_append.mp he with hp | hi
      · exact hB.params e hp
      · exact hB.indices e hi) ρ0
  exact he.trans (ofFrame_updated P μ fd C hf vs)

theorem recursiveField_ed_at (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (vs : List Nat) (σ : Nat → Nat) (ls : List Level) (hls : ls.map (evalTotal σ) = vs)
    (ds args : List (Expr Nat)) (ha : args.length = (fd.params ++ fd.indices).length)
    (ρ : Nat → PSet.{4}) :
    let M := mkM P (table P μ fd C)
    Equiv (Ed M ((tel M σ ds args ρ).erasedType M (fitFrame P μ fd C vs)))
      (Ed M (den M σ ρ (policyPi ds (foldApps (.const fd.fref ls) args)))) := by
  dsimp only
  let M := mkM P (table P μ fd C)
  apply PiIndependent.compile_ed M σ (read M σ args)
    (fitFrame P μ fd C vs) (fitFrame_dich P μ fd C hC vs)
    (foldApps (.const fd.fref ls) args)
  intro ρ'
  rw [den_foldApps]
  change Equiv (fitFrame P μ fd C vs (key (args.map (den M σ ρ'))))
    (Ed M (fapps (M.μ fd.fref (ls.map (evalTotal σ) ))
      (args.map (den M σ ρ'))))
  rw [hls]
  exact fitFrame_key P μ fd C hC hf vs _ ((List.length_map _ _).trans ha)
end Rcic.F3.PSet.RawFamily

namespace Rcic.F3.PSet.RawFamilyIH
open Rcic.Declarative PiIndex RawFamily
theorem ih_mem_at_parameters_at (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (vs : List Nat) (σ : Nat → Nat) (h0 : evalTotal (σOf vs) fd.resLevel ≠ 0)
    (ls : List Level) (hls : ls.map (evalTotal σ) = vs)
    (ds args : List (Expr Nat)) (ha : args.length = (fd.params ++ fd.indices).length)
    (ρ : Nat → PSet.{4}) (ps : List PSet.{4})
    (hp : ∀ p, RawFamilyRec.paramKey ps.length
      ((tel (mkM P (table P μ fd C)) σ ds args ρ).result p) = key ps)
    (Q : Index.{4} → PSet.{4} → PSet.{4}) (hQ : ∀ i y, Dich (Q i y))
    (g : PSet.{4} → PSet.{4})
    (hg : ∀ x y, Equiv x y → Equiv (g x) (g y)) (z x : PSet.{4})
    (hmap : ∀ i y, RawFamilyRec.paramKey ps.length i = key ps →
      MemT y z → y ∈ C vs i → g y ∈ Q i y)
    (hx : x ∈ Ed (mkM P (table P μ fd C))
      (den (mkM P (table P μ fd C)) σ ρ
        (policyPi ds (foldApps (.const fd.fref ls) args))))
    (hxz : MemT x z) :
    let M := mkM P (table P μ fd C)
    ihAtN g ds.length x ∈ Ed M ((tel M σ ds args ρ).erasedIHType M Q x) := by
  dsimp only
  let M := mkM P (table P μ fd C)
  let t := tel M σ ds args ρ
  let X := fitFrame P μ fd C vs
  let Y := fun i => sep (fun _ => RawFamilyRec.paramKey ps.length i = key ps) (X i)
  have hX : ∀ i, Dich (X i) := fitFrame_dich P μ fd C hC vs
  have hY : ∀ i, Dich (Y i) := by
    intro i
    cases hX i with
    | inl h => exact Or.inl (fun y hy => h y (mem_sep_subset hy))
    | inr h => exact Or.inr (fun hy => h (mem_sep_subset hy))
  have hx' : x ∈ Ed M (t.erasedType M X) :=
    mem_congr_right (recursiveField_ed_at P μ fd C hC hf vs σ ls hls ds args ha ρ).symm hx
  have ht := PiSyntaxCompile.compile_domains M σ (read M σ args) ds ρ
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

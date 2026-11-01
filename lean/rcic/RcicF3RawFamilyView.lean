import rcic.RcicF3RawFamilyLaws
import rcic.RcicF3PiValueRule
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamily
open Rcic.Declarative PiIndex
/-- A constructed family abstracts over the same parameter/index telescope
in its updated table. Family-free domains pay this equality structurally. -/
theorem ofFrame_updated (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (vs : List Nat) :
    Equiv (piLam (mkM P (table P μ fd C)) (σOf vs)
      (endValue C vs (fd.params.length + fd.indices.length)) ρ0 (famType fd))
      (ofFrame P μ fd C vs) := by
  exact piLam_agreeOn P (agreeOn_upd_off μ fd.fref (ofFrame P μ fd C))
    (σOf vs) (endValue_resp C vs _) (fun _ => Equiv.rfl) (famType fd)
    (famType_refs fd (fun e he r hr => denRefs_ne_of_occurs e (hf e he) r hr)) ρ0
/-- Complete applications in the actual updated table retain fitting and
read exactly the chosen fibre. Both proof and data faces are covered. -/
theorem apply_updated_mem_iff (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (vs : List Nat) (xs : List PSet.{4})
    (hl : xs.length = (fd.params ++ fd.indices).length) (z : PSet.{4}) :
    let M := mkM P (table P μ fd C)
    z ∈ Ed M (fapps (M.μ fd.fref vs) xs) ↔
      TelFits M (σOf vs) (fd.params ++ fd.indices) ρ0 xs ∧ z ∈ C vs (key xs) := by
  dsimp only
  let M := mkM P (table P μ fd C)
  have htable : M.μ fd.fref vs = ofFrame P μ fd C vs := upd_eq _ _ _ _
  have he : Equiv (M.μ fd.fref vs) (ofFrame P (table P μ fd C) fd C vs) := by
    rw [htable]
    exact (ofFrame_updated P μ fd C hf vs).symm
  have hread (hfit : TelFits M (σOf vs) (fd.params ++ fd.indices) ρ0 xs) :
      Equiv (Ed M (fapps (M.μ fd.fref vs) xs)) (C vs (key xs)) :=
    (ed_congr M (fapps_congr he xs)).trans
      (apply_ofFrame_ed P (table P μ fd C) fd C hC vs xs hfit)
  constructor
  · intro hz
    have hn : ¬ Equiv (fapps (ofFrame P (table P μ fd C) fd C vs) xs) pempty := by
      intro hn
      exact not_mem_pempty (mem_congr_right
        ((ed_congr M hn).trans (ed_pempty M))
        (mem_congr_right (ed_congr M (fapps_congr he xs)) hz))
    have hfit := fits_of_fapps_ne M (σOf vs)
      (endValue_resp C vs (fd.params.length + fd.indices.length)) (.sort fd.resLevel)
      (fd.params ++ fd.indices) ρ0 xs hl hn
    exact ⟨hfit, mem_congr_right (hread hfit) hz⟩
  · intro ⟨hfit, hz⟩
    exact mem_congr_right (hread hfit).symm hz

/-- The chosen frame restricted to fitting complete applications. Invalid
keys contribute no recursive children, including under empty inner domains. -/
def fitFrame (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (vs : List Nat) (i : Index.{4}) : PSet.{4} :=
  sep (fun _ => PiValueRule.fits (mkM P (table P μ fd C)) (σOf vs)
    (fd.params ++ fd.indices) ρ0 i) (C vs i)

theorem fitFrame_dich (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C) (vs : List Nat) (i : Index.{4}) :
    Dich (fitFrame P μ fd C vs i) := by
  cases admissible_dich hC vs i with
  | inl hp => exact Or.inl (fun z hz => hp z (mem_sep_subset hz))
  | inr hd => exact Or.inr (fun hz => hd (mem_sep_subset hz))

theorem fitFrame_key (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (vs : List Nat) (xs : List PSet.{4})
    (hl : xs.length = (fd.params ++ fd.indices).length) :
    let M := mkM P (table P μ fd C)
    Equiv (fitFrame P μ fd C vs (key xs)) (Ed M (fapps (M.μ fd.fref vs) xs)) := by
  dsimp only
  apply ext
  intro z
  have hh := apply_updated_mem_iff P μ fd C hC hf vs xs hl z
  dsimp only at hh
  rw [hh]
  constructor
  · intro hz
    obtain ⟨j, hfit, he⟩ := mem_sep.mp hz
    exact ⟨hfit, mem_congr_left he ⟨j, Equiv.rfl⟩⟩
  · intro ⟨hfit, hz⟩
    obtain ⟨j, he⟩ := hz
    exact mem_sep.mpr ⟨j, hfit, he⟩

/-- Actual normalized recursive fields decode to arbitrary-depth semantic
telescopes. The family may have the data face; invalid leaf keys stay empty. -/
theorem recursiveField_ed (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (vs : List Nat) (ls : List Level) (hls : ls.map (evalTotal (σOf vs)) = vs)
    (ds args : List (Expr Nat)) (ha : args.length = (fd.params ++ fd.indices).length)
    (ρ : Nat → PSet.{4}) :
    let M := mkM P (table P μ fd C)
    Equiv (Ed M ((tel M (σOf vs) ds args ρ).erasedType M (fitFrame P μ fd C vs)))
      (Ed M (den M (σOf vs) ρ (policyPi ds (foldApps (.const fd.fref ls) args)))) := by
  dsimp only
  let M := mkM P (table P μ fd C)
  apply PiIndependent.compile_ed M (σOf vs) (read M (σOf vs) args)
    (fitFrame P μ fd C vs) (fitFrame_dich P μ fd C hC vs)
    (foldApps (.const fd.fref ls) args)
  intro ρ'
  rw [den_foldApps]
  change Equiv (fitFrame P μ fd C vs (key (args.map (den M (σOf vs) ρ'))))
    (Ed M (fapps (M.μ fd.fref (ls.map (evalTotal (σOf vs)) ))
      (args.map (den M (σOf vs) ρ'))))
  rw [hls]
  exact fitFrame_key P μ fd C hC hf vs _ ((List.length_map _ _).trans ha)
end Rcic.F3.PSet.RawFamily

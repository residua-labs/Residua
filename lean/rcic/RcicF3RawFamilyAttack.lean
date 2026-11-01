import rcic.RcicF3RawFamilyCtor
/-! Inhabited nullary data probe of the raw role at every family label.
This is not the PendA W certificate. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamilyAttack
open Rcic.Declarative PiIndex RawFamily

def fd (f : Nat) : FamData := ⟨f, [], [], .succ .zero, [([], [])], .anySort⟩
def candidate : Frame := fun _ _ => singleton (dataVal 0 [])

theorem admissible (P : Premises4) (f : Nat) : Admissible (fd f) candidate := by
  intro vs i
  let s := stageW4 P 1
  refine ⟨s.singleton_mem (s.ordPair_mem s.empty (s.ordPair_mem s.empty s.empty)), ?_⟩
  change ∀ z, z ∈ singleton (dataVal 0 []) → ¬Equiv z pempty
  intro z hz he
  exact dataVal_ne_pempty 0 [] ((mem_singleton.mp hz).symm.trans he)
theorem closed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat) :
    Closed P μ (fd f) candidate := by
  intro vs i z ⟨j, ps, xs, hp, hx, _, _, hz⟩
  have hj : j = ⟨0, show 0 < 1 from by decide⟩ := Fin.ext
    (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
  subst j
  cases ps with
  | cons _ _ => exact False.elim hp
  | nil =>
    cases xs with
    | cons _ _ => exact False.elim hx
    | nil => exact mem_singleton.mpr hz
theorem leaf_inAll (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (f : Nat) (vs : List Nat) :
    InAll P μ (fd f) vs (key []) (dataVal 0 []) := by
  intro C _ hc
  apply hc vs (key []) (dataVal 0 [])
  exact ⟨⟨0, show 0 < 1 from by decide⟩, [], [], True.intro,
    True.intro, True.intro, rfl, Equiv.rfl⟩
theorem leaf_member (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (f : Nat) (vs : List Nat) :
    dataVal 0 [] ∈ frame P μ (fd f) vs (key []) := by
  have hmem : dataVal 0 [] ∈ W4 1 :=
    (stageW4 P 1).trans (admissible P f vs (key [])).1
      (mem_singleton.mpr Equiv.rfl)
  obtain ⟨i, hi⟩ := hmem
  apply mem_sep.mpr
  exact ⟨i, (inAll_resp P μ (fd f) vs (key []) hi.symm).mp
    (leaf_inAll P μ f vs), hi⟩
theorem frame_closed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat) :
    Closed P μ (fd f) (frame P μ (fd f)) := by
  intro vs i z ⟨j, ps, xs, hp, hx, _, hi, hz⟩
  have hj : j = ⟨0, show 0 < 1 from by decide⟩ := Fin.ext
    (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
  subst j
  cases ps with
  | cons _ _ => exact False.elim hp
  | nil =>
    cases xs with
    | cons _ _ => exact False.elim hx
    | nil =>
      change i = key [] at hi
      rw [hi]
      exact mem_congr_left hz.symm (leaf_member P μ f vs)
/-- Actual family and literal constructor inhabit their stored types.
No closure or size condition is an external premise of this test. -/
theorem role_inhabited (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (f : Nat) (vs : List Nat) :
    role P μ (fd f) vs ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 (famType (fd f))) ∧
    dataVal 0 [] ∈ Ed (mkM P μ) (role P μ (fd f) vs) := by
  have hC : Admissible (fd f) (frame P μ (fd f)) :=
    frame_admissible P μ (fd f) ⟨candidate, admissible P f, closed P μ f⟩
  refine ⟨ofFrame_mem P μ (fd f) _ hC vs, ?_⟩
  change dataVal 0 [] ∈ Ed (mkM P μ) (tyv (frame P μ (fd f) vs (key [])))
  exact mem_congr_right (ed_tyv (mkM P μ) (admissible_dich hC vs (key []))).symm
    (leaf_member P μ f vs)
theorem wrong_tag_refused (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (f : Nat) (vs : List Nat) :
    ¬ dataVal 1 [] ∈ frame P μ (fd f) vs (key []) := by
  intro hz
  have he := mem_singleton.mp
    (frame_least P μ (fd f) candidate (admissible P f) (closed P μ f) vs (key []) _ hz)
  have ht : 1 = 0 := (dataVal_inj rfl he).1
  exact Nat.noConfusion ht
end Rcic.F3.PSet.RawFamilyAttack

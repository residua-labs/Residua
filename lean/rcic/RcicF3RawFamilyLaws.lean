import rcic.RcicF3RawFamily

/-! Structural laws of the raw intersection role. Small closed frames are
explicit component inputs here; their production from admission is a separate
obligation. No new condition is added to `StepAG`. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamily
open Rcic.Declarative PiIndex

theorem endValue_resp (C : Frame) (vs : List Nat) (q : Nat) :
    EnvResp (endValue C vs q) := by
  intro ρ ρ' h
  unfold endValue
  rw [(key_eq_iff _ _).mpr (lastVals_congr q h)]
  exact Equiv.rfl

theorem admissible_dich {fd : FamData} {C : Frame} (hC : Admissible fd C)
    (vs : List Nat) (i : Index.{4}) : Dich (C vs i) := by
  have h := (hC vs i).2
  by_cases h0 : evalTotal (σOf vs) fd.resLevel = 0
  · exact Or.inl (by simpa only [h0, if_pos rfl] using h)
  · rw [if_neg h0] at h
    exact Or.inr (fun hz => h pempty hz Equiv.rfl)

/-- Full family-type membership for any correctly sized frame. No claim that
an admitted signature already supplies such a frame is made by this lemma. -/
theorem ofFrame_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C) (vs : List Nat) :
    ofFrame P μ fd C vs ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 (famType fd)) := by
  refine piLam_mem (mkM P μ) (σOf vs)
    (endValue_resp C vs (fd.params.length + fd.indices.length)) _ ρ0 ?_
  unfold famType
  apply piGood_policyPi
  intro ρ
  change tyv (C vs (key (lastVals (fd.params.length + fd.indices.length) ρ))) ∈
    Ed (mkM P μ) (tyv (U W4 (evalTotal (σOf vs) fd.resLevel)))
  apply mem_congr_right (ed_tyv (mkM P μ) (U4_dich _)).symm
  by_cases h0 : evalTotal (σOf vs) fd.resLevel = 0
  · rw [h0]
    exact mem_sImage_tyv.mpr ⟨_, mem_propSets.mpr
      (by simpa only [h0, if_pos rfl] using (hC vs _).2), Equiv.rfl⟩
  · obtain ⟨k, hk⟩ : ∃ k, evalTotal (σOf vs) fd.resLevel = k + 1 :=
      ⟨evalTotal (σOf vs) fd.resLevel - 1, by omega⟩
    rw [hk]
    have hm := (hC vs (key (lastVals (fd.params.length + fd.indices.length) ρ))).1
    rw [hk] at hm
    obtain ⟨i, hi⟩ := hm
    exact mem_sImage_tyv.mpr ⟨_, mem_sep.mpr
      ⟨i, (dich_congr hi.symm).mp (admissible_dich hC vs _), hi⟩, Equiv.rfl⟩

/-- Complete fitting application reads the entire extensional argument key. -/
theorem apply_ofFrame (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (vs : List Nat) (xs : List PSet.{4})
    (hx : TelFits (mkM P μ) (σOf vs) (fd.params ++ fd.indices) ρ0 xs) :
    Equiv (fapps (ofFrame P μ fd C vs) xs) (tyv (C vs (key xs))) := by
  have he := fapps_piLam (mkM P μ) (σOf vs)
    (endValue_resp C vs (fd.params.length + fd.indices.length)) (.sort fd.resLevel)
    (fd.params ++ fd.indices) ρ0 xs hx
  change Equiv (fapps (ofFrame P μ fd C vs) xs)
    (tyv (C vs (key (lastVals (fd.params.length + fd.indices.length) (push xs ρ0))))) at he
  have hl : fd.params.length + fd.indices.length = xs.length := by
    rw [hx.length, List.length_append]
  rw [hl, lastVals_push] at he
  exact he

/-- The intersection lies in every small closed frame. Constructor closure
of the intersection itself does not follow merely from this structural law. -/
theorem frame_least (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C) (hc : Closed P μ fd C)
    (vs : List Nat) (i : Index.{4}) : Sub (frame P μ fd vs i) (C vs i) := by
  intro z hz
  unfold frame at hz
  split at hz
  · obtain ⟨ha, he⟩ := mem_tv.mp hz
    exact mem_congr_left he.symm (ha C hC hc)
  · obtain ⟨j, ha, he⟩ := mem_sep.mp hz
    exact mem_congr_left he (ha C hC hc)

theorem inAll_resp (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (vs : List Nat) (i : Index.{4}) {z z' : PSet.{4}}
    (he : Equiv z z') : InAll P μ fd vs i z ↔ InAll P μ fd vs i z' := by
  exact ⟨fun h C hC hc => mem_congr_left he (h C hC hc),
    fun h C hC hc => mem_congr_left he.symm (h C hC hc)⟩

/-- A single produced small closed frame bounds the intersection. This
does not assume or establish closure of the intersection. -/
theorem frame_admissible (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (hex : ∃ C, Admissible fd C ∧ Closed P μ fd C) :
    Admissible fd (frame P μ fd) := by
  obtain ⟨C, hC, hc⟩ := hex
  intro vs i
  refine ⟨(stageW4 P _).subset (hC vs i).1 (frame_least P μ fd C hC hc vs i), ?_⟩
  by_cases h0 : evalTotal (σOf vs) fd.resLevel = 0
  · rw [if_pos h0]
    intro z hz
    unfold frame at hz
    rw [if_pos h0] at hz
    exact (mem_tv.mp hz).2
  · rw [if_neg h0]
    intro z hz
    have hface := (hC vs i).2
    rw [if_neg h0] at hface
    exact hface z (frame_least P μ fd C hC hc vs i z hz)

/-- Exact decoded fibre at fitting applications, on either proof/data face. -/
theorem apply_ofFrame_ed (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C) (vs : List Nat) (xs : List PSet.{4})
    (hx : TelFits (mkM P μ) (σOf vs) (fd.params ++ fd.indices) ρ0 xs) :
    Equiv (Ed (mkM P μ) (fapps (ofFrame P μ fd C vs) xs)) (C vs (key xs)) := by
  exact (ed_congr (mkM P μ) (apply_ofFrame P μ fd C vs xs hx)).trans
    (ed_tyv (mkM P μ) (admissible_dich hC vs _))

end Rcic.F3.PSet.RawFamily

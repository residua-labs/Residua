import rcic.RcicF3RawFamilyLaws
/-! Indexed induction for the raw role, by separation of its frame. This is
an indexed form of RcicF3KT.lfp_induction, using the existing stage subset
law. Constructor monotonicity and a small closed candidate remain explicit
production inputs. No ordinal-continuity or raw-shape premise is used. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamily
open Rcic.Declarative PiIndex

abbrev FrameSub (C D : Frame) : Prop := ∀ vs i, Sub (C vs i) (D vs i)

def ConstructorMono (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) : Prop :=
  ∀ C D, Admissible fd C → Admissible fd D → FrameSub C D →
    ∀ vs i z, CtorAt P μ fd C vs i z → CtorAt P μ fd D vs i z

def restrict (C : Frame) (Q : List Nat → Index.{4} → PSet.{4} → Prop) : Frame :=
  fun vs i => sep (Q vs i) (C vs i)

theorem restrict_admissible (P : Premises4) (fd : FamData) (C : Frame)
    (hC : Admissible fd C) (Q : List Nat → Index.{4} → PSet.{4} → Prop) :
    Admissible fd (restrict C Q) := by
  intro vs i
  refine ⟨(stageW4 P _).subset (hC vs i).1 (fun _ hz => mem_sep_subset hz), ?_⟩
  by_cases h0 : evalTotal (σOf vs) fd.resLevel = 0
  · rw [if_pos h0]
    have hp := (hC vs i).2
    rw [if_pos h0] at hp
    exact fun z hz => hp z (mem_sep_subset hz)
  · rw [if_neg h0]
    have hp := (hC vs i).2
    rw [if_neg h0] at hp
    exact fun z hz => hp z (mem_sep_subset hz)

/-- Constructor closure follows from monotonicity and a produced small
closed frame. Neither production input is asserted universally here. -/
theorem frame_closed_of_mono (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (hex : ∃ C, Admissible fd C ∧ Closed P μ fd C)
    (hmono : ConstructorMono P μ fd) : Closed P μ fd (frame P μ fd) := by
  have hF := frame_admissible P μ fd hex
  intro vs i z hz
  have hall : InAll P μ fd vs i z := by
    intro C hC hc
    exact hc vs i z (hmono _ _ hF hC (frame_least P μ fd C hC hc) vs i z hz)
  obtain ⟨C, hC, hc⟩ := hex
  by_cases h0 : evalTotal (σOf vs) fd.resLevel = 0
  · have hp := (hC vs i).2
    rw [if_pos h0] at hp
    have he := hp z (hall C hC hc)
    unfold frame
    rw [if_pos h0]
    apply mem_tv.mpr
    refine ⟨?_, he⟩
    intro D hD hd
    exact mem_congr_left he (hall D hD hd)
  · have hzw := (stageW4 P _).trans (hC vs i).1 (hall C hC hc)
    obtain ⟨j, hj⟩ := hzw
    unfold frame
    rw [if_neg h0]
    exact mem_sep.mpr ⟨j, (inAll_resp P μ fd vs i hj.symm).mp hall, hj⟩

/-- Induction with the complete universe vector and argument key retained.
The local step sees fields in the property-restricted frame. -/
theorem frame_induction (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (hF : Admissible fd (frame P μ fd))
    (hc : Closed P μ fd (frame P μ fd)) (hmono : ConstructorMono P μ fd)
    (Q : List Nat → Index.{4} → PSet.{4} → Prop)
    (hQ : ∀ vs i z z', Equiv z z' → Q vs i z → Q vs i z')
    (hstep : ∀ vs i z, CtorAt P μ fd (restrict (frame P μ fd) Q) vs i z → Q vs i z) :
    ∀ vs i z, z ∈ frame P μ fd vs i → Q vs i z := by
  let R := restrict (frame P μ fd) Q
  have hR : Admissible fd R := restrict_admissible P fd _ hF Q
  have hsub : FrameSub R (frame P μ fd) := fun _ _ _ hz => mem_sep_subset hz
  have hRc : Closed P μ fd R := by
    intro vs i z hz
    have hzF := hc vs i z (hmono R _ hR hF hsub vs i z hz)
    obtain ⟨j, hj⟩ := hzF
    exact mem_sep.mpr ⟨j, hQ vs i z _ hj.symm (hstep vs i z hz), hj⟩
  intro vs i z hz
  have hzR := frame_least P μ fd R hR hRc vs i z hz
  obtain ⟨j, hjQ, hj⟩ := mem_sep.mp hzR
  exact hQ vs i _ z hj hjQ
/-- Elementary transport of the literal constructor output. -/
theorem ctorAt_resp (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (vs : List Nat) (i : Index.{4})
    {z z' : PSet.{4}} (he : Equiv z z') (hz : CtorAt P μ fd C vs i z) :
    CtorAt P μ fd C vs i z' := by
  obtain ⟨j, ps, xs, hp, hx, hs, hi, hz⟩ := hz
  exact ⟨j, ps, xs, hp, hx, hs, hi, he.symm.trans hz⟩

/-- Every member of the intersection has a literal constructor presentation.
This is the indexed analogue of the existing KT density law. -/
theorem frame_dense (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (hF : Admissible fd (frame P μ fd))
    (hc : Closed P μ fd (frame P μ fd)) (hmono : ConstructorMono P μ fd) :
    ∀ vs i z, z ∈ frame P μ fd vs i → CtorAt P μ fd (frame P μ fd) vs i z := by
  apply frame_induction P μ fd hF hc hmono
    (fun vs i z => CtorAt P μ fd (frame P μ fd) vs i z)
    (fun vs i _ _ he hz => ctorAt_resp P μ fd _ vs i he hz)
  intro vs i z hz
  exact hmono _ _ (restrict_admissible P fd _ hF _) hF
    (fun _ _ _ hm => mem_sep_subset hm) vs i z hz
end Rcic.F3.PSet.RawFamily

import rcic.RcicF3RawFamilyRec

/-!
# Global candidate existence is necessary for one small data fibre

The present role intersects frames whose admissibility and closure are
both global. If that class is empty, its data fibre is the entire stage
carrier. Hence smallness at even one data world and key already requires
a globally admissible closed frame. This is a property of the current
role definition, not a refutation of admitted small-frame production.

The proof uses the supplied decision procedure and well-founded set
membership. It makes no representative choice and changes no role,
soundness target or check. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamilyGlobalSize
open Rcic.Declarative PiIndex RawFamily

/-- An empty global candidate class makes the data intersection vacuous. -/
theorem empty_class_carrier (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData)
    (hn : ¬ ∃ C : Frame, Admissible fd C ∧ Closed P μ fd C)
    (vs : List Nat) (i : Index.{4})
    (h0 : evalTotal (σOf vs) fd.resLevel ≠ 0) :
    Equiv (frame P μ fd vs i) (W4 (evalTotal (σOf vs) fd.resLevel)) := by
  unfold frame
  rw [if_neg h0]
  apply ext
  intro z
  constructor
  · exact mem_sep_subset
  · intro hz
    obtain ⟨a, ha⟩ := hz
    exact mem_sep.mpr ⟨a, fun C hC hc => (hn ⟨C, hC, hc⟩).elim, ha⟩

/-- At the supplied positive DATA stage, smallness of the given fibre
forces the global candidate class to be inhabited. This implication uses
the literal global intersection; canonicalization and bounded typing are
not premises of this result. -/
theorem global_candidate_of_small_fibre (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (vs : List Nat) (i : Index.{4})
    (h0 : evalTotal (σOf vs) fd.resLevel ≠ 0)
    (hs : frame P μ fd vs i ∈ W4 (evalTotal (σOf vs) fd.resLevel)) :
    ∃ C : Frame, Admissible fd C ∧ Closed P μ fd C := by
  cases P.dec (∃ C : Frame, Admissible fd C ∧ Closed P μ fd C) with
  | isTrue h => exact h
  | isFalse hn =>
      have he := empty_class_carrier P μ fd hn vs i h0
      have hself : W4 (evalTotal (σOf vs) fd.resLevel) ∈
          W4 (evalTotal (σOf vs) fd.resLevel) := mem_congr_left he hs
      have hirr : ∀ z : PSet.{4}, ¬ MemT z z := by
        intro z
        induction z using memT_wf.induction with
        | h z ih => intro hzz; exact ih z hzz hzz
      exact (hirr _ (.single hself)).elim

theorem small_fibre_iff (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (vs : List Nat) (i : Index.{4})
    (h0 : evalTotal (σOf vs) fd.resLevel ≠ 0) :
    frame P μ fd vs i ∈ W4 (evalTotal (σOf vs) fd.resLevel) ↔
      ∃ C : Frame, Admissible fd C ∧ Closed P μ fd C :=
  ⟨global_candidate_of_small_fibre P μ fd vs i h0,
    fun h => (frame_admissible P μ fd h vs i).1⟩

end Rcic.F3.PSet.RawFamilyGlobalSize

import rcic.RcicF3PropEvalCandidate
import rcic.RcicF3PropEvalTypedAttack

/-!
# An actual closed guarded evaluation candidate at AccR

The candidate is the same restricted raw frame used by the generic leaf
extraction. At the admitted AccR descriptor its constructor step is produced:
the complete constructor key has one parameter and no index suffix, so the
guard identifies the actual key with the existing evaluated fixture. Raw
membership comes from the actual AccR monotonicity/closure proofs. Leastness
then supplies a nonempty evaluation. This is a local closure/non-refutability
witness, not universal StepAG. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalCandidateAttack
open Rcic.Declarative PiIndex RawFamilyRec RawFamily PlanPropEndAttack
open PropEvalUniqueAttack (ctx)

noncomputable def X (P : Premises4) : Frame :=
  PropEvalCandidate.candidate P (installed P) (ctx P)

theorem candidate_admissible (P : Premises4) : Admissible fd (X P) :=
  PropEvalCandidate.admissible P (installed P) (ctx P)
    (RawFamilyPropAttack.acc_closed P (installed P)).1

/-- The actual AccR candidate constructor step, with all local inputs produced. -/
theorem candidate_closed (P : Premises4) : Closed P (installed P) fd (X P) := by
  intro vs i z hc
  have hRaw := RawFamilyPropAttack.acc_closed P (installed P)
  have hzRaw : z ∈ frame P (installed P) fd vs i :=
    hRaw.2 vs i z (RawFamilyPropAttack.acc_mono P (installed P)
      (X P) (frame P (installed P) fd) (candidate_admissible P) hRaw.1
      (fun _ _ _ hm => mem_sep_subset hm) vs i z hc)
  have hQ : PropEvalCandidate.EvalPredicate (ctx P) vs i z := by
    intro _ hp
    obtain ⟨j, ps, xs, hps, _, _, hkey, _⟩ := hc
    rcases j with ⟨j, hj⟩
    have hj0 : j = 0 := by change j < 1 at hj; omega
    subst j
    change i = key (ps ++ []) at hkey
    simp only [List.append_nil] at hkey
    have hlen : ps.length = 1 := hps.length
    have hi : paramKey 1 i = i := by
      rw [hkey]
      simpa only [List.append_nil, hlen] using paramKey_append ps []
    change paramKey 1 i = key [parameter] at hp
    rw [hi] at hp
    rw [hp]
    exact ⟨datum, PropEvalAttack.inhabited P⟩
  obtain ⟨j, hj⟩ := hzRaw
  exact mem_sep.mpr ⟨j, hQ, hj⟩

/-- Literal closure, inhabited source and produced evaluation consequences. -/
def Witness (P : Premises4) : Prop :=
  Admissible fd (X P) ∧ Closed P (installed P) fd (X P) ∧
  pempty ∈ frame P (installed P) fd [] (key [parameter]) ∧
  pempty ∈ X P [] (key [parameter]) ∧
  ∃ z, PropEval.Eval (ctx P) (key [parameter]) z ∧ z ∈ domain ∧ ¬ Equiv z pempty

theorem component_witness (P : Premises4) : Witness P := by
  have hRaw := RawFamilyPropAttack.acc_closed P (installed P)
  have hmajor : pempty ∈ frame P (installed P) fd [] (key [parameter]) :=
    RawFamilyPropAttack.empty_parameter_inhabited P (installed P) []
  have hX : pempty ∈ X P [] (key [parameter]) :=
    frame_least P (installed P) fd (X P) (candidate_admissible P)
      (candidate_closed P) [] (key [parameter]) pempty hmajor
  obtain ⟨z, hz⟩ := PropEvalCandidate.exists_of_closed P (installed P) (ctx P)
    hRaw.1 (candidate_closed P) [] (key [parameter]) pempty hmajor
    (fun u hu => by change u < 0 at hu; omega) rfl
  have ht := PropEvalAttack.eval_typed P hz
  refine ⟨candidate_admissible P, candidate_closed P, hmajor, hX, z, hz, ht, ?_⟩
  intro he
  exact dataVal_ne_pempty _ _ ((mem_singleton.mp ht).symm.trans he)

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropEvalCandidateAttack

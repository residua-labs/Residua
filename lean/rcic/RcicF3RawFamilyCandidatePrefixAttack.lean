import rcic.RcicF3RawFamilyCandidatePrefix
import rcic.RcicF3PropEvalTypedAttack

/-!
# A sound typed family prefix whose candidate is not constructor-closed

The actual AccR descriptor admits the empty candidate, and its family-only
prefix is sound at every syntax valuation. The candidate is provably not
closed, so candidate-prefix soundness does not conceal a closure premise.
The actual bounded field derivations still produce PropTel at the selected
parameter. This component does not assert a recursor on the empty candidate.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamilyCandidatePrefixAttack
open Rcic.Declarative PiIndex RawFamily PlanPropEndAttack

def emptyCandidate : Frame := fun _ _ => pempty

theorem admissible (P : Premises4) : Admissible fd emptyCandidate := by
  intro vs i
  exact ⟨(stageW4 P 0).prop_mem (fun _ hz => (not_mem_pempty hz).elim),
    fun _ hz => (not_mem_pempty hz).elim⟩

theorem not_closed (P : Premises4) :
    ¬ Closed P (installed P) fd emptyCandidate := by
  intro hc
  exact not_mem_pempty
    (frame_least P (installed P) fd emptyCandidate (admissible P) hc
      [] (key [tyv pempty]) pempty
      (RawFamilyPropAttack.empty_parameter_inhabited P (installed P) []))

/-- The original predecessor invariant is used at the updated candidate table. -/
theorem prefix_sound (P : Premises4) (K τ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (table P (installed P) fd emptyCandidate)) τ K accFamOnly n := by
  apply candidate_prefix_envSound P K (.empty : EnvWfT emptyEnv)
    (PlanPropStepAttack.empty_gInv P K) (installed P)
    (envCtx (.empty : EnvWfT emptyEnv)) (PlanRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ hm => by nomatch hm) (fun _ _ hm => by nomatch hm)
    fd emptyCandidate (admissible P) ?_ accFamMember rfl
    (fun _ => rfl) rfl rfl rfl rfl τ n
  intro e he
  have he' : e = .sort .zero := List.mem_singleton.mp he
  subst e
  rfl

/-- The same actual bounded AccR field typing works over the nonclosed candidate. -/
theorem fields_prop (P : Premises4) (K τ : Nat → Nat) :
    PropTel (mkM P (table P (installed P) fd emptyCandidate)) τ
      [accField] (push [parameter] ρ0) := by
  apply propTel_of_typings_at P (table P (installed P) fd emptyCandidate) K τ
    [.sort .zero] [accField] (prefix_sound P K τ 0) ?_ [parameter] ?_
  · intro k
    obtain ⟨l, hl, d, hd⟩ := PlanPropStepAttack.propFieldBound K
      PlanPropStepAttack.pNode ⟨0, by change 0 < 1; decide⟩ τ k
    exact ⟨l, hl τ, d, hd⟩
  · exact ⟨mem_congr_right
      (ed_tyv (mkM P (table P (installed P) fd emptyCandidate)) (U4_dich 0)).symm
      (parameter_mem P), True.intro⟩

def Witness (P : Premises4) (K : Nat → Nat) : Prop :=
  Admissible fd emptyCandidate ∧
  ¬ Closed P (installed P) fd emptyCandidate ∧
  (∀ τ n, EnvSound (mkM P (table P (installed P) fd emptyCandidate)) τ K accFamOnly n) ∧
  (∀ τ, PropTel (mkM P (table P (installed P) fd emptyCandidate)) τ
    [accField] (push [parameter] ρ0))

theorem component_witness (P : Premises4) (K : Nat → Nat) : Witness P K :=
  ⟨admissible P, not_closed P, prefix_sound P K, fields_prop P K⟩

theorem component_nonrefutable (P : Premises4) (K : Nat → Nat) :
    ¬ (Witness P K → (Premises4 → False)) :=
  fun h => h (component_witness P K) P

end Rcic.F3.PSet.RawFamilyCandidatePrefixAttack

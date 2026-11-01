import rcic.RcicF3CandidatePrefixFromGroup
import rcic.RcicF3CandidateTupleAttack

/-!
# Actual AccR inhabitant of the produced group-prefix package

The full ordinary prefix package is produced from the empty predecessor's
invariant, the actual admitted AccR group, and the installed raw family.
Its candidate-prefix conclusion is instantiated at a provably nonclosed
candidate, preserving the negative closure control. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.CandidatePrefixFromGroupAttack
open Rcic.Declarative RawFamily PlanPropEndAttack CandidatePrefixFromGroup

theorem facts (P : Premises4) (K : Nat → Nat) :
    GroupPrefixFacts P (installed P) K emptyEnv accEnv 0 2
      accRecMember accFamMember PlanPropStepAttack.pNode := by
  exact group_facts P K (installed P)
    (E := emptyEnv) (E' := accEnv) (f := 0) (rr := 2)
    (fm := accFamMember) (rm := accRecMember) (ctors := [(1, accIntroMember)])
    .empty rfl AccEnv.accMembersT PlanPropStepAttack.pNode
    (PlanPropStepAttack.empty_gInv P K)
    (envCtx (.empty : EnvWfT emptyEnv)) (PlanRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ hm => by nomatch hm) (fun _ _ hm => by nomatch hm)
    (CandidateTupleAttack.family_all P) (CandidateTupleAttack.raw_admissible P)

def Witness (P : Premises4) (K : Nat → Nat) : Prop :=
  GroupPrefixFacts P (installed P) K emptyEnv accEnv 0 2
    accRecMember accFamMember PlanPropStepAttack.pNode ∧
  ¬ Closed P (installed P) fd RawFamilyCandidatePrefixAttack.emptyCandidate ∧
  (∀ σ n, EnvSound (mkM P (CandidateScopeAttack.accμ P)) σ K accFamOnly n)

theorem component_witness (P : Premises4) (K : Nat → Nat) : Witness P K :=
  ⟨facts P K, RawFamilyCandidatePrefixAttack.not_closed P,
    (facts P K).candidateEnv RawFamilyCandidatePrefixAttack.emptyCandidate
      (RawFamilyCandidatePrefixAttack.admissible P)⟩

theorem component_nonrefutable (P : Premises4) (K : Nat → Nat) :
    ¬ (Witness P K → (Premises4 → False)) :=
  fun h => h (component_witness P K) P

end Rcic.F3.PSet.CandidatePrefixFromGroupAttack

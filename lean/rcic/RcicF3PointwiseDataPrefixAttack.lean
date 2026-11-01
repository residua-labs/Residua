import rcic.RcicF3PointwiseDataPrefix
import rcic.RcicF3PointwiseRoleAttack
import rcic.RcicF3PointwiseNatInvariant
import rcic.RcicF3NormDataGroupAttack

/-!
# The actual new W table's constructor and reader prefix

The public checked prefix producer is called at the NEW installed table.
Actual W local candidates come from its independently produced W frame,
for every ambient table and K. The predecessor is the new Nat invariant;
no current-W invariant or recursor package is used by the prefix proof.

The same-P witness keeps both constructor stored-type memberships, the
ordinary reader at every valuation, and the actual installed height-omega
family witness. Complete current-recursion soundness is a later component.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseDataPrefixAttack
open Rcic.Declarative RawFamily
open NormPendAW (plan)
open PointwiseRoleAttack (table)

theorem local_candidates (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) : PointwiseDataLocal.LocalCandidates P μ plan K :=
  PointwiseDataLocal.of_global_candidate P μ plan PendAW.fam
    [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT PendAW.membersT
    ⟨RawFamily.frame P μ (EvalPlanNormal.fd plan),
      NormPendAW.normalized_admissible P μ, NormPendAW.normalized_closed P μ⟩ K

theorem produced (P : Premises4) (k : Nat) :
    (∀ r m, PendAW.eAll.members r = some m → r ≠ 7 →
      MemberSound P (table P) (fun _ => k) r m) ∧
    (∀ σ n, EnvSound (mkM P (table P)) σ (fun _ => k) plan.node.E0 n) :=
  PointwiseDataPrefix.sound_of_local_candidates P (table P) (fun _ => k)
    natEnvUWfT rfl PendAWGroup.ctorClasses rfl PendAW.membersT
    PendAWGroup.walkAgree (PendAWGroup.boundG _) (PointwiseNatInvariant.gInv P _)
    (PointwiseRole.arities PendAW.eAll) PointwiseRoleAttack.metadata
    (NormRole.envCtx PendAWGroup.wft) (EvalRole.envPlan PendAWGroup.wft)
    (fun _ _ => rfl) (fun _ _ => rfl) (PointwiseRoleAttack.faithful P)
    (NormDataGroupAttack.group_check k) (local_candidates P (table P) _)
    NormDataRecMemAttack.type_family

theorem leaf_sound (P : Premises4) (k : Nat) :
    MemberSound P (table P) (fun _ => k) 5 PendAW.leaf :=
  (produced P k).1 5 PendAW.leaf rfl (by decide)

theorem node_sound (P : Premises4) (k : Nat) :
    MemberSound P (table P) (fun _ => k) 6 PendAW.node :=
  (produced P k).1 6 PendAW.node rfl (by decide)

def Witness (P : Premises4) : Prop :=
  PointwiseRoleAttack.Witness P ∧ PointwiseNatInvariant.Witness P ∧
  (∀ μ K, PointwiseDataLocal.LocalCandidates P μ plan K) ∧
  (∀ k, (∀ r m, PendAW.eAll.members r = some m → r ≠ 7 →
    MemberSound P (table P) (fun _ => k) r m) ∧
    (∀ σ n, EnvSound (mkM P (table P)) σ (fun _ => k) plan.node.E0 n)) ∧
  (∀ k, MemberSound P (table P) (fun _ => k) 5 PendAW.leaf) ∧
  (∀ k, MemberSound P (table P) (fun _ => k) 6 PendAW.node)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨PointwiseRoleAttack.component_witness P, PointwiseNatInvariant.component_witness P,
    local_candidates P, produced P, leaf_sound P, node_sound P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PointwiseDataPrefixAttack

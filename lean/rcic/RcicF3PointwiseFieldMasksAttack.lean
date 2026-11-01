import rcic.RcicF3PointwiseFieldMasks
import rcic.RcicF3ReaderPacketBinderAttack
import rcic.RcicF3CheckedCtorWorldListAttack

/-!
# Produced reader masks and local candidates at the installed W table

Both public group producers are called at the actual pointwise W table,
with the new Nat predecessor and the original constant-K bounds. The
resulting local candidate then supplies the actual checked constructor
and reader prefix; its leaf is independently inhabited by the new local
closure. No fixture-specific mask is supplied to those producer calls.

The same-P witness also retains the incompatible beta-capture reader
fixture and the ACTUAL arity-one List check at vector [2], where the other
constructor's own bound is smaller. These are distinct scopes: W's family
vector is empty, and the List component proves the checked-world bound
adapter, not an installed List invariant. Dependent inner domains, full
keys, the auxiliary masked-context failure and height-omega witnesses are
retained with their original literal scopes. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseFieldMasksAttack
open Rcic.Declarative Rcic.Model.PS RawFamily PiIndex
open NormPendAW (plan)
open PointwiseRoleAttack (table)

/-- These are calls to the general admitted-field producer, rather than
the W-specific reader-domain calculation used by the earlier assembler. -/
theorem produced (P : Premises4) (k : Nat) :
    NormSmallFrameLocal.BoundedReachedMasks P (table P) plan (fun _ => k) ∧
    PointwiseDataLocal.LocalCandidates P (table P) plan (fun _ => k) := by
  have hα : PointwiseRole.AritiesAgree (PointwiseRole.arities PendAW.eAll) natEnvU :=
    PointwiseRoleAttack.metadata.mono (groupMembersT_preserve PendAW.membersT)
  have hctx : ∀ r, Dom natEnvU r →
      NormRole.envCtx PendAWGroup.wft r = NormRole.envCtx natEnvUWfT r :=
    NormRole.envCtx_group_stable natEnvUWfT rfl PendAWGroup.ctorClasses rfl PendAW.membersT
  have hplans : ∀ r, Dom natEnvU r →
      EvalRole.envPlan PendAWGroup.wft r = EvalRole.envPlan natEnvUWfT r :=
    EvalRole.envPlan_group_stable natEnvUWfT rfl PendAWGroup.ctorClasses rfl PendAW.membersT
  have hFaith : EvalRole.Faithful (PointwiseRole.familyValue (PointwiseRole.arities PendAW.eAll))
      P (table P) (NormRole.envCtx PendAWGroup.wft)
      (EvalRole.envPlan PendAWGroup.wft) natEnvU :=
    fun r m hm => PointwiseRoleAttack.faithful P r m
      (groupMembersT_preserve PendAW.membersT r m hm)
  refine ⟨?_, ?_⟩
  · exact PointwiseFieldMasks.bounded_masks P (table P) (fun _ => k) plan PendAW.fam
      [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT rfl PendAWGroup.ctorClasses rfl
      PendAW.membersT (PendAWGroup.boundG _) (PendAWGroup.boundDG k)
      NormDataRecMemAttack.matching_parameters (PointwiseNatInvariant.gInv P _)
      (PointwiseRole.arities PendAW.eAll) hα (NormRole.envCtx PendAWGroup.wft)
      (EvalRole.envPlan PendAWGroup.wft) hctx hplans hFaith NormDataRecMemAttack.type_family
  · exact PointwiseFieldMasks.local_candidates P (table P) (fun _ => k) plan PendAW.fam
      [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT rfl PendAWGroup.ctorClasses rfl
      PendAW.membersT (PendAWGroup.boundG _) (PendAWGroup.boundDG k)
      NormDataRecMemAttack.matching_parameters (PointwiseNatInvariant.gInv P _)
      (PointwiseRole.arities PendAW.eAll) hα (NormRole.envCtx PendAWGroup.wft)
      (EvalRole.envPlan PendAWGroup.wft) hctx hplans hFaith NormDataRecMemAttack.type_family

/-- The actual checked prefix consumes the newly produced local candidates
at the SAME installed table; no current W invariant is used here. -/
theorem reader_prefix (P : Premises4) (k : Nat) :
    (∀ r m, PendAW.eAll.members r = some m → r ≠ 7 →
      MemberSound P (table P) (fun _ => k) r m) ∧
    (∀ σ n, EnvSound (mkM P (table P)) σ (fun _ => k) plan.node.E0 n) :=
  PointwiseDataPrefix.sound_of_local_candidates P (table P) (fun _ => k)
    natEnvUWfT rfl PendAWGroup.ctorClasses rfl PendAW.membersT
    PendAWGroup.walkAgree (PendAWGroup.boundG _) (PointwiseNatInvariant.gInv P _)
    (PointwiseRole.arities PendAW.eAll) PointwiseRoleAttack.metadata
    (NormRole.envCtx PendAWGroup.wft) (EvalRole.envPlan PendAWGroup.wft)
    (fun _ _ => rfl) (fun _ _ => rfl) (PointwiseRoleAttack.faithful P)
    (NormDataGroupAttack.group_check k) (produced P k).2 NormDataRecMemAttack.type_family

/-- The closure here is derived from the new produced mask. The leaf
inhabitant then uses its exact parameter key and the empty field tuple. -/
theorem closed_and_leaf (P : Premises4) (k : Nat) :
    (∀ i z, CtorAt P (table P) (EvalPlanNormal.fd plan)
      (NormSmallFrame.candidate P (table P) plan) [] i z →
      z ∈ NormSmallFrame.candidate P (table P) plan [] i) ∧
    dataVal 0 [] ∈ NormSmallFrame.candidate P (table P) plan [] (key [tyv fxS]) := by
  have har : plan.node.a.family.member.arity = 0 := NormFreshHeadAttack.arity
  have hm := (produced P k).1 [] har.symm
    (fun v hv => (List.not_mem_nil v hv).elim)
  have hc := NormSmallFrameLocal.closed_at P (table P) plan PendAW.fam
    [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT PendAW.membersT
    NormDataRecMemAttack.type_family []
    (by
      simpa only [har, PiSmallFrame.canonical, canonL, List.range_zero, List.map_nil] using hm)
  refine ⟨hc, ?_⟩
  rw [NormPendAW.normalized_descriptor] at hc
  apply hc (key [tyv fxS]) (dataVal 0 [])
  refine ⟨⟨0, by decide⟩, [tyv fxS], [], ?_, True.intro, True.intro, rfl, Equiv.rfl⟩
  exact PendAWBridge.argsFit P _ pempty

def Witness (P : Premises4) : Prop :=
  ReaderPacketBinderAttack.Witness P ∧ CheckedCtorWorldListAttack.Witness P ∧
  (∀ k, NormSmallFrameLocal.BoundedReachedMasks P (table P) plan (fun _ => k) ∧
    PointwiseDataLocal.LocalCandidates P (table P) plan (fun _ => k)) ∧
  (∀ k, (∀ r m, PendAW.eAll.members r = some m → r ≠ 7 →
    MemberSound P (table P) (fun _ => k) r m) ∧
    (∀ σ n, EnvSound (mkM P (table P)) σ (fun _ => k) plan.node.E0 n)) ∧
  (∀ k : Nat, (∀ i z, CtorAt P (table P) (EvalPlanNormal.fd plan)
    (NormSmallFrame.candidate P (table P) plan) [] i z →
    z ∈ NormSmallFrame.candidate P (table P) plan [] i) ∧
    dataVal 0 [] ∈ NormSmallFrame.candidate P (table P) plan [] (key [tyv fxS]))

theorem component_witness (P : Premises4) : Witness P :=
  ⟨ReaderPacketBinderAttack.component_witness P, CheckedCtorWorldListAttack.component_witness P,
    produced P, reader_prefix P, closed_and_leaf P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PointwiseFieldMasksAttack

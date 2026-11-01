import rcic.RcicF3NormSmallFrameLocal
import rcic.RcicF3NormSmallFrameAttack
import rcic.RcicF3PointwiseDataPrefixAttack
import rcic.RcicF3RecFieldMaskSupportAttack

/-!
# Local bounded assembly at the actual admitted W group

The W reader's literal bvar domain supplies the reached masks. The NEW
local assembler is called directly to construct LocalCandidates, then the
new checked constructor/reader-prefix consumer is called at its actual
installed pointwise table. Neither call uses global closure of the
signature candidate. A direct leaf constructor inhabits the locally
closed candidate at its exact complete parameter key.

The same-P conjunction retains the independent height-omega assembly,
actual installation, supported differing-capture typing witness, and
their literal scopes. This fixture pays the bounded mask input for W;
the corresponding producer for arbitrary admitted groups is still open.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormSmallFrameLocalAttack
open Rcic.Declarative RawFamily PiIndex
open NormPendAW (plan)

def Witness (P : Premises4) : Prop :=
  RecFieldMaskSupportAttack.Witness P ∧ NormSmallFrameAttack.Witness P ∧
  PointwiseRoleAttack.Witness P ∧ PointwiseNatInvariant.Witness P ∧
  (∀ μ K, NormSmallFrameLocal.BoundedReachedMasks P μ plan K ∧
    PointwiseDataLocal.LocalCandidates P μ plan K) ∧
  (∀ μ, PointwiseData.ExistsAt P μ (EvalPlanNormal.fd plan)
      plan.node.a.family.member.arity [] ∧
    (∀ i z, CtorAt P μ (EvalPlanNormal.fd plan) (NormSmallFrame.candidate P μ plan)
      [] i z → z ∈ NormSmallFrame.candidate P μ plan [] i) ∧
    dataVal 0 [] ∈ NormSmallFrame.candidate P μ plan [] (key [tyv fxS])) ∧
  (∀ k, (∀ r m, PendAW.eAll.members r = some m → r ≠ 7 →
    MemberSound P (PointwiseRoleAttack.table P) (fun _ => k) r m) ∧
    (∀ σ n, EnvSound (mkM P (PointwiseRoleAttack.table P)) σ (fun _ => k)
      plan.node.E0 n))

/-- Local assembly and the actual installed-prefix consumer are both
invoked here, so the component does not merely repeat a global closure. -/
theorem component_witness (P : Premises4) : Witness P := by
  have hMasks : ∀ μ K, NormSmallFrameLocal.BoundedReachedMasks P μ plan K := by
    intro μ K vs hvl _
    exact NormSmallFrameAttack.masks P μ vs hvl
  have hLocal : ∀ μ K, PointwiseDataLocal.LocalCandidates P μ plan K := by
    intro μ K
    exact NormSmallFrameLocal.local_candidates P μ plan PendAW.fam
      [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT PendAW.membersT
      NormDataRecMemAttack.type_family K (hMasks μ K)
  have hMask0 : ∀ μ, NormSmallFrameLocal.ReachedMasksAt P μ plan
      (PiSmallFrame.canonical plan.node.a.family.member.arity []) := by
    intro μ
    exact NormSmallFrameAttack.masks P μ _ (PiSmallFrame.canonical_length _ [])
  have hClose : ∀ μ, ∀ i z,
      CtorAt P μ (EvalPlanNormal.fd plan) (NormSmallFrame.candidate P μ plan) [] i z →
      z ∈ NormSmallFrame.candidate P μ plan [] i := by
    intro μ
    exact NormSmallFrameLocal.closed_at P μ plan PendAW.fam
      [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT PendAW.membersT
      NormDataRecMemAttack.type_family [] (hMask0 μ)
  refine ⟨RecFieldMaskSupportAttack.component_witness P,
    NormSmallFrameAttack.component_witness P, PointwiseRoleAttack.component_witness P,
    PointwiseNatInvariant.component_witness P, fun μ K => ⟨hMasks μ K, hLocal μ K⟩,
    ?_, ?_⟩
  · intro μ
    have he := NormSmallFrameLocal.exists_at P μ plan PendAW.fam
      [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT PendAW.membersT
      NormDataRecMemAttack.type_family [] (hMask0 μ)
    have har : plan.node.a.family.member.arity = 0 := NormFreshHeadAttack.arity
    have hc := hClose μ
    refine ⟨?_, hc, ?_⟩
    · simpa only [har, PiSmallFrame.canonical, canonL, List.range_zero, List.map_nil]
        using he
    · rw [NormPendAW.normalized_descriptor] at hc
      apply hc (key [tyv fxS]) (dataVal 0 [])
      refine ⟨⟨0, by decide⟩, [tyv fxS], [], ?_, True.intro, True.intro,
        rfl, Equiv.rfl⟩
      exact PendAWBridge.argsFit P _ pempty
  · intro k
    exact PointwiseDataPrefix.sound_of_local_candidates P (PointwiseRoleAttack.table P)
      (fun _ => k) natEnvUWfT rfl PendAWGroup.ctorClasses rfl PendAW.membersT
      PendAWGroup.walkAgree (PendAWGroup.boundG _) (PointwiseNatInvariant.gInv P _)
      (PointwiseRole.arities PendAW.eAll) PointwiseRoleAttack.metadata
      (NormRole.envCtx PendAWGroup.wft) (EvalRole.envPlan PendAWGroup.wft)
      (fun _ _ => rfl) (fun _ _ => rfl) (PointwiseRoleAttack.faithful P)
      (NormDataGroupAttack.group_check k) (hLocal (PointwiseRoleAttack.table P) _)
      NormDataRecMemAttack.type_family

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormSmallFrameLocalAttack

import rcic.RcicF3PointwiseDataNormal
import rcic.RcicF3NormSmallFrameAttack

/-!
# Pointwise interpretation at the exact admitted PendA W group

The new pointwise interpretation is instantiated at the actual canonical
plan. Its local candidate existence is produced from the independently
assembled W candidate, at every world and every ambient table. The new
local closure theorem then gives actual global closure for this fixture.
Both the leaf and fxZW enter the new frame; the latter remains excluded
by the old finite-stage family. Every component uses the same Premises4.

This witness concerns the separate family interpretation. No new table
installer, new invariant, universal bounded mask producer, or checked
kernel tier is asserted. The retained auxiliary depth-three component
remains a separate semantic fixture. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseDataAttack
open Rcic.Declarative PiIndex RawFamily
open NormPendAW (plan)

noncomputable def candidate (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) : Frame :=
  PointwiseData.frame P μ (EvalPlanNormal.fd plan) plan.node.a.family.member.arity

/-- This constructor-free size proof needs no local candidate existence. -/
theorem admissible (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Admissible (EvalPlanNormal.fd plan) (candidate P μ) :=
  PointwiseData.frame_admissible P μ _ _
    (EvalPlanNormal.bounded_of_group plan PendAW.fam
      [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT PendAW.membersT)

/-- The new local-existence adapter is invoked on a genuinely produced
candidate. It uses only the selected world's constructor closure. -/
theorem local_exists (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (vs : List Nat) :
    PointwiseData.ExistsAt P μ (EvalPlanNormal.fd plan) plan.node.a.family.member.arity
      (PiSmallFrame.canonical plan.node.a.family.member.arity vs) :=
  PointwiseData.exists_of_candidate P μ plan PendAW.fam
    [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT PendAW.membersT
    (NormSmallFrame.candidate P μ plan) (NormSmallFrameAttack.component P μ).1
    (PiSmallFrame.canonical plan.node.a.family.member.arity vs)
    (PiSmallFrame.canonical_idem _ vs)
    ((NormSmallFrameAttack.component P μ).2 _)

theorem closed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Closed P μ (EvalPlanNormal.fd plan) (candidate P μ) := by
  intro vs i z hz
  exact PointwiseData.frame_closed_at P μ plan PendAW.fam
    [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT PendAW.membersT
    vs (local_exists P μ vs) i z hz

theorem exact_stage (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (vs : List Nat) (i : Index.{4}) :
    candidate P μ vs i ∈ W4 1 ∧ ¬ pempty ∈ candidate P μ vs i := by
  have h := admissible P μ vs i
  have hr : (EvalPlanNormal.fd plan).resLevel = .succ .zero :=
    congrArg FamData.resLevel NormPendAW.normalized_descriptor
  rw [hr] at h
  refine ⟨h.1, ?_⟩
  have hd := h.2
  change ∀ z, z ∈ candidate P μ vs i → ¬ Equiv z pempty at hd
  exact fun hz => hd pempty hz Equiv.rfl

theorem leaf_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    dataVal 0 [] ∈ candidate P μ [] (key [tyv fxS]) := by
  apply closed P μ [] (key [tyv fxS]) (dataVal 0 [])
  rw [NormPendAW.normalized_descriptor]
  refine ⟨⟨0, by decide⟩, [tyv fxS], [], ?_, True.intro, True.intro, rfl, Equiv.rfl⟩
  exact PendAWBridge.argsFit P _ pempty

/-- Independent raw membership is included by leastness into the new
frame only after its new admissibility and closure have been proved. -/
theorem omega_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    fxZW P ∈ candidate P μ [] (key [tyv fxS]) := by
  have hfit : TelFits (mkM P μ) (σOf [])
      ((EvalPlanNormal.fd plan).params ++ (EvalPlanNormal.fd plan).indices) ρ0 [tyv fxS] := by
    rw [NormPendAW.normalized_descriptor]
    exact PendAWBridge.argsFit P μ pempty
  have hr := mem_congr_right
    (apply_ofFrame_ed P μ (EvalPlanNormal.fd plan)
      (RawFamily.frame P μ (EvalPlanNormal.fd plan)) (NormPendAW.normalized_admissible P μ)
      [] [tyv fxS] hfit) (NormPendAW.normalized_height_omega P μ).1
  exact RawFamily.frame_least P μ (EvalPlanNormal.fd plan) (candidate P μ)
    (admissible P μ) (closed P μ) [] (key [tyv fxS]) (fxZW P) hr

/-- This invokes the new density theorem, not old global frame density. -/
theorem omega_constructor (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    CtorAt P μ (EvalPlanNormal.fd plan) (candidate P μ)
      [] (key [tyv fxS]) (fxZW P) :=
  PointwiseData.frame_dense P μ plan PendAW.fam
    [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT PendAW.membersT
    [] (key [tyv fxS]) (fxZW P) (omega_mem P μ)

theorem role_typed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (vs : List Nat) :
    PointwiseData.role P μ (EvalPlanNormal.fd plan) plan.node.a.family.member.arity vs ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 (famType (EvalPlanNormal.fd plan))) :=
  PointwiseData.role_mem P μ _ _
    (EvalPlanNormal.bounded_of_group plan PendAW.fam
      [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT PendAW.membersT) vs

theorem role_height_omega (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    fxZW P ∈ Ed (mkM P μ) (fapps
      (PointwiseData.role P μ (EvalPlanNormal.fd plan) plan.node.a.family.member.arity [])
      [tyv fxS]) := by
  have hfit : TelFits (mkM P μ) (σOf [])
      ((EvalPlanNormal.fd plan).params ++ (EvalPlanNormal.fd plan).indices) ρ0 [tyv fxS] := by
    rw [NormPendAW.normalized_descriptor]
    exact PendAWBridge.argsFit P μ pempty
  exact mem_congr_right
    (apply_ofFrame_ed P μ (EvalPlanNormal.fd plan) (candidate P μ)
      (admissible P μ) [] [tyv fxS] hfit).symm (omega_mem P μ)

def Witness (P : Premises4) : Prop :=
  NormSmallFrameAttack.Witness P ∧
  (∀ μ vs, PointwiseData.ExistsAt P μ (EvalPlanNormal.fd plan)
    plan.node.a.family.member.arity (PiSmallFrame.canonical plan.node.a.family.member.arity vs)) ∧
  (∀ μ, Admissible (EvalPlanNormal.fd plan) (candidate P μ) ∧
    Closed P μ (EvalPlanNormal.fd plan) (candidate P μ)) ∧
  (∀ μ vs i, candidate P μ vs i ∈ W4 1 ∧ ¬ pempty ∈ candidate P μ vs i) ∧
  (∀ μ vs, PointwiseData.role P μ (EvalPlanNormal.fd plan) plan.node.a.family.member.arity vs ∈
    Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 (famType (EvalPlanNormal.fd plan)))) ∧
  (∀ μ, dataVal 0 [] ∈ candidate P μ [] (key [tyv fxS]) ∧
    fxZW P ∈ candidate P μ [] (key [tyv fxS]) ∧
    CtorAt P μ (EvalPlanNormal.fd plan) (candidate P μ) [] (key [tyv fxS]) (fxZW P) ∧
    fxZW P ∈ Ed (mkM P μ) (fapps
      (PointwiseData.role P μ (EvalPlanNormal.fd plan) plan.node.a.family.member.arity [])
      [tyv fxS]) ∧
    fxZW P ∉ El (fapps (famLim P μ (EvalPlanNormal.fd plan) []) [tyv fxS]))

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormSmallFrameAttack.component_witness P, local_exists P,
    (fun μ => ⟨admissible P μ, closed P μ⟩), exact_stage P, role_typed P,
    (fun μ => ⟨leaf_mem P μ, omega_mem P μ, omega_constructor P μ,
      role_height_omega P μ, (NormPendAW.normalized_height_omega P μ).2⟩)⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PointwiseDataAttack

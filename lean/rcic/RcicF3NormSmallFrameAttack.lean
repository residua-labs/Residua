import rcic.RcicF3NormSmallFrame
import rcic.RcicF3NormDataGroup
import rcic.RcicF3PiSmallMaskShapeAttack

/-!
# All-instance small-frame assembly at the admitted PendA W group

The actual W node has one recursive field with domain bvar 0, before any
recursive local is introduced. Its exact domain mask is produced at all
valuations and all ambient tables. The new general frame assembler then
supplies a small closed candidate and the new generic DATA group step.
The candidate contains both the leaf and the exact height-omega element.

The depth-three masked compiler fixture is retained as a separate
auxiliary semantic component; it is not identified with the admitted W
environment. All components use the same Premises4 value. This proves
neither universal admitted masks nor a bounded-to-all-world erasure rule.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormSmallFrameAttack
open Rcic.Declarative PiIndex RawFamily
open NormPendAW (plan)

theorem empty_mask (P : Premises4) (μ ν : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {ss : List FieldShape} {Fs : List (Expr Nat)}
    (cache : EvalPlan.Fields E fuel f nu np ni prior ss Fs)
    (hFs : Fs = []) (ρ : Nat → PSet.{4}) :
    PiSmallMaskShape.TupleMask (mkM P μ) (mkM P ν) σ
      (EvalPlanNormal.specs cache) ρ ρ [] := by
  subst Fs
  cases cache
  trivial

/-- This is a literal domain proof for the actual successful W reader.
It uses neither field soundness at K nor a previous family invariant. -/
theorem singleton_mask (P : Premises4) (μ ν : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {ss : List FieldShape} {Fs : List (Expr Nat)}
    (cache : EvalPlan.Fields E fuel f nu np ni prior ss Fs)
    (hFs : Fs = [PendAW.field]) (hf : f = 4)
    (hbody : transparentBody E 4 [] = none) (ρ : Nat → PSet.{4}) (x : PSet.{4}) :
    PiSmallMaskShape.TupleMask (mkM P μ) (mkM P ν) σ
      (EvalPlanNormal.specs cache) ρ ρ [x] := by
  subst Fs
  subst f
  cases cache with
  | cons head tail =>
      cases tail
      cases head with
      | plain hfree =>
          change true = false at hfree
          cases hfree
      | recursive r =>
          have hd : r.domains = [.bvar 0] := congrArg Prod.fst
            (NormPendAW.field_reader E hbody fuel r.domains
              (foldApps (.const 4 (canonL nu)) r.arguments) r.read)
          change PiSmallMaskSpine.Domains (mkM P μ) (mkM P ν) σ r.domains ρ ρ ∧ True
          rw [hd]
          exact ⟨⟨Equiv.rfl, fun _ _ => True.intro⟩, True.intro⟩

/-- All canonical worlds are covered, with no bound on their values.
In fact the local domain calculation does not use the vector length. -/
theorem masks (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    NormSmallFrame.ReachedMasks P μ plan := by
  intro vs _ j ps xs _ hx _
  rw [NormPendAW.fields_eq] at hx
  rcases (PendAWGroup.views plan.node j).2.2 with ⟨hf, _⟩ | ⟨hf, _⟩
  · have hxs : xs = [] := List.length_eq_zero.mp (hx.length.trans (congrArg List.length hf))
    subst xs
    exact empty_mask P _ μ (σOf vs) (plan.constructors j).fields hf (push ps ρ0)
  · have hxs : xs.length = 1 := hx.length.trans (congrArg List.length hf)
    obtain ⟨x, hxs⟩ := List.length_eq_one.mp hxs
    subst xs
    exact singleton_mask P _ μ (σOf vs) (plan.constructors j).fields hf
      plan.node.fam NormPendAW.family_body (push ps ρ0) x

/-- Invoke the new general assembler with the actual plan and its
produced all-instance mask, for every ambient table. -/
theorem component (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Admissible (EvalPlanNormal.fd plan) (NormSmallFrame.candidate P μ plan) ∧
      Closed P μ (EvalPlanNormal.fd plan) (NormSmallFrame.candidate P μ plan) :=
  NormSmallFrame.component P μ plan PendAW.fam [(5, PendAW.leaf), (6, PendAW.node)]
    natEnvUWfT PendAW.membersT NormDataRecMemAttack.type_family (masks P μ)

theorem exact_stage (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (vs : List Nat) (i : Index.{4}) :
    NormSmallFrame.candidate P μ plan vs i ∈ W4 1 ∧
      ¬ pempty ∈ NormSmallFrame.candidate P μ plan vs i := by
  have h := (component P μ).1 vs i
  have hr : (EvalPlanNormal.fd plan).resLevel = .succ .zero :=
    congrArg FamData.resLevel NormPendAW.normalized_descriptor
  rw [hr] at h
  refine ⟨h.1, ?_⟩
  have hd := h.2
  change (∀ z, z ∈ NormSmallFrame.candidate P μ plan vs i → ¬ Equiv z pempty) at hd
  exact fun hz => hd pempty hz Equiv.rfl

/-- A direct constructor step independently inhabits the new candidate. -/
theorem leaf_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    dataVal 0 [] ∈ NormSmallFrame.candidate P μ plan [] (key [tyv fxS]) := by
  have hc := (component P μ).2
  rw [NormPendAW.normalized_descriptor] at hc
  apply hc [] (key [tyv fxS]) (dataVal 0 [])
  refine ⟨⟨0, by decide⟩, [tyv fxS], [], ?_, True.intro, True.intro, rfl, Equiv.rfl⟩
  exact PendAWBridge.argsFit P _ pempty

/-- The independent raw least-frame membership projects into this new
closed candidate. No comparison of small parameter signatures is used. -/
theorem omega_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    fxZW P ∈ NormSmallFrame.candidate P μ plan [] (key [tyv fxS]) := by
  have hfit : TelFits (mkM P μ) (σOf [])
      ((EvalPlanNormal.fd plan).params ++ (EvalPlanNormal.fd plan).indices) ρ0 [tyv fxS] := by
    rw [NormPendAW.normalized_descriptor]
    exact PendAWBridge.argsFit P μ pempty
  have hr := mem_congr_right
    (apply_ofFrame_ed P μ (EvalPlanNormal.fd plan)
      (frame P μ (EvalPlanNormal.fd plan)) (NormPendAW.normalized_admissible P μ)
      [] [tyv fxS] hfit) (NormPendAW.normalized_height_omega P μ).1
  exact frame_least P μ (EvalPlanNormal.fd plan) (NormSmallFrame.candidate P μ plan)
    (component P μ).1 (component P μ).2 [] (key [tyv fxS]) (fxZW P) hr

/-- The candidate supplies the complete generic group-step context,
including arbitrary faithful ambient tables. -/
theorem small_frames (P : Premises4) (K : Nat → Nat) :
    NormDataGroup.SmallFrameAt P K natEnvUWfT rfl PendAWGroup.ctorClasses rfl
      PendAW.membersT := by
  intro _ _ _ _ _ _ _ _ μ _
  exact ⟨NormSmallFrame.candidate P μ plan, component P μ⟩

theorem group_step (P : Premises4) (K : Nat → Nat) :
    NormRole.GroupStepAt P K natEnvUWfT rfl PendAWGroup.ctorClasses rfl
      PendAW.membersT :=
  NormDataGroup.group_step P K natEnvUWfT rfl PendAWGroup.ctorClasses rfl
    PendAW.membersT NormDataRecMemAttack.type_family
    NormDataRecMemAttack.matching_parameters (small_frames P K)

def Witness (P : Premises4) : Prop :=
  PiSmallMaskShapeAttack.Witness P ∧
  Nonempty (EnvWfT PendAW.eAll) ∧ PendA PendAW.pNode ∧
  (∀ μ, NormSmallFrame.ReachedMasks P μ plan) ∧
  (∀ μ, Admissible (EvalPlanNormal.fd plan) (NormSmallFrame.candidate P μ plan) ∧
    Closed P μ (EvalPlanNormal.fd plan) (NormSmallFrame.candidate P μ plan)) ∧
  (∀ μ vs i, NormSmallFrame.candidate P μ plan vs i ∈ W4 1 ∧
    ¬ pempty ∈ NormSmallFrame.candidate P μ plan vs i) ∧
  (∀ μ, dataVal 0 [] ∈ NormSmallFrame.candidate P μ plan [] (key [tyv fxS]) ∧
    fxZW P ∈ NormSmallFrame.candidate P μ plan [] (key [tyv fxS]) ∧
    fxZW P ∉ El (fapps (famLim P μ (EvalPlanNormal.fd plan) []) [tyv fxS])) ∧
  (∀ K, NormDataGroup.SmallFrameAt P K natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT) ∧
  (∀ K, NormRole.GroupStepAt P K natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨PiSmallMaskShapeAttack.component_witness P, ⟨PendAWGroup.wft⟩, PendAW.pendA,
    masks P, component P, exact_stage P,
    (fun μ => ⟨leaf_mem P μ, omega_mem P μ, (NormPendAW.normalized_height_omega P μ).2⟩),
    small_frames P, group_step P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormSmallFrameAttack

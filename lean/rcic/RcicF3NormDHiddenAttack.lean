import rcic.RcicF3NormDFallbackAttack
import rcic.RcicF3DFixture

/-!
# The new checked D step at the actual delta-hidden recursive group

The definition Id is handled by the new normalized singleton producer.
The admitted group whose original field is Id F then uses the new checked
fallback step, at exactly the existing K 2 <= K 3 condition. This produces
the normalized invariant and soundness of its actual installed table.

The original field is not replaced in the stored constructor or its typing.
The fixture is outside ClassG, and its successful recursive analysis reads
through delta and beta. The family itself has no base constructor; this
module does not claim an inhabitant of that empty recursive family. The
retained Nat and height-omega W components supply the nontrivial elements
of the complete conjunction. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.NormDHiddenAttack
open Rcic.Declarative Rcic.Model.PS Rcic.F3.StepDGOrder

theorem ctorClasses : ∀ c ∈ [(2, drMkMember)], c.2.mclass = .constructorM := by
  intro c hc
  cases List.mem_singleton.mp hc
  rfl

noncomputable def plan : EvalPlan.Plan :=
  EvalPlan.ofGroup drBaseWfT (f := 1) (fm := drFamMember)
    (ctors := [(2, drMkMember)]) (rr := 3) (rm := drRecMember)
    rfl ctorClasses rfl drMembersT

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  NormRole.table P drEnvWfT

/-- The actual singleton predecessor is produced under the new role and
plan invariant. No old singleton or group invariant is transported. -/
theorem base_invariant (P : Premises4) (K : Nat → Nat) :
    NormRole.GInv P K drBaseWfT := by
  intro ctx hctx plans hplans μ hFaith
  let d : HasTyT emptyEnv 0 []
      (.lam (.sort (.succ .zero)) (.bvar 0)) drIdMember.mtype :=
    .lam [] _ (.succ (.succ .zero)) (.bvar 0) _
      (.sort [] _) (.bvar _ 0 _ rfl)
  have hd : LOKt (fun _ => 0) 4 K d := (drEnvWfT_classGD.2 K).1.1.2
  exact NormRole.gInv_singleW P K (E := emptyEnv) (hE := EnvWfT.empty)
    (r := 0) (k := .definitionM) (A := drIdMember.mtype)
    (v := .lam (.sort (.succ .zero)) (.bvar 0))
    (Or.inl rfl) rfl (fun _ => rfl) (fun _ => rfl) rfl rfl d hd
    (NormRole.gInv_empty P K) ctx hctx plans hplans μ hFaith

/-- The exact existing check is sufficient at this admitted hidden-field
group. Its negative-A and data cases are proved from the actual node. -/
theorem group_step (P : Premises4) (K : Nat → Nat) (hk : K 2 ≤ K 3) :
    NormRole.GroupStepAt P K drBaseWfT (f := 1) (fm := drFamMember)
      (ctors := [(2, drMkMember)]) (rr := 3) (rm := drRecMember)
      rfl ctorClasses rfl drMembersT := by
  have hFallback : ¬ (UniformProp plan.node.a.family.resultLevel ∧
      plan.node.a.policy = .anySort) := by
    intro ⟨hU, _⟩
    rw [(dr_family plan.node).2.2] at hU
    exact Nat.noConfusion (hU (fun _ => 0))
  exact NormDFallback.group_step_of_check P K drBaseWfT
    (f := 1) (fm := drFamMember) (ctors := [(2, drMkMember)])
    (rr := 3) (rm := drRecMember) rfl ctorClasses rfl drMembersT
    (Rcic.F3.StepWDApex.dr_groupCheck_passes K hk)
    (fun ⟨node, ha⟩ => Rcic.F3.TierGroup.drGroup_dArm.1 node ha) hFallback

/-- The actual bounded admission and walk compose with the new singleton
predecessor; all semantic inputs of the new group step are supplied. -/
theorem invariant (P : Premises4) (K : Nat → Nat) (hk : K 2 ≤ K 3) :
    NormRole.GInv P K drEnvWfT :=
  group_step P K hk Rcic.F3.TierGroup.drAgree
    (drEnvWfT_classGD.2 K).1 (drEnvWfT_classGD.2 K).2 (base_invariant P K)

def Witness (P : Premises4) : Prop :=
  NormDFallbackAttack.Witness P ∧
  (¬ ClassG drEnvWfT) ∧
  (∀ j : Fin plan.node.a.constructors.length,
    (plan.node.a.constructorViews j).fields = [drField] ∧
      plan.node.h14.shapesAt j = [.recursive 0]) ∧
  EvalRole.Faithful RawFamily.role P (table P) (NormRole.envCtx drEnvWfT)
    (EvalRole.envPlan drEnvWfT) drEnv ∧
  (∀ K, NormRole.GInv P K drBaseWfT) ∧
  (∀ K, K 2 ≤ K 3 →
    NormRole.GroupStepAt P K drBaseWfT (f := 1) (fm := drFamMember)
      (ctors := [(2, drMkMember)]) (rr := 3) (rm := drRecMember)
      rfl ctorClasses rfl drMembersT ∧
    NormRole.GInv P K drEnvWfT ∧
    ∀ σ n, EnvSound (mkM P (table P)) σ K drEnv n) ∧
  (∀ k, Rcic.F3.StepWDApex.envCheck (fun _ => k) drEnvWfT = true)

theorem component_witness (P : Premises4) : Witness P := by
  refine ⟨NormDFallbackAttack.component_witness P, drEnvWfT_not_classG,
    fun j => ⟨(dr_view plan.node j).2.2, dr_shapes plan.node j⟩,
    (NormRole.table_spec P drEnvWfT).1, base_invariant P, ?_, ?_⟩
  · intro K hk
    have hI := invariant P K hk
    exact ⟨group_step P K hk, hI,
      fun σ n => NormRole.envSound_of_gInv P K drEnvWfT hI σ n⟩
  · intro k
    apply (Rcic.F3.StepWDApex.envCheck_pass_iff (fun _ => k) drEnvWfT).mpr
    exact ⟨True.intro,
      (Rcic.F3.StepDGCheck.drSide_iff (fun _ => k) _).mpr (Nat.le_refl k)⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormDHiddenAttack

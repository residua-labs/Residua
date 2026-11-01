import rcic.RcicF3NormRoleTable
import rcic.RcicF3NormRoleDelta
import rcic.RcicF3EvalPlanNormalProp
import rcic.RcicF3EvalInstalledAttack

/-!
# Actual AccR composition for the normalized role, reads and table

The actual admitted environment supplies its normalized role descriptor,
unchanged original evaluation plan, both read-along certificates, faithful
table, read closure, transparent-body equations and small closed Prop frame.
These conjuncts concern the new table itself. No equality to the old raw
table or semantic invariant is assumed.

The AccR child-domain fixture used elsewhere is empty; this installation
witness makes no stronger child-domain, imported-environment or soundness
claim. It is conditional on Premises4. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormRoleTableAttack
open Rcic.Declarative
open EvalPlanValueAttack (plan)

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  NormRole.table P AccEnv.accEnvWfT

def Witness (P : Premises4) : Prop :=
  NormRole.envCtx AccEnv.accEnvWfT 0 = .fam (EvalPlanNormal.fd plan) ∧
  NormRole.envCtx AccEnv.accEnvWfT 1 = .ctor (EvalPlanNormal.fd plan) 0 ∧
  EvalRole.envPlan AccEnv.accEnvWfT 2 = some plan ∧
  PSet.ReadsOKAlong (NormRole.envCtx AccEnv.accEnvWfT) AccEnv.accEnvWfT ∧
  EvalRole.ReadsOKAlong (NormRole.envCtx AccEnv.accEnvWfT)
    (EvalRole.envPlan AccEnv.accEnvWfT) AccEnv.accEnvWfT ∧
  EvalRole.Faithful RawFamily.role P (table P) (NormRole.envCtx AccEnv.accEnvWfT)
    (EvalRole.envPlan AccEnv.accEnvWfT) accEnv ∧
  EvalRole.ReadsClosed (NormRole.envCtx AccEnv.accEnvWfT)
    (EvalRole.envPlan AccEnv.accEnvWfT) accEnv ∧
  (∀ σ, DeltaNormalize.BodyEquations (mkM P (table P)) plan.node.E0 σ) ∧
  RawFamily.Admissible (EvalPlanNormal.fd plan)
    (RawFamily.frame P (table P) (EvalPlanNormal.fd plan)) ∧
  RawFamily.Closed P (table P) (EvalPlanNormal.fd plan)
    (RawFamily.frame P (table P) (EvalPlanNormal.fd plan))

theorem component_witness (P : Premises4) : Witness P := by
  have hctors : ∀ c ∈ [(1, accIntroMember)], c.2.mclass = .constructorM := by
    intro c hc
    cases List.mem_singleton.mp hc
    rfl
  have hp : EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
      (fm := accFamMember) (ctors := [(1, accIntroMember)])
      (rr := 2) (rm := accRecMember) rfl hctors rfl AccEnv.accMembersT = plan := by
    have h := EvalInstalledAttack.canonical_plan
    change some (EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
      (fm := accFamMember) (ctors := [(1, accIntroMember)])
      (rr := 2) (rm := accRecMember) rfl hctors rfl AccEnv.accMembersT) = some plan at h
    exact Option.some.inj h
  have hcontext := NormRole.envCtx_group (.empty : EnvWfT emptyEnv)
    (fm := accFamMember) (ctors := [(1, accIntroMember)])
    (rr := 2) (rm := accRecMember) rfl hctors rfl AccEnv.accMembersT
  change NormRole.envCtx AccEnv.accEnvWfT =
    groupRoles (EvalPlanNormal.fd (EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
      (fm := accFamMember) (ctors := [(1, accIntroMember)])
      (rr := 2) (rm := accRecMember) rfl hctors rfl AccEnv.accMembersT))
      0 2 (fun _ => .plain) at hcontext
  rw [hp] at hcontext
  have ht := NormRole.table_spec P AccEnv.accEnvWfT
  have hn := EvalPlanNormalProp.normalized_closed P (table P) plan accFamMember
    [(1, accIntroMember)] .empty AccEnv.accMembersT (fun _ => 0) rfl rfl
  refine ⟨?_, ?_, EvalInstalledAttack.canonical_plan,
    NormRole.readsOKAlong_envCtxT AccEnv.accEnvWfT _ (fun _ _ => rfl),
    NormRole.planReadsOKAlong AccEnv.accEnvWfT _ _ (fun _ _ => rfl) (fun _ _ => rfl),
    ht.1, ht.2, ?_, hn.1, hn.2⟩
  · rw [hcontext, groupRoles_at_f]
  · rw [hcontext]
    exact groupRoles_at_ctor _ _ (by decide : 0 + 1 + 0 < 2)
  · intro σ
    exact NormRoleDelta.bodyEquations_at_node P (table P)
      (NormRole.envCtx AccEnv.accEnvWfT) (EvalRole.envPlan AccEnv.accEnvWfT)
      (fm := accFamMember) (ctors := [(1, accIntroMember)])
      .empty rfl hctors rfl AccEnv.accMembersT (fun _ _ => rfl) ht.1 plan.node σ

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormRoleTableAttack

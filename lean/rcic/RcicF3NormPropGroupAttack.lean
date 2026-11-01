import rcic.RcicF3NormPropGroup
import rcic.RcicF3NormPropCtorAttack

/-!
# Produced new invariant and non-refutability at the actual AccR group

All four literal GroupStepAt antecedents are supplied at the admitted
AccR fixture. The resulting normalized-role invariant is then applied to
its produced faithful table, yielding every stored member's soundness and
the stable literal recursor package. The original constructor's inhabited
argument tuple remains in the retained witness.

The old planned raw-role StepAG refutation is retained in the same
conjunction. No equivalence of old and new targets, universal StepAG,
admitted real Acc-on-Nat.lt, or checked W/D apex is claimed. The current
IotaAt conjunct has its literal legacy-witness scope. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPropGroupAttack
open Rcic.Declarative RawFamily
open NormRoleTableAttack (table)
open EvalPlanValueAttack (plan)
open PropEvalAdmittedInputsAttack (bound)

/-- Invoke the produced group step with the original walk and both
boundedness clauses, rather than supplying the invariant as an assumption. -/
theorem produced_gInv (P : Premises4) :
    NormRole.GInv P bound AccEnv.accEnvWfT := by
  have hctors : ∀ c ∈ [(1, accIntroMember)], c.2.mclass = .constructorM := by
    intro c hc
    cases List.mem_singleton.mp hc
    rfl
  let p := EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
    (fm := accFamMember) (ctors := [(1, accIntroMember)])
    (rr := 2) (rm := accRecMember) rfl hctors rfl AccEnv.accMembersT
  have hp : p = plan := by
    have h := EvalInstalledAttack.canonical_plan
    change some p = some plan at h
    exact Option.some.inj h
  have hProp : UniformProp p.node.a.family.resultLevel := by
    rw [hp]
    intro σ
    rfl
  have hpolicy : p.node.a.policy = .anySort := by rw [hp]; rfl
  exact NormPropGroup.group_step P bound .empty rfl hctors rfl AccEnv.accMembersT
    hProp hpolicy ⟨PlanPropStepAttack.pNode, PlanPropStepAttack.pendA⟩
    PlanPropStepAttack.walkAgree (PlanPropStepAttack.boundG bound)
    PlanPropStepAttack.boundDG (NormRole.gInv_empty P bound)

def Witness (P : Premises4) : Prop :=
  NormPropCtorAttack.Witness P ∧
  NormRole.GInv P bound AccEnv.accEnvWfT ∧
  AllSound P (table P) bound accEnv ∧
  RecPkg P (table P) bound accEnv 2 accRecMember ∧
  ¬ PlanRole.StepAG role P (fun _ => 1)

/-- The new invariant, actual faithful installation and all stored members
compose in the same environment in which the old target is refuted. -/
theorem component_witness (P : Premises4) : Witness P := by
  have hG := produced_gInv P
  have hSound := hG (NormRole.envCtx AccEnv.accEnvWfT) (fun _ _ => rfl)
    (EvalRole.envPlan AccEnv.accEnvWfT) (fun _ _ => rfl) (table P)
    (NormRole.table_spec P AccEnv.accEnvWfT).1
  exact ⟨NormPropCtorAttack.component_witness P, hG, hSound.1,
    ⟨hSound.1 2 accRecMember rfl,
      fun Efin hsub => hSound.2 Efin hsub 2 accRecMember rfl rfl⟩,
    PlanPropStepAttack.stepAG_false P⟩

/-- Non-refutability of the produced normalized-role group invariant at
this actual fixture. Universal production remains a separate obligation. -/
theorem invariant_nonrefutable (P : Premises4) :
    ¬ (NormRole.GInv P bound AccEnv.accEnvWfT → (Premises4 → False)) :=
  fun h => h (produced_gInv P) P

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormPropGroupAttack

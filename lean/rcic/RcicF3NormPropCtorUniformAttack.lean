import rcic.RcicF3NormPropCtorUniform
import rcic.RcicF3NormRoleTableAttack
import rcic.RcicF3PropEvalAdmittedInputsAttack

/-!
# The policy-independent constructor producer at the actual AccR table

The universal constructor theorem has no policy premise. This component
witness instantiates it at the available admitted AccR group, whose
literal policy is anySort. It does not label AccR a propOnly fixture.
The new uniform closure supplier, the actual faithful normalized table,
the original stored constructor and its inhabited argument application
are composed here. The selected recursive field has an empty child domain.

The propOnly recursor bridge and the universal A target remain unpaid.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPropCtorUniformAttack
open Rcic.Declarative PiIndex RawFamily PlanPropEndAttack
open EvalPlanValueAttack (plan)
open NormRoleTableAttack (table)
open PropEvalAdmittedInputsAttack (bound)

def Witness (P : Premises4) : Prop :=
  NormRoleTableAttack.Witness P ∧
  UniformProp plan.node.a.family.resultLevel ∧
  plan.node.a.policy = .anySort ∧
  Admissible (EvalPlanNormal.fd plan) (frame P (table P) (EvalPlanNormal.fd plan)) ∧
  Closed P (table P) (EvalPlanNormal.fd plan) (frame P (table P) (EvalPlanNormal.fd plan)) ∧
  MemberSound P (table P) bound 1 accIntroMember ∧
  TelFits (mkM P (table P)) σ [.sort .zero, accField] ρ0 [parameter, pempty] ∧
  fapps (table P 1 []) [parameter, pempty] ∈
    Ed (mkM P (table P)) (fapp (table P 0 []) parameter)

theorem component_witness (P : Premises4) : Witness P := by
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
  have hPropPlan : UniformProp plan.node.a.family.resultLevel := fun _ => rfl
  have hN := NormPropCtorUniform.normalized_closed P (table P) plan accFamMember
    [(1, accIntroMember)] .empty AccEnv.accMembersT hPropPlan
  have hFaith := (NormRole.table_spec P AccEnv.accEnvWfT).1
  have hj : p.node.a.constructors[0]? = some accIntroMember := by rw [hp]; rfl
  let j : Fin p.node.a.constructors.length := ⟨0, (List.getElem?_eq_some_iff.mp hj).1⟩
  have hget : p.node.a.constructors[j.val] = accIntroMember :=
    (List.getElem?_eq_some_iff.mp hj).2
  have hctor := NormPropCtorUniform.member_sound P (table P) bound
    (fm := accFamMember) (ctors := [(1, accIntroMember)])
    .empty rfl hctors rfl AccEnv.accMembersT (PlanPropStepAttack.boundG bound)
    (NormRole.gInv_empty P bound)
    (NormRole.envCtx AccEnv.accEnvWfT) (EvalRole.envPlan AccEnv.accEnvWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) hFaith hProp j
  change MemberSound P (table P) bound 1 (p.node.a.constructors[j.val]) at hctor
  rw [hget] at hctor
  have hfit : TelFits (mkM P (table P)) σ [.sort .zero, accField]
      ρ0 [parameter, pempty] :=
    TelFits.append (PropEvalAttack.parameters_fit P (table P))
      (PropEvalAttack.original_field_fit P (table P))
  refine ⟨NormRoleTableAttack.component_witness P, hPropPlan, rfl,
    hN.1, hN.2, hctor, hfit, ?_⟩
  have hm := (hctor σ [] ρ0 rfl (fun l hl => (List.not_mem_nil l hl).elim)).1
  change table P 1 [] ∈ Ed (mkM P (table P))
    (den (mkM P (table P)) σ ρ0 (policyPi [.sort .zero, accField]
      (accApp (.bvar 1)))) at hm
  exact mem_fapps (mkM P (table P)) σ (accApp (.bvar 1))
    [.sort .zero, accField] ρ0 (table P 1 []) [parameter, pempty] hm hfit

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormPropCtorUniformAttack

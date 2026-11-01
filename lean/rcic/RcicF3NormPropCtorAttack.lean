import rcic.RcicF3NormPropCtor
import rcic.RcicF3NormRoleTableAttack
import rcic.RcicF3PropEvalAdmittedInputsAttack

/-!
# Original AccR constructor soundness at the actual normalized table

The public constructor producer is applied to the actual typed group and
its produced normalized table. The witness retains the complete prefix
facts, an inhabited original constructor argument tuple, and membership
of the actual installed constructor application in its dependent result.

The recursive field is inhabited because the selected AccR parameter has
an empty child domain. This does not claim an inhabited recursive child,
a real imported Acc-on-Nat.lt environment, or the complete checked apex.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPropCtorAttack
open Rcic.Declarative PiIndex PlanPropEndAttack
open EvalPlanValueAttack (plan)
open NormRoleTableAttack (table)
open PropEvalAdmittedInputsAttack (bound)

def Witness (P : Premises4) : Prop :=
  NormRoleTableAttack.Witness P ∧
  NormRole.GInv P bound (.empty : EnvWfT emptyEnv) ∧
  CandidatePrefixFromGroup.GroupPrefixFacts P (table P) bound
    emptyEnv accEnv 0 2 accRecMember accFamMember plan.node ∧
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
  have hpolicy : p.node.a.policy = .anySort := by rw [hp]; rfl
  have hFaith := (NormRole.table_spec P AccEnv.accEnvWfT).1
  have hN := (EvalPlanNormalProp.normalized_closed P (table P) p accFamMember
    [(1, accIntroMember)] .empty AccEnv.accMembersT (fun _ => 0) (hProp _) hpolicy).1
  have hFacts := NormCandidatePrefix.canonical_group_facts P bound (table P)
    (fm := accFamMember) (ctors := [(1, accIntroMember)])
    .empty rfl hctors rfl AccEnv.accMembersT (NormRole.gInv_empty P bound)
    (NormRole.envCtx AccEnv.accEnvWfT) (EvalRole.envPlan AccEnv.accEnvWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) hFaith hN
  have hj : p.node.a.constructors[0]? = some accIntroMember := by rw [hp]; rfl
  let j : Fin p.node.a.constructors.length := ⟨0, (List.getElem?_eq_some_iff.mp hj).1⟩
  have hget : p.node.a.constructors[j.val] = accIntroMember :=
    (List.getElem?_eq_some_iff.mp hj).2
  have hctor := NormPropCtor.member_sound P (table P) bound
    (fm := accFamMember) (ctors := [(1, accIntroMember)])
    .empty rfl hctors rfl AccEnv.accMembersT (PlanPropStepAttack.boundG bound)
    (NormRole.gInv_empty P bound)
    (NormRole.envCtx AccEnv.accEnvWfT) (EvalRole.envPlan AccEnv.accEnvWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) hFaith hProp hpolicy j
  change MemberSound P (table P) bound 1 (p.node.a.constructors[j.val]) at hctor
  rw [hget] at hctor
  have hfit : TelFits (mkM P (table P)) σ [.sort .zero, accField]
      ρ0 [parameter, pempty] :=
    TelFits.append (PropEvalAttack.parameters_fit P (table P))
      (PropEvalAttack.original_field_fit P (table P))
  refine ⟨NormRoleTableAttack.component_witness P, NormRole.gInv_empty P bound,
    ?_, hctor, hfit, ?_⟩
  · change CandidatePrefixFromGroup.GroupPrefixFacts P (table P) bound
      emptyEnv accEnv 0 2 accRecMember accFamMember p.node at hFacts
    exact Eq.mp (congrArg (fun q : EvalPlan.Plan =>
      CandidatePrefixFromGroup.GroupPrefixFacts P (table P) bound
        q.E q.E' q.f q.rr q.rm accFamMember q.node) hp) hFacts
  · have hm := (hctor σ [] ρ0 rfl (fun l hl => (List.not_mem_nil l hl).elim)).1
    change table P 1 [] ∈ Ed (mkM P (table P))
      (den (mkM P (table P)) σ ρ0 (policyPi [.sort .zero, accField]
        (accApp (.bvar 1)))) at hm
    have h := mem_fapps (mkM P (table P)) σ (accApp (.bvar 1))
      [.sort .zero, accField] ρ0 (table P 1 []) [parameter, pempty] hm hfit
    exact h

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormPropCtorAttack

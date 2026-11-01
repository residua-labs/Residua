import rcic.RcicF3PropEvalNormalValue
import rcic.RcicF3EvalPlanNormalCompareAttack
import rcic.RcicF3EvalEndpointContract

/-!
# Actual installed AccR composition of normalized evaluation totality

The public normalized-candidate closure, raw-member evaluation producer and
typed scalar endpoint are instantiated at the new canonical AccR table.
The inputs are the actual admitted group, its BoundG, the empty repaired
predecessor, produced table faithfulness and the typed recursor arguments.
No raw closure or monotonicity is passed to those producers.

The selected AccR parameter has an empty recursive child domain. The
inherited depth-three inhabited auxiliary field and height-omega W case
remain separate conjuncts in the complete prior component suite. The
fixture does not claim imported Acc-on-Nat.lt or universal StepAG.
closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Rcic.F3.PSet.PropEvalNormalAttack
open Rcic.Declarative PiIndex RawFamily PropEval PlanPropEndAttack
open PropEvalAdmittedInputsAttack (bound)

noncomputable def C (P : Premises4) : Context := EvalInstalledAttack.currentContext P
noncomputable def μ (P : Premises4) : Nat → List Nat → PSet.{4} := EvalInstalledAttack.table P
noncomputable def X (P : Premises4) : Frame := PropEvalNormalized.candidate P (μ P) (C P)
noncomputable def result (P : Premises4) : PSet.{4} :=
  PropEvalValue.result (C P) (.param 0) (key [parameter])

private theorem ed_table (P : Premises4)
    (μ ν : Nat → List Nat → PSet.{4}) (A : PSet.{4}) :
    Ed (mkM P μ) A = Ed (mkM P ν) A := rfl

def Witness (P : Premises4) : Prop :=
  EvalEndpointContract.Components P ∧
  EvalPlanNormalCompareAttack.Witness P ∧
  Admissible (EvalPlanNormal.fd (EvalPlan.ofNode (C P).node)) (X P) ∧
  Closed P (μ P) (EvalPlanNormal.fd (EvalPlan.ofNode (C P).node)) (X P) ∧
  (∀ vs i z, z ∈ frame P (μ P) (famDataOf (C P).node.a) vs i →
    PropEvalCandidate.EvalPredicate (C P) vs i z) ∧
  Eval (C P) (key [parameter]) (result P) ∧
  result P ∈ childCarrier (C P) (.param 0) (key [parameter]) ∧
  result P ∈ Ed (C P).M (fapp (C P).motive pempty) ∧
  result P ∈ domain ∧ ¬ Equiv (result P) pempty

/-- The complete constructor/closure/leastness/extraction chain invokes
the new public producers on the same actual installed table. -/
theorem component_witness (P : Premises4) : Witness P := by
  have hctors : ∀ c ∈ [(1, accIntroMember)], c.2.mclass = .constructorM := by
    intro c hc
    have he : c = (1, accIntroMember) := List.mem_singleton.mp hc
    cases he
    rfl
  have hFamily : ∀ vs, Equiv (μ P (C P).node.a.family.ref vs)
      (role P (μ P) (famDataOf (C P).node.a) vs) := by
    intro vs
    have h := (EvalRole.rawTable_spec P AccEnv.accEnvWfT).1 0 accFamMember rfl vs
    rw [family_context] at h
    exact h
  have hArgs := EvalInstalledAttack.arguments_fit P
  have hps : TelFits (C P).M (C P).σ (C P).node.a.family.parameters ρ0
      (C P).parameters := ⟨hArgs.1, True.intro⟩
  have hmo : (C P).motive ∈ Ed (C P).M (den (C P).M (C P).σ
      (push (C P).parameters ρ0) accMotTy) := hArgs.2.1
  have hminors : TelFits (C P).M (C P).σ (C P).node.a.minorTypes
      (vcons (C P).motive (push (C P).parameters ρ0)) (C P).minors :=
    ⟨hArgs.2.2.1, True.intro⟩
  have hmajor : pempty ∈ Ed (C P).M
      (fapps ((C P).M.μ (C P).node.a.family.ref
        ((canonL (C P).node.a.family.member.arity).map (evalTotal (C P).σ)))
        ((C P).parameters ++ [])) := hArgs.2.2.2.1
  have hvs : ∀ u, u ∈ [1] → u ≤ bound (C P).rr := by
    intro u hu
    have he : u = 1 := List.mem_singleton.mp hu
    subst u
    exact Nat.le_refl 1
  have hClose := PropEvalNormalized.candidate_closed P (μ P) bound (C P) rfl
    accFamMember [(1, accIntroMember)] .empty rfl hctors rfl
    AccEnv.accMembersT (PlanPropStepAttack.boundG bound)
    (EvalCandidateStepAttack.empty_gInv P bound)
    (envCtx (.empty : EnvWfT emptyEnv)) (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ hm => by nomatch hm)
    hFamily [1] rfl hvs rfl rfl (.param 0) hmo hminors
  have hEval := PropEvalNormalized.raw_evaluates P (μ P) bound (C P) rfl
    accFamMember [(1, accIntroMember)] .empty rfl hctors rfl
    AccEnv.accMembersT (PlanPropStepAttack.boundG bound)
    (EvalCandidateStepAttack.empty_gInv P bound)
    (envCtx (.empty : EnvWfT emptyEnv)) (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ hm => by nomatch hm)
    hFamily [1] rfl hvs rfl rfl (.param 0) hmo hminors
    (envCtx AccEnv.accEnvWfT) (EvalRole.envPlan AccEnv.accEnvWfT)
    (fun _ _ => rfl) (EvalRole.rawTable_spec P AccEnv.accEnvWfT).1
  have hs := PropEvalNormalized.result_spec P (μ P) bound (C P) rfl
    accFamMember [(1, accIntroMember)] .empty rfl hctors rfl
    AccEnv.accMembersT (PlanPropStepAttack.boundG bound)
    (EvalCandidateStepAttack.empty_gInv P bound)
    (envCtx (.empty : EnvWfT emptyEnv)) (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ hm => by nomatch hm)
    hFamily [1] rfl hvs rfl rfl (.param 0) hmo hminors
    (envCtx AccEnv.accEnvWfT) (EvalRole.envPlan AccEnv.accEnvWfT)
    (fun _ _ => rfl) (EvalRole.rawTable_spec P AccEnv.accEnvWfT).1
    [] pempty hps True.intro hmajor
  have ht : result P ∈ Ed (C P).M (fapp (C P).motive pempty) := hs.2.2
  have htOld : result P ∈ Ed (mkM P (installed P))
      (fapp (motive P (installed P)) pempty) := by
    change result P ∈ Ed (mkM P (μ P))
      (fapp (motive P (installed P)) pempty) at ht
    rw [ed_table P (μ P) (installed P)] at ht
    exact ht
  have hd : result P ∈ domain :=
    mem_congr_right (ed_tyv (mkM P (installed P)) PiRawIHAnyAttack.domain_dich)
      (mem_congr_right (ed_congr (mkM P (installed P))
        (motive_empty P (installed P) (installed_family P))) htOld)
  refine ⟨EvalEndpointContract.components P, EvalPlanNormalCompareAttack.component_witness P,
    hClose.1, hClose.2, hEval, hs.2.1, hs.1, ht, hd, ?_⟩
  intro he
  exact dataVal_ne_pempty _ _ ((mem_singleton.mp hd).symm.trans he)

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropEvalNormalAttack

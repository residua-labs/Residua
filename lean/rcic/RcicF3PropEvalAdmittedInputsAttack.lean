import rcic.RcicF3PropEvalAdmittedInputs
import rcic.RcicF3PropEvalRawFamilyAttack
import rcic.RcicF3PropEvalMotiveGuardAttack
import rcic.RcicF3RawFamilyCandidatePrefixAttack
import rcic.RcicF3RawFamilyGroup
import rcic.RcicF3PropEvalCandidateLeafAttack

/-!
# The complete candidate-field evaluation producer at actual AccR

This fixture invokes eval_of_candidate_fields with the real admitted node,
the actual stored typed motive/minor list, and the original raw/candidate
field tuple. Every premise is produced. Candidate-prefix soundness uses
admissibility alone, and the original field is inhabited directly because
its proposition parameter is empty; no earlier evaluation-existence theorem
is used to construct the new evaluation. The result lies in the nonempty
data motive at its extra universe slot. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PropEvalAdmittedInputsAttack
open Rcic.Declarative PiIndex RawFamily PlanPropEndAttack
open PropEvalUniqueAttack (ctx)
open PropEvalCandidateAttack (X)

def bound : Nat → Nat := fun _ => 1

noncomputable def candidateTable (P : Premises4) : Nat → List Nat → PSet.{4} :=
  table P (installed P) fd (X P)

/-- This prefix is produced from candidate admissibility, without candidate
closure or an evaluation-existence input. -/
theorem candidate_prefix (P : Premises4) :
    EnvSound (mkM P (candidateTable P)) (ctx P).σ bound accFamOnly 0 := by
  apply candidate_prefix_envSound P bound (.empty : EnvWfT emptyEnv)
    (PlanPropStepAttack.empty_gInv P bound) (installed P)
    (envCtx (.empty : EnvWfT emptyEnv)) (PlanRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ hm => by nomatch hm) (fun _ _ hm => by nomatch hm)
    fd (X P) (PropEvalCandidateAttack.candidate_admissible P)
    PropEvalCandidateLeafAttack.parameters_free accFamMember rfl (fun _ => rfl) rfl rfl rfl rfl (ctx P).σ 0

theorem prefix_bodies (P : Premises4) : BodiesOK accFamOnly (ctx P).σ bound := by
  intro r m b ls hm hb
  change (if r = 0 then some accFamMember else none) = some m at hm
  by_cases hr : r = 0
  · subst r
    simp only [ite_true, Option.some.injEq] at hm
    subst m
    cases hb
  · simp only [hr, ite_false] at hm
    cases hm

theorem reader_closed : EnvClosed PlanPropStepAttack.pNode.E0 := by
  intro r m hm
  have ht := typeFacts_of_envWfT AccEnv.accEnvWfT r m
    (PlanPropStepAttack.pNode.sub r m
      (members_extend_preserved PlanPropStepAttack.pNode.fresh r m hm))
  exact ⟨ht.1, fun b hb => (ht.2.2 b hb).1⟩

/-- The actual bounded field typing supplies the original field's instances. -/
theorem instances (P : Premises4) :
    ∀ A ∈ [accField], InstOK accFamOnly (ctx P).σ bound A := by
  intro A hA
  have he : A = accField := List.mem_singleton.mp hA
  subst A
  obtain ⟨l, _, d, hd⟩ := PropEvalTypedAttack.typed_fields P bound
    ⟨0, by change 0 < 1; decide⟩ ⟨0, by change 0 < 1; decide⟩
  exact instOK_of_lokt (ctx P).σ 4 bound d hd

theorem candidate_fields (P : Premises4) :
    TelFits (mkM P (candidateTable P)) (ctx P).σ [accField]
      (push [parameter] ρ0) [pempty] :=
  PropEvalAttack.original_field_fit P (candidateTable P)

def Witness (P : Premises4) : Prop :=
  PropEvalRawFamilyAttack.Witness P ∧
  BoundG bound AccEnv.accEnvWfT ∧
  EnvSound (mkM P (candidateTable P)) (ctx P).σ bound accFamOnly 0 ∧
  TelFits (mkM P (candidateTable P)) (ctx P).σ [accField]
    (push [parameter] ρ0) [pempty] ∧
  ∃ z, PropEval.Eval (ctx P) (key [parameter]) z ∧
    z ∈ PropEval.childCarrier (ctx P) (.param 0) (key [parameter]) ∧
    z ∈ domain ∧ ¬ Equiv z pempty

/-- Exercise the generic constructor-input producer inside its complete witness. -/
theorem component_witness (P : Premises4) : Witness P := by
  have produced : ∃ z, PropEval.Eval (ctx P) (key [parameter]) z := by
    obtain ⟨_, endVal, hEnd, hFamily, hProp, _⟩ :=
      PropEvalRawFamilyAttack.component_witness P
    have hfunctional : ∀ i z z', PropEval.Eval (ctx P) i z →
        PropEval.Eval (ctx P) i z' → Equiv z z' := by
      intro i z z' he he'
      exact PropEval.Eval.functional_of_typed_proof_fields (ctx P) P (installed P)
        bound accFamOnly 0 rfl rfl rfl (PropEvalTypedAttack.prefix_sound P bound)
        (PropEvalTypedAttack.typed_fields P bound) he he'
    have hminors : TelFits (ctx P).M (ctx P).σ (ctx P).node.a.minorTypes
        (vcons (ctx P).motive (push (ctx P).parameters ρ0)) (ctx P).minors := by
      exact ⟨minor_mem P (installed P) (installed_family P) (installed_constructor P), True.intro⟩
    exact PropEval.eval_of_candidate_fields P (installed P) (ctx P) rfl
      (RawFamilyPropAttack.acc_closed P (installed P)).1 PropEvalCandidateLeafAttack.parameters_free
      accFamMember [(1, accIntroMember)] AccEnv.accMembersT bound
      (PropEvalTypedAttack.prefix_sound P bound) (candidate_prefix P)
      (prefix_bodies P) reader_closed (.param 0) rfl endVal hEnd hFamily
      (motive_mem P (installed P)) hProp hfunctional
      (PropEvalAttack.parameters_fit P (installed P)) hminors
      ⟨0, by change 0 < 1; decide⟩ [pempty] (instances P)
      (PropEvalAttack.original_field_fit P (installed P)) (candidate_fields P)
  obtain ⟨z, he⟩ := produced
  have ht := PropEvalAttack.eval_typed P he
  refine ⟨PropEvalRawFamilyAttack.component_witness P,
    PlanPropStepAttack.boundG bound, candidate_prefix P, candidate_fields P,
    z, he, PropEvalMotiveGuardAttack.guarded P he, ht, ?_⟩
  intro h
  exact dataVal_ne_pempty _ _ ((mem_singleton.mp ht).symm.trans h)

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropEvalAdmittedInputsAttack

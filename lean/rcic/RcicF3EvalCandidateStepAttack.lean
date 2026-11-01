import rcic.RcicF3EvalCandidateStep
import rcic.RcicF3PropEvalCandidateStepAttack

/-!
# Composition of the candidate producer with the new predecessor invariant

This fixture instantiates the public EvalCandidateStep producer at the
actual AccR group, deriving candidate closure and evaluation existence
through the new EvalRole.GInv. All canonical plan reads are produced
internally, as is raw-frame admissibility on this Prop/anySort face.
The AccR parameter has the explicitly empty recursive child
domain; inhabited depth-three fields and height-omega W remain separate
suite conjuncts. No universal StepAG is asserted. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.EvalCandidateStepAttack
open Rcic.Declarative PiIndex RawFamily PlanPropEndAttack
open PropEvalUniqueAttack (ctx)
open PropEvalCandidateAttack (X)
open PropEvalAdmittedInputsAttack (bound)

theorem empty_gInv (P : Premises4) (K : Nat → Nat) :
    EvalRole.GInv role P K (.empty : EnvWfT emptyEnv) := by
  intro ctx hc plans hp μ hF
  constructor
  · intro r m hm
    nomatch hm
  · intro Efin hsub r m hm
    nomatch hm

/-- Invoke the public producer, including its predecessor-invariant composition. -/
theorem produced_step (P : Premises4) :
    ∀ vs i z, CtorAt P (installed P) fd (X P) vs i z →
      PropEvalCandidate.EvalPredicate (ctx P) vs i z := by
  have hminors : TelFits (ctx P).M (ctx P).σ (ctx P).node.a.minorTypes
      (vcons (ctx P).motive (push (ctx P).parameters ρ0)) (ctx P).minors := by
    exact ⟨minor_mem P (installed P) (installed_family P) (installed_constructor P),
      True.intro⟩
  exact EvalCandidateStep.constructor_step P (installed P) bound (ctx P) rfl
    accFamMember [(1, accIntroMember)] .empty rfl
    (fun c hc => by cases List.mem_singleton.mp hc; rfl)
    rfl AccEnv.accMembersT (PlanPropStepAttack.boundG bound)
    (empty_gInv P bound)
    (envCtx (.empty : EnvWfT emptyEnv)) (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ hm => by nomatch hm)
    (PropEvalRawFamilyAttack.installed_family_all P)
    [1] rfl
    (fun u hu => by
      have hu1 : u = 1 := List.mem_singleton.mp hu
      subst u
      exact Nat.le_refl 1)
    rfl rfl (.param 0) (motive_mem P (installed P)) hminors

def Witness (P : Premises4) : Prop :=
  EvalRole.GInv role P bound (.empty : EnvWfT emptyEnv) ∧
  (∀ vs i z, CtorAt P (installed P) fd (X P) vs i z →
    PropEvalCandidate.EvalPredicate (ctx P) vs i z) ∧
  Closed P (installed P) fd (X P) ∧
  pempty ∈ X P [] (key [parameter]) ∧
  ∃ z, PropEval.Eval (ctx P) (key [parameter]) z ∧
    z ∈ PropEval.childCarrier (ctx P) (.param 0) (key [parameter]) ∧
    z ∈ domain ∧ ¬ Equiv z pempty

/-- The checked chain uses the newly produced step, raw closure and leastness. -/
theorem component_witness (P : Premises4) : Witness P := by
  have hRaw := EvalCandidateStep.raw_admissible P (installed P) (ctx P) rfl rfl
  have hClosed := PropEvalCandidate.closed_of_constructor_step P (installed P) (ctx P)
    hRaw (RawFamilyPropAttack.acc_closed P (installed P)).2
    (RawFamilyPropAttack.acc_mono P (installed P)) (produced_step P)
  have hMajor : pempty ∈ X P [] (key [parameter]) :=
    frame_least P (installed P) fd (X P)
      (PropEvalCandidate.admissible P (installed P) (ctx P) hRaw)
      hClosed [] (key [parameter]) pempty (PropEvalCandidateStepAttack.raw_major P)
  obtain ⟨z, he⟩ := PropEvalCandidate.exists_of_mem P (installed P) (ctx P)
    [] (key [parameter]) pempty hMajor (fun u hu => by change u < 0 at hu; omega) rfl
  have ht := PropEvalAttack.eval_typed P he
  refine ⟨empty_gInv P bound, produced_step P, hClosed, hMajor, z, he,
    PropEvalMotiveGuardAttack.guarded P he, ht, ?_⟩
  intro h
  exact dataVal_ne_pempty _ _ ((mem_singleton.mp ht).symm.trans h)

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.EvalCandidateStepAttack

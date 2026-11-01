import rcic.RcicF3PropEvalCandidateStep
import rcic.RcicF3PropEvalAdmittedInputsAttack
import rcic.RcicF3PropEvalRawFamilyAttack

/-!
# The public candidate constructor producer, closure and leastness at AccR

The public constructor_step is instantiated with the real admitted AccR
group, its predecessor invariant, bound, raw family equation and typed
motive/minors. Its produced step composes with the independently proved
AccR raw-frame closure and constructor monotonicity. Leastness then gives
actual candidate membership, from which the evaluation is extracted.

No previously inhabited evaluation or previously closed evaluation candidate
is used to supply this result. The final result is typed in the guarded
motive at its extra universe slot and lies in the nonempty data domain.
This is the AccR fixture, not an imported Acc-on-Nat.lt environment.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalCandidateStepAttack
open Rcic.Declarative PiIndex RawFamily PlanPropEndAttack
open PropEvalUniqueAttack (ctx)
open PropEvalCandidateAttack (X)
open PropEvalAdmittedInputsAttack (bound)

/-- Invoke the public producer, including its predecessor-invariant composition. -/
theorem produced_step (P : Premises4) :
    ∀ vs i z, CtorAt P (installed P) fd (X P) vs i z →
      PropEvalCandidate.EvalPredicate (ctx P) vs i z := by
  have hminors : TelFits (ctx P).M (ctx P).σ (ctx P).node.a.minorTypes
      (vcons (ctx P).motive (push (ctx P).parameters ρ0)) (ctx P).minors := by
    exact ⟨minor_mem P (installed P) (installed_family P) (installed_constructor P),
      True.intro⟩
  exact PropEvalCandidate.constructor_step P (installed P) bound (ctx P) rfl
    accFamMember [(1, accIntroMember)] .empty rfl
    (fun c hc => by cases List.mem_singleton.mp hc; rfl)
    rfl AccEnv.accMembersT (PlanPropStepAttack.boundG bound)
    (PlanPropStepAttack.empty_gInv P bound)
    (envCtx (.empty : EnvWfT emptyEnv)) (PlanRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ hm => by nomatch hm) (fun _ _ hm => by nomatch hm)
    (PropEvalRawFamilyAttack.installed_family_all P)
    (RawFamilyPropAttack.acc_closed P (installed P)).1
    [1] rfl
    (fun u hu => by
      have hu1 : u = 1 := List.mem_singleton.mp hu
      subst u
      exact Nat.le_refl 1)
    rfl rfl (.param 0) (motive_mem P (installed P)) hminors

/-- The all-instance closure composition uses the produced public step. -/
theorem produced_closed (P : Premises4) :
    Closed P (installed P) fd (X P) :=
  PropEvalCandidate.closed_of_constructor_step P (installed P) (ctx P)
    (RawFamilyPropAttack.acc_closed P (installed P)).1
    (RawFamilyPropAttack.acc_closed P (installed P)).2
    (RawFamilyPropAttack.acc_mono P (installed P)) (produced_step P)

theorem raw_major (P : Premises4) :
    pempty ∈ frame P (installed P) fd [] (key [parameter]) :=
  RawFamilyPropAttack.empty_parameter_inhabited P (installed P) []

/-- Leastness is applied to the newly produced closed candidate. -/
theorem candidate_major (P : Premises4) :
    pempty ∈ X P [] (key [parameter]) :=
  frame_least P (installed P) fd (X P)
    (PropEvalCandidate.admissible P (installed P) (ctx P)
      (RawFamilyPropAttack.acc_closed P (installed P)).1)
    (produced_closed P) [] (key [parameter]) pempty (raw_major P)

/-- Evaluation existence comes from candidate membership obtained by leastness. -/
theorem produced (P : Premises4) :
    ∃ z, PropEval.Eval (ctx P) (key [parameter]) z :=
  PropEvalCandidate.exists_of_mem P (installed P) (ctx P) [] (key [parameter])
    pempty (candidate_major P) (fun u hu => by change u < 0 at hu; omega) rfl

def Witness (P : Premises4) : Prop :=
  BoundG bound AccEnv.accEnvWfT ∧ (ctx P).σ 0 = 1 ∧
  (∀ vs i z, CtorAt P (installed P) fd (X P) vs i z →
    PropEvalCandidate.EvalPredicate (ctx P) vs i z) ∧
  Admissible fd (frame P (installed P) fd) ∧
  Closed P (installed P) fd (frame P (installed P) fd) ∧
  ConstructorMono P (installed P) fd ∧
  Admissible fd (X P) ∧ Closed P (installed P) fd (X P) ∧
  pempty ∈ frame P (installed P) fd [] (key [parameter]) ∧
  pempty ∈ X P [] (key [parameter]) ∧
  ∃ z, PropEval.Eval (ctx P) (key [parameter]) z ∧
    z ∈ PropEval.childCarrier (ctx P) (.param 0) (key [parameter]) ∧
    z ∈ domain ∧ ¬ Equiv z pempty

/-- Every literal conjunct is produced, including the two all-instance closure inputs. -/
theorem component_witness (P : Premises4) : Witness P := by
  obtain ⟨z, he⟩ := produced P
  have ht := PropEvalAttack.eval_typed P he
  refine ⟨PlanPropStepAttack.boundG bound, rfl, produced_step P,
    (RawFamilyPropAttack.acc_closed P (installed P)).1,
    (RawFamilyPropAttack.acc_closed P (installed P)).2,
    RawFamilyPropAttack.acc_mono P (installed P),
    PropEvalCandidate.admissible P (installed P) (ctx P)
      (RawFamilyPropAttack.acc_closed P (installed P)).1,
    produced_closed P, raw_major P, candidate_major P, z, he,
    PropEvalMotiveGuardAttack.guarded P he, ht, ?_⟩
  intro h
  exact dataVal_ne_pempty _ _ ((mem_singleton.mp ht).symm.trans h)

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropEvalCandidateStepAttack

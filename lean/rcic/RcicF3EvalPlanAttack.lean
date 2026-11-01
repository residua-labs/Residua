import rcic.RcicF3EvalPlan
import rcic.RcicF3CandidateScopeAttack

/-!
# Concrete normalized plan data at hidden fields and the actual AccR node

The hidden cases inspect the data returned by the new Type-valued cache
producer. They include beta, delta, zeta, depth three, relabelled families,
and the complete dependent index. Those alias environments are reader
fixtures only. The AccR component uses the actual admitted typed node and
its actual stored minor, including the recursor's extra universe slot.
This is a plan-data witness, not universal recursor soundness.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.EvalPlanAttack
open Rcic.Declarative EvalPlan
open PiRawIHAttack (field beta delta zeta ds args)

/-- The actual produced data agrees with the independently pinned full read. -/
theorem hidden_cache : ∀ (f : Nat) (hf : f ∈ [1, 2, 987]),
    ∀ (A : Expr Nat) (hA : A ∈ [field f, beta f, delta f, zeta f]),
      ∃ r : Recursive (CandidateScopeAttack.extended f) 32 f 0 0 1 0 A 3,
        of_admitted (np := 0) (prior := 0)
          (CandidateScopeAttack.hidden_scans f hf A hA).1 = Field.recursive r ∧
        r.domains = ds f ∧ r.arguments = args := by
  intro f hf A hA
  cases hp : of_admitted (np := 0) (prior := 0)
      (CandidateScopeAttack.hidden_scans f hf A hA).1 with
  | recursive r =>
      refine ⟨r, rfl, ?_, ?_⟩
      · exact congrArg Prod.fst (Option.some.inj
          (r.read.symm.trans (CandidateScopeAttack.hidden_reads f hf A hA)))
      · exact (foldApps_const_inj (congrArg Prod.snd (Option.some.inj
          (r.read.symm.trans (CandidateScopeAttack.hidden_reads f hf A hA))))).2

noncomputable def accPlan : Plan := ofNode PlanPropStepAttack.pNode

noncomputable def accConstructor :
    Constructor PlanPropStepAttack.pNode ⟨0, by decide⟩ :=
  constructorOfNode PlanPropStepAttack.pNode ⟨0, by decide⟩

/-- The cache points to the literal stored minor of the admitted AccR group. -/
theorem acc_minor : accConstructor.minor = accMinorTy := by
  have hstored : PlanPropStepAttack.pNode.a.minorTypes[0]? = some accMinorTy := rfl
  exact Option.some.inj (accConstructor.minor_stored.symm.trans hstored)

def Witness : Prop :=
  (∀ f ∈ [1, 2, 987],
    ∀ A ∈ [field f, beta f, delta f, zeta f],
      ∃ r : Recursive (CandidateScopeAttack.extended f) 32 f 0 0 1 0 A 3,
        r.domains = ds f ∧ r.arguments = args) ∧
  accPlan.f = 0 ∧ accPlan.rr = 2 ∧
  accPlan.node.a.family.member.arity = 0 ∧ accPlan.rm.arity = 1 ∧
  accConstructor.minor = accMinorTy ∧
  (∃ minorFuel : Nat,
    fieldShapesFuel PlanPropStepAttack.pNode.E0 minorFuel 0 0 1 0 1
      (PlanPropStepAttack.pNode.a.constructorViews ⟨0, by decide⟩).fields =
        some accConstructor.shapes ∧
      derivedMinor PlanPropStepAttack.pNode.a ⟨0, by decide⟩ minorFuel
        accConstructor.shapes = some accConstructor.minor)

/-- This witness composes the actual cache producer and actual stored-minor
admission. It does not substitute an independent hand-written descriptor. -/
theorem component_witness : Witness := by
  refine ⟨?_, rfl, rfl, rfl, rfl, acc_minor, accConstructor.minor_derivation⟩
  intro f hf A hA
  obtain ⟨r, _, hd, ha⟩ := hidden_cache f hf A hA
  exact ⟨r, hd, ha⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness → (Premises4 → False)) :=
  fun h => h component_witness P

end Rcic.F3.PSet.EvalPlanAttack

import rcic.RcicF3PointwiseCheckedApex
import rcic.RcicF3PointwiseFieldMasksAttack
import rcic.RcicF3PointwiseCheckedMigrationAttack

/-!
# Concrete composition of the universal checked producer and non-vacuity

The new universal local-candidate producer is instantiated at the admitted
W group. The new checked admission fold independently produces its actual
installed-table invariant from the whole-environment checks and bounds.
The prior W witness retains its height-omega value and typed legacy leaf
iota, with the other constructor still higher-order.

Overall tier non-vacuity uses the separate actual distinguished-False
environment: False at slots 0/1 and the Prop definition at slot 2. Every
literal environment antecedent of TierF3WDChecked is exhibited, and two
inequivalent values inhabit the SAME installed slot-2 fibre; only one has
a proof. The actual universal checked apex is invoked at this environment.
The AccR component remains its own admitted fixture, with its explicitly
empty selected child domain. No imported Acc-on-Nat.lt or combined W/False
environment is claimed. All conjuncts share one Premises4.

This is a source composition, pending native and RCC verification.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseCheckedApexAttack
open Rcic.Declarative RawFamily

/-- This is a call to the UNIVERSAL checked producer on the actual W
group, with its original existential PendA and selected D acceptance. -/
theorem w_local_candidates (P : Premises4) (k : Nat) :
    PointwiseDataGroup.LocalCandidatesAt P (fun _ => k) natEnvUWfT rfl
      PendAWGroup.ctorClasses rfl PendAW.membersT :=
  PointwiseLocalProducer.localCandidatesChecked P (fun _ => k)
    natEnvUWfT rfl PendAWGroup.ctorClasses rfl PendAW.membersT
    NormDataRecMemAttack.type_family ⟨PendAW.pNode, PendAW.pendA⟩
    (NormDataGroupAttack.group_check k)

/-- The actual full W environment now uses the generic checked admission
fold. No fixture-specific local frame or W invariant is supplied. -/
theorem w_invariant (P : Premises4) (k : Nat) :
    PointwiseRole.GInv P (fun _ => k) PendAWGroup.wft :=
  PointwiseCheckedApex.invariant_of_checks P (fun _ => k) PendAWGroup.wft
    NormPendAWChecked.w_check (NormPendAWChecked.d_check k)
    (PendAWGroup.boundG _) (PendAWGroup.boundDG k) NormPendAWChecked.axiom_free

/-- All original checked-F3 environment antecedents, with an actual
semantic distinction in one entry of that environment's installed table. -/
def Nonvacuity (P : Premises4) (K : Nat → Nat) : Prop :=
  ∃ (E : ResolvedEnv) (hW : EnvWfT E),
    Rcic.F3.StepWApex.envCheck hW = true ∧
    Rcic.F3.StepWDApex.envCheck K hW = true ∧
    BoundG K hW ∧ BoundDG K hW ∧ AxiomFreeEnv' E ∧
    E.members 0 = some falseFamMember ∧
    E.members 1 = some falseRecMemberU ∧
    (∀ σ n, EnvSound (mkM P (PointwiseRole.table P hW)) σ K E n) ∧
    (∃ (r : Nat) (a b : PSet.{4}),
      a ∈ Ed (mkM P (PointwiseRole.table P hW)) (PointwiseRole.table P hW r []) ∧
      b ∈ Ed (mkM P (PointwiseRole.table P hW)) (PointwiseRole.table P hW r []) ∧
      (¬ Equiv a b) ∧
      pempty ∈ Ed (mkM P (PointwiseRole.table P hW)) b ∧
      pempty ∉ Ed (mkM P (PointwiseRole.table P hW)) a) ∧
    (∀ (n : Nat) (e : Expr Nat) (D : HasTyT E n [] e (.const 0 [])),
      LevelsBelow 4 K D → False)

/-- The existential environment is the actual admitted False prefix plus
the Prop definition. Soundness and consistency call the new universal
checked producer; the two values come from this same final table. -/
theorem nonvacuity (P : Premises4) (K : Nat → Nat) : Nonvacuity P K := by
  refine ⟨NormFalseNonvacuity.env, NormFalseNonvacuity.wf,
    NormFalseNonvacuity.w_check, NormFalseNonvacuity.d_check K,
    NormFalseNonvacuity.boundG K, NormFalseNonvacuity.boundDG K,
    NormFalseNonvacuity.axiom_free, NormFalseNonvacuity.false_present,
    NormFalseNonvacuity.falseRec_present, ?_, ?_, ?_⟩
  · exact PointwiseCheckedApex.envSound_of_checks P K NormFalseNonvacuity.wf
      NormFalseNonvacuity.w_check (NormFalseNonvacuity.d_check K)
      (NormFalseNonvacuity.boundG K) (NormFalseNonvacuity.boundDG K)
      NormFalseNonvacuity.axiom_free
  · exact ⟨2, NormFalseNonvacuity.falseValue, NormFalseNonvacuity.trueValue,
      PointwiseFalseNonvacuity.false_mem P, PointwiseFalseNonvacuity.true_mem P,
      PointwiseFalseNonvacuity.distinct P, PointwiseFalseNonvacuity.true_inhabited P,
      PointwiseFalseNonvacuity.false_empty P⟩
  · exact PointwiseCheckedApex.kernelSoundnessTierWDChecked.2 P K
      NormFalseNonvacuity.env NormFalseNonvacuity.wf
      NormFalseNonvacuity.w_check (NormFalseNonvacuity.d_check K)
      (NormFalseNonvacuity.boundG K) (NormFalseNonvacuity.boundDG K)
      NormFalseNonvacuity.axiom_free NormFalseNonvacuity.false_present
      NormFalseNonvacuity.falseRec_present

def Witness (P : Premises4) : Prop :=
  PointwiseFieldMasksAttack.Witness P ∧
  PointwiseCheckedMigrationAttack.Witness P ∧
  (∀ k, PointwiseDataGroup.LocalCandidatesAt P (fun _ => k) natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT ∧
    PointwiseRole.GInv P (fun _ => k) PendAWGroup.wft) ∧
  (∀ K, Nonvacuity P K)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨PointwiseFieldMasksAttack.component_witness P,
    PointwiseCheckedMigrationAttack.component_witness P,
    (fun k => ⟨w_local_candidates P k, w_invariant P k⟩), nonvacuity P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PointwiseCheckedApexAttack

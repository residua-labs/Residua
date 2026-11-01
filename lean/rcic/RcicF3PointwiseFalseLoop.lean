import rcic.RcicF3PointwiseRemainingTier
import rcic.RcicF3OriginalTierLoopCoverage

/-!
# The new pointwise fold at the original-domain D-refusal witness

The exact False-prefixed Loop environment has two admitted Prop/anySort
groups. Their actual selected plans satisfy `AllPropAnySort`, so the new
fold produces its pointwise invariant and environment soundness under both
original bounds. The final consistency consumer uses this same produced
table. No ClassG semantic theorem or assumed soundness is used.

The older whole-environment D check still refuses at every K. This is a
concrete consumer of the closed Prop/anySort branch, not closure of the
remaining DATA or PropOnly producer obligations. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwiseFalseLoop
open Rcic.Declarative

abbrev FalseNode := RecNode emptyEnv falseEnvU 0 1 falseRecMemberU

/-- The actual stored family identifies every node for the False block. -/
theorem false_family_member (node : FalseNode) :
    node.a.family.member = falseFamMember :=
  Option.some.inj ((node_fam_member node).symm.trans rfl)

/-- This uses the stored type, so it applies to the actual selected plan. -/
theorem false_family (node : FalseNode) :
    node.a.family.parameters = [] ∧ node.a.family.indices = [] ∧
      node.a.family.resultLevel = .zero := by
  have hst := node.a.family.storedType
  rw [false_family_member node] at hst
  obtain ⟨h1, h2⟩ := policyPi_split_eq [] _ _ _
    (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) hst
  have h3 := List.append_eq_nil.mp h1.symm
  injection h2 with h4
  exact ⟨h3.1, h3.2, h4.symm⟩

/-- The stored recursor has one universe argument; propOnly has none. -/
theorem false_policy (node : FalseNode) : node.a.policy = .anySort := by
  cases hp : node.a.policy with
  | anySort => rfl
  | propOnly =>
      have ha := node.a.recursorArity
      rw [false_family_member node, hp] at ha
      change 1 = 0 at ha
      exact False.elim (Nat.noConfusion ha)

theorem false_allPropAnySort :
    PointwiseRemainingTier.AllPropAnySort falseEnvUWfT := by
  refine ⟨True.intro, ?_, ?_⟩
  · intro σ
    rw [(false_family _).2.2]
    rfl
  · exact false_policy _

/-- Both group occurrences in the same refusal witness are produced. -/
theorem allPropAnySort :
    PointwiseRemainingTier.AllPropAnySort FalseLoopCoverage.loopWfT := by
  refine ⟨false_allPropAnySort, ?_, ?_⟩
  · intro σ
    rw [(FalseLoopCoverage.loop_family _).2.2]
    rfl
  · exact FalseLoopCoverage.policy_any _

theorem invariant (P : Premises4) (K : Nat → Nat) :
    PointwiseRole.GInv P K FalseLoopCoverage.loopWfT :=
  PointwiseRemainingTier.invariant_of_allPropAnySort P K FalseLoopCoverage.loopWfT
    allPropAnySort (FalseLoopCoverage.boundG K) (FalseLoopCoverage.boundDG K)
    FalseLoopCoverage.axiom_free

/-- Soundness of the actual new pointwise table at this exact environment. -/
theorem env_sound (P : Premises4) (K σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (PointwiseRole.table P FalseLoopCoverage.loopWfT)) σ K
      FalseLoopCoverage.pinLoopEnvT n :=
  PointwiseRemainingTier.envSound_of_allPropAnySort P K FalseLoopCoverage.loopWfT
    allPropAnySort (FalseLoopCoverage.boundG K) (FalseLoopCoverage.boundDG K)
    FalseLoopCoverage.axiom_free σ n

/-- The original conclusion, proved by the new fold and final consumer. -/
theorem consistent (P : Premises4) (K : Nat → Nat)
    (n : Nat) (e : Expr Nat)
    (D : HasTyT FalseLoopCoverage.pinLoopEnvT n [] e (.const 0 []))
    (hl : LevelsBelow 4 K D) : False :=
  PointwiseRemainingTier.false_of_allPropAnySort P K FalseLoopCoverage.loopWfT
    allPropAnySort (FalseLoopCoverage.boundG K) (FalseLoopCoverage.boundDG K)
    FalseLoopCoverage.axiom_free FalseLoopCoverage.falseRec_present n e D hl

/-- All original environment antecedents and the produced pointwise
invariant hold together where the old D check refuses, at the same K. -/
theorem produced_original_domain_refusal (P : Premises4) (K : Nat → Nat) :
    BoundG K FalseLoopCoverage.loopWfT ∧ BoundDG K FalseLoopCoverage.loopWfT ∧
      AxiomFreeEnv' FalseLoopCoverage.pinLoopEnvT ∧
      FalseLoopCoverage.pinLoopEnvT.members 0 = some falseFamMember ∧
      FalseLoopCoverage.pinLoopEnvT.members 1 = some falseRecMemberU ∧
      PointwiseRole.GInv P K FalseLoopCoverage.loopWfT ∧
      Rcic.F3.StepWDApex.envCheck K FalseLoopCoverage.loopWfT = false :=
  ⟨FalseLoopCoverage.boundG K, FalseLoopCoverage.boundDG K,
    FalseLoopCoverage.axiom_free, FalseLoopCoverage.false_present,
    FalseLoopCoverage.falseRec_present, invariant P K, FalseLoopCoverage.d_check_false K⟩

end Rcic.F3.PSet.PointwiseFalseLoop

#print axioms Rcic.F3.PSet.PointwiseFalseLoop.allPropAnySort
#print axioms Rcic.F3.PSet.PointwiseFalseLoop.invariant
#print axioms Rcic.F3.PSet.PointwiseFalseLoop.env_sound
#print axioms Rcic.F3.PSet.PointwiseFalseLoop.consistent
#print axioms Rcic.F3.PSet.PointwiseFalseLoop.produced_original_domain_refusal

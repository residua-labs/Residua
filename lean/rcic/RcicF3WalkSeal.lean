import rcic.RcicF3Cover
import rcic.RcicF3WalkWitness

/-!
# F3 coverage: the PendW witness is outside the proved class

For the admitted group `pwEnvWfT` (`RcicF3WalkWitness`) every recursor node has a family view with
a parameter count different from the constructor's own admission view: `WalkClass` fails, so
`ClassG pwEnvWfT` is false, while the group conditions that `GroupClass` states about fields hold.
The group is therefore covered only by the named pending class W (`nodeCovered`).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

theorem motive_ne_wMinor {E : ResolvedEnv} (fam : PolicyFamilyView E) (policy : EliminationPolicy) :
    policyMotiveType fam policy ≠ pwMinor := by
  intro h
  unfold policyMotiveType at h
  cases hi : fam.indices with
  | nil =>
      rw [hi] at h
      simp only [policyPi] at h
      injection h with _ h2
      exact Expr.noConfusion h2
  | cons I rest =>
      rw [hi] at h
      simp only [policyPi] at h
      injection h with _ h2
      cases rest with
      | nil =>
          simp only [policyPi] at h2
          exact Expr.noConfusion h2
      | cons J rest' =>
          simp only [policyPi] at h2
          exact Expr.noConfusion h2

/-- Every recursor node of the witness has a family view with a parameter count other than 1. -/
theorem pwNode_params_ne_one (node : RecNode emptyEnv pwEnv 0 2 pwRec) :
    node.a.family.parameters.length ≠ 1 := by
  intro h1
  obtain ⟨p0, hp⟩ := List.length_eq_one.mp h1
  have hty := node.a.recursorType
  rw [policyRecursorType_eq, hp] at hty
  have hty' : pwRecType = Expr.pi p0 (Expr.pi (policyMotiveType node.a.family node.a.policy) _) := hty
  unfold pwRecType at hty'
  injection hty' with h1' h2'
  injection h2' with h3' _
  exact motive_ne_wMinor node.a.family node.a.policy h3'.symm

/-- **PendW at the witness**: for every recursor node, the constructors' admission views disagree
with the recursor's family view. -/
theorem pwEnvWfT_pendW (node : RecNode emptyEnv pwEnv 0 2 pwRec) : PendW pwMembersT node := by
  intro hW
  exact pwNode_params_ne_one node hW.2.1.symm

/-- The witness derivation is not in `ClassG`. -/
theorem pwEnvWfT_not_classG : ¬ ClassG pwEnvWfT := by
  intro hC
  obtain ⟨node, _⟩ := group_node (E := emptyEnv) (f := 0) (rr := 2) (fm := pwV) (rm := pwRec)
    (ctors := [(1, pwMk)]) .empty rfl (fun c hc => by simp at hc; subst hc; rfl) rfl pwMembersT
  exact pwEnvWfT_pendW node (hC.2.2 node)

end PSet

end Rcic.F3

#print axioms Rcic.F3.PSet.pwEnvWfT_pendW
#print axioms Rcic.F3.PSet.pwEnvWfT_not_classG

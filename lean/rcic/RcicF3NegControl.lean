import rcic.RcicF3ClassFixtures
import rcic.RcicF3Target

/-!
# F3 negative control: the axiom-freeness hypothesis is what can fail

`axFalseEnv` is the admitted empty-type environment (`falseEnvU`) extended by
an axiom `ax : False` at reference 2. It is admitted (`axFalseEnvWfT`), has the
empty type at 0 and its recursor at 1, and has a closed term of the type at 0
(`axFalseProof`, the constant `ax`), whose derivation respects every level
bound. So:

- `axFalseEnv_control`: every hypothesis of `RcicConsistentEmpty` except
  `AxiomFreeEnv'` holds there, and its conclusion fails;
- `rcicConsistentEmpty_without_axiomFree_false`: the target with the
  axiom-freeness hypothesis dropped is false;
- `axFalseEnv_not_classG`: the class of `consistent4_G` excludes it, through
  its axiom step and nothing else.

Hence `RcicConsistentEmpty` and `consistent4_G` are not vacuous: their
conclusion is false at an admitted environment that differs from an
environment in their class only by one axiom.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-- The axiom `ax : False`. -/
def axFalseMember : CheckedMember := ⟨.axiomM, 0, .const 0 [], none⟩

/-- The empty-type environment with the axiom `ax : False` at reference 2. -/
def axFalseEnv : ResolvedEnv := extendEnv falseEnvU 2 axFalseMember

def axFalseEnvWfT : EnvWfT axFalseEnv :=
  .axiom falseEnvU 2 (.const 0 []) .zero falseEnvUWfT rfl (.const [] 0 [] falseFamMember rfl rfl rfl)
    (fun _ => rfl) rfl

/-- The closed term `ax` of the type at 0. -/
def axFalseProof : HasTyT axFalseEnv 0 [] (.const 2 []) (.const 0 []) :=
  .const [] 2 [] axFalseMember rfl rfl rfl

/-- **Negative control.** Every hypothesis of `RcicConsistentEmpty` other than
axiom-freeness holds at `axFalseEnv`, axiom-freeness fails, and so does the
conclusion: there is a closed term of the type at 0, by a derivation within
every level bound. -/
theorem axFalseEnv_control :
    Nonempty (EnvWfT axFalseEnv) ∧ axFalseEnv.members 0 = some falseFamMember ∧
      axFalseEnv.members 1 = some falseRecMemberU ∧ ¬ AxiomFreeEnv' axFalseEnv ∧
      (∀ (N : Nat) (K : Nat → Nat), LOKt (fun _ => 0) N K axFalseProof) := by
  refine ⟨⟨axFalseEnvWfT⟩, rfl, rfl, fun h => h 2 axFalseMember rfl rfl, fun _ _ l hl => ?_⟩
  exact absurd hl (List.not_mem_nil _)

/-- The target without its axiom-freeness hypothesis is false. -/
theorem rcicConsistentEmpty_without_axiomFree_false :
    ¬ (∀ (E : ResolvedEnv), EnvWfT E → E.members 0 = some falseFamMember →
      E.members 1 = some falseRecMemberU →
      ∀ (n : Nat) (e : Expr Nat), HasTyT E n [] e (.const 0 []) → False) :=
  fun h => h axFalseEnv axFalseEnvWfT rfl rfl 0 _ axFalseProof

/-- `consistent4_G`'s class excludes the control, at its axiom step. -/
theorem axFalseEnv_not_classG : ¬ ClassG axFalseEnvWfT := fun h => h

end PSet

end Rcic.F3

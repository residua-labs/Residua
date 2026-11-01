import rcic.RcicF3NormPropTree

/-!
# Both unchanged whole-environment checks on the inhabited PropOnly group

The actual Prop tree environment supplies the existing W condition from
its admission walk and the existing D condition at every constant bound.
The same installed table already has a produced invariant and soundness.
This is a concrete checked positive-depth PropOnly instance, not a claim
about every admitted group or the distinguished False-prefix environment.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPropTreeChecks
open Rcic.Declarative Rcic.Model.PS Rcic.F3.StepWCheck
open Rcic.Declarative.PropTree
open PropTreeBounds (wft)

theorem w_checked : EnvWChecked wft := by
  refine ⟨True.intro, ?_⟩
  intro n hW _ _
  exact False.elim (hW (PropTreeBounds.walkClass n))

theorem w_check : Rcic.F3.StepWApex.envCheck wft = true :=
  (Rcic.F3.StepWApex.envCheck_pass_iff wft).mpr w_checked

theorem d_checked (k : Nat) : Rcic.F3.StepWDApex.EnvDChecked (fun _ => k) wft :=
  ⟨True.intro, NormPropTree.d_side k _⟩

theorem d_check (k : Nat) :
    Rcic.F3.StepWDApex.envCheck (fun _ => k) wft = true :=
  (Rcic.F3.StepWDApex.envCheck_pass_iff (fun _ => k) wft).mpr (d_checked k)

def Witness (P : Premises4) : Prop :=
  NormPropTree.Witness P ∧ Rcic.F3.StepWApex.envCheck wft = true ∧
  (∀ k : Nat, Rcic.F3.StepWDApex.envCheck (fun _ => k) wft = true ∧
    ∀ (σ : Nat → Nat) (n : Nat),
      EnvSound (mkM P (NormPropTree.table P)) σ (fun _ => k) eAll n)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormPropTree.component_witness P, w_check,
    fun k => ⟨d_check k, NormPropTree.env_sound P (fun _ => k)⟩⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormPropTreeChecks

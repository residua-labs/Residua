import rcic.RcicF3RawFamilyRecAt
import rcic.RcicF3TableSound
import rcic.RcicF3RawFamilyInductionAttack
import rcic.RcicF3RawFamilyIHBuilderAttack

/-!
# Actual height-omega recursion at an independent valuation

Every frame, environment and field-instance premise is supplied at the
original PendA W descriptor. The two minors erase to the proof value and
the produced target is tv True. The syntax valuation has the extra level 1;
the separate MinorAttack supplies the data-valued motive/IH spine there.
This is component non-vacuity, not universal StepAG. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace Rcic.F3.PSet.RawFamilyRecAtAttack
open Rcic.Declarative PiIndex RawFamily
open PendAWBridge (fd)

abbrev σ : Nat → Nat := RawFamilyIHBuilderAttack.σ
def K : Nat → Nat := fun _ => 1
noncomputable def base (P : Premises4) : Nat → List Nat → PSet.{4} := PendARoleW.table P
noncomputable def model (P : Premises4) : Interp.{4} := RawFamilyRec.model P (base P) fd

theorem tables (P : Premises4) :
    ∀ r vs, Equiv (base P r vs) (table P (base P) fd (frame P (base P) fd) r vs) := by
  apply table_equiv
  intro vs
  have h := PendARoleW.faithful P 4 PendAW.fam rfl vs
  rw [PendAWGroup.familyRole] at h
  exact h.trans (RawWGeneral.role_value P (base P) vs).symm

theorem environment (P : Premises4) : EnvSound (model P) σ K PendAW.pNode.E0 0 := by
  have hGI := (PendARoleW.gInv P 1) _ (fun _ _ => rfl)
    (base P) (PendARoleW.faithful P)
  have hI := hGI.2 PendAW.eAll (fun _ _ h => h)
  have he : EnvSound (mkM P (base P)) σ K PendAW.pNode.E0 0 :=
    envSound_of P (node_sub' PendAW.pNode)
      (fun r m hm => hGI.1 r m (node_sub' PendAW.pNode r m hm))
      (fun r m hm hk => hI r m (node_sub' PendAW.pNode r m hm) hk) σ 0
  exact TableSound.environment P (tables P) σ he

theorem bodies : BodiesOK PendAW.pNode.E0 σ K :=
  bodiesOK_node natEnvUWfT PendAW.membersT PendAW.pNode K (natEnvUWfT_classG.2 K) σ

theorem instances : ∀ j : Fin PendAW.pNode.a.constructors.length,
    ∀ A ∈ (PendAW.pNode.a.constructorViews j).fields, InstOK PendAW.pNode.E0 σ K A := by
  intro j A hA
  rcases j with ⟨j, hj⟩
  cases j with
  | zero => exact (List.not_mem_nil A hA).elim
  | succ j =>
    cases j with
    | zero =>
      have he : A = PendAW.field := List.mem_singleton.mp hA
      subst A
      intro r ls hr
      change (r, ls) ∈ [(4, [])] at hr
      cases List.mem_singleton.mp hr
      exact ⟨PendAW.fam, rfl, rfl, fun _ h => (List.not_mem_nil _ h).elim⟩
    | succ j => exact False.elim (by change j + 2 < 2 at hj; omega)

theorem omega_mem (P : Premises4) : fxZW P ∈ frame P (base P) fd [] (key [tyv fxS]) := by
  exact mem_congr_right (apply_ofFrame_ed P (base P) fd (frame P (base P) fd)
    (RawWFrame.raw_admissible P (base P)) [] [tyv fxS]
    (PendAWBridge.argsFit P (base P) pempty)) (RawWFrame.heightOmega_gap P (base P)).1

private theorem empty_minor_true (j : Nat) (args : List PSet.{4}) :
    fapps (([pempty, pempty] : List PSet.{4}).getD j pempty) args ∈
      (tv True : PSet.{4}) := by
  have hm : ([pempty, pempty] : List PSet.{4}).getD j pempty = pempty := by
    cases j with
    | zero => rfl
    | succ j => cases j <;> rfl
  rw [hm]
  exact mem_tv.mpr ⟨True.intro, fapps_pempty _⟩

/-- The fixed-parameter recursion theorem is used, with its local minor
contract proved and both actual minor slots supplied. -/
theorem produced (P : Premises4) :
    ∀ (i : Index.{4}) (z : PSet.{4}), RawFamilyRec.paramKey 1 i = key [tyv fxS] →
      z ∈ frame P (base P) fd [] i →
      RecPlan.nodeCore (model P) PendAW.pNode [pempty, pempty] z ∈ (tv True : PSet.{4}) := by
  have h := RawFamilyRec.produce_at_parameters_at P (base P) K PendAW.pNode [] σ
    PendAWLim.Typed.bounded (fun i hi => (Nat.not_lt_zero i hi).elim)
    (environment P) bodies instances (RawWFrame.raw_admissible P (base P))
    (RawFamilyInductionAttack.w_closed P (base P))
    (RawFamilyInductionAttack.w_mono P (base P)) (by change 1 ≠ 0; decide)
    [tyv fxS] [pempty, pempty] (fun _ _ => tv True) (fun _ _ _ _ => Equiv.rfl)
    (fun j _ _ _ _ _ _ => empty_minor_true j.val _)
  exact h

/-- All hypotheses of the changed recursion component are paid at the
height-omega value. The canonical empty vector cannot read this extra level. -/
theorem inhabited (P : Premises4) :
    RecPlan.nodeCore (model P) PendAW.pNode [pempty, pempty] (fxZW P) ∈ tv True ∧
    fxZW P ∈ frame P (base P) fd [] (key [tyv fxS]) ∧
    fxZW P ∉ El (fapps (famLim P (base P) fd []) [tyv fxS]) ∧
    σ 0 = 1 ∧ σ 0 ≠ σOf [] 0 := by
  exact ⟨produced P (key [tyv fxS]) (fxZW P) rfl (omega_mem P), omega_mem P,
    (RawWFrame.heightOmega_gap P (base P)).2, rfl, by decide⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ ((RecPlan.nodeCore (model P) PendAW.pNode [pempty, pempty] (fxZW P) ∈ tv True) →
      (Premises4 → False)) := by
  intro h
  exact h (inhabited P).1 P

end Rcic.F3.PSet.RawFamilyRecAtAttack

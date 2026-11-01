import rcic.RcicF3NormDataMember
import rcic.RcicF3NormDataRecAttack

/-!
# The complete DATA member producer at the original W fixture

The canonical W plan supplies its exact small closed normalized frame.
The generic constructor-prefix and stored-recursion producers then yield
AllSound and the actual stored recursor MemberSound at the installed table,
for every constant bound. No invariant or recursor package of the current
W group is passed to this composition: its predecessor is the produced Nat
invariant. The original height-omega member, actual typed stored minors and
nonempty produced recursion result are retained in the component witness.

This tests the public DATA member producer on the actual previously
refuting group. Universal small-frame production and stable DATA iota are
not concluded. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDataRecMemAttack
open Rcic.Declarative Rcic.Model.PS RawFamily
open RawDataRecAttack (base)

noncomputable abbrev plan : EvalPlan.Plan := NormPendAW.plan

theorem small_closed (P : Premises4) :
    ∃ A, Admissible (EvalPlanNormal.fd plan) A ∧
      Closed P (base P) (EvalPlanNormal.fd plan) A :=
  ⟨frame P (base P) (EvalPlanNormal.fd plan),
    NormPendAW.normalized_admissible P (base P),
    NormPendAW.normalized_closed P (base P)⟩

theorem matching_parameters : ∀ j : Fin plan.node.a.constructors.length,
    (plan.node.a.constructorViews j).parameters = plan.node.a.family.parameters :=
  fun j => (PendAWGroup.views plan.node j).1.trans
    (PendAWGroup.familyInfo plan.node).1.symm

theorem type_family : UniformType plan.node.a.family.resultLevel := by
  rw [(PendAWGroup.familyInfo plan.node).2.2]
  intro σ
  exact Nat.zero_lt_succ 0

/-- This call produces the actual stored-member soundness of the whole
W environment from the Nat predecessor and the exact small W frame. -/
theorem all_sound (P : Premises4) (k : Nat) :
    AllSound P (base P) (fun _ => k) PendAW.eAll :=
  NormDataMember.sound_of_small_frame P (base P) (fun _ => k)
    natEnvUWfT (f := 4) (fm := PendAW.fam)
    (ctors := [(5, PendAW.leaf), (6, PendAW.node)])
    (rr := 7) (rm := PendAW.recMem)
    rfl PendAWGroup.ctorClasses rfl PendAW.membersT
    PendAWGroup.walkAgree (PendAWGroup.boundG _) (PendAWGroup.boundDG k)
    matching_parameters (NormNatInvariant.gInv P _)
    (NormRole.envCtx PendAWGroup.wft) (EvalRole.envPlan PendAWGroup.wft)
    (fun _ _ => rfl) (fun _ _ => rfl) (NormPendAW.faithful P)
    (small_closed P) type_family

/-- The recursor-specific public composition is also instantiated
literally; its reader environment comes from the preceding bounded walk. -/
theorem member_sound (P : Premises4) (k : Nat) :
    MemberSound P (base P) (fun _ => k) 7 PendAW.recMem :=
  NormDataMember.member_sound_of_small_frame P (base P) (fun _ => k)
    natEnvUWfT (f := 4) (fm := PendAW.fam)
    (ctors := [(5, PendAW.leaf), (6, PendAW.node)])
    (rr := 7) (rm := PendAW.recMem)
    rfl PendAWGroup.ctorClasses rfl PendAW.membersT
    PendAWGroup.walkAgree (PendAWGroup.boundG _) (PendAWGroup.boundDG k)
    matching_parameters (NormNatInvariant.gInv P _)
    (NormRole.envCtx PendAWGroup.wft) (EvalRole.envPlan PendAWGroup.wft)
    (fun _ _ => rfl) (fun _ _ => rfl) (NormPendAW.faithful P)
    (small_closed P) type_family

def Witness (P : Premises4) : Prop :=
  NormDataRecAttack.Witness P ∧
  EvalPlanNormal.fd plan = PendAWBridge.fd ∧
  (∃ A, Admissible (EvalPlanNormal.fd plan) A ∧
    Closed P (base P) (EvalPlanNormal.fd plan) A) ∧
  (∀ k, AllSound P (base P) (fun _ => k) PendAW.eAll) ∧
  (∀ k, MemberSound P (base P) (fun _ => k) 7 PendAW.recMem) ∧
  fxZW P ∈ Ed (mkM P (base P)) (fapps (base P 4 []) [tyv fxS])

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormDataRecAttack.component_witness P, NormPendAW.normalized_descriptor,
    small_closed P, all_sound P, member_sound P, NormPendAW.installed_height_omega P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormDataRecMemAttack

import rcic.RcicF3PointwiseRole
import rcic.RcicF3PointwiseDataAttack

/-!
# Actual faithful installation of the separate interpretation at W

This is the new installer at the actual admitted W environment, with its
actual declaration arities and unchanged original plans. Its family entry
contains fxZW and has its stored family type. The Prop interpretation is
retained literally for every uniformly Prop descriptor.

No soundness invariant of this W table or universal DATA producer is
asserted. All earlier family components and this installation are composed
at the same Premises4. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseRoleAttack
open Rcic.Declarative PiIndex
open NormPendAW (plan)

noncomputable abbrev table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  PointwiseRole.table P PendAWGroup.wft

theorem metadata : PointwiseRole.AritiesAgree (PointwiseRole.arities PendAW.eAll) PendAW.eAll :=
  PointwiseRole.arities_agree PendAW.eAll

theorem faithful (P : Premises4) :
    EvalRole.Faithful (PointwiseRole.familyValue (PointwiseRole.arities PendAW.eAll))
      P (table P) (NormRole.envCtx PendAWGroup.wft)
      (EvalRole.envPlan PendAWGroup.wft) PendAW.eAll :=
  (PointwiseRole.table_spec P PendAWGroup.wft).2.1

theorem reads_closed (P : Premises4) :
    EvalRole.ReadsClosed (NormRole.envCtx PendAWGroup.wft)
      (EvalRole.envPlan PendAWGroup.wft) PendAW.eAll :=
  (PointwiseRole.table_spec P PendAWGroup.wft).2.2

theorem family_value (P : Premises4) (vs : List Nat) :
    Equiv (table P 4 vs)
      (PointwiseData.role P (table P) (EvalPlanNormal.fd plan)
        plan.node.a.family.member.arity vs) := by
  have h := faithful P 4 PendAW.fam rfl vs
  rw [NormPendAW.family_role] at h
  change Equiv (table P 4 vs)
    (PointwiseRole.familyValue (PointwiseRole.arities PendAW.eAll)
      P (table P) (EvalPlanNormal.fd plan) vs) at h
  rw [PointwiseRole.familyValue_data _ P _ _ NormDataRecMemAttack.type_family vs] at h
  have har : PointwiseRole.arities PendAW.eAll (EvalPlanNormal.fd plan).fref =
      plan.node.a.family.member.arity := PointwiseRole.arity_at_node metadata plan.node
  rw [har] at h
  exact h

theorem family_typed (P : Premises4) (vs : List Nat) :
    table P 4 vs ∈ Ed (mkM P (table P))
      (den (mkM P (table P)) (σOf vs) ρ0 (famType (EvalPlanNormal.fd plan))) :=
  mem_congr_left (family_value P vs).symm
    (PointwiseDataAttack.role_typed P (table P) vs)

theorem installed_height_omega (P : Premises4) :
    fxZW P ∈ Ed (mkM P (table P)) (fapps (table P 4 []) [tyv fxS]) :=
  mem_congr_right (ed_congr (mkM P (table P))
    (fapps_congr (family_value P []) [tyv fxS])).symm
    (PointwiseDataAttack.role_height_omega P (table P))

def Witness (P : Premises4) : Prop :=
  PointwiseDataAttack.Witness P ∧
  PointwiseRole.AritiesAgree (PointwiseRole.arities PendAW.eAll) PendAW.eAll ∧
  EvalRole.Faithful (PointwiseRole.familyValue (PointwiseRole.arities PendAW.eAll))
    P (table P) (NormRole.envCtx PendAWGroup.wft)
    (EvalRole.envPlan PendAWGroup.wft) PendAW.eAll ∧
  EvalRole.ReadsClosed (NormRole.envCtx PendAWGroup.wft)
    (EvalRole.envPlan PendAWGroup.wft) PendAW.eAll ∧
  (∀ vs, table P 4 vs ∈ Ed (mkM P (table P))
    (den (mkM P (table P)) (σOf vs) ρ0 (famType (EvalPlanNormal.fd plan)))) ∧
  fxZW P ∈ Ed (mkM P (table P)) (fapps (table P 4 []) [tyv fxS]) ∧
  (∀ α μ fd, UniformProp fd.resLevel → ∀ vs,
    PointwiseRole.familyValue α P μ fd vs = RawFamily.role P μ fd vs)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨PointwiseDataAttack.component_witness P, metadata, faithful P, reads_closed P,
    family_typed P, installed_height_omega P,
    fun α μ fd hp vs => PointwiseRole.familyValue_prop α P μ fd hp vs⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PointwiseRoleAttack

import rcic.RcicF3NormFieldMaskContext
import rcic.RcicF3RecFieldMaskTypingAttack

/-!
# The actual admitted W cache produces its recursive local relation

This witness invokes the group-level constructor-context producer, using
the real W cache, original bounds, checked parameter equality and Nat
predecessor. The source tuple contains the actual nonempty height-omega
branching function. Both original contexts fit; the produced masked
context does not fit the original recursive field type.

The new group invocation is at the family's canonical vector []. The
retained complete typing witness separately keeps the extra universe
slot 1, hidden beta/zeta domains and the dependent depth-three example.
Neither invocation claims a universal normalized-reader domain mask or
an all-universe small candidate. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormFieldMaskContextAttack
open Rcic.Declarative Rcic.Model.PS RawFamily RecFieldMask
open NormFreshHeadAttack (base C D model parameter admissible_C nodeIndex
  node_parameters node_fields arity)
open NormPendAW (plan)
open PendAWBridge (fd)

def marks : Marks := recursive 1 (fun _ => none)
def Γ : LCtx := [.assumption PendAW.field, .assumption (.sort (.succ .zero))]
def fieldType : Expr Nat := Declarative.lift 0 1 PendAW.field
noncomputable def ρ (P : Premises4) : Nat → PSet.{4} :=
  vcons (RawFamilyIHBuilderAttack.x P) (vcons parameter ρ0)
def masked : Nat → PSet.{4} := vcons pempty (vcons parameter ρ0)

/-- The public producer supplies every lookup fact from the actual
stored field certificate and the two original constructor fits. -/
theorem actual_context (P : Premises4) (bound : Nat) :
    Context P (base P) fd (C P) (σOf []) marks Γ (ρ P) masked := by
  have hC : Admissible (famDataOf plan.node.a) (C P) := by
    rw [NormPendAW.raw_descriptor]
    exact admissible_C P
  have hps : TelFits (mkM P (base P)) (σOf []) plan.node.a.family.parameters
      ρ0 [parameter] := by
    rw [(PendAWGroup.familyInfo plan.node).1]
    exact PendAWBridge.argsFit P (base P) pempty
  have hxs : TelFits (mkM P (table P (base P) (famDataOf plan.node.a) (C P)))
      (σOf []) (EvalPlanNormal.fields plan nodeIndex) (push [parameter] ρ0)
      [RawFamilyIHBuilderAttack.x P] := by
    rw [NormPendAW.raw_descriptor, NormPendAW.fields_eq, node_fields]
    refine ⟨?_, True.intro⟩
    have h := RawFamilyMinorAttack.raw_field_mem P (base P)
    change RawFamilyIHBuilderAttack.x P ∈ Ed (model P (C P))
      (den (model P (C P)) NormFreshHeadAttack.σ (push [parameter] ρ0)
        PendAW.field) at h
    rw [den_levels_closed (model P (C P)) NormFreshHeadAttack.σ
      (σOf []) PendAW.field rfl] at h
    exact h
  have h0 : evalTotal (σOf []) plan.node.a.family.resultLevel ≠ 0 := by
    rw [(PendAWGroup.familyInfo plan.node).2.2]
    change 1 ≠ 0
    decide
  have hp := NormFieldMaskContext.constructor_contexts P (base P) (fun _ => bound)
    plan PendAW.fam [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT (PendAWGroup.boundG _)
    (PendAWGroup.boundDG bound)
    (fun j => (PendAWGroup.views plan.node j).1.trans
      (PendAWGroup.familyInfo plan.node).1.symm)
    (NormNatInvariant.gInv P _) (NormRole.envCtx PendAWGroup.wft)
    (EvalRole.envPlan PendAWGroup.wft)
    (fun r hr => NormRole.envCtx_group_stable natEnvUWfT rfl
      PendAWGroup.ctorClasses rfl PendAW.membersT r hr)
    (fun r hr => EvalRole.envPlan_group_stable natEnvUWfT rfl
      PendAWGroup.ctorClasses rfl PendAW.membersT r hr)
    (fun r m hm => NormPendAW.faithful P r m
      (groupMembersT_preserve PendAW.membersT r m hm))
    (C P) hC [] arity.symm (fun _ h => (List.not_mem_nil _ h).elim) h0
    nodeIndex [parameter] [RawFamilyIHBuilderAttack.x P] hps hxs 1
    (by rw [node_fields]; exact Nat.le_refl 1)
  have hs : (plan.constructors nodeIndex).shapes = [.recursive 1] :=
    (plan.constructors nodeIndex).shapes_admitted.trans
      ((NormPendAWValue.node_shapes plan.node nodeIndex).trans
        (if_neg (by change ¬ (1 : Nat) = 0; decide)))
  rw [NormPendAW.raw_descriptor, node_parameters, node_fields, hs] at hp
  exact hp

/-- Projecting the produced recursive lookup retains the complete
dependent W field, rather than a chosen depth-only approximation. -/
theorem actual_origin (P : Premises4) (bound : Nat) :
    RecFieldOrigin.Origin (mkM P (base P)) fd (C P) 1
      (Ed (model P (C P)) (den (model P (C P)) (σOf []) (ρ P) fieldType))
      (Ed (model P (D P)) (den (model P (D P)) (σOf []) (ρ P) fieldType))
      (RawFamilyIHBuilderAttack.x P) :=
  (actual_context P bound 0 fieldType rfl).2

/-- The actual field is not an erasable proof. Thus the masking relation
is used without inventing a fitting erased constructor prefix. -/
theorem masked_not_fit (P : Premises4) :
    ¬ Fits (model P (C P)) (σOf []) Γ masked := by
  intro hmask
  have hz := fits_lookupType (model P (C P)) (σOf []) Γ masked hmask 0 fieldType rfl
  have hx := fits_lookupType (model P (C P)) (σOf []) Γ (ρ P)
    (NormFreshHeadAttack.constructor_prefixes P 1).1 0 fieldType rfl
  change pempty ∈ Ed (model P (C P))
    (den (model P (C P)) (σOf []) (ρ P) fieldType) at hz
  rcases dich_ed (model P (C P))
      (den (model P (C P)) (σOf []) (ρ P) fieldType) with hp | hn
  · exact RecFieldOriginCasesAttack.field_nonempty P (fun _ => 1) (hp _ hx)
  · exact hn hz

def Witness (P : Premises4) : Prop :=
  RecFieldMaskTypingAttack.Witness P ∧
  Fits (model P (C P)) (σOf []) Γ (ρ P) ∧
  Fits (model P (D P)) (σOf []) Γ (ρ P) ∧
  ¬ Fits (model P (C P)) (σOf []) Γ masked ∧
  ¬ Equiv (RawFamilyIHBuilderAttack.x P) pempty ∧
  (∀ _bound : Nat, Context P (base P) fd (C P) (σOf []) marks Γ (ρ P) masked ∧
    RecFieldOrigin.Origin (mkM P (base P)) fd (C P) 1
      (Ed (model P (C P)) (den (model P (C P)) (σOf []) (ρ P) fieldType))
      (Ed (model P (D P)) (den (model P (D P)) (σOf []) (ρ P) fieldType))
      (RawFamilyIHBuilderAttack.x P))

theorem component_witness (P : Premises4) : Witness P :=
  ⟨RecFieldMaskTypingAttack.component_witness P,
    (NormFreshHeadAttack.constructor_prefixes P 1).1,
    (NormFreshHeadAttack.constructor_prefixes P 1).2,
    masked_not_fit P, RecFieldOriginCasesAttack.field_nonempty P (fun _ => 1),
    fun bound => ⟨actual_context P bound, actual_origin P bound⟩⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormFieldMaskContextAttack
